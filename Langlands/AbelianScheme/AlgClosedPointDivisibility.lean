import Langlands.AbelianScheme.AlgClosedPointDivisibilityStatement
import Langlands.AbelianScheme.AlgClosedIsogenyPointLifting
import Langlands.AbelianScheme.MultiplicationEtale

/-! # Divisibility of geometric points of abelian schemes -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

/-- Over a field, multiplication by a natural number that is nonzero in the
field is étale on an abelian scheme. -/
theorem multiplication_etale_of_field {K : Type u} [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (m : ℕ) (hm : (m : K) ≠ 0) :
    Etale (GroupScheme.multiplication A.toGrp (m : ℤ)).hom.hom.left := by
  have hpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm Nat.cast_zero)
  have hunit : IsUnit ((m : ℕ) : Γ(Spec (CommRingCat.of K), ⊤)) := by
    simpa using (Ne.isUnit hm).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  exact multiplicationEtale _ A m hpos hunit

/-- Over a field, multiplication by a natural number that is nonzero in the
field is surjective on an abelian scheme. -/
theorem multiplication_surjective_of_field {K : Type u} [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (m : ℕ) (hm : (m : K) ≠ 0) :
    Surjective (GroupScheme.multiplication A.toGrp (m : ℤ)).hom.hom.left := by
  have := multiplication_etale_of_field A m hm
  set f := (GroupScheme.multiplication A.toGrp (m : ℤ)).hom.hom.left
  have hw : f ≫ A.X.hom = A.X.hom := Over.w _
  have : UniversallyClosed (f ≫ A.X.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed f := UniversallyClosed.of_comp_of_isSeparated f A.X.hom
  have : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : ConnectedSpace A.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.X.hom
  have hclopen : IsClopen (Set.range f) :=
    ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
  have hne : (Set.range f).Nonempty := by
    obtain ⟨z⟩ : Nonempty A.X.left := by
      obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
      obtain ⟨z, -⟩ := A.X.hom.surjective t
      exact ⟨z⟩
    exact ⟨f z, z, rfl⟩
  exact ⟨Set.range_eq_univ.mp (hclopen.eq_univ hne)⟩

/-- Every point of an abelian scheme valued in an algebraically closed field is
divisible by any natural number that is nonzero in the field. -/
theorem algClosedPointDivisibility : AlgClosedPointDivisibilityStatement.{u} := by
  intro S B K _ _ s m hm y
  let BK := (baseChange s).obj B
  let g := (GroupScheme.multiplication B.toGrp (m : ℤ)).hom.hom
  let f : pullback B.X.hom s ⟶ pullback B.X.hom s :=
    (GroupScheme.multiplication BK.toGrp (m : ℤ)).hom.hom.left
  have : Etale f := multiplication_etale_of_field BK m hm
  have : Surjective f := multiplication_surjective_of_field BK m hm
  have hf : f = ((Over.pullback s).map g).left := by
    change ((GroupScheme.multiplication ((Over.pullback s).mapGrp.obj B.toGrp)
      (m : ℤ)).hom.hom.left) = _
    rw [← GroupScheme.multiplication_baseChange s B.toGrp (m : ℤ)]
    rfl
  have hfst : f ≫ pullback.fst B.X.hom s = pullback.fst B.X.hom s ≫ g.left := by
    rw [hf]
    exact pullback.lift_fst _ _ _
  have hsnd : f ≫ pullback.snd B.X.hom s = pullback.snd B.X.hom s :=
    Over.w (GroupScheme.multiplication BK.toGrp (m : ℤ)).hom.hom
  let y' : Spec (CommRingCat.of K) ⟶ pullback B.X.hom s :=
    pullback.lift y.left (𝟙 _) (by simp)
  obtain ⟨a, ha⟩ := exists_point_lift_of_locallyOfFiniteType_surjective f y'
  have haS : a ≫ pullback.snd B.X.hom s = 𝟙 _ := by
    rw [← hsnd, ← Category.assoc, ha, pullback.lift_snd]
  refine ⟨Over.homMk (a ≫ pullback.fst B.X.hom s) ?_, ?_⟩
  · change (a ≫ pullback.fst B.X.hom s) ≫ B.X.hom = s
    rw [Category.assoc, pullback.condition, ← Category.assoc, haS, Category.id_comp]
  · rw [← zpow_natCast, ← GroupScheme.points_multiplication]
    ext1
    change (a ≫ pullback.fst B.X.hom s) ≫ g.left = y.left
    rw [Category.assoc, ← hfst, ← Category.assoc, ha, pullback.lift_fst]

end Langlands.AbelianScheme
