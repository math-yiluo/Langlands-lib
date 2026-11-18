import Langlands.GroupScheme.Torus.ClosedImmersionLocus
import Langlands.GroupScheme.Torus.ClosedImmersionLocusAffine
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.Descent.EtaleReflection
import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Closed immersions from isotrivial groups of multiplicative type over local bases -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MultiplicativeTypeLocalClosed

section Algebra

open CommutativeAlgebra

variable {R : Type u} [CommRing R] {M : Type u} [AddCommMonoid M]
  {B : Type u} [CommRing B] [Bialgebra R B]

/-- A surjective scalar extension to a nontrivial ring has, in every degree, a coefficient
whose image is nonzero. -/
theorem exists_coefficient_ne_zero (φ : B →ₐ[R] AddMonoidAlgebra R M)
    (K : Type u) [CommRing K] [Nontrivial K] [Algebra R K]
    (hφ : Function.Surjective (DiagonalCoalgebraLocus.scalarExtension φ K)) (m : M) :
    ∃ b : B, algebraMap R K ((φ b).coeff m) ≠ 0 := by
  by_contra! h
  have hz : ∀ z : K ⊗[R] B, (DiagonalCoalgebraLocus.scalarExtension φ K z).coeff m = 0 := by
    intro z
    induction z with
    | tmul a b => simp [h b]
    | add a b ha hb => simp [ha, hb]
  obtain ⟨z, hz'⟩ := hφ (AddMonoidAlgebra.single m 1)
  have := hz z
  rw [hz'] at this
  simp at this

/-- If a bialgebra map into a monoid algebra becomes surjective modulo every maximal
ideal, then every degree-`m` monomial lies in its image. -/
theorem single_one_mem_range_of_forall_maximal (φ : B →ₐc[R] AddMonoidAlgebra R M)
    (h : ∀ n : Ideal R, n.IsMaximal →
      Function.Surjective (DiagonalCoalgebraLocus.scalarExtension φ.toAlgHom (R ⧸ n)))
    (m : M) :
    AddMonoidAlgebra.single m 1 ∈ φ.toAlgHom.range := by
  let P : Ideal R :=
    { carrier := {r | AddMonoidAlgebra.single m r ∈ φ.toAlgHom.range}
      zero_mem' := by
        change AddMonoidAlgebra.single m 0 ∈ φ.toAlgHom.range
        rw [AddMonoidAlgebra.single_zero]
        exact φ.toAlgHom.range.zero_mem
      add_mem' := by
        intro a b ha hb
        change AddMonoidAlgebra.single m (a + b) ∈ φ.toAlgHom.range
        rw [AddMonoidAlgebra.single_add]
        exact φ.toAlgHom.range.add_mem ha hb
      smul_mem' := by
        intro c a ha
        change AddMonoidAlgebra.single m (c * a) ∈ φ.toAlgHom.range
        rw [← AddMonoidAlgebra.smul_single']
        exact φ.toAlgHom.range.smul_mem ha c }
  have hP : P = ⊤ := by
    by_contra hne
    obtain ⟨n, hn, hPn⟩ := Ideal.exists_le_maximal P hne
    have hnt : Nontrivial (R ⧸ n) := Ideal.Quotient.nontrivial_iff.mpr hn.ne_top
    obtain ⟨b, hb⟩ := exists_coefficient_ne_zero φ.toAlgHom (R ⧸ n) (h n hn) m
    apply hb
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hPn (DiagonalCoalgebraImage.single_coefficient_mem_range φ b m)
  have h1 : (1 : R) ∈ P := hP ▸ Submodule.mem_top
  exact h1

/-- A bialgebra map into a monoid algebra is surjective as soon as it becomes surjective
after reduction modulo every maximal ideal of the base. -/
theorem surjective_of_forall_maximal (φ : B →ₐc[R] AddMonoidAlgebra R M)
    (h : ∀ n : Ideal R, n.IsMaximal →
      Function.Surjective (DiagonalCoalgebraLocus.scalarExtension φ.toAlgHom (R ⧸ n))) :
    Function.Surjective φ.toAlgHom :=
  DiagonalCoalgebraLocus.surjective_of_generators_mem φ.toAlgHom Set.univ
    AddSubmonoid.closure_univ
    (fun m _ => single_one_mem_range_of_forall_maximal φ h m)

end Algebra

section Transport

variable {S : Scheme.{u}} {H H' G G' : GroupScheme S}

/-- Being a closed subgroup inclusion is invariant under isomorphisms of source and
target compatible with the two inclusions. -/
theorem isClosedSubgroup_iff_of_comm {i : H ⟶ G} {j : H' ⟶ G'} (a : H ≅ H') (b : G ≅ G')
    (w : i ≫ b.hom = a.hom ≫ j) : IsClosedSubgroup i ↔ IsClosedSubgroup j := by
  have hi : i = a.hom ≫ j ≫ b.inv := by
    rw [← reassoc_of% w, Iso.hom_inv_id, Category.comp_id]
  subst hi
  let ha : IsIso a.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso a.hom
  let hb : IsIso b.inv.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso b.inv
  change IsClosedImmersion (a.hom.hom.hom.left ≫ j.hom.hom.left ≫ b.inv.hom.hom.left) ↔
    IsClosedImmersion j.hom.hom.left
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]

/-- Base change along a composite agrees with the iterated base change for the closed
subgroup property. -/
theorem isClosedSubgroup_baseChange_comp_iff {S' S'' : Scheme.{u}} (a : S' ⟶ S)
    (b : S'' ⟶ S') (i : H ⟶ G) :
    IsClosedSubgroup ((GroupScheme.baseChange (b ≫ a)).map i) ↔
      IsClosedSubgroup ((GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map i)) :=
  TorusClosedImmersionLocus.closed_comp_baseChange_iff a b i

end Transport

section Local

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The residue map of a finite local algebra to a residue field of the algebra. -/
def residueLift (R : Type u) [CommRing R] [Algebra A R] [Algebra.IsIntegral A R]
    (n : Ideal R) [n.IsMaximal] : IsLocalRing.ResidueField A →+* R ⧸ n :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A (R ⧸ n)) (by
    intro a ha
    have hmax : (n.under A).IsMaximal := inferInstance
    rw [← IsLocalRing.eq_maximalIdeal hmax] at ha
    rw [IsScalarTower.algebraMap_apply A R (R ⧸ n), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact ha)

theorem specMap_residueLift (R : Type u) [CommRing R] [Algebra A R] [Algebra.IsIntegral A R]
    (n : Ideal R) [n.IsMaximal] :
    Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R) (R ⧸ n))) ≫
        Spec.algebraMap A R =
      Spec.map (CommRingCat.ofHom (residueLift R n)) ≫
        Spec.algebraMap A (IsLocalRing.ResidueField A) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- **Closed immersions over a local base.** Let `A` be a local ring, `R` a finite
`A`-algebra with `Spec R → Spec A` étale and surjective, `H` a group over `Spec A`
which becomes diagonalizable over `Spec R`, and `G` an affine group over `Spec A`.
If the special fibre of `f : H ⟶ G` is a closed immersion, then so is `f`. -/
theorem isClosedSubgroup_of_finite_split (R : Type u) [CommRing R] [Algebra A R]
    [Module.Finite A R] [Etale (Spec.algebraMap A R)] [Surjective (Spec.algebraMap A R)]
    {H G : GroupScheme (Spec (CommRingCat.of A))} [IsAffineHom G.X.hom]
    (hH : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap A R)).obj H))
    (f : H ⟶ G)
    (hf : IsClosedSubgroup
      ((GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f)) :
    IsClosedSubgroup f := by
  classical
  let p := Spec.algebraMap A R
  obtain ⟨Λ, _, _, ⟨eH⟩⟩ := hH
  apply IsClosedSubgroup.of_baseChange_of_etale p
  let GR := (GroupScheme.baseChange p).obj G
  have : IsAffine GR.X.left := by
    change IsAffine (Limits.pullback G.X.hom p)
    infer_instance
  let e : TorusClosedImmersionLocus.diagonalSource (CommRingCat.of R) Λ ≅
      (GroupScheme.baseChange p).obj H :=
    Diagonalizable.hopfSpecIso (CommRingCat.of R) Λ ≪≫
      Diagonalizable.relativeModelIso (CommRingCat.of R) Λ ≪≫ eH.symm
  let i : TorusClosedImmersionLocus.diagonalSource (CommRingCat.of R) Λ ⟶ GR :=
    e.hom ≫ (GroupScheme.baseChange p).map f
  suffices hi : IsClosedSubgroup i from
    (isClosedSubgroup_iff_of_comm e (Iso.refl _) (by simp [i])).mp hi
  let φ := TorusClosedImmersionLocus.diagonalCoordinateMap i
  have hφ : Function.Surjective φ.toAlgHom := by
    apply surjective_of_forall_maximal φ
    intro n hn
    have := hn
    rw [← TorusClosedImmersionLocus.diagonal_closed_iff i (R ⧸ n),
      TorusClosedImmersionLocus.closed_baseChange_precomp_iso_iff]
    change IsClosedSubgroup
      ((GroupScheme.baseChange _).map ((GroupScheme.baseChange p).map f))
    rw [← isClosedSubgroup_baseChange_comp_iff, specMap_residueLift R n,
      isClosedSubgroup_baseChange_comp_iff]
    exact hf.baseChange _
  have hc : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom φ.toAlgHom.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hφ
  have hcomp : IsClosedImmersion
      (i.hom.hom.left ≫ (AffineCoordinates.hopfSpecIso GR).inv.hom.hom.left) := by
    change IsClosedImmersion ((i ≫ (AffineCoordinates.hopfSpecIso GR).inv).hom.hom.left)
    rw [← TorusClosedImmersionLocus.diagonalCoordinateMap_map i]
    exact hc
  let he : IsIso (AffineCoordinates.hopfSpecIso GR).inv.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso (AffineCoordinates.hopfSpecIso GR).inv
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ _).mp hcomp

/-- **Closed immersions over a local base, for an arbitrary finite étale splitting.** Let
`A` be a local ring, `G` an affine group over `Spec A` and `H` a group over `Spec A` which
becomes diagonalizable after some finite étale surjective `S' ⟶ Spec A`. If the special
fibre of `f : H ⟶ G` is a closed immersion, then so is `f`. -/
theorem isClosedSubgroup_of_isotrivial
    {H G : GroupScheme (Spec (CommRingCat.of A))} [IsAffineHom G.X.hom]
    (hsplit : ∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of A)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        RelativeMultiplicativeType.IsDiagonalizable ((GroupScheme.baseChange p).obj H))
    (f : H ⟶ G)
    (hf : IsClosedSubgroup
      ((GroupScheme.baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).map f)) :
    IsClosedSubgroup f := by
  obtain ⟨S', p, hfin, het, hsurj, hH⟩ := hsplit
  have : IsAffine S' := isAffine_of_isAffineHom p
  let R : CommRingCat.{u} := Γ(S', ⊤)
  let q : Spec R ⟶ Spec (CommRingCat.of A) := S'.isoSpec.inv ≫ p
  let φ : CommRingCat.of A ⟶ R := Spec.preimage q
  let : Algebra A R := φ.hom.toAlgebra
  have hq : Spec.algebraMap A R = q := Spec.map_preimage q
  have : Module.Finite A R := by
    have hqf : IsFinite q := inferInstance
    rw [← hq, IsFinite.SpecMap_iff] at hqf
    exact RingHom.finite_algebraMap.mp hqf
  have : Etale (Spec.algebraMap A R) := by
    rw [hq]
    infer_instance
  have : Surjective (Spec.algebraMap A R) := by
    rw [hq]
    infer_instance
  have hH' : RelativeMultiplicativeType.IsDiagonalizable
      ((GroupScheme.baseChange (Spec.algebraMap A R)).obj H) := by
    rw [hq]
    exact RelativeMultiplicativeType.IsDiagonalizable.of_iso
      (baseChangeCompIso p S'.isoSpec.inv H) (hH.baseChange _)
  exact isClosedSubgroup_of_finite_split R hH' f hf

end Local

end Langlands.GroupScheme.MultiplicativeTypeLocalClosed
