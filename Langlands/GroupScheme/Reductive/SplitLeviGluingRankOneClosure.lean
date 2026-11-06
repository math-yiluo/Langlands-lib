import Langlands.GroupScheme.Absolute.TripleCellGeneration
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Rational points of the three-factor cell are dense -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k] {H M Z A : GroupScheme (Spec (CommRingCat.of k))}

/-- The rational points `x * y * w` of `H` with `x`, `y` and `w` rational points of the
images of `m`, `z` and `a`. -/
def rationalTripleProduct (m : M ⟶ H) (z : Z ⟶ H) (a : A ⟶ H) :
    Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :=
  ((SubgroupFunctor.range m).carrier (Over.mk (𝟙 _)) :
      Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) *
    ((SubgroupFunctor.range z).carrier (Over.mk (𝟙 _)) :
      Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) *
    ((SubgroupFunctor.range a).carrier (Over.mk (𝟙 _)) :
      Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X))

theorem rationalTripleProduct_eq (m : M ⟶ H) (z : Z ⟶ H) (a : A ⟶ H) :
    rationalTripleProduct m z a =
      ((SubgroupFunctor.range m).carrier (Over.mk (𝟙 _)) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) *
        ((SubgroupFunctor.range z).carrier (Over.mk (𝟙 _)) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) *
        ((SubgroupFunctor.range a).carrier (Over.mk (𝟙 _)) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)) :=
  rfl

/-- A rational point located in the image of an open three-factor cell is a product of
rational points of the three factors. -/
theorem mem_rationalTripleProduct_of_mem_range (m : M ⟶ H) (z : Z ⟶ H) (a : A ⟶ H)
    (hopen : IsOpenImmersion (Dynamic.tripleCellMultiplication m z a).left)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (hx : x.left (IsLocalRing.closedPoint k) ∈
      Set.range (Dynamic.tripleCellMultiplication m z a).left) :
    x ∈ rationalTripleProduct m z a := by
  let c := Dynamic.tripleCellMultiplication m z a
  have : Subsingleton (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hrange : Set.range x.left ⊆ Set.range c.left := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint k)]
    exact hx
  let l := IsOpenImmersion.lift c.left x.left hrange
  have hl : l ≫ c.left = x.left := IsOpenImmersion.lift_fac c.left x.left hrange
  have hlw : l ≫ (M.X ⊗ (Z.X ⊗ A.X)).hom = (Over.mk (𝟙 (Spec (CommRingCat.of k)))).hom := by
    rw [← Over.w c, ← Category.assoc, hl, Over.w x]
  let y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ M.X ⊗ (Z.X ⊗ A.X) := Over.homMk l hlw
  have hy : y ≫ c = x := Over.OverMorphism.ext hl
  have hsplit : y = lift (y ≫ fst M.X (Z.X ⊗ A.X))
      (lift (y ≫ snd M.X (Z.X ⊗ A.X) ≫ fst Z.X A.X)
        (y ≫ snd M.X (Z.X ⊗ A.X) ≫ snd Z.X A.X)) := by
    ext1
    · simp
    · ext1 <;> simp
  rw [← hy, hsplit, Dynamic.lift_tripleCellMultiplication, ← mul_assoc]
  refine Set.mul_mem_mul (Set.mul_mem_mul ?_ ?_) ?_
  · exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
  · exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
  · exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩

/-- Over an algebraically closed field, if the three-factor multiplication is an open
immersion with dense image, then every rational point of `H` lies in the closure of the
rational three-factor products. -/
theorem rationalPointClosure_rationalTripleProduct_eq_univ [IsAlgClosed k]
    [LocallyOfFiniteType H.X.hom] (m : M ⟶ H) (z : Z ⟶ H) (a : A ⟶ H)
    (hopen : IsOpenImmersion (Dynamic.tripleCellMultiplication m z a).left)
    (hdense : IsDominant (Dynamic.tripleCellMultiplication m z a).left) :
    rationalPointClosure H (rationalTripleProduct m z a) = Set.univ := by
  let c := Dynamic.tripleCellMultiplication m z a
  have : JacobsonSpace H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  have hd : Dense (rationalPointImage H (rationalTripleProduct m z a)) := by
    refine dense_iff_inter_open.mpr fun U hU hne => ?_
    have hUc : (U ∩ Set.range c.left).Nonempty :=
      c.left.denseRange.inter_open_nonempty U hU hne
    obtain ⟨y, ⟨hyU, hyc⟩, hyclosed⟩ := nonempty_inter_closedPoints hUc
      (hU.inter c.left.isOpenEmbedding.isOpen_range).isLocallyClosed
    let p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X :=
      Over.homMk (pointOfClosedPoint H.X.hom y hyclosed)
        (pointOfClosedPoint_comp H.X.hom y hyclosed)
    have hp : p.left (IsLocalRing.closedPoint k) = y := pointOfClosedPoint_apply _ _ _ _
    refine ⟨y, hyU, p, ?_, hp⟩
    exact mem_rationalTripleProduct_of_mem_range m z a hopen p (hp ▸ hyc)
  refine Set.eq_univ_of_forall fun x => ?_
  change x.left (IsLocalRing.closedPoint k) ∈ closure (rationalPointImage H _)
  rw [hd.closure_eq]
  exact Set.mem_univ _

/-- **Rational density of the dynamic three-factor cell.** For a cocharacter `χ` of a smooth
connected affine group `H` over an algebraically closed field and any representatives `m`,
`z`, `a` of `U(-χ)`, `Z(χ)` and `U(χ)`, every rational point of `H` lies in the closure of the
rational products `x * y * w` with `x`, `y`, `w` rational points of the three factors. -/
theorem rationalPointClosure_dynamicTripleProduct_eq_univ [IsAlgClosed k]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ H) {m : M ⟶ H} {z : Z ⟶ H} {a : A ⟶ H}
    (hm : (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy m)
    (hz : (Dynamic.centralizer χ).IsRepresentedBy z)
    (ha : (Dynamic.unipotent χ).IsRepresentedBy a) :
    rationalPointClosure H (rationalTripleProduct m z a) = Set.univ :=
  rationalPointClosure_rationalTripleProduct_eq_univ m z a
    (Dynamic.isOpenImmersion_tripleCellMultiplication χ hm hz ha)
    (Dynamic.isDominant_tripleCellMultiplication χ hm hz ha)

end Langlands.GroupScheme.LeviGluing
