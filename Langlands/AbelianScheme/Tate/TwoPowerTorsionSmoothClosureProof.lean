import Langlands.AlgebraicGeometry.ClosedPointHomogeneousSmoothProof
import Langlands.AbelianScheme.Tate.TwoPowerTorsionSmoothClosureStatement
import Langlands.AbelianScheme.Tate.TwoPowerTorsionReducedClosureProof

/-! # Smoothness of the reduced actual torsion closure from translation restrictions -/

noncomputable section

open CategoryTheory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : AbelianScheme (Spec (CommRingCat.of K)))

omit [IsAlgClosed K] in
private lemma unit_comp_mulRight
    (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) :
    (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) ≫
      (GrpObj.mulRight s).hom = s := by
  change (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) ≫
    ((𝟙 A.X) * (toUnit A.X ≫ s)) = s
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc]
  have h : (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) ≫
      toUnit A.X = 𝟙 _ := toUnit_unique _ _
  rw [h, Category.id_comp, one_mul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma smooth_of_twoPowerTorsionClosureRestrictions
    (Y : Scheme.{u}) (i : Y ⟶ A.X.left) [IsClosedImmersion i] [IsReduced Y]
    (hi : Set.range i = closure (twoPowerTorsionLocus A))
    (e : Spec (CommRingCat.of K) ⟶ Y)
    (he : e ≫ i = (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X).left)
    (htrans : ∀ (s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X),
      s.left (default : Spec (CommRingCat.of K)) ∈ closure (twoPowerTorsionLocus A) →
      ∃ t : Y ≅ Y, t.hom ≫ i = i ≫ (GrpObj.mulRight s).hom.left) :
    Smooth (i ≫ A.X.hom) := by
  let p := i ≫ A.X.hom
  have : LocallyOfFiniteType p := inferInstance
  apply Langlands.AlgebraicGeometry.closedPointHomogeneousSmooth K Y p
  intro x y hx hy
  let x' := pointOfClosedPoint p x hx
  let y' := pointOfClosedPoint p y hy
  let sx : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X :=
    Over.homMk (x' ≫ i) (by
      change x' ≫ p = 𝟙 _
      exact pointOfClosedPoint_comp p x hx)
  let sy : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X :=
    Over.homMk (y' ≫ i) (by
      change y' ≫ p = 𝟙 _
      exact pointOfClosedPoint_comp p y hy)
  have hsx : sx.left (default : Spec (CommRingCat.of K)) ∈
      closure (twoPowerTorsionLocus A) := by
    rw [← hi]
    exact ⟨x' (default : Spec (CommRingCat.of K)), rfl⟩
  have hsy : sy.left (default : Spec (CommRingCat.of K)) ∈
      closure (twoPowerTorsionLocus A) := by
    rw [← hi]
    exact ⟨y' (default : Spec (CommRingCat.of K)), rfl⟩
  obtain ⟨tx, htx⟩ := htrans sx hsx
  obtain ⟨ty, hty⟩ := htrans sy hsy
  have htxe : e ≫ tx.hom = x' := by
    apply (cancel_mono i).mp
    rw [Category.assoc, htx, ← Category.assoc, he]
    exact congrArg Over.Hom.left (unit_comp_mulRight A sx)
  have htye : e ≫ ty.hom = y' := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hty, ← Category.assoc, he]
    exact congrArg Over.Hom.left (unit_comp_mulRight A sy)
  have htxp : tx.hom ≫ p = p := by
    dsimp only [p]
    rw [← Category.assoc, htx, Category.assoc, Over.w]
  have htyp : ty.hom ≫ p = p := by
    dsimp only [p]
    rw [← Category.assoc, hty, Category.assoc, Over.w]
  let α := tx.symm ≪≫ ty
  refine ⟨α, ?_, ?_⟩
  · change tx.inv ≫ ty.hom ≫ p = p
    rw [htyp]
    calc
      tx.inv ≫ p = tx.inv ≫ tx.hom ≫ p := by rw [htxp]
      _ = p := by simp
  · have hxy : x' ≫ α.hom = y' := by
      dsimp only [α, Iso.trans_hom, Iso.symm_hom]
      rw [← htxe]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using htye
    simpa [x', y'] using congrArg
      (fun q : Spec (CommRingCat.of K) ⟶ Y =>
        q (default : Spec (CommRingCat.of K))) hxy

/-- The actual torsion closure has a smooth closed realization. -/
theorem twoPowerTorsionSmoothClosure_exists :
    TwoPowerTorsionSmoothClosureStatement.{u} := by
  intro K _ _ A
  obtain ⟨Y, i, hi, hred, hrange, ⟨e, he⟩, hv, htrans⟩ := twoPowerTorsionReducedClosure_exists K A
  have : IsClosedImmersion i := hi
  have : IsReduced Y := hred
  exact ⟨Y, i, hi,
    smooth_of_twoPowerTorsionClosureRestrictions A Y i hrange e he htrans,
    hrange, ⟨e, he⟩, hv, htrans⟩

end Langlands.AbelianScheme.Tate
