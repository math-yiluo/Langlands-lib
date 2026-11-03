import Langlands.AlgebraicGeometry.FullProductFactorizationOver
import Langlands.AlgebraicGeometry.ClosedSieveAffineTests

/-! # Gluing full-product factorization loci -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FullProductFactorization

/-- The affine-target, affine-test closed-representability premise. -/
def AffineTargetRepresentable {S : Scheme.{u}} (X : Over S) : Prop :=
  ∀ (Y D : Over S) [IsAffine Y.left] (d : D ⟶ X ⊗ Y)
    [IsClosedImmersion d.left],
    ∃ (Z : Over S) (i : Z ⟶ Y), IsClosedImmersion i.left ∧
      ∀ (T : Over S) [IsAffine T.left] (t : T ⟶ Y),
        (∃ z : T ⟶ Z, z ≫ i = t) ↔
          ∃ q : X ⊗ T ⟶ D, q ≫ d = (X ◁ t)

/-- Closed representatives for affine targets and affine tests suffice for all
targets and all tests. The source and base are fixed throughout. -/
theorem of_affine_targets {S : Scheme.{u}} (X : Over S)
    (haff : AffineTargetRepresentable X)
    (Y D : Over S) (d : D ⟶ X ⊗ Y) [IsClosedImmersion d.left] :
    ∃ (Z : Over S) (i : Z ⟶ Y), IsClosedImmersion i.left ∧
      ∀ (T : Over S) (t : T ⟶ Y),
        (∃ z : T ⟶ Z, z ≫ i = t) ↔
          ∃ q : X ⊗ T ⟶ D, q ≫ d = (X ◁ t) := by
  let E := sieve X.hom Y.hom d.left
  have hchart : ∀ U : Y.left.affineOpens,
      ∃ (Z : Scheme.{u}) (i : Z ⟶ (U : Y.left.Opens).toScheme),
        IsClosedImmersion i ∧
          ClosedSieveAffineTests.AffineTestRepresents (E.pullback (U : Y.left.Opens).ι) i := by
    intro U
    let YU : Over S := Over.mk ((U : Y.left.Opens).ι ≫ Y.hom)
    let u : YU ⟶ Y := Over.homMk (U : Y.left.Opens).ι rfl
    let a := (X ◁ u).left
    let DU : Over S := Over.mk (pullback.snd d.left a ≫ (X ⊗ YU).hom)
    let dU : DU ⟶ X ⊗ YU := Over.homMk (pullback.snd d.left a) rfl
    have : IsAffine YU.left := U.property
    have : IsClosedImmersion dU.left := by
      change IsClosedImmersion (pullback.snd d.left a)
      infer_instance
    obtain ⟨Z, i, hi, hrep⟩ := haff YU DU dU
    refine ⟨Z.left, i.left, hi, ?_⟩
    intro T hT g
    let TO : Over S := Over.mk (g ≫ YU.hom)
    let t : TO ⟶ YU := Over.homMk g rfl
    have : IsAffine TO.left := hT
    have hbase :
        (∃ q : X ⊗ TO ⟶ DU, q ≫ dU = (X ◁ t)) ↔
          ∃ q : X ⊗ TO ⟶ D, q ≫ d = (X ◁ (t ≫ u)) := by
      rw [exists_over_lift_iff, exists_over_lift_iff]
      have hcomp : (X ◁ (t ≫ u)).left = (X ◁ t).left ≫ a := by
        rw [whiskerLeft_comp]
        rfl
      rw [hcomp]
      constructor
      · rintro ⟨q, hq⟩
        change q ≫ pullback.snd d.left a = (X ◁ t).left at hq
        refine ⟨q ≫ pullback.fst d.left a, ?_⟩
        rw [Category.assoc, pullback.condition, ← Category.assoc, hq]
      · rintro ⟨q, hq⟩
        exact ⟨pullback.lift q (X ◁ t).left hq, pullback.lift_snd _ _ _⟩
    have hmem : E (g ≫ (U : Y.left.Opens).ι) ↔
        ∃ q : X ⊗ TO ⟶ D, q ≫ d = (X ◁ (t ≫ u)) :=
      mem_iff_over d (t ≫ u)
    exact (exists_over_lift_iff i t).symm.trans ((hrep TO t).trans (hbase.trans hmem.symm))
  obtain ⟨Z, i, hi, hrep⟩ := ClosedSieveAffineTests.glue Scheme.fpqcTopology
    Scheme.zariskiTopology_le_fpqcTopology E (fpqc_isClosed X.hom Y.hom d.left) hchart
  let ZO : Over S := Over.mk (i ≫ Y.hom)
  let iO : ZO ⟶ Y := Over.homMk i rfl
  refine ⟨ZO, iO, hi, fun T t ↦ ?_⟩
  exact (exists_over_lift_iff iO t).trans ((hrep T.left t.left).trans (mem_iff_over d t))

end Langlands.AlgebraicGeometry.FullProductFactorization
