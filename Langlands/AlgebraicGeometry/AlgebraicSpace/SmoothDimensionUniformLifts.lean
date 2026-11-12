import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionFieldPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionModelGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.OriginalBaseUniformLangWeilLifts

/-! # Uniform lifts without a constant relative dimension hypothesis -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Global.AdelicSpaceProperModelReduction

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionUniformLifts

variable (C : Type u) [CommRing C] [IsNoetherianRing C]
  [Algebra (ULift.{u} ℤ) C] [LocallyOfFiniteType (Spec.algebraMap (ULift.{u} ℤ) C)]

/-- Assuming the exact space estimate, a smooth connected-fibre map of separated
finite-type spaces has one residue-field surjectivity bound, with no hypothesis
that its relative dimension is constant. -/
theorem exists_uniform_field_surjectivity (hLW : SpaceUniformLangWeilStatement.{u})
    (X Y : AlgebraicSpace (Spec (CommRingCat.of C))) (f : X ⟶ Y)
    (hXs : IsSeparated X) (hXft : FiniteTypeOverRing C X)
    (hYs : IsSeparated Y) (hYft : FiniteTypeOverRing C Y)
    (hf : IsSmoothMorphism f) (hfc : HasGeometricallyConnectedFibres f) :
    ∃ c : ℝ, 0 < c ∧ ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra C κ],
      c ^ 2 < (Nat.card κ : ℝ) →
        Function.Surjective (RingPoints.map f : RingPoints C X κ → RingPoints C Y κ) := by
  classical
  have hX := finitePresentationAtlas hXft
  have hY := finitePresentationAtlas hYft
  have hYqs := quasiSeparated_of_separated hYs
  let d := smoothTargetPointDimensions hX hY hYqs hf hfc.isSurjectiveMorphism hfc
  let := Fintype.ofFinite d.Index
  have hstrata (n : d.Index) :
      ∃ c : ℝ, 0 < c ∧ ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra C κ]
        (x : RingPoints C (d.targetSpace n.val) κ),
        |(Nat.card {y : RingPoints C (d.sourceSpace n.val) κ //
            RingPoints.map (d.restrictedMap n.val) y = x} : ℝ) -
            (Nat.card κ : ℝ) ^ n.val| ≤
          c * (Nat.card κ : ℝ) ^ ((n.val : ℝ) - 1 / 2) := by
    obtain ⟨U, V, a, b, φ, _, _, ha, hs, hb, _, _, _, hφ, hw⟩ :=
      d.restrictedMap_fixedDimensionChart hX hY hYqs hf n.val
    let chart : EtaleMorphismChart (d.restrictedMap n.val) :=
      ⟨U, V, a, b, φ, ha, hb, hw⟩
    exact OriginalBaseUniformLangWeilLifts.exists_bound C hLW
      (d.targetSpace n.val) (d.sourceSpace n.val) (d.restrictedMap n.val) n.val
      (d.targetSpace_isQuasiSeparated hYqs n.val)
      (finiteType_of_finitePresentationAtlas (d.targetSpace_finitePresentation hY n.val))
      chart hs hφ (d.restrictedMap_separated hXs n.val)
      (d.restrictedMap_quasiCompact hX hYqs n.val)
      (d.restrictedMap_surjective hfc n.val) (d.restrictedMap_connected hfc n.val)
  choose c hc hb using hstrata
  let cAll : ℝ := 1 + ∑ n : d.Index, c n
  have hsum : 0 ≤ ∑ n : d.Index, c n := Finset.sum_nonneg fun n _ => (hc n).le
  have hcAll : 0 < cAll := by dsimp [cAll]; linarith
  refine ⟨cAll, hcAll, ?_⟩
  intro κ hκ hfin hCκ hlarge
  apply d.surjective_fieldPoints_of_restrictions
  intro n
  have hcn : c n ≤ cAll := by
    have hle : c n ≤ ∑ m : d.Index, c m :=
      Finset.single_le_sum (fun m _ => (hc m).le) (Finset.mem_univ n)
    dsimp [cAll]
    linarith
  have hsq : (c n) ^ 2 ≤ cAll ^ 2 := pow_le_pow_left₀ (hc n).le hcn 2
  exact UniformLangWeilFiniteFieldLifts.surjective_of_bound
    (d.restrictedMap n.val) n.val (hc n).le (hsq.trans_lt hlarge) (hb n κ)

/-- The same single residue bound gives surjectivity on all compatible
Henselian local coefficient algebras. -/
theorem exists_uniform_henselian_surjectivity (hLW : SpaceUniformLangWeilStatement.{u})
    (X Y : AlgebraicSpace (Spec (CommRingCat.of C))) (f : X ⟶ Y)
    (hXs : IsSeparated X) (hXft : FiniteTypeOverRing C X)
    (hYs : IsSeparated Y) (hYft : FiniteTypeOverRing C Y)
    (hf : IsSmoothMorphism f) (hfc : HasGeometricallyConnectedFibres f) :
    ∃ c : ℝ, 0 < c ∧ ∀ (R : Type u) [CommRing R] [HenselianLocalRing R] [Algebra C R]
      (κ : Type u) [Field κ] [Finite κ] [Algebra C κ]
      (φ : R →ₐ[C] κ), Function.Surjective φ → c ^ 2 < (Nat.card κ : ℝ) →
        Function.Surjective (RingPoints.map f : RingPoints C X R → RingPoints C Y R) := by
  obtain ⟨c, hc, hsurj⟩ :=
    exists_uniform_field_surjectivity C hLW X Y f hXs hXft hYs hYft hf hfc
  refine ⟨c, hc, ?_⟩
  intro R hR hHen hCR κ hκ hfin hCκ φ hφ hlarge
  exact HenselianSmoothPointLifting.surjective_of_residue f hf φ hφ (hsurj κ hlarge)

/-- Choose actual integral lifts for the original coefficient action, uniformly
over all sufficiently large finite-field quotients. -/
def pointLifts (hLW : SpaceUniformLangWeilStatement.{u})
    (X Y : AlgebraicSpace (Spec (CommRingCat.of C))) (f : X ⟶ Y)
    (hXs : IsSeparated X) (hXft : FiniteTypeOverRing C X)
    (hYs : IsSeparated Y) (hYft : FiniteTypeOverRing C Y)
    (hf : IsSmoothMorphism f) (hfc : HasGeometricallyConnectedFibres f) :
    Σ c : {c : ℝ // 0 < c},
      (R : Type u) → [CommRing R] → [HenselianLocalRing R] → [Algebra C R] →
        (κ : Type u) → [Field κ] → [Finite κ] → [Algebra C κ] →
          (φ : R →ₐ[C] κ) → Function.Surjective φ → c.1 ^ 2 < (Nat.card κ : ℝ) →
            (p : RingPoints C Y R) → {x : RingPoints C X R // RingPoints.map f x = p} := by
  let h := exists_uniform_henselian_surjectivity C hLW X Y f hXs hXft hYs hYft hf hfc
  refine ⟨⟨Classical.choose h, (Classical.choose_spec h).1⟩, ?_⟩
  intro R hR hHen hCR κ hκ hfin hCκ φ hφ hlarge p
  exact ⟨Classical.choose ((Classical.choose_spec h).2 R κ φ hφ hlarge p),
    Classical.choose_spec ((Classical.choose_spec h).2 R κ φ hφ hlarge p)⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionUniformLifts
