import Langlands.Geometry.Building.RootValueTorusFieldAxioms

/-! # Original-point shifts and conditional torus-then-field valuation assembly -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" a => characterLattice.baseChange b S a

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable {T : CommGroupScheme (Spec (CommRingCat.of K))}

/-- Normalizer shifts for the canonical upper torus family tested only at
scalar extensions of original root-group points. -/
def TorusFieldOriginalPointShifts
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) : Prop :=
  ∀ n : normalizerPoints i, ∃ v : V S,
    ∀ a ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i a,
      (normalizerPointsFieldExtend (K := K) i n •
          torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b) hT hE hφ f)
          (a_K a) (rationalExtend k K G g) =
        torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b) hT hE hφ f
            (a_K a) (rationalExtend k K G g) +
          ((eval S a v : ℝ) : WithTop ℝ)

/-- Under the actual factorization, original-point tests are precisely
normalizer translations of the entire original scalar family. -/
theorem torusFieldOriginalPointShifts_iff
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K) :
    TorusFieldOriginalPointShifts i hS hT hE hφ f ↔
      ∀ n : normalizerPoints i, ∃ v : V S,
        n • torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f =
          v +ᵥ torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f := by
  have hnorm := torusFieldRestrictedRootFunctionFamily_normalization i hS hT hE hφ f hfactor
  constructor
  · intro h n
    obtain ⟨v, hv⟩ := h n
    exact ⟨v, (RootFunctionFamily.fieldRestrict_smul_eq_vadd_iff (K := K) i
      (torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b) hT hE hφ f)
        hnorm.1 hnorm.2 n v).mpr hv⟩
  · intro h n
    obtain ⟨v, hv⟩ := h n
    exact ⟨v, (RootFunctionFamily.fieldRestrict_smul_eq_vadd_iff (K := K) i
      (torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b) hT hE hφ f)
        hnorm.1 hnorm.2 n v).mp hv⟩

/-- The exact original-point shift condition supplies V2 for the literal family. -/
theorem torusFieldRestrictedRootFunctionFamily_reflection_of_originalPointShifts
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (hshift : TorusFieldOriginalPointShifts i hS hT hE hφ f) :
    ∀ a ∈ relativeRoots i, ∀ n : normalizerPoints i,
      RealizesReflection i a n →
        ∃ c : ℝ, ∀ g ∈ rootGroupPoints i a, g ≠ 1 →
          torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f a g =
            torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f (-a)
              ((n : rationalPoints G) * g * (n : rationalPoints G)⁻¹) +
                (c : WithTop ℝ) := by
  have hnorm := torusFieldRestrictedRootFunctionFamily_normalization i hS hT hE hφ f hfactor
  exact RootFunctionFamily.fieldRestrict_reflection_of_originalPointShifts (K := K) i
    (torusRestrictedRootFunctionFamily (i := j) (hS.baseChange b) hT hE hφ f)
      hnorm.1 hnorm.2 hshift

/-- Assemble a valuation of the unchanged original family once its
original-point normalizer shifts and exact original V5 have been proved. -/
def torusFieldRestrictedValuationOfOriginalPointShifts
    {j : T.toGrp ⟶ G_K} [Mono j.hom.hom.left]
    {φ : RootFunctionFamily T G_K}
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S_K ⟶ T) (hfactor : CommGroupScheme.groupHom f ≫ j = i_K)
    (hEbase : RelativeRoot.HasOppositeFactorPairs i)
    (ω : Kˣ →* Multiplicative ℝ)
    (hcompat : IsSplitTorusCompatible j (fun t => (ω t).toAdd) φ)
    (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)
    (hshift : TorusFieldOriginalPointShifts i hS hT hE hφ f)
    (hopposite : ∀ a ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i a, g ≠ 1 →
      ∀ g' ∈ rootGroupPoints i (-a), ∀ g'' ∈ rootGroupPoints i (-a),
        g' * g * g'' ∈ normalizerPoints i →
          torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f (-a) g' +
            torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f a g = 0) :
    {ψ : RootFunctionFamily S G // IsRootDatumValuation i ψ} :=
  ⟨torusFieldRestrictedRootFunctionFamily (G := G) (j := j) hS hT hE hφ f,
    { eq_top_of_not_mem_roots :=
        (torusFieldRestrictedRootFunctionFamily_normalization i hS hT hE hφ f hfactor).1
      eq_top_of_not_mem :=
        (torusFieldRestrictedRootFunctionFamily_normalization i hS hT hE hφ f hfactor).2
      three_le_encard := fun _ ha =>
        torusFieldRestrictedRootFunctionFamily_three_le_encard i hS hT hE hφ f hfactor
          ω hcompat hω ha
      one_mem := torusFieldRestrictedRootFunctionFamily_one_mem i hS hT hE hφ f hfactor
      mul_mem := torusFieldRestrictedRootFunctionFamily_mul_mem i hS hT hE hφ f hfactor
      inv_mem := torusFieldRestrictedRootFunctionFamily_inv_mem i hS hT hE hφ f hfactor
      eq_top_iff := torusFieldRestrictedRootFunctionFamily_eq_top_iff i hS hT hE hφ f hfactor
      reflection := torusFieldRestrictedRootFunctionFamily_reflection_of_originalPointShifts
        i hS hT hE hφ f hfactor hshift
      commutator := torusFieldRestrictedRootFunctionFamily_commutator
        i hS hT hE hφ f hfactor hEbase
      double := torusFieldRestrictedRootFunctionFamily_double i hS hT hE hφ f hfactor
      opposite := hopposite }⟩

end Langlands.Geometry.Building
