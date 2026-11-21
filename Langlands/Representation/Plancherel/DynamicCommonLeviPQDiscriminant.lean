import Langlands.Representation.Plancherel.DynamicRepresentedGalleryOperators
import Langlands.Representation.Plancherel.RationalUnitaryPoleFactorization
import Langlands.Representation.Plancherel.UnramifiedNormalizedModels

/-! # A factored scalar controlling the represented PQ-regular locus -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.UnramifiedPointSeparation

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local instance pointTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X

set_option hygiene false in
local notation "ν" => fun a => (rationalNormCharacters H a).toMul
local notation "R" => unramifiedRegularFunctions ν
local notation "X" => unramifiedCharacters ν

/-- Divide the two valuation monomials to obtain one lattice exponent. -/
def exponent (t : UnramifiedPointSeparation H) : Additive (rationalDiscreteValuationImage H) :=
  Additive.ofMul (rationalValuationImageProjection H (t.left * t.right⁻¹))

omit [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
theorem exponent_ne_zero (t : UnramifiedPointSeparation H) : t.exponent H ≠ 0 := by
  intro h
  have he := congrArg Additive.toMul h
  change rationalValuationImageProjection H (t.left * t.right⁻¹) = 1 at he
  rw [map_mul, map_inv, mul_inv_eq_one] at he
  exact t.distinct he

/-- The ambient regular binomial cutting out failure of this test. -/
def factor (t : UnramifiedPointSeparation H) : R :=
  rationalUnramifiedLatticeMonomial H (t.exponent H) - algebraMap ℂ R t.scalar

theorem factor_nonzero_iff (t : UnramifiedPointSeparation H) (z : X) :
    (t.factor H).val z ≠ 0 ↔ t.holds H z := by
  change ((rationalUnramifiedLatticeMonomial H
    (Additive.ofMul (rationalValuationImageProjection H (t.left * t.right⁻¹)))).val z -
      t.scalar ≠ 0) ↔ _
  rw [rationalUnramifiedLatticeMonomial_eval_projection, map_mul, map_inv,
    Units.val_mul, Units.val_inv_eq_inv_val, sub_ne_zero]
  change (z.val t.left : ℂ) * (z.val t.right : ℂ)⁻¹ ≠ t.scalar ↔
    (z.val t.left : ℂ) ≠ t.scalar * (z.val t.right : ℂ)
  simpa only [div_eq_mul_inv] using
    not_congr (div_eq_iff (Units.ne_zero (z.val t.right)) :
      (z.val t.left : ℂ) / (z.val t.right : ℂ) = t.scalar ↔
      (z.val t.left : ℂ) = t.scalar * (z.val t.right : ℂ))

set_option maxHeartbeats 420000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite product has only the unitary poles coming from its binomial factors. -/
def factorsOfList (hH : IsConnectedReductive H) (tests : List (UnramifiedPointSeparation H)) :
    RationalUnitaryPoleFactorization H (tests.map (factor H)).prod := by
  let coords := tests.map fun t => (t.exponent H, t.scalar)
  let binomial (t : Additive (rationalDiscreteValuationImage H) × ℂ) : R :=
    rationalUnramifiedLatticeMonomial H t.1 - algebraMap ℂ R t.2
  have hne : ∀ t ∈ coords, t.1 ≠ 0 := by
    intro t ht
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp ht
    exact s.exponent_ne_zero H
  have hm : coords.map binomial = tests.map (factor H) := by
    dsimp only [coords]
    rw [List.map_map]
    rfl
  have h := RationalUnitaryPoleFactorization.ofMonomialDifferences H hH
    coords hne 1 (fun _ => one_ne_zero)
  change RationalUnitaryPoleFactorization H ((coords.map binomial).prod * 1) at h
  rw [hm, mul_one] at h
  exact h

theorem holds_of_prod_nonzero (tests : List (UnramifiedPointSeparation H)) (z : X)
    (hz : ((tests.map (factor H)).prod).val z ≠ 0) :
    ∀ t ∈ tests, t.holds H z := by
  let ev := UnramifiedNormalized.evaluation ν z
  change ev ((tests.map (factor H)).prod) ≠ 0 at hz
  rw [map_list_prod, List.map_map] at hz
  intro t ht
  apply (factor_nonzero_iff H t z).mp
  intro h
  exact hz (List.prod_eq_zero (List.mem_map.mpr ⟨t, ht, h⟩))

end Langlands.Plancherel.UnramifiedPointSeparation

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General.RepresentedParabolic DynamicOppositeStandardIntertwining
open DynamicOppositeCanonicalScalar

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
  (x y : GalleryVertex χ)
  (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))

local notation "d" => galleryVertexData hG ha
local notation "L" => parameterScheme χ
local notation "X" => unramifiedCharacters (normCharacters χ)

/-- A factored scalar whose nonzero locus is regular for the ordered pair. -/
structure GalleryPQDiscriminant where
  scalar : unramifiedRegularFunctions (normCharacters χ)
  factors : RationalUnitaryPoleFactorization L scalar
  regular : ∀ z : X, scalar.val z ≠ 0 →
    representedIsPQRegular hG (d x) (d y)
      (σ.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker (normCharacters χ) z))

set_option maxHeartbeats 750000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite valuation separation tests give a factored `PQ`-regularity scalar. -/
def galleryPQDiscriminant (hσ : σ.IsIrreducible) (hA : σ.IsAdmissible) :
    GalleryPQDiscriminant hG ha x y σ :=
  Classical.choice (by
    obtain ⟨tests, htests⟩ := exists_pointSeparations_isPQRegular.{u, uV} F G hG
      (d x).P L (d x).U (d y).P (d y).U
      (d x).p (d x).l (d x).n (d x).r.isCompatible.parabolic (d x).r.isCompatible.levi (d x).radical
      (multiplication_isIso hG (d x))
      (d y).p (d y).l (d y).n (d y).r.isCompatible.parabolic (d y).r.isCompatible.levi (d y).radical
      (multiplication_isIso hG (d y)) ((d x).levi_comp.trans (d y).levi_comp.symm) T a ha σ hσ hA
    refine ⟨⟨_, UnramifiedPointSeparation.factorsOfList L (parameterScheme_isConnectedReductive χ hG) tests,
      fun z hz => ?_⟩⟩
    exact htests z (UnramifiedPointSeparation.holds_of_prod_nonzero L tests z hz))

end Langlands.Plancherel.DynamicCommonLeviPresentations
