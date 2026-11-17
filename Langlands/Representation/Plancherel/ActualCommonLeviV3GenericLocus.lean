import Langlands.Representation.Plancherel.ActualCommonLeviV3Statement
import Langlands.Representation.Plancherel.PlancherelWeightPositivity

/-! # The genuine common-Levi generic locus on fixed compact carriers -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open UnramifiedOperatorFamily

private theorem bijective_iff_of_equiv_square
    {V W Vc Wc : Type*} (E₀ : V ≃ Vc) (E₁ : W ≃ Wc)
    (T : V → W) (S : Vc → Wc) (hsq : ∀ v, E₁ (T v) = S (E₀ v)) :
    Function.Bijective T ↔ Function.Bijective S := by
  have hS : S = E₁ ∘ T ∘ E₀.symm := by
    funext x
    simpa using (hsq (E₀.symm x)).symm
  have hT : T = E₁.symm ∘ S ∘ E₀ := by
    funext v
    simpa using congrArg E₁.symm (hsq v)
  constructor
  · intro h
    rw [hS]
    exact E₁.bijective.comp (h.comp E₀.symm.bijective)
  · intro h
    rw [hT]
    exact E₁.symm.bijective.comp (h.comp E₀.bijective)

section ScalarDensity

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (hH : IsConnectedReductive H)

local instance scalarDensityPointTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology k H.X

include hH in
/-- The nonzero evaluations of a nonzero actual regular function are dense
in the full actual unitary character group. -/
theorem dense_rationalUnitaryRegularRestriction_ne_zero
    (b : unramifiedRegularFunctions (fun a => (rationalNormCharacters H a).toMul))
    (hb : b ≠ 0) :
    Dense {z | rationalUnitaryRegularRestriction H b z ≠ 0} := by
  let R := unramifiedRegularFunctions (fun a => (rationalNormCharacters H a).toMul)
  let Q := rationalUnramifiedFunctionField H (continuous_rationalValuationImageProjection H) hH
  have hi := rationalUnramifiedFunctionField_algebraMap_injective H
    (continuous_rationalValuationImageProjection H) hH
  have hbQ : algebraMap R Q b ≠ 0 := by
    intro he
    exact hb (hi (he.trans (map_zero (algebraMap R Q)).symm))
  have hd := dense_rationalUnitaryValue_ne_zero H hH
    (rationalFunctionUnitaryRegular_algebraMap H hH b) hbQ
  change Dense {z | b.val (unitaryToUnramified H z) ≠ 0}
  simpa only [rationalUnitaryValue_algebraMap] using hd

end ScalarDensity

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "V₀" => compactFiber χ K ψ hψ A
local notation "V₁" => compactFiber χ K ψ' hψ' A
local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "J" => compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q

/-- The same regularity and bijectivity conditions as the genuine generic
locus, expressed entirely on the two fixed compact carriers. -/
def compactGenericLocus : Set X :=
  {z | ∃ hz : z ∈ regularLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q,
    Function.Bijective (p.presentation.continuedOperator ⟨z, hz.1⟩) ∧
    Function.Bijective (q.presentation.continuedOperator ⟨z⁻¹, hz.2⟩)}

/-- Bijectivity of the actual forward continuation is exactly bijectivity of
its own compact operator. -/
theorem forward_bijective_iff_compact (z : p.regularRegion) :
    Function.Bijective (ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p z) ↔
      Function.Bijective (p.presentation.continuedOperator z) :=
  bijective_iff_of_equiv_square
    (compactEquiv χ hG K hK ψ hψ hψK z.val A).toEquiv
    (compactEquiv χ hG K hK ψ' hψ' hψ'K z.val A).toEquiv _ _
    (forward_compact_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p z)

/-- The inverse-parameter reverse-dual continuation is bijective precisely
when its specified compact reverse operator is bijective. -/
theorem reverseDual_bijective_iff_compact
    (z : regularLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q) :
    Function.Bijective (reverseDual χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z) ↔
      Function.Bijective (q.presentation.continuedOperator ⟨z.val⁻¹, z.property.2⟩) :=
  bijective_iff_of_equiv_square
    (dualCompactEquiv χ hG K hK ψ' hψ' hψ'K A z.val).toEquiv
    (dualCompactEquiv χ hG K hK ψ hψ hψK A z.val).toEquiv _ _
    (reverseDual_compact_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z)

/-- This compact characterization retains the genuine generic locus of the
actual operators, without introducing any invertibility assumption. -/
theorem compactGenericLocus_eq :
    compactGenericLocus χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q = D := by
  ext z
  constructor
  · rintro ⟨hz, hp, hq⟩
    exact ⟨hz,
      (forward_bijective_iff_compact χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p
        ⟨z, hz.1⟩).mpr hp,
      (reverseDual_bijective_iff_compact χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q
        ⟨z, hz⟩).mpr hq⟩
  · rintro ⟨hz, hp, hq⟩
    exact ⟨hz,
      (forward_bijective_iff_compact χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p
        ⟨z, hz.1⟩).mp hp,
      (reverseDual_bijective_iff_compact χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q
        ⟨z, hz⟩).mp hq⟩

include hG in
/-- A nonzero actual regular equation can be avoided densely in the entire
unitary parameter group. -/
theorem dense_unitary_regular_nonzero
    (b : unramifiedRegularFunctions (normCharacters χ)) (hb : b ≠ 0) :
    Dense {z : Xu | b.val (unitaryParameter χ z) ≠ 0} :=
  dense_rationalUnitaryRegularRestriction_ne_zero (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hG) b hb

/-- A single nonzero regular equation, outside of which the actual compact
operators are regular and bijective, suffices for every generic-density
clause of the closed V.3.1 target. The invertibility input remains explicit. -/
theorem hasDenseGenericLocus_of_regular_nonzero_subset
    (b : unramifiedRegularFunctions (normCharacters χ)) (hb : b ≠ 0)
    (hsub : {z | b.val z ≠ 0} ⊆
      compactGenericLocus χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q) :
    HasDenseGenericLocus χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q := by
  let O : Set X := {z | b.val z ≠ 0}
  have hO : IsOpen O :=
    isOpen_ne_fun (continuous_unramifiedRegularFunction (normCharacters χ) b) continuous_const
  have hd : Dense O := rationalUnramifiedRegular_dense_nonzero (parameterScheme χ)
    (DynamicOppositeCanonicalScalar.parameterProjection_continuous χ)
    (parameterScheme_isConnectedReductive χ hG) b hb
  have hdu : Dense ((unitaryParameter χ) ⁻¹' O) := dense_unitary_regular_nonzero χ hG b hb
  have hOD : O ⊆ D := by
    rw [← compactGenericLocus_eq χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q]
    exact hsub
  have hne : O.Nonempty := hd.nonempty
  refine ⟨hne.mono hOD, hd.mono hOD, hdu.mono (Set.preimage_mono hOD),
    O, hO, hne, hOD, hd, hdu⟩

end Langlands.Plancherel.ActualCommonLeviV3
