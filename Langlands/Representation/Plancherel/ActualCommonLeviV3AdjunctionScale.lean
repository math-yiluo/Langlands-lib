import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericPreservation
import Langlands.Representation.Unitary.AdmissibleFormUniqueness

/-! # The scale in the actual generic compact adjunction -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction

universe u uV

open DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor
open CompactInduction

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
  ambientMeasurable ambientBorel leviMeasurable leviBorel
  leviLocallyCompact parabolicLocallyCompact

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

variable
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

variable (z : genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q)

local notation "Az" => twistObject χ z.val A
local notation "h₀" => commonDecomposition χ ψ hψ
local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'
local notation "hδ₀" => DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
local notation "hδ₁" => DynamicOppositeCanonicalScalar.radical_unimodular ψ' hG
set_option quotPrecheck false in
local notation "I₀" => (normalizedInductionFunctor h₀ hU₀).obj Az
set_option quotPrecheck false in
local notation "I₁" => (normalizedInductionFunctor h₁ hU₁).obj Az
set_option quotPrecheck false in
local notation "I₀d" => (DynamicNormalization.leviTwistedInductionFunctor h₀ hU₀).obj (Az).contragredient
set_option quotPrecheck false in
local notation "I₁d" => (DynamicNormalization.leviTwistedInductionFunctor h₁ hU₁).obj (Az).contragredient
local notation "e₀" => normalizedInductionLeviEquiv h₀ hU₀ hδ₀ Az
local notation "e₁" => normalizedInductionLeviEquiv h₁ hU₁ hδ₁ Az
set_option quotPrecheck false in
local notation "J" => ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p
  ⟨z.val, z.property.choose.1⟩
set_option quotPrecheck false in
local notation "R" => reverseDual χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
  ⟨z.val, z.property.choose⟩

local notation "e" => genericNormalizedForwardEquiv χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z

variable (hA : (twistObject χ z.val A).IsAdmissible)

local notation "hP₀" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
local notation "hP₁" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ'
local notation "hr₀" => commonProjection_continuous χ ψ hψ
local notation "hr₁" => commonProjection_continuous χ ψ' hψ'
local notation "hPK₀" => iwasawa_sets K ψ hψK
local notation "hPK₁" => iwasawa_sets K ψ' hψ'K
local notation "hH" => ambient_modularCharacter hG
local notation "hmod₀" => common_modularCharacter χ hG ψ hψ
local notation "hmod₁" => common_modularCharacter χ hG ψ' hψ'
local notation "d₀" => leviInducedSmoothDualEquiv h₀ hU₀ Az K hδ₀ hK hP₀ hr₀ hPK₀ hH hmod₀ hA
local notation "d₁" => leviInducedSmoothDualEquiv h₁ hU₁ Az K hδ₁ hK hP₁ hr₁ hPK₁ hH hmod₁ hA

set_option quotPrecheck false in
local notation "pairTarget[" f "," ℓ "]" => smoothDualPairing (I₁).representation (d₁ ℓ) (e f)
set_option quotPrecheck false in
local notation "pairSource[" f "," ℓ "]" => smoothDualPairing (I₀).representation (d₀ (R ℓ)) f

set_option maxHeartbeats 4000000 in
/-- On an irreducible generic target, the two actual compact pairings are
proportional, with nonzero scale obtained by Schur's lemma. -/
theorem exists_genericAdjunctionScale (hirr : (I₁).IsIrreducible) :
    ∃ r : ℂ, r ≠ 0 ∧ ∀ (f : I₀) (ℓ : I₁d), pairTarget[f, ℓ] = r * pairSource[f, ℓ] := by
  have ha := induced_isAdmissible h₁ hU₁ K hK hPK₁ Az hr₁ hA
  have hdual := (SmoothRep.isIrreducible_contragredient_iff
    (compactOpenCofinal_of_nonarchimedean (RationalPoint F G.X)) I₁ ha).mpr hirr
  let reverse := (d₁).symm.trans (((R).ofBijective z.property.choose_spec.2).trans d₀)
  let forwardDual := smoothContragredientEquiv e
  let compare := forwardDual.trans reverse.symm
  obtain ⟨r, hr, _⟩ := Schur.separableSmooth_scalarEndomorphism (I₁).contragredient.representation
    (I₁).contragredient.isSmooth hdual compare.toIntertwiningMap
  have hscale (m : (I₁).contragredient) : compare m = r • m :=
    congrArg (fun T : (I₁).contragredient.representation.IntertwiningMap
      (I₁).contragredient.representation => T m) hr
  have hrne : r ≠ 0 := by
    let : (I₁).contragredient.representation.IsIrreducible := hdual
    let : Nontrivial (I₁).contragredient :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (RationalPoint F G.X))
        (I₁).contragredient.representation.asModule
    obtain ⟨m, hm⟩ := exists_ne (0 : (I₁).contragredient)
    intro hzero
    have h := hscale m
    rw [hzero, zero_smul] at h
    exact hm (compare.injective (h.trans (map_zero compare).symm))
  refine ⟨r, hrne, fun f ℓ => ?_⟩
  have he : reverse (d₁ ℓ) = d₀ (R ℓ) :=
    congrArg (fun m : I₁d => d₀ (R m)) ((d₁).symm_apply_apply ℓ)
  have hfirst : forwardDual (d₁ ℓ) = reverse (compare (d₁ ℓ)) :=
    (reverse.apply_symm_apply _).symm
  have hsecond : reverse (compare (d₁ ℓ)) = r • d₀ (R ℓ) :=
    (congrArg reverse (hscale (d₁ ℓ))).trans ((map_smul reverse r _).trans
      (congrArg (fun m : (I₀).contragredient => r • m) he))
  exact congrArg (fun m : (I₀).contragredient => smoothDualPairing (I₀).representation m f)
    (hfirst.trans hsecond)

set_option maxHeartbeats 4000000 in
/-- A single equal, nonzero pair of test values determines scale one for the
entire generic adjunction. Both tests use the prescribed compact pairing. -/
theorem genericAdjunction_of_test (hirr : (I₁).IsIrreducible)
    (f₀ : I₀) (ℓ₀ : I₁d) (hne : pairSource[f₀, ℓ₀] ≠ 0)
    (htest : pairTarget[f₀, ℓ₀] = pairSource[f₀, ℓ₀]) :
    ∀ (f : I₀) (ℓ : I₁d), pairTarget[f, ℓ] = pairSource[f, ℓ] := by
  obtain ⟨r, _, h⟩ := exists_genericAdjunctionScale χ hG A K hK ψ hψ hψK
    ψ' hψ' hψ'K p q z hA hirr
  have hr : r = 1 := mul_right_cancel₀ hne ((h f₀ ℓ₀).symm.trans (htest.trans (one_mul _).symm))
  intro f ℓ
  simpa only [hr, one_mul] using h f ℓ

/-- Choose the normalized forward operator's positive similarity factor on
an irreducible source, for the exact compact probability forms. -/
def genericForwardSimilitude
    (hirr : (I₀).IsIrreducible) (b : InvariantPositiveForm (Az).representation) :
    {r : ℝ // ∃ hr : 0 < r,
      (invariantPositiveForm h₁ hU₁ hP₁ K hK hPK₁ hH hmod₁ Az b).ofEquiv e =
        (invariantPositiveForm h₀ hU₀ hP₀ K hK hPK₀ hH hmod₀ Az b).rescale r hr} :=
  Classical.choice (by
    have hI := induced_isAdmissible h₀ hU₀ K hK hPK₀ Az hr₀ hA
    obtain ⟨r, hr, he⟩ := InvariantPositiveForm.exists_pos_rescale_eq
      (invariantPositiveForm h₀ hU₀ hP₀ K hK hPK₀ hH hmod₀ Az b)
      ((invariantPositiveForm h₁ hU₁ hP₁ K hK hPK₁ hH hmod₁ Az b).ofEquiv e)
      (compactOpenCofinal_of_nonarchimedean (RationalPoint F G.X)) hI hirr
    exact ⟨⟨r, hr, he⟩⟩)

end Langlands.Plancherel.ActualCommonLeviV3
