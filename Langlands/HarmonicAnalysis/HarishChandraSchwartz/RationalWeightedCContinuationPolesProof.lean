import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionRegularityAssembly
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionFactorContinuation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeightedCScalarPoles
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCompactTensor

/-! # Whole-operator continuation and unitary poles of the weighted c-family -/

noncomputable section

set_option maxHeartbeats 160000
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped CategoryTheory.MonObj NNReal TensorProduct

namespace Langlands.Plancherel

universe u

open UnramifiedOperatorFamily ValuationKernelCoordinates

section TensorRatio

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {V W V' W' S T : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
  [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]

local instance assemblyPointTopology : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

set_option hygiene false in
local notation "X" => unramifiedCharacters (fun a => (rationalNormCharacters G a).toMul)
set_option hygiene false in
local notation "R" => unramifiedRegularFunctions (fun a => (rationalNormCharacters G a).toMul)

variable {D : Set X}

local notation "Dᵛ" => (Inv.inv ⁻¹' D)

omit [LocallyOfFiniteType G.X.hom] in
private theorem mem_inverse_domain (z : D) : z.val⁻¹ ∈ Dᵛ := by
  change z.val⁻¹⁻¹ ∈ D
  rw [inv_inv]
  exact z.property

private theorem continuationOfTensorAndRatio (hG : IsConnectedReductive G)
    {P : D → V →ₗ[ℂ] W} {Q : Dᵛ → V' →ₗ[ℂ] W'} {F : D → S →ₗ[ℂ] T}
    (p : RationalOperatorContinuationData D P) (q : RationalOperatorContinuationData Dᵛ Q)
    (p' : RationalOperatorPolePresentation G p.denominator p.numerator)
    (q' : RationalOperatorPolePresentation G q.denominator q.numerator)
    (source : S →ₗ[ℂ] V ⊗[ℂ] V') (target : W ⊗[ℂ] W' →ₗ[ℂ] T)
    {a b : R} (hb : ∀ z : D, b.val z.val ≠ 0) (r : RankOneScalarPolePresentation G a b)
    (he : ∀ z : D, (a.val z.val / b.val z.val) •
      (target ∘ₗ TensorProduct.map (P z) (Q ⟨z.val⁻¹, mem_inverse_domain G z⟩) ∘ₗ source) = F z) :
    ∃ v : RationalOperatorContinuationData D F,
      Nonempty (RationalOperatorPolePresentation G v.denominator v.numerator) := by
  have hsub : D ⊆ D ∩ Inv.inv ⁻¹' Dᵛ := fun z hz => ⟨hz, mem_inverse_domain G ⟨z, hz⟩⟩
  let v := ((p.tensor q.inversion).restrict hsub).fixedMaps source target
  let v' := (p'.tensor G (q'.inversion G hG)).fixedMaps G source target
  exact ⟨(v.regularRatio a b hb).ofFamilyEq he, ⟨v'.regularRatio G r⟩⟩

private theorem emptyDomain_continuationWithPoles (P : D → S →ₗ[ℂ] T) (hD : ¬ D.Nonempty) :
    ∃ v : RationalOperatorContinuationData D P,
      Nonempty (RationalOperatorPolePresentation G v.denominator v.numerator) := by
  let p : RationalOperatorContinuationData D P :=
    ⟨1, fun _ => one_ne_zero, fun _ => 0, isPolynomialOperatorOn_const 0,
      fun z => (hD ⟨z.val, z.property⟩).elim⟩
  let q : RationalOperatorPolePresentation G p.denominator p.numerator :=
    ⟨1, RationalUnitaryPoleFactorization.ofNonvanishing G 1 (fun _ => one_ne_zero),
      fun _ => 0, isPolynomialOperatorOn_const 0, fun _ => rfl⟩
  exact ⟨p, ⟨q⟩⟩

end TensorRatio
private theorem scalarComparison_reparam {P Q R T : Type*} [SMul ℂ T]
    (p : P → Q) (q : Q → R) (r : P → R) (A : Q → T) (a : Q → ℂ) (B : R → T)
    (h : ∀ x, A x = a x • B (q x)) (he : ∀ z, q (p z) = r z) (z : P) :
    A (p z) = a (p z) • B (r z) :=
  (h (p z)).trans (congrArg (fun x => a (p z) • B x) (he z))

end Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open UnramifiedOperatorFamily

universe u uV

section Weighted

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance weightedContinuationAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance weightedContinuationLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance weightedContinuationLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance weightedContinuationLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)

local instance weightedContinuationPointTopology : TopologicalSpace (rationalPoints M₀) :=
  rationalPointTopology F (M₀).X

set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul
set_option hygiene false in
local notation "eM" => leviRationalPointHomeomorph i ν I
set_option hygiene false in
local notation "Φ" => unramifiedCharactersHomeomorph eM ν₀

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
  (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)

set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "Wₛ" => ProductInducedCompactPicture (decomposition χs)
  (lowerK hG hi hν I I' hζ n hn hRefl hCST π PM) (SmoothRep.pullback (eₛ).symm π.obj)
set_option hygiene false in
local notation "D₀" => cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
set_option hygiene false in
local notation "A₀" => weightedCompactFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN
set_option hygiene false in
local notation "Ω" => Φ ⁻¹' interior D₀
set_option hygiene false in
local notation "A" => fun z : (Ω : Set (unramifiedCharacters ν₀)) =>
  A₀ ⟨Φ z.val, interior_subset z.property⟩


variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  (sc : Tc.toGrp ⟶ M₀) (hs : IsSplitComponent sc)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

variable [(CM).Normal] [MeasurableSpace (𝐌 ⧸ CM)] (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]

set_option hygiene false in
local notation "X" => unramifiedCharacters ν₀
set_option hygiene false in
local notation "dM" => isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)
set_option hygiene false in
local notation "dL" => decomposition χs
set_option hygiene false in
local notation "K'" => lowerK hG hi hν I I' hζ n hn hRefl hCST π PM
set_option hygiene false in
local notation "hK'" => lowerK_isCompact hG hi hν I I' hζ n hn hRefl hCST π PM
set_option hygiene false in
local notation "hPK'" => lowerPackage_iwasawa hG hi hν I I' hζ n hn hRefl hCST π PM
set_option hygiene false in
local notation "C" => ProductInducedCompactPicture dM K π.obj
set_option hygiene false in
local notation "CS" => CompactInductionPicture dM K π.obj
set_option hygiene false in
local notation "CSᵛ" => CompactInductionPicture dM K π.obj.contragredient
set_option hygiene false in
local notation "CT" => CompactInductionPicture dL K' (SmoothRep.pullback (eₛ).symm π.obj)
set_option hygiene false in
local notation "CTᵛ" => CompactInductionPicture dL K' (SmoothRep.pullback (eₛ).symm π.obj.contragredient)
set_option hygiene false in
local notation "C₀" => cCompactFamily hG hi hν I I' hζ hζ' n hn K hK hCST hPK hK' hPK' π.obj
set_option hygiene false in
local notation "CD" => cDomain hG hi hν I I' hζ hζ' n hn K hK π.obj
set_option hygiene false in
local notation "wZ" => fun z : (Ω : Set X) => (⟨Φ z.val, interior_subset z.property⟩ : D₀)
set_option hygiene false in
local notation "cZ" => fun z : (Ω : Set X) => (⟨Φ z.val, (interior_subset z.property).1⟩ : CD)
set_option hygiene false in
local notation "ρ" => cWeightedScalarAt hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
set_option hygiene false in
local notation "α₊" => outerCentralizer_pos hG hi hν I' hζ'
set_option hygiene false in
local notation "α₋" => outerCentralizer_neg hG hi hν I' hζ'
set_option hygiene false in
local notation "D₊" => cFactorConvergenceRegion hG hi hν I I' hζ n hn ζ' α₊ K hK π.obj
set_option hygiene false in
local notation "D₋" => cFactorConvergenceRegion hG hi hν I I' hζ n hn (-ζ') α₋ K hK π.obj.contragredient
set_option hygiene false in
local notation "F₊" => cFactorOnCompact hG hi hν I I' hζ n hn ζ' α₊ K hK hPK hCST π.obj K' hK' hPK'
set_option hygiene false in
local notation "F₋" => cFactorOnCompact hG hi hν I I' hζ n hn (-ζ') α₋ K hK hPK hCST π.obj.contragredient K' hK' hPK'
set_option hygiene false in
local notation "Ωᵛ" => {z : X | z⁻¹ ∈ Ω}

private theorem weightedInterior_open : IsOpen (Ω : Set X) :=
  isOpen_interior.preimage (Φ).continuous

private theorem weightedInterior_inverse_open : IsOpen (Ωᵛ : Set X) :=
  (weightedInterior_open hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM).preimage continuous_inv

omit [LocallyOfFiniteType G.X.hom] in
private theorem nonempty_inverseConvergence {D : Set X} (h : D.Nonempty) :
    ({z : X | z⁻¹ ∈ D} : Set X).Nonempty := by
  obtain ⟨z, hz⟩ := h
  exact ⟨z⁻¹, by simpa only [Set.mem_ofPred_eq, inv_inv] using hz⟩

private theorem weightedInterior_subset_pos : (Ω : Set X) ⊆ D₊ :=
  fun _ hz => (interior_subset hz).1.1

private theorem weightedInterior_subset_neg
    (h : ∀ z : X, Φ z ∈ CD → z⁻¹ ∈ D₋) : (Ωᵛ : Set X) ⊆ D₋ := by
  intro z hz
  have hh : z⁻¹⁻¹ ∈ D₋ := h z⁻¹ (interior_subset hz).1
  simpa only [inv_inv] using hh

include hN in
private theorem lowerCompact_mapsTo_ambient (α : cocharacterLattice T)
    (hα : Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) = standardLevi i ν (rootSet i ν I'))
    (k : K') :
    ((RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i))
      (Standard.leviHom i ν (rootSet i ν I')) (outer_isRepresentedBy (i := i) (ν := ν) I' α hα)
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I')) k.val) : rationalPoints G) ∈ K := by
  have hk : k.val ∈ PM.K.toSubgroup := k.property
  rw [hN.lower] at hk
  exact hk

set_option maxHeartbeats 480000 in
private theorem weightedCompactFamily_scalar (z : D₀) :
    A₀ z = ρ z • C₀ ⟨z.val, z.property.1⟩ := by
  simp only [weightedCompactFamily, cWeightedCompactFamily, cWeightedScalarAt]

private theorem unweightedParameter_eq (z : (Ω : Set X)) :
    (⟨(wZ z).val, (wZ z).property.1⟩ : CD) = cZ z :=
  Subtype.ext rfl

set_option linter.defProp false in
private def weightedCompactFamily_scalar_on_interior (z : (Ω : Set X)) :=
  scalarComparison_reparam (T := C →ₗ[ℂ] Wₛ) wZ (fun x : D₀ => (⟨x.val, x.property.1⟩ : CD)) cZ A₀ ρ C₀
    (weightedCompactFamily_scalar hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN)
    (unweightedParameter_eq hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM) z

set_option maxHeartbeats 80000 in
private theorem weightedScalarComparisonOnInterior (z : (Ω : Set X)) :
    A₀ (wZ z) = ρ (wZ z) • C₀ (cZ z) := by
  have he := weightedCompactFamily_scalar_on_interior hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK
    π PG PM hN z
  refine Eq.trans ?_ (Eq.trans he ?_)
  · rfl
  · congr 1

set_option hygiene false in
local notation "hpos" => weightedInterior_subset_pos hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
set_option hygiene false in
local notation "hneg(" h ")" => weightedInterior_subset_neg hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM h

section Assembly

variable [BorelSpace (𝐌 ⧸ CM)]

set_option maxHeartbeats 400000 in
private theorem weightedCContinuation_of_tensor
    (dconv : ∀ z : X, Φ z ∈ CD → z⁻¹ ∈ D₋)
    (source : C →ₗ[ℂ] CS ⊗[ℂ] CSᵛ) (target : CT ⊗[ℂ] CTᵛ →ₗ[ℂ] Wₛ)
    (htensor : ∀ z : (Ω : Set X),
      target ∘ₗ TensorProduct.map (F₊ ⟨z.val, hpos z.property⟩)
        (F₋ ⟨z.val⁻¹, dconv z.val (cZ z).property⟩) ∘ₗ source =
        C₀ (cZ z))
    (hscalar : ∀ z : (Ω : Set X), A₀ (wZ z) = ρ (wZ z) • C₀ (cZ z))
    (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu) :
    ∃ p : RationalOperatorContinuationData Ω A,
      Nonempty (RationalOperatorPolePresentation M₀ p.denominator p.numerator) := by
  by_cases hne : (Ω : Set X).Nonempty
  · have hopen := weightedInterior_open hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
    have hopenDual := weightedInterior_inverse_open hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
    have hneDual := nonempty_inverseConvergence I hne
    have hcof := compactOpenCofinal_of_isClosed (isClosed_standardLeviPoints i ν (rootSet i ν I))
    have hadm : π.obj.contragredient.IsAdmissible :=
      (SmoothRep.isAdmissible_contragredient_iff hcof π.obj).mpr π.property.2
    have hirr : π.obj.contragredient.IsIrreducible :=
      (SmoothRep.isIrreducible_contragredient_iff hcof π.obj π.property.2).mpr π.property.1
    have hsubDual := hneg(dconv)
    have hp := exists_cFactorOnCompactContinuationWithPoles hG hi hν I I' hζ n hn ζ' α₊
      K hK hPK hCST π.obj hopen hne hpos K' hK' hPK' sc hs π.property.1 π.property.2
      (lowerCompact_mapsTo_ambient hG hi hν I I' hζ n hn K hRefl hCST π PG PM hN ζ' α₊)
    have hq := exists_cFactorOnCompactContinuationWithPoles hG hi hν I I' hζ n hn (-ζ') α₋
      K hK hPK hCST π.obj.contragredient hopenDual hneDual hsubDual K' hK' hPK' sc hs hirr hadm
      (lowerCompact_mapsTo_ambient hG hi hν I I' hζ n hn K hRefl hCST π PG PM hN (-ζ') α₋)
    obtain ⟨p, ⟨q⟩⟩ := hp
    obtain ⟨pDual, ⟨qDual⟩⟩ := hq
    have hr := exists_weightedCScalarPolePresentation hG hi hν I I' hζ hζ' n hn
      K hK hRefl hCST π PG PM sc hs mu hsq hne
    obtain ⟨a, b, hb, hratio, ⟨r⟩⟩ := hr
    refine continuationOfTensorAndRatio M₀ (lowerAmbient_isConnectedReductive hG hi hν I)
      p pDual q qDual source target hb r ?_
    intro z
    have ht := congrArg (fun op : C →ₗ[ℂ] Wₛ => (a.val z.val / b.val z.val) • op) (htensor z)
    have hr := congrArg (fun x : ℂ => x • C₀ (cZ z)) (hratio z).symm
    exact ht.trans (hr.trans (hscalar z).symm)
  · exact emptyDomain_continuationWithPoles M₀ A hne

set_option maxHeartbeats 120000 in
/-- The actual weighted c-family on the transported interior has a whole-operator
continuation and a unitary pole presentation. -/
theorem weightedCContinuationPoles :
    WeightedCContinuationPolesStatement hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK
      π PG PM hN sc hs mu := by
  intro hsq _hSpecial
  let dconv := cFactorDualConvergence hG hi hν I I' hζ hζ' n hn K hK π.obj
  let e := (cCompactSourceChart hG hi hν I K hK hPK π.obj).symm.toLinearMap
  let f := cCompactTargetMap hG hi hν I I' hζ (ζ' := ζ') n hn K hK π.obj K' hK' hPK'
  refine weightedCContinuation_of_tensor hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK
    π PG PM hN sc hs mu dconv e f ?_
    (weightedScalarComparisonOnInterior hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN) hsq
  · intro z
    have ht := cCompactFamily_eq_tensor hG hi hν I I' hζ hζ' n hn K hK hCST hPK π.obj K' hK' hPK'
      z.val (cZ z).property
    refine Eq.trans (α := C →ₗ[ℂ] Wₛ) ?_ (Eq.trans ht.symm ?_)
    · rfl
    · rfl

end Assembly
end Weighted
end Langlands.HarishChandraSchwartz.WeakExpansion
