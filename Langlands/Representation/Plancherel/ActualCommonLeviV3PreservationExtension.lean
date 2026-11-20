import Langlands.Representation.Plancherel.ActualCommonLeviV3CompactNormalization
import Langlands.Representation.Plancherel.RationalUnitaryOperatorCancellation

/-! # Extending exact common-Levi preservation to the unitary parameters -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor
open UnramifiedOperatorFamily

private theorem continuous_postcomp_of_local_rational
    {Y L I V W E : Type*} [TopologicalSpace Y] [Group L] [TopologicalSpace L]
    {ν : I → (L →* ℝ≥0ˣ)} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (incl : Y → unramifiedCharacters ν) (hincl : Continuous incl)
    (T : Y → V →ₗ[ℂ] W) (M : W →ₗ[ℂ] E)
    (h : ∀ y, ∃ (U : Set (unramifiedCharacters ν))
      (N : unramifiedCharacters ν → V →ₗ[ℂ] W) (b : unramifiedRegularFunctions ν),
      incl y ∈ U ∧ IsOpen U ∧ IsPolynomialOperatorOn Set.univ (fun z => N z.val) ∧
      (∀ z ∈ U, b.val z ≠ 0) ∧
      (∀ w, incl w ∈ U → T w = (b.val (incl w))⁻¹ • N (incl w)))
    (v : V) : Continuous (fun y => M (T y v)) := by
  rw [continuous_iff_continuousAt]
  intro y
  obtain ⟨U, N, b, hy, hU, hN, hb, he⟩ := h y
  have hInv : ContinuousOn (fun w => (b.val (incl w))⁻¹) (incl ⁻¹' U) :=
    ((continuous_unramifiedRegularFunction ν b).comp hincl).continuousOn.inv₀
      (fun w hw => hb (incl w) hw)
  have hNum : Continuous (fun w => M (N (incl w) v)) :=
    (continuous_of_polynomial_univ (fun z => M (N z v)) ((hN v).linearMap M)).comp hincl
  have hEq : Set.EqOn (fun w => M (T w v))
      (fun w => (b.val (incl w))⁻¹ • M (N (incl w) v)) (incl ⁻¹' U) := by
    intro w hw
    have hv : T w v = (b.val (incl w))⁻¹ • N (incl w) v :=
      congrArg (fun J : V →ₗ[ℂ] W => J v) (he w hw)
    exact (congrArg M hv).trans (M.map_smul _ _)
  exact ((hInv.smul hNum.continuousOn).congr hEq).continuousAt ((hU.preimage hincl).mem_nhds hy)

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
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

local notation "H" => RationalPoint F G.X
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "E₀" => compactTensorEquiv χ hG K hK ψ hψ hψK A
local notation "C₀" => coefficientMap χ hG A C hC qMeasure hsq K hK ψ hψ hψK
local notation "B₀" => formalDegreeForm χ hG A C hC qMeasure hsq hi K hK ψ hψ hψK
local notation "L₀" => compactCoefficientAtOne χ hG A K hK ψ hψ hψK C hC qMeasure hsq
local notation "M₀" => compactFormalDegreeModel χ hG A K hK ψ hψ hψK C hC qMeasure hsq hi
local notation "F₀" z => coefficientFiber χ ψ hψ A (unitaryParameter χ z)
local notation "V₀" => compactFiber χ K ψ hψ A

omit [BorelSpace (levi χ ⧸ C)] [qMeasure.IsInvInvariant] in
private theorem coefficientMap_eq_one_action (z : Xu) (v : F₀ z) (g : H) :
    C₀ z v g = C₀ z ((F₀ z).representation (g, 1) v) 1 := by
  have he := CompactInduction.leviCoefficientMap_action
    (commonDecomposition χ ψ hψ) (radical_isClosed ψ) (twistObject χ (unitaryParameter χ z) A)
    K (DynamicOppositeCanonicalScalar.radical_unimodular ψ hG) hK
    (DynamicOppositeCanonicalScalar.parabolic_isClosed ψ) (commonProjection_continuous χ ψ hψ)
    (iwasawa_sets K ψ hψK) (ambient_modularCharacter hG) (common_modularCharacter χ hG ψ hψ)
    (unitaryTwist_squareIntegrable χ A C hC qMeasure hsq z).1 (g, 1) v 1
  change C₀ z ((F₀ z).representation (g, 1) v) 1 = C₀ z v ((1 : H)⁻¹ * 1 * g) at he
  simpa only [inv_one, one_mul] using he.symm

variable
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)
  (T : UnitaryComparisonFamily χ A ψ hψ ψ' hψ')

local notation "V₁" => compactFiber χ K ψ' hψ' A
local notation "F₁" z => coefficientFiber χ ψ' hψ' A (unitaryParameter χ z)
local notation "E₁" => compactTensorEquiv χ hG K hK ψ' hψ' hψ'K A
local notation "C₁" => coefficientMap χ hG A C hC qMeasure hsq K hK ψ' hψ' hψ'K
local notation "B₁" => formalDegreeForm χ hG A C hC qMeasure hsq hi K hK ψ' hψ' hψ'K
local notation "L₁" => compactCoefficientAtOne χ hG A K hK ψ' hψ' hψ'K C hC qMeasure hsq
local notation "M₁" => compactFormalDegreeModel χ hG A K hK ψ' hψ' hψ'K C hC qMeasure hsq hi
local notation "Tc" => compactValue χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K T
local notation "D" => ActualCommonLeviTensor.genericLocus χ hG K hK
  ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "Du" => (unitaryParameter χ) ⁻¹' D
local notation "Reg" => IsRegularUnitaryExtension χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T

/-- The compact transport square evaluated at an actual coefficient vector. -/
theorem compactValue_compactTensorEquiv (z : Xu) (v : F₀ z) :
    Tc z (E₀ (unitaryParameter χ z) v) = E₁ (unitaryParameter χ z) (T z v) := by
  let e := E₀ (unitaryParameter χ z)
  exact congrArg (fun a : F₀ z => E₁ (unitaryParameter χ z) (T z a)) (e.symm_apply_apply v)

/-- After a linear test into a normed carrier, regularity of the ambient
representatives gives continuity in the full unitary parameter group. -/
theorem IsRegularUnitaryExtension.continuous_compactValue_postcomp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hR : Reg) (M : V₁ →ₗ[ℂ] E) (v : V₀) :
    Continuous (fun z : Xu => M (Tc z v)) := by
  have hu : Continuous (unitaryParameter χ) :=
    continuous_subtype_val.subtype_mk (fun z => z.property.1)
  apply continuous_postcomp_of_local_rational (unitaryParameter χ) hu Tc M _ v
  intro z
  obtain ⟨U, N, b, hz, hN, hval⟩ := hR z
  exact ⟨U, N, b, hz, hN.1, hN.2.1, hN.2.2.1, hval⟩

omit [BorelSpace (levi χ ⧸ C)] [qMeasure.IsInvInvariant] in
private theorem coefficient_at_one_compactValue (z : Xu) (v : F₀ z) :
    L₁ (Tc z (E₀ (unitaryParameter χ z) v)) = C₁ z (T z v) 1 :=
  (congrArg L₁ (compactValue_compactTensorEquiv χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K T z v)).trans
    (compactCoefficientAtOne_compactTensorEquiv χ hG A K hK ψ' hψ' hψ'K C hC qMeasure hsq z (T z v))

omit [BorelSpace (levi χ ⧸ C)] [qMeasure.IsInvInvariant] in
/-- The identity coefficient on a dense unitary set determines the whole
coefficient at every unitary parameter for a regular product intertwiner. -/
theorem preserves_coefficients_of_regular_of_dense (hR : Reg) (hD : Dense Du)
    (hcoeff : ∀ z ∈ Du, ∀ v : F₀ z, C₁ z (T z v) 1 = C₀ z v 1)
    (z : Xu) (v : F₀ z) : C₁ z (T z v) = C₀ z v := by
  have he (a : V₀) : (fun w : Xu => L₁ (Tc w a)) = (fun _ : Xu => L₀ a) := by
    apply Continuous.ext_on hD
      (hR.continuous_compactValue_postcomp χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T L₁ a)
      continuous_const
    intro w hw
    let e := E₀ (unitaryParameter χ w)
    let b := e.symm a
    have hb : e b = a := e.apply_symm_apply a
    calc
      L₁ (Tc w a) = L₁ (Tc w (e b)) := congrArg (fun x : V₀ => L₁ (Tc w x)) hb.symm
      _ = C₁ w (T w b) 1 :=
        coefficient_at_one_compactValue χ hG A C hC qMeasure hsq K hK
          ψ hψ hψK ψ' hψ' hψ'K T w b
      _ = C₀ w b 1 := hcoeff w hw b
      _ = L₀ (e b) :=
        (compactCoefficientAtOne_compactTensorEquiv χ hG A K hK ψ hψ hψK
          C hC qMeasure hsq w b).symm
      _ = L₀ a := congrArg L₀ hb
  have hone (a : F₀ z) : C₁ z (T z a) 1 = C₀ z a 1 :=
    (coefficient_at_one_compactValue χ hG A C hC qMeasure hsq K hK ψ hψ hψK ψ' hψ' hψ'K T z a).symm.trans
      ((congrFun (he (E₀ (unitaryParameter χ z) a)) z).trans
        (compactCoefficientAtOne_compactTensorEquiv χ hG A K hK ψ hψ hψK C hC qMeasure hsq z a))
  apply LocallyConstant.ext
  intro g
  have ha : T z ((F₀ z).representation (g, 1) v) = (F₁ z).representation (g, 1) (T z v) :=
    Representation.IntertwiningMap.isIntertwining
      (F₀ z).representation (F₁ z).representation (T z) (g, 1) v
  calc
    C₁ z (T z v) g = C₁ z ((F₁ z).representation (g, 1) (T z v)) 1 :=
      coefficientMap_eq_one_action χ hG A C hC qMeasure hsq K hK ψ' hψ' hψ'K z (T z v) g
    _ = C₁ z (T z ((F₀ z).representation (g, 1) v)) 1 :=
      congrArg (fun a : F₁ z => C₁ z a 1) ha.symm
    _ = C₀ z ((F₀ z).representation (g, 1) v) 1 := hone _
    _ = C₀ z v g := (coefficientMap_eq_one_action χ hG A C hC qMeasure hsq K hK ψ hψ hψK z v g).symm

/-- The value of the comparison on the fixed source compact tensor with
target in the normed carrier of the exact fixed formal-degree form. -/
def formalDegreeCompactValue (z : Xu) := (M₁).toLinearMap.comp (Tc z)

local notation "Tm" => formalDegreeCompactValue χ hG A C hC qMeasure hsq hi
  K hK ψ hψ hψK ψ' hψ' hψ'K T

private theorem formalDegreeCompactValue_inner (z : Xu) (v w : F₀ z) :
    inner ℂ (Tm z (E₀ (unitaryParameter χ z) v)) (Tm z (E₀ (unitaryParameter χ z) w)) =
      (B₁ z).inner (T z v) (T z w) := by
  have hv := compactValue_compactTensorEquiv χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K T z v
  have hw := compactValue_compactTensorEquiv χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K T z w
  exact (congrArg₂ (fun a b : V₁ => inner ℂ (M₁ a) (M₁ b)) hv hw).trans
    (compactFormalDegreeModel_inner χ hG A K hK ψ' hψ' hψ'K C hC qMeasure hsq hi z (T z v) (T z w))

/-- The exact generic identity for the formal-degree forms extends to all
unitary points. Each input is held fixed in the compact tensor as the
unitary parameter varies. -/
theorem preserves_formalDegreeForm_of_regular_of_dense (hR : Reg) (hD : Dense Du)
    (hform : ∀ z ∈ Du, ∀ v w : F₀ z, (B₁ z).inner (T z v) (T z w) = (B₀ z).inner v w)
    (z : Xu) (v w : F₀ z) : (B₁ z).inner (T z v) (T z w) = (B₀ z).inner v w := by
  have hc (a : V₀) : Continuous (fun s : Xu => Tm s a) :=
    hR.continuous_compactValue_postcomp χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T (M₁).toLinearMap a
  have he (a b : V₀) : (fun s : Xu => inner ℂ (Tm s a) (Tm s b)) =
      (fun _ : Xu => inner ℂ (M₀ a) (M₀ b)) := by
    apply Continuous.ext_on hD ((hc a).inner (hc b)) continuous_const
    intro s hs
    let e := E₀ (unitaryParameter χ s)
    let v' := e.symm a
    let w' := e.symm b
    have hv : e v' = a := e.apply_symm_apply a
    have hw : e w' = b := e.apply_symm_apply b
    calc
      inner ℂ (Tm s a) (Tm s b) = inner ℂ (Tm s (e v')) (Tm s (e w')) :=
        congrArg₂ (fun x y : V₀ => inner ℂ (Tm s x) (Tm s y)) hv.symm hw.symm
      _ = (B₁ s).inner (T s v') (T s w') :=
        formalDegreeCompactValue_inner χ hG A C hC qMeasure hsq hi
          K hK ψ hψ hψK ψ' hψ' hψ'K T s v' w'
      _ = (B₀ s).inner v' w' := hform s hs v' w'
      _ = inner ℂ (M₀ (e v')) (M₀ (e w')) :=
        (compactFormalDegreeModel_inner χ hG A K hK ψ hψ hψK C hC qMeasure hsq hi s v' w').symm
      _ = inner ℂ (M₀ a) (M₀ b) :=
        congrArg₂ (fun x y : V₀ => inner ℂ (M₀ x) (M₀ y)) hv hw
  exact (formalDegreeCompactValue_inner χ hG A C hC qMeasure hsq hi
      K hK ψ hψ hψK ψ' hψ' hψ'K T z v w).symm.trans
    ((congrFun (he (E₀ (unitaryParameter χ z) v) (E₀ (unitaryParameter χ z) w)) z).trans
      (compactFormalDegreeModel_inner χ hG A K hK ψ hψ hψK C hC qMeasure hsq hi z v w))

end Langlands.Plancherel.ActualCommonLeviV3
