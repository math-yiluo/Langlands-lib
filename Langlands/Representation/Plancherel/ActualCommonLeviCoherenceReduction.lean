import Langlands.Representation.Plancherel.ActualCommonLeviCoherenceStatement
import Langlands.Representation.Plancherel.RationalUnramifiedScalarCancellation

/-! # Closed common-Levi coherence from V.3.1 and dense coefficient injectivity -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviCoherence

/-! ### Weakly continuous operator families on fixed carriers -/

section WeakContinuity

variable {Z : Type*} [TopologicalSpace Z]
  {V W X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

/-- Every algebraic scalar test of every fixed input gives a continuous function. -/
def IsWeaklyContinuousFamily (T : Z → V →ₗ[ℂ] W) : Prop :=
  ∀ (x : V) (f : W →ₗ[ℂ] ℂ), Continuous fun z => f (T z x)

/-- Near every parameter, each fixed input has a finite expansion in fixed
vectors with continuous scalar coefficients. -/
def IsLocallyFiniteFamily (T : Z → V →ₗ[ℂ] W) : Prop :=
  ∀ (z₀ : Z) (x : V), ∃ O : Set Z, IsOpen O ∧ z₀ ∈ O ∧
    ∃ (n : ℕ) (c : Fin n → Z → ℂ) (v : Fin n → W),
      (∀ i, ContinuousOn (c i) O) ∧ ∀ z ∈ O, T z x = ∑ i, c i z • v i

/-- A locally finite family followed by a weakly continuous family is weakly
continuous. -/
theorem IsLocallyFiniteFamily.comp_weaklyContinuous
    {T : Z → V →ₗ[ℂ] W} {S : Z → W →ₗ[ℂ] X}
    (hT : IsLocallyFiniteFamily T) (hS : IsWeaklyContinuousFamily S) :
    IsWeaklyContinuousFamily fun z => (S z).comp (T z) := by
  intro x f
  refine continuous_iff_continuousAt.mpr fun z₀ => ?_
  obtain ⟨O, hO, hz₀, n, c, v, hc, hTO⟩ := hT z₀ x
  have hcont : ContinuousOn (fun z => ∑ i, c i z * f (S z (v i))) O :=
    continuousOn_finsetSum _ fun i _ => (hc i).mul (hS (v i) f).continuousOn
  refine (hcont.continuousAt (hO.mem_nhds hz₀)).congr ?_
  filter_upwards [hO.mem_nhds hz₀] with z hz
  simp only [LinearMap.comp_apply, hTO z hz, _root_.map_sum, map_smul, smul_eq_mul]

/-- A locally finite family is weakly continuous. -/
theorem IsLocallyFiniteFamily.weaklyContinuous {T : Z → V →ₗ[ℂ] W}
    (hT : IsLocallyFiniteFamily T) : IsWeaklyContinuousFamily T := by
  have h := hT.comp_weaklyContinuous (S := fun _ => (LinearMap.id : W →ₗ[ℂ] W))
    (fun _ _ => continuous_const)
  simpa only [LinearMap.id_comp] using h

/-- Two weakly continuous families that agree on a dense set agree everywhere. -/
theorem IsWeaklyContinuousFamily.eq_of_eqOn_dense
    {T S : Z → V →ₗ[ℂ] W}
    (hT : IsWeaklyContinuousFamily T) (hS : IsWeaklyContinuousFamily S)
    {D : Set Z} (hD : Dense D) (hTS : ∀ z ∈ D, T z = S z) : T = S := by
  funext z
  apply LinearMap.ext
  intro x
  rw [← sub_eq_zero]
  apply (Module.forall_dual_apply_eq_zero_iff ℂ (T z x - S z x)).mp
  intro f
  have h := Continuous.ext_on hD (hT x f) (hS x f) (fun y hy => by
    simp only [hTS y hy])
  rw [map_sub, sub_eq_zero]
  exact congrFun h z

end WeakContinuity

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open ActualCommonLeviV3 UnramifiedOperatorFamily

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
  ambientMeasurable ambientBorel leviMeasurable leviBorel leviLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)

local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)

omit [LocallyOfFiniteType G.X.hom] in
/-- The inclusion of unitary parameters is continuous for the subspace topologies. -/
theorem continuous_unitaryParameter : Continuous (unitaryParameter χ) := by
  exact continuous_induced_rng.2 continuous_subtype_val

variable
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (qMeasure : Measure (levi χ ⧸ C)) [qMeasure.IsHaarMeasure] [qMeasure.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation qMeasure)
  (hi : A.representation.IsIrreducible)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

local notation "Par" => ParabolicPresentation χ K

/-- The fixed compact-carrier value of a comparison between two presentations. -/
abbrev pairValue (P Q : Par)
    (T : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq) (z : Xu) :
    compactFiber χ K P.cocharacter P.centralizer_eq A →ₗ[ℂ]
      compactFiber χ K Q.cocharacter Q.centralizer_eq A :=
  compactValue χ hG A K hK P.cocharacter P.centralizer_eq P.iwasawa
    Q.cocharacter Q.centralizer_eq Q.iwasawa T z

/-- The actual coefficient map of a presentation at a unitary parameter. -/
abbrev presentationCoefficientMap (P : Par) (z : Xu) :=
  coefficientMap χ hG A C hC qMeasure hsq K hK P.cocharacter P.centralizer_eq P.iwasawa z

/-- Evaluation of the fixed compact-carrier value. -/
theorem pairValue_apply (P Q : Par)
    (T : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq) (z : Xu)
    (v : coefficientFiber χ P.cocharacter P.centralizer_eq A (unitaryParameter χ z)) :
    pairValue χ hG A K hK P Q T z
        (compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
          (unitaryParameter χ z) v) =
      compactTensorEquiv χ hG K hK Q.cocharacter Q.centralizer_eq Q.iwasawa A
        (unitaryParameter χ z) (T z v) := by
  change compactTensorEquiv χ hG K hK Q.cocharacter Q.centralizer_eq Q.iwasawa A
      (unitaryParameter χ z) (T z ((compactTensorEquiv χ hG K hK P.cocharacter
        P.centralizer_eq P.iwasawa A (unitaryParameter χ z)).symm
          (compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
            (unitaryParameter χ z) v))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The fixed-carrier value determines the comparison on the actual fibers. -/
theorem eq_of_pairValue_eq (P Q : Par)
    {T S : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq} (z : Xu)
    (h : pairValue χ hG A K hK P Q T z = pairValue χ hG A K hK P Q S z) :
    T z = S z := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have hv := LinearMap.congr_fun h
    (compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
      (unitaryParameter χ z) v)
  rw [pairValue_apply, pairValue_apply] at hv
  exact (compactTensorEquiv χ hG K hK Q.cocharacter Q.centralizer_eq Q.iwasawa A
    (unitaryParameter χ z)).injective hv

/-- The fixed-carrier value at a point depends only on the comparison there. -/
theorem pairValue_congr (P Q : Par)
    {T S : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq} (z : Xu) (h : T z = S z) :
    pairValue χ hG A K hK P Q T z = pairValue χ hG A K hK P Q S z := by
  change compactValue χ hG A K hK P.cocharacter P.centralizer_eq P.iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa T z =
    compactValue χ hG A K hK P.cocharacter P.centralizer_eq P.iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa S z
  unfold compactValue
  rw [h]

/-- On the fixed compact carriers, a pointwise identity comparison is the
identity map. -/
theorem pairValue_eq_id_iff (P : Par)
    (T : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      P.cocharacter P.centralizer_eq) (z : Xu) :
    (∀ v : coefficientFiber χ P.cocharacter P.centralizer_eq A (unitaryParameter χ z),
      T z v = v) ↔ pairValue χ hG A K hK P P T z = LinearMap.id := by
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := (compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq
      P.iwasawa A (unitaryParameter χ z)).surjective x
    rw [pairValue_apply, h v, LinearMap.id_apply]
  · intro h v
    apply (compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
      (unitaryParameter χ z)).injective
    exact ((pairValue_apply χ hG A K hK P P T z v).symm.trans
      (LinearMap.congr_fun h _)).trans (LinearMap.id_apply _)

/-- On the fixed compact carriers, a pointwise composition identity is the
composition identity of the carrier values. -/
theorem pairValue_comp_eq_iff (P Q R : Par)
    (T₀₁ : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq)
    (T₁₂ : UnitaryComparisonFamily χ A Q.cocharacter Q.centralizer_eq
      R.cocharacter R.centralizer_eq)
    (T₀₂ : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      R.cocharacter R.centralizer_eq) (z : Xu) :
    (∀ v : coefficientFiber χ P.cocharacter P.centralizer_eq A (unitaryParameter χ z),
      T₁₂ z (T₀₁ z v) = T₀₂ z v) ↔
      (pairValue χ hG A K hK Q R T₁₂ z).comp (pairValue χ hG A K hK P Q T₀₁ z) =
        pairValue χ hG A K hK P R T₀₂ z := by
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := (compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq
      P.iwasawa A (unitaryParameter χ z)).surjective x
    exact (LinearMap.comp_apply (pairValue χ hG A K hK Q R T₁₂ z)
        (pairValue χ hG A K hK P Q T₀₁ z) _).trans
      (((congrArg (pairValue χ hG A K hK Q R T₁₂ z)
        (pairValue_apply χ hG A K hK P Q T₀₁ z v)).trans
        ((pairValue_apply χ hG A K hK Q R T₁₂ z (T₀₁ z v)).trans
          (congrArg (compactTensorEquiv χ hG K hK R.cocharacter R.centralizer_eq R.iwasawa A
            (unitaryParameter χ z)) (h v)))).trans
        (pairValue_apply χ hG A K hK P R T₀₂ z v).symm)
  · intro h v
    apply (compactTensorEquiv χ hG K hK R.cocharacter R.centralizer_eq R.iwasawa A
      (unitaryParameter χ z)).injective
    exact (pairValue_apply χ hG A K hK Q R T₁₂ z (T₀₁ z v)).symm.trans
      ((congrArg (pairValue χ hG A K hK Q R T₁₂ z)
        (pairValue_apply χ hG A K hK P Q T₀₁ z v)).symm.trans
        ((LinearMap.comp_apply (pairValue χ hG A K hK Q R T₁₂ z)
          (pairValue χ hG A K hK P Q T₀₁ z) _).symm.trans
          ((LinearMap.congr_fun h _).trans (pairValue_apply χ hG A K hK P R T₀₂ z v))))

/-- Ambient local regular representatives make the compact-carrier value
locally finite on the unitary parameters, for any presentation. -/
theorem isLocallyFinite_of_regularUnitaryExtension (P Q : Par)
    (p : ContinuedPair χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa A)
    (q : ContinuedPair χ hG K hK Q.cocharacter Q.centralizer_eq Q.iwasawa
      P.cocharacter P.centralizer_eq P.iwasawa A.contragredient)
    (T : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq)
    (hT : IsRegularUnitaryExtension χ hG A K hK P.cocharacter P.centralizer_eq P.iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa p q T) :
    IsLocallyFiniteFamily (pairValue χ hG A K hK P Q T) := by
  intro z₀ x
  obtain ⟨U, N, b, hzU, ⟨hUo, hN, hb, -⟩, hval⟩ := hT z₀
  obtain ⟨n, c, v, hc⟩ := hN x
  refine ⟨unitaryParameter χ ⁻¹' U, hUo.preimage (continuous_unitaryParameter χ), hzU, n,
    fun i w => (b.val (unitaryParameter χ w))⁻¹ * (c i).val (unitaryParameter χ w), v,
    fun i => ?_, fun w hw => ?_⟩
  · have hbc := (continuous_unramifiedRegularFunction _ b).comp
      (continuous_unitaryParameter χ)
    have hcc := (continuous_unramifiedRegularFunction _ (c i)).comp
      (continuous_unitaryParameter χ)
    exact (hbc.continuousOn.inv₀ (fun w hw => hb _ hw)).mul hcc.continuousOn
  · change compactValue χ hG A K hK P.cocharacter P.centralizer_eq P.iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa T w x = _
    have hcw := hc ⟨unitaryParameter χ w, Set.mem_univ _⟩
    simp only at hcw
    rw [hval w hw, LinearMap.smul_apply, hcw, Finset.smul_sum]
    simp only [smul_smul]

/-! ### Uniqueness at coefficient-injective unitary parameters -/

section Pointwise

/-- Two coefficient-preserving bijective comparisons agree wherever the source
coefficient map is injective. -/
theorem eq_of_preservesCoefficients (P Q : Par) (z : Xu)
    {T S : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq}
    (hT : PreservesCoefficientsAndForms χ hG A C hC qMeasure hsq hi K hK
      P.cocharacter P.centralizer_eq P.iwasawa Q.cocharacter Q.centralizer_eq Q.iwasawa T)
    (hS : PreservesCoefficientsAndForms χ hG A C hC qMeasure hsq hi K hK
      P.cocharacter P.centralizer_eq P.iwasawa Q.cocharacter Q.centralizer_eq Q.iwasawa S)
    (hinj : Function.Injective (presentationCoefficientMap χ hG A C hC qMeasure hsq K hK P z)) :
    T z = S z := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  obtain ⟨u, hu⟩ := (hS z).1.2 (T z v)
  have hcoef : presentationCoefficientMap χ hG A C hC qMeasure hsq K hK P z u =
      presentationCoefficientMap χ hG A C hC qMeasure hsq K hK P z v := by
    rw [← (hS z).2.1 u, hu, (hT z).2.1 v]
  have huv := hinj hcoef
  subst huv
  exact hu.symm

/-- A coefficient-preserving self-comparison is the identity wherever the
coefficient map is injective. -/
theorem eq_self_of_preservesCoefficients (P : Par) (z : Xu)
    {T : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      P.cocharacter P.centralizer_eq}
    (hT : PreservesCoefficientsAndForms χ hG A C hC qMeasure hsq hi K hK
      P.cocharacter P.centralizer_eq P.iwasawa P.cocharacter P.centralizer_eq P.iwasawa T)
    (hinj : Function.Injective (presentationCoefficientMap χ hG A C hC qMeasure hsq K hK P z))
    (v : coefficientFiber χ P.cocharacter P.centralizer_eq A (unitaryParameter χ z)) :
    T z v = v :=
  hinj ((hT z).2.1 v)

/-- Coefficient-preserving bijective comparisons compose wherever the source
coefficient map is injective. -/
theorem comp_eq_of_preservesCoefficients (P Q R : Par) (z : Xu)
    {T₀₁ : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq}
    {T₁₂ : UnitaryComparisonFamily χ A Q.cocharacter Q.centralizer_eq
      R.cocharacter R.centralizer_eq}
    {T₀₂ : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      R.cocharacter R.centralizer_eq}
    (h₀₁ : PreservesCoefficientsAndForms χ hG A C hC qMeasure hsq hi K hK
      P.cocharacter P.centralizer_eq P.iwasawa Q.cocharacter Q.centralizer_eq Q.iwasawa T₀₁)
    (h₁₂ : PreservesCoefficientsAndForms χ hG A C hC qMeasure hsq hi K hK
      Q.cocharacter Q.centralizer_eq Q.iwasawa R.cocharacter R.centralizer_eq R.iwasawa T₁₂)
    (h₀₂ : PreservesCoefficientsAndForms χ hG A C hC qMeasure hsq hi K hK
      P.cocharacter P.centralizer_eq P.iwasawa R.cocharacter R.centralizer_eq R.iwasawa T₀₂)
    (hinj : Function.Injective (presentationCoefficientMap χ hG A C hC qMeasure hsq K hK P z))
    (v : coefficientFiber χ P.cocharacter P.centralizer_eq A (unitaryParameter χ z)) :
    T₁₂ z (T₀₁ z v) = T₀₂ z v := by
  obtain ⟨u, hu⟩ := (h₀₂ z).1.2 (T₁₂ z (T₀₁ z v))
  have hcoef : presentationCoefficientMap χ hG A C hC qMeasure hsq K hK P z u =
      presentationCoefficientMap χ hG A C hC qMeasure hsq K hK P z v := by
    rw [← (h₀₂ z).2.1 u, hu, (h₁₂ z).2.1, (h₀₁ z).2.1 v]
  have huv := hinj hcoef
  subst huv
  exact hu.symm


end Pointwise

/-! ### The reduction -/

/-- Closed common-Levi coherence follows from the pairwise closed V.3.1
statements together with density, on the unitary parameters, of the points
where each source coefficient map is injective. -/
theorem closedCommonLeviCoherence_of_v31_of_dense_injective
    (hV31 : ∀ P Q : Par, ClosedV31Statement χ hG A C hC qMeasure hsq hi K hK
      P.cocharacter P.centralizer_eq P.iwasawa Q.cocharacter Q.centralizer_eq Q.iwasawa)
    (hdense : IsActualSplitCenter χ C → ∀ P : Par, Dense {z : Xu |
      Function.Injective (presentationCoefficientMap χ hG A C hC qMeasure hsq K hK P z)}) :
    ClosedCommonLeviCoherenceStatement χ hG A C hC qMeasure hsq hi K hK := by
  intro hcenter
  have hD := hdense hcenter
  have hfin : ∀ (P Q : Par) (T : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq),
      IsActualNormalizedComparison χ hG A C hC qMeasure hsq hi K hK P Q T →
        IsLocallyFiniteFamily (pairValue χ hG A K hK P Q T) := by
    rintro P Q T ⟨p, q, -, -, -, hreg, -, -, -⟩
    exact isLocallyFinite_of_regularUnitaryExtension χ hG A K hK P Q p q T hreg
  have hpres : ∀ (P Q : Par) (T : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq),
      IsActualNormalizedComparison χ hG A C hC qMeasure hsq hi K hK P Q T →
        PreservesCoefficientsAndForms χ hG A C hC qMeasure hsq hi K hK
          P.cocharacter P.centralizer_eq P.iwasawa Q.cocharacter Q.centralizer_eq Q.iwasawa T := by
    rintro P Q T ⟨-, -, -, -, -, -, -, -, h⟩
    exact h
  have hindep : PresentationIndependenceStatement χ hG A C hC qMeasure hsq hi K hK := by
    intro P Q T S hT hS
    have hval : pairValue χ hG A K hK P Q T = pairValue χ hG A K hK P Q S :=
      (hfin P Q T hT).weaklyContinuous.eq_of_eqOn_dense (hfin P Q S hS).weaklyContinuous
        (hD P) fun z hz => pairValue_congr χ hG A K hK P Q z
          (eq_of_preservesCoefficients χ hG A C hC qMeasure hsq hi K hK P Q z
            (hpres P Q T hT) (hpres P Q S hS) hz)
    funext z
    exact eq_of_pairValue_eq χ hG A K hK P Q z (congrFun hval z)
  have hex : ∀ P Q : Par, ∃ T : UnitaryComparisonFamily χ A P.cocharacter P.centralizer_eq
      Q.cocharacter Q.centralizer_eq,
      IsActualNormalizedComparison χ hG A C hC qMeasure hsq hi K hK P Q T := fun P Q =>
    (closedV31_iff_exists χ hG A C hC qMeasure hsq hi K hK hcenter P Q).mp (hV31 P Q)
  choose T hT using hex
  have hid : IdentityLaw χ A K T := by
    intro P
    have hval : pairValue χ hG A K hK P P (T P P) = fun _ => LinearMap.id :=
      (hfin P P (T P P) (hT P P)).weaklyContinuous.eq_of_eqOn_dense
        (fun _ _ => continuous_const) (hD P) fun z hz =>
          (pairValue_eq_id_iff χ hG A K hK P (T P P) z).mp
            (eq_self_of_preservesCoefficients χ hG A C hC qMeasure hsq hi K hK P z
              (hpres P P (T P P) (hT P P)) hz)
    intro z v
    exact (pairValue_eq_id_iff χ hG A K hK P (T P P) z).mpr (congrFun hval z) v
  have hcomp : CompositionLaw χ A K T := by
    intro P Q R
    have hval : (fun z => (pairValue χ hG A K hK Q R (T Q R) z).comp
        (pairValue χ hG A K hK P Q (T P Q) z)) = pairValue χ hG A K hK P R (T P R) :=
      ((hfin P Q (T P Q) (hT P Q)).comp_weaklyContinuous
        (hfin Q R (T Q R) (hT Q R)).weaklyContinuous).eq_of_eqOn_dense
          (hfin P R (T P R) (hT P R)).weaklyContinuous (hD P) fun z hz =>
            (pairValue_comp_eq_iff χ hG A K hK P Q R (T P Q) (T Q R) (T P R) z).mp
              (comp_eq_of_preservesCoefficients χ hG A C hC qMeasure hsq hi K hK P Q R z
                (hpres P Q (T P Q) (hT P Q)) (hpres Q R (T Q R) (hT Q R))
                (hpres P R (T P R) (hT P R)) hz)
    intro z v
    exact (pairValue_comp_eq_iff χ hG A K hK P Q R (T P Q) (T Q R) (T P R) z).mpr
      (congrFun hval z) v
  exact ⟨⟨T, hT, hid, hcomp, inverseLaw_of_identity_composition χ A K T hid hcomp⟩, hindep⟩

end Langlands.Plancherel.ActualCommonLeviCoherence
