import Langlands.Representation.Plancherel.ActualConjugateLeviCoherenceStatement
import Langlands.Representation.Plancherel.ActualCommonLeviCoherenceProof

/-! # Compact charts, weak continuity and dense coefficient agreement -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualConjugateLeviCoherence

open ActualCommonLeviCoherence

/-! ### Locally finite families -/

section Families

variable {Z Z' : Type*} [TopologicalSpace Z] [TopologicalSpace Z']
  {U V W X : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]

/-- A constant family of linear maps is locally finite. -/
theorem isLocallyFiniteFamily_const (T : V →ₗ[ℂ] W) :
    IsLocallyFiniteFamily (fun _ : Z => T) := by
  intro z₀ x
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, fun _ _ => 1, fun _ => T x,
    fun _ => continuousOn_const, ?_⟩
  intro z _
  simp

/-- Precomposition with a fixed linear map keeps local finiteness. -/
theorem IsLocallyFiniteFamily.precomp {T : Z → V →ₗ[ℂ] W}
    (hT : IsLocallyFiniteFamily T) (S : U →ₗ[ℂ] V) :
    IsLocallyFiniteFamily fun z => (T z).comp S :=
  fun z₀ x => hT z₀ (S x)

/-- Postcomposition with a fixed linear map keeps local finiteness. -/
theorem IsLocallyFiniteFamily.postcomp {T : Z → V →ₗ[ℂ] W}
    (hT : IsLocallyFiniteFamily T) (S : W →ₗ[ℂ] X) :
    IsLocallyFiniteFamily fun z => S.comp (T z) := by
  intro z₀ x
  obtain ⟨O, hO, hz, n, c, v, hc, h⟩ := hT z₀ x
  refine ⟨O, hO, hz, n, c, fun i => S (v i), hc, fun z hz => ?_⟩
  simp only [LinearMap.comp_apply, h z hz, _root_.map_sum, map_smul]

/-- Reindexing along a continuous map keeps local finiteness. -/
theorem IsLocallyFiniteFamily.comp_continuous {T : Z' → V →ₗ[ℂ] W}
    (hT : IsLocallyFiniteFamily T) {φ : Z → Z'} (hφ : Continuous φ) :
    IsLocallyFiniteFamily fun z => T (φ z) := by
  intro z₀ x
  obtain ⟨O, hO, hz, n, c, v, hc, h⟩ := hT (φ z₀) x
  exact ⟨φ ⁻¹' O, hO.preimage hφ, hz, n, fun i z => c i (φ z), v,
    fun i => (hc i).comp hφ.continuousOn (Set.mapsTo_preimage φ O),
    fun z hz => h (φ z) hz⟩

end Families

/-! ### Dense coefficient agreement -/

section Agreement

variable {Z : Type*} [TopologicalSpace Z]
  {S T : Z → Type*} [∀ z, AddCommGroup (S z)] [∀ z, Module ℂ (S z)]
  [∀ z, AddCommGroup (T z)] [∀ z, Module ℂ (T z)]
  {V₀ W₀ : Type*} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup W₀] [Module ℂ W₀]
  {Y : Type*}

/-- Two families on varying carriers agree when both preserve coefficients,
the second is pointwise surjective, the source coefficients are injective on a
dense set of parameters, and both families are weakly continuous in fixed
charts. -/
theorem eq_of_coefficient_dense
    (cS : ∀ z, S z ≃ₗ[ℂ] V₀) (cT : ∀ z, T z ≃ₗ[ℂ] W₀)
    (coefS : ∀ z, S z → Y) (coefT : ∀ z, T z → Y)
    (Φ Ψ : ∀ z, S z →ₗ[ℂ] T z)
    (hΦ : ∀ z v, coefT z (Φ z v) = coefS z v)
    (hΨ : ∀ z v, coefT z (Ψ z v) = coefS z v)
    (hΨs : ∀ z, Function.Surjective (Ψ z))
    {D : Set Z} (hD : Dense D) (hinj : ∀ z ∈ D, Function.Injective (coefS z))
    (hΦc : IsWeaklyContinuousFamily fun z =>
      (cT z).toLinearMap.comp ((Φ z).comp (cS z).symm.toLinearMap))
    (hΨc : IsWeaklyContinuousFamily fun z =>
      (cT z).toLinearMap.comp ((Ψ z).comp (cS z).symm.toLinearMap))
    (z : Z) (v : S z) : Φ z v = Ψ z v := by
  have hpt : ∀ z ∈ D, Φ z = Ψ z := by
    intro z hz
    apply LinearMap.ext
    intro v
    obtain ⟨u, hu⟩ := hΨs z (Φ z v)
    have hc : coefS z u = coefS z v := by
      rw [← hΨ z u, hu, hΦ z v]
    rw [← hu, hinj z hz hc]
  have hval := hΦc.eq_of_eqOn_dense hΨc hD fun z hz => by rw [hpt z hz]
  have h := LinearMap.congr_fun (congrFun hval z) (cS z v)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  exact (cT z).injective h

end Agreement

/-! ### Families read in fixed charts -/

section ChartValues

variable {Z : Type*} [TopologicalSpace Z]
  {S T R : Z → Type*} [∀ z, AddCommGroup (S z)] [∀ z, Module ℂ (S z)]
  [∀ z, AddCommGroup (T z)] [∀ z, Module ℂ (T z)]
  [∀ z, AddCommGroup (R z)] [∀ z, Module ℂ (R z)]
  {V₀ V₁ V₂ V₃ : Type*} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]

/-- A family of linear maps between varying carriers, read in fixed charts. -/
def chartValue (cS : ∀ z, S z ≃ₗ[ℂ] V₀) (cT : ∀ z, T z ≃ₗ[ℂ] V₁)
    (Φ : ∀ z, S z →ₗ[ℂ] T z) (z : Z) : V₀ →ₗ[ℂ] V₁ :=
  (cT z).toLinearMap.comp ((Φ z).comp (cS z).symm.toLinearMap)

omit [TopologicalSpace Z] in
/-- The chart value of a pointwise composite is the composite of the chart
values. -/
theorem chartValue_comp (cS : ∀ z, S z ≃ₗ[ℂ] V₀) (cT : ∀ z, T z ≃ₗ[ℂ] V₁)
    (cR : ∀ z, R z ≃ₗ[ℂ] V₂) (Φ : ∀ z, S z →ₗ[ℂ] T z) (Ψ : ∀ z, T z →ₗ[ℂ] R z) (z : Z) :
    chartValue cS cR (fun z => (Ψ z).comp (Φ z)) z =
      (chartValue cT cR Ψ z).comp (chartValue cS cT Φ z) := by
  apply LinearMap.ext
  intro x
  simp only [chartValue, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

omit [TopologicalSpace Z] in
/-- The chart value of the identity family is the identity. -/
theorem chartValue_id (cS : ∀ z, S z ≃ₗ[ℂ] V₀) (z : Z) :
    chartValue cS cS (fun z => (LinearMap.id : S z →ₗ[ℂ] S z)) z = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [chartValue, LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- A family that does not depend on the parameter is locally finite. -/
theorem isLocallyFiniteFamily_of_forall_eq {T : Z → V₀ →ₗ[ℂ] V₁}
    (h : ∀ z z', T z = T z') : IsLocallyFiniteFamily T := by
  intro z₀ x
  have hT : T = fun _ => T z₀ := funext fun z => h z z₀
  rw [hT]
  exact isLocallyFiniteFamily_const (T z₀) z₀ x

/-- A locally finite family between two parameter-independent families is
locally finite. -/
theorem IsLocallyFiniteFamily.sandwich {a : Z → V₀ →ₗ[ℂ] V₁} {b : Z → V₁ →ₗ[ℂ] V₂}
    {c : Z → V₂ →ₗ[ℂ] V₃} (ha : ∀ z z', a z = a z') (hb : IsLocallyFiniteFamily b)
    (hc : ∀ z z', c z = c z') :
    IsLocallyFiniteFamily fun z => (c z).comp ((b z).comp (a z)) := by
  intro z₀ x
  have he : (fun z => (c z).comp ((b z).comp (a z))) =
      fun z => (c z₀).comp ((b z).comp (a z₀)) :=
    funext fun z => by rw [ha z z₀, hc z z₀]
  rw [he]
  exact IsLocallyFiniteFamily.postcomp (IsLocallyFiniteFamily.precomp hb (a z₀)) (c z₀) z₀ x

/-- A locally finite family after a parameter-independent family is locally
finite. -/
theorem IsLocallyFiniteFamily.comp_const {a : Z → V₀ →ₗ[ℂ] V₁} {b : Z → V₁ →ₗ[ℂ] V₂}
    (ha : ∀ z z', a z = a z') (hb : IsLocallyFiniteFamily b) :
    IsLocallyFiniteFamily fun z => (b z).comp (a z) := by
  intro z₀ x
  have he : (fun z => (b z).comp (a z)) = fun z => (b z).comp (a z₀) :=
    funext fun z => by rw [ha z z₀]
  rw [he]
  exact IsLocallyFiniteFamily.precomp hb (a z₀) z₀ x

/-- The chart value of the identity family is weakly continuous. -/
theorem isWeaklyContinuousFamily_chartValue_id (cS : ∀ z, S z ≃ₗ[ℂ] V₀) :
    IsWeaklyContinuousFamily (chartValue cS cS fun z => (LinearMap.id : S z →ₗ[ℂ] S z)) := by
  have he : chartValue cS cS (fun z => (LinearMap.id : S z →ₗ[ℂ] S z)) =
      fun _ => LinearMap.id := funext fun z => chartValue_id cS z
  rw [he]
  exact fun _ _ => continuous_const

/-- The chart value of a family that is a translation, a locally finite family
and a transport, the outer two parameter-independent in the charts, is
weakly continuous. -/
theorem isLocallyFiniteFamily_chartValue_comp₃ {I J : Z → Type*}
    [∀ z, AddCommGroup (I z)] [∀ z, Module ℂ (I z)]
    [∀ z, AddCommGroup (J z)] [∀ z, Module ℂ (J z)]
    (cS : ∀ z, S z ≃ₗ[ℂ] V₀) (cI : ∀ z, I z ≃ₗ[ℂ] V₁) (cJ : ∀ z, J z ≃ₗ[ℂ] V₂)
    (cT : ∀ z, T z ≃ₗ[ℂ] V₃)
    (Tr : ∀ z, S z →ₗ[ℂ] I z) (U : ∀ z, I z →ₗ[ℂ] J z) (E : ∀ z, J z →ₗ[ℂ] T z)
    (hTr : ∀ z z', chartValue cS cI Tr z = chartValue cS cI Tr z')
    (hU : IsLocallyFiniteFamily (chartValue cI cJ U))
    (hE : ∀ z z', chartValue cJ cT E z = chartValue cJ cT E z') :
    IsLocallyFiniteFamily (chartValue cS cT fun z => (E z).comp ((U z).comp (Tr z))) := by
  have he : chartValue cS cT (fun z => (E z).comp ((U z).comp (Tr z))) =
      fun z => (chartValue cJ cT E z).comp ((chartValue cI cJ U z).comp (chartValue cS cI Tr z)) :=
    funext fun z => by rw [chartValue_comp cS cJ cT, chartValue_comp cS cI cJ]
  rw [he]
  exact IsLocallyFiniteFamily.sandwich hTr hU hE

/-- The chart value of a translation followed by a locally finite family is
locally finite when the translation is parameter-independent in the charts. -/
theorem isLocallyFiniteFamily_chartValue_comp₂ {I : Z → Type*}
    [∀ z, AddCommGroup (I z)] [∀ z, Module ℂ (I z)]
    (cS : ∀ z, S z ≃ₗ[ℂ] V₀) (cI : ∀ z, I z ≃ₗ[ℂ] V₁) (cT : ∀ z, T z ≃ₗ[ℂ] V₂)
    (Tr : ∀ z, S z →ₗ[ℂ] I z) (U : ∀ z, I z →ₗ[ℂ] T z)
    (hTr : ∀ z z', chartValue cS cI Tr z = chartValue cS cI Tr z')
    (hU : IsLocallyFiniteFamily (chartValue cI cT U)) :
    IsLocallyFiniteFamily (chartValue cS cT fun z => (U z).comp (Tr z)) := by
  have he : chartValue cS cT (fun z => (U z).comp (Tr z)) =
      fun z => (chartValue cI cT U z).comp (chartValue cS cI Tr z) :=
    funext fun z => chartValue_comp cS cI cT Tr U z
  rw [he]
  exact IsLocallyFiniteFamily.comp_const hTr hU

/-- A loop made of a translation, a locally finite family and a transport, the
outer two parameter-independent in the charts, is the identity when it
preserves coefficients that are injective on a dense set of parameters. -/
theorem eq_self_of_loop {I J : Z → Type*} {Y : Type*}
    [∀ z, AddCommGroup (I z)] [∀ z, Module ℂ (I z)]
    [∀ z, AddCommGroup (J z)] [∀ z, Module ℂ (J z)]
    (cS : ∀ z, S z ≃ₗ[ℂ] V₀) (cI : ∀ z, I z ≃ₗ[ℂ] V₁) (cJ : ∀ z, J z ≃ₗ[ℂ] V₂)
    (coef : ∀ z, S z → Y)
    (Tr : ∀ z, S z →ₗ[ℂ] I z) (U : ∀ z, I z →ₗ[ℂ] J z) (E : ∀ z, J z →ₗ[ℂ] S z)
    (hcoef : ∀ z v, coef z (E z (U z (Tr z v))) = coef z v)
    {D : Set Z} (hD : Dense D) (hinj : ∀ z ∈ D, Function.Injective (coef z))
    (hTr : ∀ z z', chartValue cS cI Tr z = chartValue cS cI Tr z')
    (hU : IsLocallyFiniteFamily (chartValue cI cJ U))
    (hE : ∀ z z', chartValue cJ cS E z = chartValue cJ cS E z') (z : Z) (v : S z) :
    E z (U z (Tr z v)) = v :=
  eq_of_coefficient_dense cS cS coef coef (fun z => (E z).comp ((U z).comp (Tr z)))
    (fun _ => LinearMap.id) hcoef (fun _ _ => rfl) (fun _ => Function.surjective_id) hD hinj
    (isLocallyFiniteFamily_chartValue_comp₃ cS cI cJ cS Tr U E hTr hU hE).weaklyContinuous
    (isWeaklyContinuousFamily_chartValue_id cS) z v

/-- Two families agree when they preserve coefficients that are injective on a
  dense set, the second family is surjective and weakly continuous, and the
  first is a composite of two locally finite families and a transport that is
  constant in the fixed charts. -/
theorem eq_of_chain {I J : Z → Type*} {Y : Type*}
    [∀ z, AddCommGroup (I z)] [∀ z, Module ℂ (I z)]
    [∀ z, AddCommGroup (J z)] [∀ z, Module ℂ (J z)]
    (cS : ∀ z, S z ≃ₗ[ℂ] V₀) (cI : ∀ z, I z ≃ₗ[ℂ] V₁) (cJ : ∀ z, J z ≃ₗ[ℂ] V₂)
    (cT : ∀ z, T z ≃ₗ[ℂ] V₃) (coefS : ∀ z, S z → Y) (coefT : ∀ z, T z → Y)
    (U : ∀ z, S z →ₗ[ℂ] I z) (V : ∀ z, I z →ₗ[ℂ] J z) (E : ∀ z, J z →ₗ[ℂ] T z)
    (Ψ : ∀ z, S z →ₗ[ℂ] T z)
    (hΦ : ∀ z v, coefT z (E z (V z (U z v))) = coefS z v)
    (hΨ : ∀ z v, coefT z (Ψ z v) = coefS z v) (hΨs : ∀ z, Function.Surjective (Ψ z))
    {D : Set Z} (hD : Dense D) (hinj : ∀ z ∈ D, Function.Injective (coefS z))
    (hU : IsLocallyFiniteFamily (chartValue cS cI U))
    (hV : IsLocallyFiniteFamily (chartValue cI cJ V))
    (hE : ∀ z z', chartValue cJ cT E z = chartValue cJ cT E z')
    (hΨc : IsWeaklyContinuousFamily (chartValue cS cT Ψ)) (z : Z) (v : S z) :
    E z (V z (U z v)) = Ψ z v := by
  have hc : IsWeaklyContinuousFamily (chartValue cS cT fun z => ((E z).comp (V z)).comp (U z)) := by
    have he : chartValue cS cT (fun z => ((E z).comp (V z)).comp (U z)) =
        fun z => ((chartValue cJ cT E z).comp (chartValue cI cJ V z)).comp
          (chartValue cS cI U z) :=
      funext fun z => by rw [chartValue_comp cS cI cT, chartValue_comp cI cJ cT]
    rw [he]
    exact hU.comp_weaklyContinuous (hV.comp_weaklyContinuous
      (isLocallyFiniteFamily_of_forall_eq hE).weaklyContinuous)
  exact eq_of_coefficient_dense cS cT coefS coefT (fun z => ((E z).comp (V z)).comp (U z)) Ψ
    hΦ hΨ hΨs hD hinj hc hΨc z v

end ChartValues

/-! ### Fixed compact charts -/

section CompactCharts

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviV3

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
  ActualCommonLeviV3.ambientMeasurable ActualCommonLeviV3.ambientBorel
  ActualCommonLeviV3.parabolicLocallyCompact ActualCommonLeviV3.radicalLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- Values of a section of the actual coefficient fiber, at a pair of points. -/
abbrev fiberEval (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (z : unramifiedCharacters (normCharacters χ))
    (f : coefficientFiber χ ψ hψ A z) (x : RationalPoint F G.X × RationalPoint F G.X) :
    CoefficientTensor (twistObject χ z A) :=
  Induction.eval ((parabolic ψ).prod (parabolic ψ))
    (leviInflatedInducingRepresentation
      (IsSemidirectDecomposition.prod (commonDecomposition χ ψ hψ) (commonDecomposition χ ψ hψ))
      (IsClosed.prod (radical_isClosed ψ) (radical_isClosed ψ))
      (productLeviObject (twistObject χ z A) (twistObject χ z A).contragredient)) f x

/-- Removal of the unramified twist from coefficient values. -/
abbrev untwistValue (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (z : unramifiedCharacters (normCharacters χ)) :
    CoefficientTensor (twistObject χ z A) ≃ₗ[ℂ] CoefficientTensor A :=
  productCompactTwistTensorEquiv (leviNormCharacters χ) (parameterTransport χ z) A

/-- Values of a vector of the fixed compact carrier at a point of `K × K`. -/
def compactEval (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (v : compactFiber χ K ψ hψ A) (k : K.prod K) :
    CoefficientTensor A :=
  Induction.eval _ _ (compactProductTensorEquiv χ hG A K hK ψ hψ hψK v) k

theorem compactEval_injective (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) :
    Function.Injective (compactEval hG K hK χ ψ hψ hψK A) := fun _ _ h =>
  (compactProductTensorEquiv χ hG A K hK ψ hψ hψK).injective (Subtype.ext (Subtype.ext h))

/-- The fixed chart reads the untwisted values of a section on `K × K`. -/
theorem compactEval_compactTensorEquiv (χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (z : unramifiedCharacters (normCharacters χ))
    (f : coefficientFiber χ ψ hψ A z) (k : K.prod K) :
    compactEval hG K hK χ ψ hψ hψK A (compactTensorEquiv χ hG K hK ψ hψ hψK A z f) k =
      untwistValue χ A z (fiberEval χ ψ hψ A z f (k : RationalPoint F G.X × RationalPoint F G.X)) := by
  unfold compactEval
  rw [compactProductTensorEquiv_compactTensorEquiv]
  exact compactProductRestriction_eval χ hG A K hK ψ hψ hψK z f k

/-- A family of maps between actual coefficient fibers whose values are, after
removal of the twists, a fixed value map applied at the left translate by a
point of `K`, has a constant value in the fixed compact charts. -/
theorem compactValue_const_of_eval
    (χ₁ ψ₁ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ₁ : Dynamic.centralizer ψ₁ = Dynamic.centralizer χ₁)
    (hψ₁K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ₁, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A₁ : SmoothRep.{0, u, uV} ℂ (levi χ₁))
    (χ₂ ψ₂ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hψ₂ : Dynamic.centralizer ψ₂ = Dynamic.centralizer χ₂)
    (hψ₂K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ₂, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (A₂ : SmoothRep.{0, u, uV} ℂ (levi χ₂))
    {Z : Type*} (w₁ : Z → unramifiedCharacters (normCharacters χ₁))
    (w₂ : Z → unramifiedCharacters (normCharacters χ₂))
    (M : ∀ z, coefficientFiber χ₁ ψ₁ hψ₁ A₁ (w₁ z) →ₗ[ℂ] coefficientFiber χ₂ ψ₂ hψ₂ A₂ (w₂ z))
    (g : RationalPoint F G.X) (hg : g ∈ K)
    (V : CoefficientTensor A₁ → CoefficientTensor A₂)
    (hM : ∀ z f (k : K.prod K),
      untwistValue χ₂ A₂ (w₂ z) (fiberEval χ₂ ψ₂ hψ₂ A₂ (w₂ z) (M z f)
          (k : RationalPoint F G.X × RationalPoint F G.X)) =
        V (untwistValue χ₁ A₁ (w₁ z) (fiberEval χ₁ ψ₁ hψ₁ A₁ (w₁ z) f
          ((g, g)⁻¹ * (k : RationalPoint F G.X × RationalPoint F G.X)))))
    (z z' : Z) :
    (compactTensorEquiv χ₂ hG K hK ψ₂ hψ₂ hψ₂K A₂ (w₂ z)).toLinearMap.comp
        ((M z).comp (compactTensorEquiv χ₁ hG K hK ψ₁ hψ₁ hψ₁K A₁ (w₁ z)).symm.toLinearMap) =
      (compactTensorEquiv χ₂ hG K hK ψ₂ hψ₂ hψ₂K A₂ (w₂ z')).toLinearMap.comp
        ((M z').comp (compactTensorEquiv χ₁ hG K hK ψ₁ hψ₁ hψ₁K A₁ (w₁ z')).symm.toLinearMap) := by
  have hmem (k : K.prod K) :
      (g, g)⁻¹ * (k : RationalPoint F G.X × RationalPoint F G.X) ∈ K.prod K :=
    ⟨K.mul_mem (K.inv_mem hg) k.property.1, K.mul_mem (K.inv_mem hg) k.property.2⟩
  have key : ∀ (y : Z) (v : compactFiber χ₁ K ψ₁ hψ₁ A₁) (k : K.prod K),
      compactEval hG K hK χ₂ ψ₂ hψ₂ hψ₂K A₂
          ((compactTensorEquiv χ₂ hG K hK ψ₂ hψ₂ hψ₂K A₂ (w₂ y)).toLinearMap.comp
            ((M y).comp (compactTensorEquiv χ₁ hG K hK ψ₁ hψ₁ hψ₁K A₁ (w₁ y)).symm.toLinearMap)
            v) k =
        V (compactEval hG K hK χ₁ ψ₁ hψ₁ hψ₁K A₁ v ⟨_, hmem k⟩) := by
    intro y v k
    obtain ⟨f, rfl⟩ := (compactTensorEquiv χ₁ hG K hK ψ₁ hψ₁ hψ₁K A₁ (w₁ y)).surjective v
    have h1 := compactEval_compactTensorEquiv hG K hK χ₂ ψ₂ hψ₂ hψ₂K A₂ (w₂ y) (M y f) k
    have h2 := compactEval_compactTensorEquiv hG K hK χ₁ ψ₁ hψ₁ hψ₁K A₁ (w₁ y) f ⟨_, hmem k⟩
    have h3 : (compactTensorEquiv χ₂ hG K hK ψ₂ hψ₂ hψ₂K A₂ (w₂ y)).toLinearMap.comp
        ((M y).comp (compactTensorEquiv χ₁ hG K hK ψ₁ hψ₁ hψ₁K A₁ (w₁ y)).symm.toLinearMap)
          (compactTensorEquiv χ₁ hG K hK ψ₁ hψ₁ hψ₁K A₁ (w₁ y) f) =
        compactTensorEquiv χ₂ hG K hK ψ₂ hψ₂ hψ₂K A₂ (w₂ y) (M y f) := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [h3, h1, hM, h2]
  apply LinearMap.ext
  intro v
  apply compactEval_injective hG K hK χ₂ ψ₂ hψ₂ hψ₂K A₂
  funext k
  exact (key z v k).trans (key z' v k).symm

end CompactCharts

end Langlands.Plancherel.ActualConjugateLeviCoherence
