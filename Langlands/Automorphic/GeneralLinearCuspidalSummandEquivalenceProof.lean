import Langlands.Automorphic.GeneralLinearCuspidalSummandEquivalenceStatement
import Langlands.Automorphic.GeneralLinearCuspidalFormClassDerivativeProof
import Langlands.Automorphic.GeneralLinearQuotientJointRecovery
import Langlands.Automorphic.CuspidalJointAdmissibility
import Langlands.Automorphic.ContragredientUniqueness

/-! # Equivalence of the cusp-form realizations of equivalent Hilbert summands -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open GeneralLinearFormClassDerivative (exponentialAdelicPoint)

private local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (R : OperatorRealization F n) : AddCommGroup R.Space := Submodule.addCommGroup R.toSubmodule

section

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  {hPD : ParabolicDynamicStatement.{u}}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)}
  {hi : Function.Injective (characterRestrict i)} [(characterRestrict i).range.FiniteIndex]
  {I : Type u} [Fintype I] {e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I}
  {hc : IsCentral i} [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

local notation "n" => r + 1
local notation "G" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "hG" => GroupScheme.isConnectedReductive_generalLinear F (Fin n)
local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
local notation "πc" => fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
local notation "E" => Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)
local notation "m" => GeneralLinearGroupPoints.adelicHomeomorph F n

private def finiteAdelicInclusion :
    FiniteAdelicGL F n →* AdelicGroupPoints F G :=
  (m).symm.toMulEquiv.toMonoidHom.comp (AdelicGL.ofFinite F n).toMonoidHom

private def infiniteCompactInclusion :
    standardInfiniteCompact F n →* AdelicGroupPoints F G :=
  ((m).symm.toMulEquiv.toMonoidHom.comp (AdelicGL.ofInfinite F n).toMonoidHom).comp
    (standardInfiniteCompact F n).subtype

variable {P : Submodule ℂ (fullAEL2CuspidalSubmodule F
  (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) hPD
  (GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))) T i hi I e hc)}
private abbrev SummandInvariant (P : Submodule ℂ (↥S)) : Prop :=
  ∀ (a : AdelicGroupPoints F G) (x : ↥S), x ∈ P → πc a x ∈ P

variable (hP : SummandInvariant P)

include hP in
private def summandAction : Representation ℂ (AdelicGroupPoints F G) P where
  toFun a := (πc a).toLinearMap.restrict (hP a)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change πc 1 x = (x : S)
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change πc (a * b) x = πc a (πc b x)
    rw [map_mul]
    rfl

include hP in
omit [CompactSpace (AdeleQuotient F)] in
private theorem summandAction_apply_coe (a : AdelicGroupPoints F G) (x : P) :
    (summandAction (F := F) (r := r) (P := P) hP a x : S) = πc a x := rfl

include hP in
private def summandFiniteAction : Representation ℂ (FiniteAdelicGL F n) P :=
  (summandAction (F := F) (r := r) (P := P) hP).comp
    (finiteAdelicInclusion (F := F) (r := r))

include hP in
private def summandCompactAction : Representation ℂ (standardInfiniteCompact F n) P :=
  (summandAction (F := F) (r := r) (P := P) hP).comp
    (infiniteCompactInclusion (F := F) (r := r))

local notation "πf" => summandFiniteAction (F := F) (r := r) (P := P) hP
local notation "πk" => summandCompactAction (F := F) (r := r) (P := P) hP

omit [CompactSpace (AdeleQuotient F)] in
private theorem cuspidalAction_inner (a : AdelicGroupPoints F G) (x y : S) :
    Inner.inner ℂ (πc a x) (πc a y) = Inner.inner ℂ x y :=
  (⟨(πc a).toLinearMap, norm_fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc a⟩ :
    S →ₗᵢ[ℂ] S).inner_map_map x y

variable {R : CuspidalOperatorRealization F r} {j : R.Space →ₗ[ℂ] (↥P)}

private abbrev SummandFormClasses (j : R.Space →ₗ[ℂ] P) : Prop :=
  ∀ f, IsGeneralLinearFormClass F r T i ((j f : S) : E) (R.realization.toContinuous f)

variable (hj : SummandFormClasses j)

include hj in
private theorem summandClass_injective : Function.Injective j := by
  intro f g hfg
  apply R.realization.toContinuous_injective
  have hg := hj g
  rw [← hfg] at hg
  exact generalLinearFormClass_form_eq F r T i hi I e hc (hj f) hg

include hj in
private theorem summandClass_finite (d : FiniteAdelicGL F n) (f : R.Space) :
    j (R.realization.finiteRepresentation d f) = πf d (j f) := by
  apply Subtype.ext
  apply Subtype.ext
  exact generalLinear_formClass_finiteRepresentation F r T i hi I e hc R.realization
    ((S).subtype.comp (P.subtype.comp j)) hj d f

include hj in
private theorem summandClass_compact (k : standardInfiniteCompact F n) (f : R.Space) :
    j (R.realization.compactRepresentation k f) = πk k (j f) := by
  apply Subtype.ext
  apply Subtype.ext
  exact generalLinear_formClass_compactRepresentation F r T i hi I e hc R.realization
    ((S).subtype.comp (P.subtype.comp j)) hj k f

include hj in
set_option maxHeartbeats 450000 in
private theorem summandClass_slope (X : ArchimedeanGL.RealLieAlgebra F n) (f : R.Space) :
    Tendsto (fun t : ℝ => t⁻¹ •
      (summandAction (F := F) (r := r) (P := P) hP (exponentialAdelicPoint F r X t) (j f) -
        summandAction (F := F) (r := r) (P := P) hP (exponentialAdelicPoint F r X 0) (j f)))
      (𝓝[≠] 0) (𝓝 (j (R.realization.lieAction X f))) := by
  have hd := generalLinearCuspidalFormClassDerivative F r hPD T i hi I e hc R X f
    (j f : S) (j (R.realization.lieAction X f) : S) (hj f) (hj _)
  rw [hasDerivAt_iff_tendsto_slope_zero] at hd
  rw [tendsto_subtype_rng]
  simpa only [zero_add, Submodule.coe_smul_of_tower, Submodule.coe_sub,
    summandAction_apply_coe] using hd

include hj in
set_option maxHeartbeats 1000000 in
private theorem mem_summandClass_range_iff (hd : DenseRange j) (x : P) :
    x ∈ LinearMap.range j ↔
      Langlands.IsSmoothVector (πf) x ∧
        Langlands.FiniteVectors.IsFiniteVector (πk) x := by
  let σ : Representation ℂ (FiniteAdelicGL F n) P := πf
  let τ : Representation ℂ (standardInfiniteCompact F n) P := πk
  have hσ (d : FiniteAdelicGL F n) (v w : P) : Inner.inner ℂ (σ d v) (σ d w) = Inner.inner ℂ v w :=
    cuspidalAction_inner (F := F) (r := r) (hPD := hPD) (i := i) (hi := hi) (e := e) (hc := hc)
      (finiteAdelicInclusion d) v w
  have hτ (k : standardInfiniteCompact F n) (v w : P) : Inner.inner ℂ (τ k v) (τ k w) = Inner.inner ℂ v w :=
    cuspidalAction_inner (F := F) (r := r) (hPD := hPD) (i := i) (hi := hi) (e := e) (hc := hc)
      (infiniteCompactInclusion k) v w
  have hfin (d : FiniteAdelicGL F n) (f : R.Space) :
      j (R.realization.finiteRepresentation d f) = σ d (j f) :=
    summandClass_finite hP hj d f
  have hcpt (k : standardInfiniteCompact F n) (f : R.Space) :
      j (R.realization.compactRepresentation k f) = τ k (j f) :=
    summandClass_compact hP hj k f
  let J : R.realization.finiteRepresentation.IntertwiningMap σ :=
    ⟨j, fun d => LinearMap.ext (hfin d)⟩
  let bH : Langlands.InvariantPositiveForm («G» := FiniteAdelicGL F n) (V := ↥P) σ := by
    refine
      { toInnerProductCore := InnerProductSpace.toCore (𝕜 := ℂ) («E» := ↥P)
        invariant := ?_ }
    exact hσ
  let b := bH.comap J (summandClass_injective hj)
  have hb k v w : b.inner (R.realization.compactRepresentation k v)
      (R.realization.compactRepresentation k w) = b.inner v w := by
    change Inner.inner ℂ (j (R.realization.compactRepresentation k v))
      (j (R.realization.compactRepresentation k w)) = Inner.inner ℂ (j v) (j w)
    exact (congrArg₂ (Inner.inner ℂ) (hcpt k v) (hcpt k w)).trans (hτ k (j v) (j w))
  exact (Langlands.jointVectorRecovery_of_dense b hb
    R.realization.finiteRepresentation_compactRepresentation R.realization.finiteRepresentation_isSmooth
    R.realization.compactRepresentation_isFiniteVector OperatorRealization.exists_compact_openSubgroup_le
    R.isJointlyAdmissible σ τ hσ hτ j hd (fun _ _ => rfl) hfin hcpt x).symm

end

private theorem denseRange_codRestrict {V H : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : V →ₗ[ℂ] H) {P : Submodule ℂ H}
    (hP : (LinearMap.range j).topologicalClosure = P) (hj : ∀ v, j v ∈ P) :
    DenseRange (j.codRestrict P hj) := by
  subst P
  exact Langlands.Archimedean.rangeClosureEmbedding_denseRange j

private theorem jointVector_transport {D K H J : Type*} [Group D] [TopologicalSpace D]
    [Group K] [AddCommGroup H] [Module ℂ H] [AddCommGroup J] [Module ℂ J]
    {σ₁ : Representation ℂ D H} {σ₂ : Representation ℂ D J}
    {τ₁ : Representation ℂ K H} {τ₂ : Representation ℂ K J}
    (U : H ≃ₗ[ℂ] J) (hσ : ∀ d x, U (σ₁ d x) = σ₂ d (U x))
    (hτ : ∀ k x, U (τ₁ k x) = τ₂ k (U x)) (x : H) :
    (Langlands.IsSmoothVector σ₁ x ∧ Langlands.FiniteVectors.IsFiniteVector τ₁ x) ↔
      (Langlands.IsSmoothVector σ₂ (U x) ∧ Langlands.FiniteVectors.IsFiniteVector τ₂ (U x)) := by
  let Uf : σ₁.IntertwiningMap σ₂ := ⟨U.toLinearMap, fun d => LinearMap.ext (hσ d)⟩
  let Uk : τ₁.IntertwiningMap τ₂ := ⟨U.toLinearMap, fun k => LinearMap.ext (hτ k)⟩
  exact and_congr
    ⟨Langlands.isSmoothVector_map Uf, Langlands.isSmoothVector_of_injective Uf U.injective⟩
    (Langlands.FiniteVectors.isFiniteVector_map_iff Uk U.injective x).symm

private theorem eq_of_intertwined_slopes {H J : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [NormedAddCommGroup J] [NormedSpace ℂ J] [Module ℝ H] [Module ℝ J]
    [IsScalarTower ℝ ℂ H] [IsScalarTower ℝ ℂ J] (U : H ≃ₗᵢ[ℂ] J)
    (p : ℝ → H) (q : ℝ → J) (h : ∀ t, U (p t) = q t) {x : H} {y : J}
    (hp : Tendsto (fun t : ℝ => t⁻¹ • (p t - p 0)) (𝓝[≠] 0) (𝓝 x))
    (hq : Tendsto (fun t : ℝ => t⁻¹ • (q t - q 0)) (𝓝[≠] 0) (𝓝 y)) : U x = y := by
  have ht := (U.continuous.tendsto x).comp hp
  have heq : (U : H → J) ∘ (fun t : ℝ => t⁻¹ • (p t - p 0)) =
      fun t : ℝ => t⁻¹ • (q t - q 0) := by
    funext t
    calc
      _ = t⁻¹ • U (p t - p 0) :=
        LinearMap.map_smul_of_tower U.toLinearEquiv.toLinearMap t⁻¹ (p t - p 0)
      _ = t⁻¹ • (U (p t) - U (p 0)) :=
        congrArg (t⁻¹ • ·) (map_sub U.toLinearEquiv (p t) (p 0))
      _ = _ := congrArg (t⁻¹ • ·) (congrArg₂ Sub.sub (h t) (h 0))
  rw [heq] at ht
  exact tendsto_nhds_unique ht hq

set_option maxHeartbeats 1800000 in
/-- An isometric equivalence of the Hilbert summands restricts to an equivalence for the
finite, compact, and differential operators on their cusp forms. -/
theorem generalLinearCuspidalSummandEquivalence :
    GeneralLinearCuspidalSummandEquivalenceStatement.{u} := by
  intro F _ _ _ r hPD T i hi _ I _ e hc _ hG S πc P Q _ hQ hPi U hU R R' Φ Φ' hΦ hPcl hΦ' hQcl
  let jP : R.Space →ₗ[ℂ] P := Φ.codRestrict P (fun f =>
    hPcl ▸ (LinearMap.range Φ).le_topologicalClosure (LinearMap.mem_range_self Φ f))
  let jQ : R'.Space →ₗ[ℂ] Q := Φ'.codRestrict Q (fun f =>
    hQcl ▸ (LinearMap.range Φ').le_topologicalClosure (LinearMap.mem_range_self Φ' f))
  have hjP : SummandFormClasses jP := hΦ
  have hjQ : SummandFormClasses jQ := hΦ'
  have hPdens : DenseRange jP := denseRange_codRestrict Φ hPcl _
  have hQdens : DenseRange jQ := denseRange_codRestrict Φ' hQcl _
  let hQi := hQ.2.2.1
  let σP := summandFiniteAction (F := F) (r := r) (P := P) hPi
  let σQ := summandFiniteAction (F := F) (r := r) (P := Q) hQi
  let τP := summandCompactAction (F := F) (r := r) (P := P) hPi
  let τQ := summandCompactAction (F := F) (r := r) (P := Q) hQi
  have hUaction (a : AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))) (x : P) :
      U (summandAction (F := F) (r := r) (P := P) hPi a x) =
        summandAction (F := F) (r := r) (P := Q) hQi a (U x) :=
    Subtype.ext (hU a x)
  have hUfin d (x : P) : U (σP d x) = σQ d (U x) := hUaction (finiteAdelicInclusion d) x
  have hUcpt k (x : P) : U (τP k x) = τQ k (U x) := hUaction (infiniteCompactInclusion k) x
  have hUrange (x : P) : x ∈ LinearMap.range jP ↔ U x ∈ LinearMap.range jQ := by
    have hPjoint : x ∈ LinearMap.range jP ↔
        Langlands.IsSmoothVector σP x ∧ Langlands.FiniteVectors.IsFiniteVector τP x :=
      mem_summandClass_range_iff hPi hjP hPdens x
    have hQjoint : U x ∈ LinearMap.range jQ ↔
        Langlands.IsSmoothVector σQ (U x) ∧ Langlands.FiniteVectors.IsFiniteVector τQ (U x) :=
      mem_summandClass_range_iff hQi hjQ hQdens (U x)
    have hJoint := jointVector_transport (H := ↥P) (J := ↥Q) (σ₁ := σP) (σ₂ := σQ)
      (τ₁ := τP) (τ₂ := τQ) U.toLinearEquiv hUfin hUcpt x
    exact hPjoint.trans (hJoint.trans hQjoint.symm)
  let a := U.toLinearEquiv.toLinearMap.comp jP
  have ha : Function.Injective a := U.injective.comp (summandClass_injective hjP)
  have hb : Function.Injective jQ := summandClass_injective hjQ
  have hrange : LinearMap.range a = LinearMap.range jQ := by
    ext y
    change (∃ f, U (jP f) = y) ↔ y ∈ LinearMap.range jQ
    constructor
    · rintro ⟨f, rfl⟩
      exact (hUrange (jP f)).mp (LinearMap.mem_range_self jP f)
    · intro hy
      have hx : U.symm y ∈ LinearMap.range jP := (hUrange _).mpr (by simpa only [U.apply_symm_apply])
      obtain ⟨f, hf⟩ := hx
      exact ⟨f, (congrArg U hf).trans (U.apply_symm_apply y)⟩
  let L : R.Space ≃ₗ[ℂ] R'.Space := (LinearEquiv.ofInjective a ha).trans
    ((LinearEquiv.ofEq _ _ hrange).trans (LinearEquiv.ofInjective jQ hb).symm)
  have hL (f : R.Space) : jQ (L f) = U (jP f) := by
    let w := LinearEquiv.ofEq _ _ hrange (LinearEquiv.ofInjective a ha f)
    have hw : (w : Q) = U (jP f) := rfl
    exact (LinearEquiv.ofInjective_symm_apply jQ (h := hb) w).trans hw
  refine ⟨OperatorRealization.Equivalence.ofGenerators L ?_ ?_
    (OperatorRealization.envelopingAction_comm_of_lieAction L ?_)⟩
  · intro d f
    apply hb
    calc
      _ = U (jP (R.realization.finiteRepresentation d f)) := hL _
      _ = U (σP d (jP f)) := congrArg U (summandClass_finite hPi hjP d f)
      _ = σQ d (U (jP f)) := hUfin d (jP f)
      _ = σQ d (jQ (L f)) := congrArg (σQ d) (hL f).symm
      _ = _ := (summandClass_finite hQi hjQ d (L f)).symm
  · intro k f
    apply hb
    calc
      _ = U (jP (R.realization.compactRepresentation k f)) := hL _
      _ = U (τP k (jP f)) := congrArg U (summandClass_compact hPi hjP k f)
      _ = τQ k (U (jP f)) := hUcpt k (jP f)
      _ = τQ k (jQ (L f)) := congrArg (τQ k) (hL f).symm
      _ = _ := (summandClass_compact hQi hjQ k (L f)).symm
  · intro X f
    apply hb
    rw [hL]
    let p (t : ℝ) := summandAction (F := F) (r := r) (P := P) hPi
      (exponentialAdelicPoint F r X t) (jP f)
    let q (t : ℝ) := summandAction (F := F) (r := r) (P := Q) hQi
      (exponentialAdelicPoint F r X t) (jQ (L f))
    have heq (t : ℝ) : U (p t) = q t :=
      (hUaction _ _).trans (congrArg (summandAction (F := F) (r := r) (P := Q) hQi
        (exponentialAdelicPoint F r X t)) (hL f).symm)
    exact eq_of_intertwined_slopes U p q heq (summandClass_slope hPi hjP X f)
      (summandClass_slope hQi hjQ X (L f))

end Langlands.Automorphic.GroupSchemeFunctions
