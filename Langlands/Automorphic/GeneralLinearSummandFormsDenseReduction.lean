import Langlands.Automorphic.GeneralLinearQuotientFormClassClosure
import Langlands.Automorphic.GeneralLinearSummandFormsEnveloping

/-! # Density of attached form classes from a single nonzero attached form -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

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

/-- **Some attached stable cusp form is nonzero.** With the data of
`GeneralLinearCuspidalSummandRealizationStatement`, every nonzero closed `πc`-invariant subspace
`P` of `S`, minimal among such subspaces, has a nonzero stable automorphic function among the
cuspidal forms whose actual quotient class lies in `P`. -/
def GeneralLinearSummandFormsNonzeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant],
    let hG := GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
    let S := fullAEL2CuspidalSubmodule F _ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F _ hPD hG T i hi I e hc
    ∀ P : Submodule ℂ S,
      (P ≠ ⊥ ∧ IsClosed (P : Set S) ∧ (∀ a, ∀ x ∈ P, πc a x ∈ P) ∧
        ∀ P' : Submodule ℂ S, P' ≤ P → IsClosed (P' : Set S) →
          (∀ a, ∀ x ∈ P', πc a x ∈ P') → P' = ⊥ ∨ P' = P) →
      summandForms F r T i (P.map S.subtype) ≠ ⊥

/-- One nonzero attached form suffices for density of all attached form classes. -/
def GeneralLinearSummandFormsDenseOfNonzeroStatement : Prop :=
  GeneralLinearSummandFormsNonzeroStatement.{u} → GeneralLinearSummandFormsDenseStatement.{u}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The class image of the attached forms has invariant closure; its trace on `S` is a nonzero
closed invariant subspace of `P`, hence equal to `P` by minimality. -/
theorem generalLinearSummandFormsDenseOfNonzero :
    GeneralLinearSummandFormsDenseOfNonzeroStatement.{u} := by
  intro hNZ F _ _ _ r hPD T i hi _ I _ e hc _ hG S πc P hPmin
  have hne := hNZ F r hPD T i hi I e hc P hPmin
  obtain ⟨hPne, hPc, hPinv, hPmin'⟩ := hPmin
  let G := GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
  let E := Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)
  let hLie := generalLinearSummandFormsEnveloping.{u}
  let V := summandRealization F r hPD T i hi I e hc hLie P hPc hPinv
  let cm := summandClassMap F r hPD T i hi I e hc hLie P hPc hPinv
  let jV : V.Space →ₗ[ℂ] E := S.subtype ∘ₗ cm
  have hjV : ∀ y, IsGeneralLinearFormClass F r T i (jV y) (V.toContinuous y) :=
    summandClassMap_isClass F r hPD T i hi I e hc hLie P hPc hPinv
  have hcmP : ∀ y, cm y ∈ P := fun y =>
    range_summandClassMap_le F r hPD T i hi I e hc hLie P hPc hPinv (LinearMap.mem_range_self _ y)
  let H := (LinearMap.range jV).topologicalClosure
  have hS : IsClosed (S : Set E) :=
    (fullAEL2CuspidalClosedSubmodule F G hPD hG T i hi I e hc).isClosed
  have hA : IsClosed ((P.map S.subtype : Submodule ℂ E) : Set E) :=
    hS.isClosedEmbedding_subtypeVal.isClosedMap _ hPc
  have hHA : H ≤ P.map S.subtype := by
    refine Submodule.topologicalClosure_minimal _ ?_ hA
    rintro _ ⟨y, rfl⟩
    exact Submodule.mem_map_of_mem (hcmP y)
  let P' : Submodule ℂ S := H.comap S.subtype
  have hP'c : IsClosed (P' : Set S) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  have hP'inv : ∀ a, ∀ x ∈ P', πc a x ∈ P' := fun a x hx =>
    generalLinearQuotientFormClassClosure F r T i hi I e hc V jV hjV a (x : E) hx
  have hP'P : P' ≤ P := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp (hHA hx)
    rwa [← Subtype.ext hpx]
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let y₀ : V.Space := ⟨f, hf⟩
  have hy₀ : jV y₀ ≠ 0 := by
    intro h
    have h0 := hjV y₀
    rw [h] at h0
    obtain ⟨k, hk, hk'⟩ := h0
    obtain ⟨k', hk₂, hk₂'⟩ := isGeneralLinearFormClass_zero F r T i
    let := positiveRationalQuotient_borelSpace F G T i hi I e hc
    let := haarQuotientMeasure_isOpenPosMeasure F G T i hi I e hc
    have hkk : k = k' := ContinuousMap.ext (congrFun
      (Measure.eq_of_ae_eq (hk'.symm.trans hk₂') k.continuous k'.continuous))
    have hzero : V.toContinuous y₀ = 0 := by rw [← hk, hkk, hk₂]
    apply hf0
    exact congrArg Subtype.val (V.toContinuous_injective (hzero.trans (map_zero _).symm))
  have hP'ne : P' ≠ ⊥ := by
    intro h
    have hmem : cm y₀ ∈ P' :=
      (LinearMap.range jV).le_topologicalClosure (LinearMap.mem_range_self jV y₀)
    rw [h, Submodule.mem_bot] at hmem
    exact hy₀ (by change ((cm y₀ : S) : E) = 0; rw [hmem]; rfl)
  have hP'eq : P' = P := (hPmin' P' hP'P hP'c hP'inv).resolve_left hP'ne
  intro x hx
  have hxP' : x ∈ P' := by
    rw [hP'eq]
    exact hx
  have hxH : (x : E) ∈ closure (Set.range jV) := by
    have h := hxP'
    change (x : E) ∈ ((LinearMap.range jV).topologicalClosure : Set E) at h
    rwa [Submodule.topologicalClosure_coe, LinearMap.coe_range] at h
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  refine closure_mono ?_ hxH
  rintro _ ⟨y, rfl⟩
  exact ⟨cm y, ⟨y.val, y.property, hjV y⟩, rfl⟩

end Langlands.Automorphic.GroupSchemeFunctions
