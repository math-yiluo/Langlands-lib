import Langlands.Representation.Hecke.NondegenerateModuleEquivalenceStatement
import Langlands.Representation.Hecke.LocalUnitsProof
import Langlands.Algebra.NondegenerateScalars
import Langlands.Algebra.IdempotentedRingRightLimitAction
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.CategoryTheory.Equivalence

/-! # Renard III.1.4: equivalence with nondegenerate Hecke modules -/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Hecke
namespace NondegenerateEquivalence

open Langlands.Algebra

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- Left translation on the measure-indexed Hecke carrier. -/
def translate (g : G) : HeckeAlgebra μ ≃ₗ[ℂ] HeckeAlgebra μ :=
  TestFunction.leftTranslate g

omit [T2Space G] [LocallyCompactSpace G] in
@[simp] theorem translate_apply (g : G) (f : HeckeAlgebra μ) (x : G) :
    translate μ g f x = f (g⁻¹ * x) := rfl

omit [T2Space G] [LocallyCompactSpace G] in
/-- Left translation commutes with right convolution. -/
theorem translate_convolution (g : G) (a b : HeckeAlgebra μ) :
    translate μ g (a * b) = translate μ g a * b := by
  apply HeckeAlgebra.ext
  intro x
  change (∫ y, a y * b (y⁻¹ * (g⁻¹ * x)) ∂μ) =
    ∫ y, a (g⁻¹ * y) * b (y⁻¹ * x) ∂μ
  rw [← integral_mul_left_eq_self (fun y => a (g⁻¹ * y) * b (y⁻¹ * x)) g]
  simp only [inv_mul_cancel_left, mul_inv_rev, mul_assoc]

/-- The existing compact-open local units make the actual Hecke ring idempotented. -/
theorem idempotented : IsIdempotented (HeckeAlgebra μ) := by
  intro s
  obtain ⟨K, hK, _, hi, hs⟩ :=
    HeckeAlgebra.finiteFamilyLocalUnits G μ s (⊤ : OpenSubgroup G)
  refine ⟨⟨HeckeAlgebra.normalizedIndicator μ K hK, hi⟩, ?_⟩
  intro a ha
  change HeckeAlgebra.normalizedIndicator μ K hK * a *
    HeckeAlgebra.normalizedIndicator μ K hK = a
  rw [(hs a ha).1, (hs a ha).2]

/-- The smooth left regular representation on actual test functions. -/
def regular : Representation ℂ G (HeckeAlgebra μ) where
  toFun g := (translate μ g).toLinearMap
  map_one' := LinearMap.ext (fun f => TestFunction.leftTranslate_one f)
  map_mul' g h := LinearMap.ext (fun f => TestFunction.leftTranslate_mul g h f)

theorem regular_smooth : IsSmooth (regular μ) := by
  classical
  intro f
  obtain ⟨K, _, _, hf⟩ := TestFunction.commonCompactOpenBiInvariance G
    {HeckeAlgebra.toTestFunction μ f} (⊤ : OpenSubgroup G)
  refine ⟨K, ?_⟩
  intro k
  exact ((TestFunction.mem_biInvariant_iff _ _ (HeckeAlgebra.toTestFunction μ f)).mp
    (hf _ (Finset.mem_singleton_self _))).1 k

/-- Dirac translation represented by its values at all idempotents. -/
def translationFamily (g : G) : IdempotentedRingRightLimit (HeckeAlgebra μ) :=
  ⟨fun e => translate μ g (e : HeckeAlgebra μ), by
    constructor
    · intro e
      rw [← translate_convolution, e.property.eq]
    · intro e f hef
      rw [← translate_convolution, ((Idempotent.le_iff_mul e f).mp hef).1]⟩

variable {M : Type v} [AddCommGroup M] [NonUnitalModule (HeckeAlgebra μ) M]

/-- Extend Dirac translation to the original additive nondegenerate carrier. -/
def act (hM : IsNondegenerate (HeckeAlgebra μ) M) (g : G) (m : M) : M :=
  IdempotentedRingRightLimitAction.act hM (translationFamily μ g) m

/-- Every fixing idempotent computes this action. -/
theorem act_eq (hM : IsNondegenerate (HeckeAlgebra μ) M) (g : G) (m : M)
    (e : Idempotent (HeckeAlgebra μ)) (he : (e : HeckeAlgebra μ) • m = m) :
    act μ hM g m = translate μ g (e : HeckeAlgebra μ) • m :=
  IdempotentedRingRightLimitAction.act_eq (idempotented μ) hM _ m e he

/-- Compatibility of the recovered action with the original Hecke action. -/
theorem act_smul (hM : IsNondegenerate (HeckeAlgebra μ) M) (g : G)
    (a : HeckeAlgebra μ) (m : M) :
    act μ hM g (a • m) = translate μ g a • m := by
  obtain ⟨e, he⟩ := (idempotented μ).exists_mem_corner a
  have hea := ((Idempotent.mem_corner_iff e a).mp he).1
  have hem : (e : HeckeAlgebra μ) • (a • m) = a • m := by
    rw [← mul_smul, hea]
  rw [act_eq μ hM g (a • m) e hem, ← mul_smul, ← translate_convolution, hea]

/-- Canonical complex scalars on the original carrier. -/
abbrev scalars (hM : IsNondegenerate (HeckeAlgebra μ) M) : Module ℂ M :=
  NondegenerateScalars.module ℂ (idempotented μ) hM

/-- The representation recovered from the nondegenerate module. -/
def recovered (hM : IsNondegenerate (HeckeAlgebra μ) M) :
    letI := scalars μ hM
    Representation ℂ G M := by
  letI := scalars μ hM
  refine
    { toFun := fun g =>
        { toFun := act μ hM g
          map_add' := IdempotentedRingRightLimitAction.act_add (idempotented μ) hM _
          map_smul' := ?_ }
      map_one' := ?_
      map_mul' := ?_ }
  · intro c m
    obtain ⟨e, he⟩ := hM m
    rw [NondegenerateScalars.smul_eq ℂ (idempotented μ) hM c m e he,
      act_smul, (translate μ _).map_smul,
      ← NondegenerateScalars.smul_action ℂ (idempotented μ) hM,
      act_eq μ hM _ m e he]
    rfl
  · apply LinearMap.ext
    intro m
    change act μ hM 1 m = m
    obtain ⟨e, he⟩ := hM m
    rw [act_eq μ hM 1 m e he]
    have ht : translate μ 1 (e : HeckeAlgebra μ) = e :=
      TestFunction.leftTranslate_one _
    rw [ht]
    exact he
  · intro g h
    apply LinearMap.ext
    intro m
    change act μ hM (g * h) m = act μ hM g (act μ hM h m)
    obtain ⟨e, he⟩ := hM m
    rw [act_eq μ hM (g * h) m e he, act_eq μ hM h m e he, act_smul]
    exact congrArg (fun a : HeckeAlgebra μ => a • m)
      (TestFunction.leftTranslate_mul g h (e : HeckeAlgebra μ))

/-- A left-invariance subgroup of a fixing idempotent fixes the vector. -/
theorem recovered_smooth (hM : IsNondegenerate (HeckeAlgebra μ) M) :
    letI := scalars μ hM
    IsSmooth (recovered μ hM) := by
  let := scalars μ hM
  intro m
  obtain ⟨e, he⟩ := hM m
  obtain ⟨K, hK⟩ := regular_smooth μ (e : HeckeAlgebra μ)
  refine ⟨K, ?_⟩
  intro k
  change act μ hM (k : G) m = m
  rw [act_eq μ hM (k : G) m e he]
  exact (congrArg (fun a : HeckeAlgebra μ => a • m) (hK k)).trans he

/-- Point evaluation is an algebraic complex-linear functional. -/
def pointEvaluation (x : G) : HeckeAlgebra μ →ₗ[ℂ] ℂ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Integration of the smooth regular representation is actual convolution. -/
theorem integrated_regular (f a : HeckeAlgebra μ) :
    integratedAction μ (regular μ) (regular_smooth μ)
      (HeckeAlgebra.toTestFunction μ f) a = f * a := by
  apply HeckeAlgebra.ext
  intro x
  change pointEvaluation μ x (integratedAction μ (regular μ) (regular_smooth μ)
    (HeckeAlgebra.toTestFunction μ f) a) = (f * a) x
  rw [integratedAction_dual]
  rfl

/-- Evaluation on a vector intertwines the regular and recovered representations. -/
def evaluation (hM : IsNondegenerate (HeckeAlgebra μ) M) (m : M) :
    letI := scalars μ hM
    (regular μ).IntertwiningMap (recovered μ hM) := by
  letI := scalars μ hM
  exact
    { toFun := fun a => a • m
      map_add' := fun a b => NonUnitalModule.add_smul a b m
      map_smul' := fun c a =>
        (NondegenerateScalars.smul_action ℂ (idempotented μ) hM c a m).symm
      isIntertwining' := fun g => LinearMap.ext (fun a => (act_smul μ hM g a m).symm) }

/-- The recovered representation integrates to the original module action. -/
theorem integrated_recovered (hM : IsNondegenerate (HeckeAlgebra μ) M)
    (f : HeckeAlgebra μ) (m : M) :
    letI := scalars μ hM
    heckeAction μ (recovered μ hM) (recovered_smooth μ hM) f m = f • m := by
  let := scalars μ hM
  let T := evaluation μ hM m
  obtain ⟨e, he⟩ := hM m
  change integratedAction μ (recovered μ hM) (recovered_smooth μ hM)
    (HeckeAlgebra.toTestFunction μ f) m = f • m
  calc
    _ = integratedAction μ (recovered μ hM) (recovered_smooth μ hM)
        (HeckeAlgebra.toTestFunction μ f) (T (e : HeckeAlgebra μ)) :=
      congrArg _ he.symm
    _ = T (integratedAction μ (regular μ) (regular_smooth μ)
        (HeckeAlgebra.toTestFunction μ f) (e : HeckeAlgebra μ)) :=
      (integratedAction_intertwiner μ (regular_smooth μ) (recovered_smooth μ hM)
        T _ (e : HeckeAlgebra μ)).symm
    _ = T (f * (e : HeckeAlgebra μ)) :=
      congrArg T (integrated_regular μ f (e : HeckeAlgebra μ))
    _ = f • m := by
      change (f * (e : HeckeAlgebra μ)) • m = f • m
      rw [mul_smul, he]

/-- Bundle the recovered representation without changing the carrier universe. -/
def recoveredObject (M : NondegenerateModuleCat.{u, v} (HeckeAlgebra μ)) :
    SmoothRep.{0, u, v} ℂ G :=
  letI := scalars μ M.property
  SmoothRep.of (recovered μ M.property) (recovered_smooth μ M.property)

/-- The identity of the original additive carrier identifies its recovered Hecke module. -/
def recoveredIso (M : NondegenerateModuleCat.{u, v} (HeckeAlgebra μ)) :
    heckeNondegenerateModule μ (recoveredObject μ M) ≅ M where
  hom := ObjectProperty.homMk
    { toAddMonoidHom := AddMonoidHom.id M.obj
      map_smul' := fun f m => integrated_recovered μ M.property f m }
  inv := ObjectProperty.homMk
    { toAddMonoidHom := AddMonoidHom.id M.obj
      map_smul' := fun f m => (integrated_recovered μ M.property f m).symm }
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    rfl
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    rfl

variable {A B : SmoothRep.{0, u, v} ℂ G}

/-- Expose the original module homomorphism across the category wrappers. -/
abbrev underlying (f : heckeNondegenerateModule μ A ⟶ heckeNondegenerateModule μ B) :
    @NonUnitalModuleHom (HeckeAlgebra μ) A B _ _ _
      (heckeNonUnitalModule μ A.representation A.isSmooth)
      (heckeNonUnitalModule μ B.representation B.isSmooth) := f.hom

omit [T2Space G] in
/-- Module maps between integrated smooth representations preserve complex scalars. -/
theorem map_complex (f : heckeNondegenerateModule μ A ⟶ heckeNondegenerateModule μ B)
    (c : ℂ) (m : A) : (underlying μ f) (c • m) = c • (underlying μ f) m := by
  let := heckeNonUnitalModule μ A.representation A.isSmooth
  let := heckeNonUnitalModule μ B.representation B.isSmooth
  obtain ⟨e, he⟩ := heckeNonUnitalModule_isNondegenerate μ A.representation A.isSmooth m
  have hf : (e : HeckeAlgebra μ) • (underlying μ f) m = (underlying μ f) m := by
    rw [← (underlying μ f).map_smul, he]
  calc
    (underlying μ f) (c • m) = (underlying μ f) ((c • (e : HeckeAlgebra μ)) • m) := by
      rw [NonUnitalModule.ofLinearEndHom_smul_assoc, he]
    _ = (c • (e : HeckeAlgebra μ)) • (underlying μ f) m := (underlying μ f).map_smul _ m
    _ = c • ((e : HeckeAlgebra μ) • (underlying μ f) m) :=
      NonUnitalModule.ofLinearEndHom_smul_assoc _ c _ _
    _ = c • (underlying μ f) m := congrArg (c • ·) hf

omit [T2Space G] in
/-- Module maps between integrated smooth representations preserve the group action. -/
theorem map_group (f : heckeNondegenerateModule μ A ⟶ heckeNondegenerateModule μ B)
    (g : G) (m : A) :
    (underlying μ f) (A.representation g m) = B.representation g ((underlying μ f) m) := by
  let := heckeNonUnitalModule μ A.representation A.isSmooth
  let := heckeNonUnitalModule μ B.representation B.isSmooth
  obtain ⟨e, he⟩ := heckeNonUnitalModule_isNondegenerate μ A.representation A.isSmooth m
  have hf : (e : HeckeAlgebra μ) • (underlying μ f) m = (underlying μ f) m := by
    rw [← (underlying μ f).map_smul, he]
  have htA : translate μ g (e : HeckeAlgebra μ) • m = A.representation g m := by
    change integratedAction μ A.representation A.isSmooth
      (TestFunction.leftTranslate g (HeckeAlgebra.toTestFunction μ (e : HeckeAlgebra μ))) m = _
    rw [integratedAction_leftTranslate]
    exact congrArg (A.representation g) he
  have htB : translate μ g (e : HeckeAlgebra μ) • (underlying μ f) m =
      B.representation g ((underlying μ f) m) := by
    change integratedAction μ B.representation B.isSmooth
      (TestFunction.leftTranslate g (HeckeAlgebra.toTestFunction μ (e : HeckeAlgebra μ)))
      ((underlying μ f) m) = _
    rw [integratedAction_leftTranslate]
    exact congrArg (B.representation g) hf
  rw [← htA, (underlying μ f).map_smul, htB]

/-- The original additive Hecke-module map as a complex-linear group intertwiner. -/
def preimage (f : heckeNondegenerateModule μ A ⟶ heckeNondegenerateModule μ B) : A ⟶ B := by
  letI := heckeNonUnitalModule μ A.representation A.isSmooth
  letI := heckeNonUnitalModule μ B.representation B.isSmooth
  exact SmoothRep.ofHom
    { toFun := underlying μ f
      map_add' := (underlying μ f).toAddMonoidHom.map_add
      map_smul' := map_complex μ f
      isIntertwining' := fun g => LinearMap.ext (fun m => map_group μ f g m) }

omit [T2Space G] in
/-- Fullness follows from automatic complex linearity and group equivariance. -/
theorem full : (heckeNondegenerateModuleFunctor.{u, v} μ).Full where
  map_surjective f := ⟨preimage μ f, by
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro m
    rfl⟩

omit [T2Space G] in
/-- Faithfulness follows because the functor keeps the entire underlying map. -/
theorem faithful : (heckeNondegenerateModuleFunctor.{u, v} μ).Faithful where
  map_injective := by
    intro A B f g h
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro m
    exact congrArg (fun k => underlying μ k m) h

/-- Every original nondegenerate module is isomorphic to a recovered smooth module. -/
theorem essSurj : (heckeNondegenerateModuleFunctor.{u, v} μ).EssSurj where
  mem_essImage M := ⟨recoveredObject μ M, ⟨recoveredIso μ M⟩⟩

end NondegenerateEquivalence

/-- Renard III.1.4, Theorem, for the published functor in independent universes. -/
theorem heckeNondegenerateModuleEquivalence :
    HeckeNondegenerateModuleEquivalenceStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ μ _
  exact
    { faithful := NondegenerateEquivalence.faithful μ
      full := NondegenerateEquivalence.full μ
      essSurj := NondegenerateEquivalence.essSurj μ }

end Langlands.Hecke
