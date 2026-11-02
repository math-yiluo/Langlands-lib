import Langlands.Representation.Classification.SegmentHeadSupportGeneric

/-!
# Exactness of the binary normalized product in its second factor

For a fixed smooth representation `L` of `GL_a(F)` with `a > 0`, the functor
`X ↦ L × X` (the binary normalized product of `L` and `X`) sends short exact
sequences of actual intertwiners to short exact sequences.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Classification.SegmentHeadSupport

open GeneralLinear

universe uG uH uV uW uF

section Consequences

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  {Φ : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uW} ℂ H}

/-- An exact functor preserves injective intertwiners. -/
theorem PreservesShortExact.map_injective (hΦ : PreservesShortExact Φ)
    {S P : SmoothRep.{0, uG, uV} ℂ G} (i : S ⟶ P) (hi : Function.Injective (SmoothRep.hom i)) :
    Function.Injective (SmoothRep.hom (Φ.map i)) := by
  let U : Subrepresentation P.representation :=
    { toSubmodule := LinearMap.range (SmoothRep.hom i).toLinearMap
      apply_mem_toSubmodule := by
        rintro g _ ⟨v, rfl⟩
        exact ⟨S.representation g v,
          Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom i) g v⟩ }
  have hex : LinearMap.range (SmoothRep.hom i).toLinearMap =
      LinearMap.ker (SmoothRep.hom (SmoothRep.mkQ P U)).toLinearMap := by
    ext v
    change v ∈ U.toSubmodule ↔ Submodule.Quotient.mk (p := U.toSubmodule) v = 0
    rw [Submodule.Quotient.mk_eq_zero]
  exact (hΦ i (SmoothRep.mkQ P U) hi (SmoothRep.mkQ_surjective P U) hex).1

/-- An exact functor preserves surjective intertwiners. -/
theorem PreservesShortExact.map_surjective (hΦ : PreservesShortExact Φ)
    {P Q : SmoothRep.{0, uG, uV} ℂ G} (q : P ⟶ Q) (hq : Function.Surjective (SmoothRep.hom q)) :
    Function.Surjective (SmoothRep.hom (Φ.map q)) := by
  let K : Subrepresentation P.representation :=
    { toSubmodule := LinearMap.ker (SmoothRep.hom q).toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        change SmoothRep.hom q (P.representation g v) = 0
        rw [Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom q) g v]
        rw [show SmoothRep.hom q v = 0 from hv, map_zero] }
  let j : SmoothRep.subrepresentation P K ⟶ P := SmoothRep.ofHom
    { toLinearMap := K.toSubmodule.subtype
      isIntertwining' := fun g => by ext v; rfl }
  have hj : Function.Injective (SmoothRep.hom j) := Submodule.injective_subtype _
  have hex : LinearMap.range (SmoothRep.hom j).toLinearMap =
      LinearMap.ker (SmoothRep.hom q).toLinearMap := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact w.2
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩
  exact (hΦ j q hj hq hex).2.2

end Consequences

section PairTensor

variable {H : Fin 2 → Type uG} [∀ i, Group (H i)]
  {V : Fin 2 → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- After splitting both indexed tensors over `Fin 2`, the external tensor of a
pair of intertwiners is the binary tensor map. -/
theorem pairSplit_externalMap {ρ : ∀ i, Representation ℂ (H i) (V i)}
    {σ : ∀ i, Representation ℂ (H i) (W i)} (f : ∀ i, (ρ i).IntertwiningMap (σ i))
    (v : PiTensorProduct ℂ V) :
    Shahidi.pairSplit W (FiniteTensor.externalMap f v) =
      TensorProduct.map (f 0).toLinearMap (f 1).toLinearMap (Shahidi.pairSplit V v) := by
  have heq : (Shahidi.pairSplit W).toLinearMap ∘ₗ (FiniteTensor.externalMap f).toLinearMap =
      TensorProduct.map (f 0).toLinearMap (f 1).toLinearMap ∘ₗ
        (Shahidi.pairSplit V).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    change Shahidi.pairSplit W (FiniteTensor.externalMap f (PiTensorProduct.tprod ℂ w)) =
      TensorProduct.map (f 0).toLinearMap (f 1).toLinearMap
        (Shahidi.pairSplit V (PiTensorProduct.tprod ℂ w))
    erw [FiniteTensor.externalMap_tprod, Shahidi.pairSplit_tprod, Shahidi.pairSplit_tprod]
    rfl
  exact LinearMap.congr_fun heq v

end PairTensor

section LeftExact

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  {S P Q A B C : Type*} [AddCommGroup S] [Module ℂ S] [AddCommGroup P] [Module ℂ P]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]

/-- Linear maps that become `M ⊗ i` and `M ⊗ q` after linear identifications
of their sources and targets form a short exact sequence when `i` and `q` do. -/
theorem shortExact_of_lTensor (eA : A ≃ₗ[ℂ] M ⊗[ℂ] S) (eB : B ≃ₗ[ℂ] M ⊗[ℂ] P)
    (eC : C ≃ₗ[ℂ] M ⊗[ℂ] Q) (ti : A →ₗ[ℂ] B) (tq : B →ₗ[ℂ] C) (i : S →ₗ[ℂ] P)
    (q : P →ₗ[ℂ] Q) (hsi : ∀ v, eB (ti v) = i.lTensor M (eA v))
    (hsq : ∀ v, eC (tq v) = q.lTensor M (eB v)) (hi : Function.Injective i)
    (hq : Function.Surjective q) (hex : LinearMap.range i = LinearMap.ker q) :
    Function.Injective ti ∧ LinearMap.range ti = LinearMap.ker tq ∧
      Function.Surjective tq := by
  have hlt : LinearMap.range (i.lTensor M) = LinearMap.ker (q.lTensor M) :=
    (lTensor_exact M (LinearMap.exact_iff.mpr hex.symm) hq).linearMap_ker_eq.symm
  refine ⟨fun x y hxy => ?_, le_antisymm ?_ ?_, fun y => ?_⟩
  · apply eA.injective
    apply Module.Flat.lTensor_preserves_injective_linearMap i hi
    rw [← hsi, ← hsi, hxy]
  · rintro _ ⟨x, rfl⟩
    change tq (ti x) = 0
    apply eC.injective
    rw [hsq, hsi, map_zero]
    have hx : i.lTensor M (eA x) ∈ LinearMap.ker (q.lTensor M) := by
      rw [← hlt]
      exact ⟨_, rfl⟩
    exact hx
  · intro x hx
    change tq x = 0 at hx
    have hqx : q.lTensor M (eB x) = 0 := by
      rw [← hsq, hx, map_zero]
    have hxmem : eB x ∈ LinearMap.range (i.lTensor M) := by
      rw [hlt]
      exact hqx
    obtain ⟨z, hz⟩ := hxmem
    refine ⟨eA.symm z, eB.injective ?_⟩
    rw [hsi, LinearEquiv.apply_symm_apply]
    exact hz
  · obtain ⟨z, hz⟩ := LinearMap.lTensor_surjective M hq (eC y)
    refine ⟨eB.symm z, eC.injective ?_⟩
    rw [hsq, LinearEquiv.apply_symm_apply]
    exact hz

end LeftExact

section Binary

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- With fixed positive-rank first factor, the published positive-block binary
product preserves short exact sequences in the second factor. -/
theorem preservesShortExact_binaryPositive_sectR {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (L : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    PreservesShortExact (Prod.sectR L _ ⋙ T.binaryPositiveProductFunctor ha hb) := by
  let := T.topology
  intro S P Q i q hi hq hex
  simp only [Functor.comp_map, PadicField.TopologicalData.binaryPositiveProductFunctor_map]
  let fam := T.binaryPairFamilyFunctor ha hb
  let ti := FiniteTensor.externalMap
    (fun k => SmoothRep.hom (fam.map ((Prod.sectR L _).map i) k))
  let tq := FiniteTensor.externalMap
    (fun k => SmoothRep.hom (fam.map ((Prod.sectR L _).map q) k))
  have h := shortExact_of_lTensor
    (Shahidi.pairSplit (R := ℂ) (fun k => (fam.obj (L, S) k : Type uV)))
    (Shahidi.pairSplit (R := ℂ) (fun k => (fam.obj (L, P) k : Type uV)))
    (Shahidi.pairSplit (R := ℂ) (fun k => (fam.obj (L, Q) k : Type uV)))
    ti.toLinearMap tq.toLinearMap (SmoothRep.hom i).toLinearMap (SmoothRep.hom q).toLinearMap
    (fun v => pairSplit_externalMap _ v) (fun v => pairSplit_externalMap _ v) hi hq hex
  exact Parabolic.normalizedInductionExactness F T (BlockShape.binary a b ha hb) _ _ _
    _ _ _ ti tq (SmoothRep.isSmooth (FiniteTensor.externalSmoothObject (fam.obj (L, S))))
    (SmoothRep.isSmooth (FiniteTensor.externalSmoothObject (fam.obj (L, P))))
    (SmoothRep.isSmooth (FiniteTensor.externalSmoothObject (fam.obj (L, Q))))
    h.1 h.2.2 h.2.1

/-- With fixed first factor, the rank-zero second-factor model preserves short
exact sequences in the second factor. -/
theorem preservesShortExact_binaryRightZero_sectR {a b : ℕ} (hb : b = 0)
    (L : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    PreservesShortExact (Prod.sectR L _ ⋙ T.binaryRightZeroTensorFunctor hb) := by
  let := T.topology
  intro S P Q i q hi hq hex
  have h := shortExact_of_lTensor (M := L) ULift.moduleEquiv ULift.moduleEquiv ULift.moduleEquiv
    (SmoothRep.hom ((Prod.sectR L _ ⋙ T.binaryRightZeroTensorFunctor hb).map i)).toLinearMap
    (SmoothRep.hom ((Prod.sectR L _ ⋙ T.binaryRightZeroTensorFunctor hb).map q)).toLinearMap
    (SmoothRep.hom i).toLinearMap (SmoothRep.hom q).toLinearMap
    (fun v => rfl) (fun v => rfl) hi hq hex
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- With fixed positive-rank first factor `L`, the binary normalized product
`X ↦ L × X` preserves short exact sequences, in every second rank. -/
theorem preservesShortExact_binaryNormalized_sectR {a b : ℕ} (ha : 0 < a)
    (L : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    PreservesShortExact (Prod.sectR L _ ⋙ T.binaryNormalizedProductFunctor a b) := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · rw [T.binaryNormalizedProductFunctor_of_right_eq_zero ha.ne' hb]
    exact preservesShortExact_binaryRightZero_sectR T hb L
  · rw [T.binaryNormalizedProductFunctor_of_pos ha hb]
    exact preservesShortExact_binaryPositive_sectR T ha hb L

end Binary

end Langlands.Classification.SegmentHeadSupport
