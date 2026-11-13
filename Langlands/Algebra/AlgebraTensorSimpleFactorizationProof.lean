import Langlands.Algebra.AlgebraExternalTensorSimpleProof

open scoped TensorProduct
noncomputable section
namespace Langlands.AlgebraTensor

universe u₁ u₂ v v₁ v₂

section Multiplicity
variable {A₁ : Type u₁} {A₂ : Type u₂} [Ring A₁] [Algebra ℂ A₁]
  [Ring A₂] [Algebra ℂ A₂]
variable {W : Type v} [AddCommGroup W] [Module ℂ W]
  [Module A₁ W] [IsScalarTower ℂ A₁ W]
  [Module A₂ W] [IsScalarTower ℂ A₂ W] [SMulCommClass A₁ A₂ W]

variable (U : Submodule A₁ W)
abbrev Mult := U →ₗ[A₁] W

instance multModule : Module A₂ (Mult U) where
  add_smul _ _ _ := LinearMap.ext fun _ => add_smul _ _ _
  zero_smul _ := LinearMap.ext fun _ => zero_smul _ _

abbrev evalAt (u : U) : Mult U →ₗ[ℂ] W :=
  { toFun := fun f => f u
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def eval : U ⊗[ℂ] Mult U →ₗ[ℂ] W :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun u (f : Mult U) => f u)
    (fun u u' f => map_add f u u') (fun c u f => (f.restrictScalars ℂ).map_smul c u)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl))

@[simp] theorem eval_tmul (u : U) (f : Mult U) : eval U (u ⊗ₜ f) = f u := by
  rfl

theorem evalAt_injective [IsSimpleModule A₁ U] {u : U} (hu : u ≠ 0) :
    Function.Injective (evalAt U u) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  rcases f.injective_or_eq_zero with hinj | hz
  · exact absurd (hinj (hf.trans (map_zero f).symm)) hu
  · exact hz

theorem eval_injective [IsSimpleModule A₁ U] [FiniteDimensional ℂ U] :
    Function.Injective (eval U) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Free.chooseBasis ℂ U
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b t
  have hc : ∀ j u, c j u = 0 := by
    intro j u
    obtain ⟨a, ha⟩ := RankOneGraded.exists_forall_eq_smul_of_isSimpleModule
      (A := A₁) ((b.coord j).smulRight u)
    have hterm : ∀ i ∈ c.support, a • eval U (b i ⊗ₜ c i) =
        (b.coord j (b i)) • c i u := by
      intro i _
      rw [eval_tmul, ← map_smul, ← ha, LinearMap.smulRight_apply]
      exact (c i).restrictScalars ℂ |>.map_smul _ _
    have h1 := congrArg (fun w : W => a • w) ht
    simp only [Finsupp.sum, map_sum, Finset.smul_sum, smul_zero] at h1
    rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single j] at h1
    · simpa using h1
    · intro i _ hij
      simp [hij]
    · intro hj
      simp [Finsupp.notMem_support_iff.mp hj]
  have hc0 : c = 0 := Finsupp.ext fun j => LinearMap.ext fun u => hc j u
  simp [hc0]

variable [Module (A₁ ⊗[ℂ] A₂) W]
variable (hact : ∀ (a : A₁) (b : A₂) (w : W), (a ⊗ₜ[ℂ] b) • w = a • b • w)
include hact

theorem eval_restricted_surjective [IsSimpleModule (A₁ ⊗[ℂ] A₂) W]
    [IsSimpleModule A₁ U] {N : Submodule A₂ (Mult U)} (hN : N ≠ ⊥) :
    Function.Surjective
      (eval U ∘ₗ TensorProduct.map (LinearMap.id : U →ₗ[ℂ] U)
        (N.subtype.restrictScalars ℂ)) := by
  have := IsSimpleModule.nontrivial A₁ U
  let T := TensorProduct.map (LinearMap.id : U →ₗ[ℂ] U) (N.subtype.restrictScalars ℂ)
  let F := eval U ∘ₗ T
  have hpure (a : A₁) (b : A₂) (t : U ⊗[ℂ] N) :
      (a ⊗ₜ[ℂ] b) • F t ∈ LinearMap.range F := by
    induction t with
    | tmul u n =>
      refine ⟨(a • u) ⊗ₜ ⟨b • (n : Mult U), N.smul_mem b n.2⟩, ?_⟩
      simp only [F, T, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.restrictScalars_apply, Submodule.subtype_apply, eval_tmul,
        LinearMap.smul_apply]
      rw [map_smul, ← smul_comm a b, hact]
    | add s t hs ht =>
      rw [map_add, smul_add]
      exact (LinearMap.range F).add_mem hs ht
  let R : Submodule (A₁ ⊗[ℂ] A₂) W :=
    { carrier := LinearMap.range F
      zero_mem' := (LinearMap.range F).zero_mem
      add_mem' := (LinearMap.range F).add_mem
      smul_mem' := by
        rintro a _ ⟨t, rfl⟩
        induction a with
        | tmul a b => exact hpure a b t
        | add a b ha hb =>
          rw [add_smul]
          exact (LinearMap.range F).add_mem ha hb }
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  have hnu : n u ≠ 0 := by
    intro h
    apply hn0
    apply evalAt_injective U hu
    exact h.trans (map_zero (evalAt U u)).symm
  have hR : R ≠ ⊥ := by
    intro h
    have hm : n u ∈ R := ⟨u ⊗ₜ ⟨n, hn⟩, rfl⟩
    rw [h] at hm
    exact hnu hm
  have hRtop : R = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top R).resolve_left hR
  intro w
  have hw : w ∈ R := hRtop.symm ▸ Submodule.mem_top
  exact hw

theorem mult_simple [IsSimpleModule (A₁ ⊗[ℂ] A₂) W]
    [IsSimpleModule A₁ U] [FiniteDimensional ℂ U] : IsSimpleModule A₂ (Mult U) := by
  have := IsSimpleModule.nontrivial A₁ U
  have hι : U.subtype ≠ 0 := by
    intro h
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    exact hu (Subtype.ext (LinearMap.congr_fun h u))
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hι ?_⟩, eq_bot_or_eq_top := fun N => ?_ }
  · have hm : U.subtype ∈ (⊤ : Submodule A₂ (Mult U)) := Submodule.mem_top
    rw [← h] at hm
    exact hm
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hu
  let T := TensorProduct.map (LinearMap.id : U →ₗ[ℂ] U) (N.subtype.restrictScalars ℂ)
  let Φ : U ⊗[ℂ] Mult U →ₗ[ℂ] Mult U :=
    (TensorProduct.lid ℂ (Mult U)).toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
  have hΦ (s : U ⊗[ℂ] N) : Φ (T s) ∈ N := by
    induction s with
    | tmul v m =>
      simp only [Φ, T, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.restrictScalars_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
        TensorProduct.lid_tmul]
      exact (N.restrictScalars ℂ).smul_mem _ m.2
    | add s t hs ht =>
      rw [map_add, map_add]
      exact N.add_mem hs ht
  apply eq_top_iff.mpr
  intro f _
  obtain ⟨t, ht⟩ := eval_restricted_surjective U hact hN (f u)
  have ht' : T t = u ⊗ₜ f := by
    apply eval_injective U
    exact ht.trans (eval_tmul U u f).symm
  have hm := hΦ t
  rw [ht'] at hm
  simpa [Φ, hφ] using hm

theorem eval_comm (a : A₁ ⊗[ℂ] A₂) (t : U ⊗[ℂ] Mult U) :
    eval U (action a t) = a • eval U t := by
  induction a with
  | tmul a b =>
    induction t with
    | tmul u f =>
      rw [action_tmul, eval_tmul, eval_tmul, LinearMap.smul_apply, map_smul,
        ← smul_comm a b, hact]
    | add s t hs ht =>
      rw [map_add, map_add, map_add, hs, ht, smul_add]
  | add a b ha hb =>
    rw [map_add, LinearMap.add_apply, map_add, ha, hb, add_smul]

end Multiplicity
end Langlands.AlgebraTensor

namespace Langlands
universe u₁ u₂ v

theorem algebraTensorSimpleFactorization :
    AlgebraTensorSimpleFactorizationStatement.{u₁, u₂, v} := by
  intro A₁ A₂ _ _ _ _ W _ _ _ _ hfin hsimp
  have := hfin
  have := hsimp
  have := IsSimpleModule.nontrivial (A₁ ⊗[ℂ] A₂) W
  let ι₁ : A₁ →ₐ[ℂ] A₁ ⊗[ℂ] A₂ := Algebra.TensorProduct.includeLeft
  let ι₂ : A₂ →ₐ[ℂ] A₁ ⊗[ℂ] A₂ := Algebra.TensorProduct.includeRight
  let : Module A₁ W := Module.compHom W ι₁.toRingHom
  let : Module A₂ W := Module.compHom W ι₂.toRingHom
  let : IsScalarTower ℂ A₁ W := IsScalarTower.of_algebraMap_smul fun c w => by
    change ι₁ (algebraMap ℂ A₁ c) • w = c • w
    rw [ι₁.commutes, algebraMap_smul]
  let : IsScalarTower ℂ A₂ W := IsScalarTower.of_algebraMap_smul fun c w => by
    change ι₂ (algebraMap ℂ A₂ c) • w = c • w
    rw [ι₂.commutes, algebraMap_smul]
  let : SMulCommClass A₁ A₂ W := ⟨fun a b w => by
    change (a ⊗ₜ[ℂ] (1 : A₂)) • ((1 : A₁) ⊗ₜ[ℂ] b) • w =
      ((1 : A₁) ⊗ₜ[ℂ] b) • (a ⊗ₜ[ℂ] (1 : A₂)) • w
    simp only [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]⟩
  have hact (a : A₁) (b : A₂) (w : W) : (a ⊗ₜ[ℂ] b) • w = a • b • w := by
    change (a ⊗ₜ[ℂ] b) • w =
      (a ⊗ₜ[ℂ] (1 : A₂)) • ((1 : A₁) ⊗ₜ[ℂ] b) • w
    simp only [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let : IsArtinian A₁ W := isArtinian_of_tower ℂ inferInstance
  obtain ⟨U, hU⟩ := IsAtomic.exists_atom (Submodule A₁ W)
  have : IsSimpleModule A₁ U := isSimpleModule_iff_isAtom.mpr hU
  have : FiniteDimensional ℂ U :=
    Module.Finite.of_injective (U.subtype.restrictScalars ℂ) U.subtype_injective
  have : IsSimpleModule A₂ (AlgebraTensor.Mult U) := AlgebraTensor.mult_simple U hact
  have := IsSimpleModule.nontrivial A₁ U
  have := IsSimpleModule.nontrivial A₂ (AlgebraTensor.Mult U)
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  have : FiniteDimensional ℂ (AlgebraTensor.Mult U) :=
    Module.Finite.of_injective (AlgebraTensor.evalAt U u) (AlgebraTensor.evalAt_injective U hu)
  have hsurj : Function.Surjective (AlgebraTensor.eval U) := by
    intro w
    obtain ⟨t, ht⟩ := AlgebraTensor.eval_restricted_surjective U hact
      (N := ⊤) (Ne.symm bot_ne_top) w
    exact ⟨TensorProduct.map (LinearMap.id : U →ₗ[ℂ] U)
      ((⊤ : Submodule A₂ (AlgebraTensor.Mult U)).subtype.restrictScalars ℂ) t, ht⟩
  refine ⟨U, inferInstance, inferInstance, inferInstance, inferInstance,
    AlgebraTensor.Mult U, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨LinearEquiv.ofBijective (AlgebraTensor.eval U)
    ⟨AlgebraTensor.eval_injective U, hsurj⟩, AlgebraTensor.eval_comm U hact⟩

end Langlands
