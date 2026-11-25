import Langlands.Cohomology.Profinite.Cup.Corestriction
import Langlands.Cohomology.Profinite.Cup.Graded
import Langlands.Cohomology.Profinite.Duality.Pairing

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory

universe u

section Module

variable {k Γ : Type u} [CommRing k] [Group Γ] (W : Subgroup Γ) (V : Type u) [AddCommGroup V]
  [Module k V]

theorem coind_trivial_apply_mul (f : Rep.coind W.subtype (Rep.trivial k W V)) (w : W) (x : Γ) :
    f.1 ((w : Γ) * x) = f.1 x :=
  f.2 w x

def coindSingleFun (a : V) : Rep.coind W.subtype (Rep.trivial k W V) :=
  ⟨(W : Set Γ).indicator fun _ => a, fun w x => by
    change (W : Set Γ).indicator (fun _ => a) ((w : Γ) * x) = (W : Set Γ).indicator (fun _ => a) x
    by_cases hx : x ∈ W
    · rw [Set.indicator_of_mem (W.mul_mem w.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
      exact fun h => hx ((Subgroup.mul_mem_cancel_left W w.2).1 h)⟩

theorem coindSingleFun_apply (a : V) (x : Γ) :
    (coindSingleFun (k := k) W V a).1 x = (W : Set Γ).indicator (fun _ => a) x :=
  rfl

def coindSingle : Rep.trivial k W V ⟶ Rep.res W.subtype (Rep.coind W.subtype (Rep.trivial k W V)) :=
  Rep.ofHom ⟨{ toFun := coindSingleFun W V
               map_add' := fun a b => Subtype.ext (funext fun x => by
                 change (W : Set Γ).indicator (fun _ => a + b) x =
                   (W : Set Γ).indicator (fun _ => a) x + (W : Set Γ).indicator (fun _ => b) x
                 by_cases hx : x ∈ W <;> simp [hx])
               map_smul' := fun c a => Subtype.ext (funext fun x => by
                 change (W : Set Γ).indicator (fun _ => c • a) x =
                   c • (W : Set Γ).indicator (fun _ => a) x
                 by_cases hx : x ∈ W <;> simp [hx]) }, fun w => by
    refine LinearMap.ext fun a => Subtype.ext (funext fun x => ?_)
    change (W : Set Γ).indicator (fun _ => a) x = (W : Set Γ).indicator (fun _ => a) (x * w)
    by_cases hx : x ∈ W
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (W.mul_mem hx w.2)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
      exact fun h => hx ((Subgroup.mul_mem_cancel_right W w.2).1 h)⟩

theorem coindSingle_hom_apply (a : V) (x : Γ) :
    ((coindSingle (k := k) W V).hom a).1 x = (W : Set Γ).indicator (fun _ => a) x :=
  rfl

variable (D : Rep.{u} k Γ)

def coindDualPairingFun (f : Rep.coind W.subtype (Rep.trivial k W V))
    (μ : Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V))) :
    Rep.coind W.subtype (Rep.res W.subtype D) :=
  ⟨fun x => (μ.1 x : V →ₗ[k] D) (f.1 x), fun w x => by
    have hμ : μ.1 ((w : Γ) * x) = _ := μ.2 w x
    have hf : f.1 ((w : Γ) * x) = _ := f.2 w x
    change (μ.1 ((w : Γ) * x) : V →ₗ[k] D) (f.1 ((w : Γ) * x)) =
      D.ρ (w : Γ) ((μ.1 x : V →ₗ[k] D) (f.1 x))
    rw [hμ, hf]
    rfl⟩

def coindDualPairing :
    Rep.coind W.subtype (Rep.trivial k W V) ⊗
        Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V)) ⟶
      Rep.coind W.subtype (Rep.res W.subtype D) :=
  pairingHom (LinearMap.mk₂ k (coindDualPairingFun W V D)
      (fun _ _ μ => Subtype.ext (funext fun x => (μ.1 x : V →ₗ[k] D).map_add _ _))
      (fun _ _ μ => Subtype.ext (funext fun x => (μ.1 x : V →ₗ[k] D).map_smul _ _))
      (fun _ _ _ => Subtype.ext (funext fun _ => rfl))
      (fun _ _ _ => Subtype.ext (funext fun _ => rfl)))
    fun _ _ _ => Subtype.ext (funext fun _ => rfl)

theorem coindDualPairing_tmul (f : Rep.coind W.subtype (Rep.trivial k W V))
    (μ : Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V))) (x : Γ) :
    ((coindDualPairing W V D).hom (f ⊗ₜ[k] μ)).1 x = (μ.1 x : V →ₗ[k] D) (f.1 x) :=
  rfl

theorem res_coindDualPairing_comp_coindEvalOne :
    (Rep.resFunctor W.subtype).map (coindDualPairing W V D) ≫
        coindEvalOne W (Rep.res W.subtype D) =
      resTensorHom W.subtype (coindEvalOne W (Rep.trivial k W V))
          (coindEvalOne W (dualRep (Rep.res W.subtype D) (Rep.trivial k W V))) ≫
        evalPairing (Rep.res W.subtype D) (Rep.trivial k W V) := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul f μ => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

def coindDualRestrict :
    Rep.res W.subtype (dualRep D (Rep.coind W.subtype (Rep.trivial k W V))) ⟶
      dualRep (Rep.res W.subtype D) (Rep.trivial k W V) :=
  Rep.ofHom ⟨{ toFun := fun l => (l : Rep.coind W.subtype (Rep.trivial k W V) →ₗ[k] D) ∘ₗ
                  (coindSingle (k := k) W V).hom.toLinearMap
               map_add' := fun _ _ => rfl
               map_smul' := fun _ _ => rfl }, fun w => by
    refine LinearMap.ext fun l => LinearMap.ext fun a => ?_
    change D.ρ (w : Γ) (l ((Rep.coind W.subtype (Rep.trivial k W V)).ρ (w : Γ)⁻¹
        ((coindSingle (k := k) W V).hom a))) =
      D.ρ (w : Γ) (l ((coindSingle (k := k) W V).hom ((Rep.trivial k W V).ρ w⁻¹ a)))
    rw [Rep.hom_comm_apply]
    rfl⟩

theorem coindDualRestrict_hom_apply
    (l : Rep.coind W.subtype (Rep.trivial k W V) →ₗ[k] D) (a : V) :
    ((coindDualRestrict W V D).hom l : V →ₗ[k] D) a = l ((coindSingle (k := k) W V).hom a) :=
  rfl

def coindDualInv :
    dualRep D (Rep.coind W.subtype (Rep.trivial k W V)) ⟶
      Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V)) :=
  Rep.resCoindToHom W.subtype _ _ (coindDualRestrict W V D)

theorem coindDualInv_hom_apply (l : Rep.coind W.subtype (Rep.trivial k W V) →ₗ[k] D) (x : Γ)
    (a : V) :
    (((coindDualInv W V D).hom l).1 x : V →ₗ[k] D) a =
      D.ρ x (l ((Rep.coind W.subtype (Rep.trivial k W V)).ρ x⁻¹
        ((coindSingle (k := k) W V).hom a))) :=
  rfl

theorem res_coindDualInv_comp_coindEvalOne :
    (Rep.resFunctor W.subtype).map (coindDualInv W V D) ≫
        coindEvalOne W (dualRep (Rep.res W.subtype D) (Rep.trivial k W V)) =
      coindDualRestrict W V D := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun l => ?_))
  refine LinearMap.ext fun a => ?_
  change D.ρ 1 (l ((Rep.coind W.subtype (Rep.trivial k W V)).ρ 1⁻¹
      ((coindSingle (k := k) W V).hom a))) = l ((coindSingle (k := k) W V).hom a)
  simp only [inv_one, map_one, Module.End.one_apply]

section Sum

variable [W.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem sum_ite_mul_out_mem {M : Type*} [AddCommMonoid M] (F : Γ → M)
    (hF : ∀ (x : Γ) (w : W), F (x * w) = F x) (h : Γ) :
    ∑ c : Γ ⧸ W, (by classical exact if h * c.out ∈ W then F c.out else 0) = F h⁻¹ := by
  classical
  rw [Finset.sum_eq_single ((h⁻¹ : Γ) : Γ ⧸ W)]
  · obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W h⁻¹
    have hmem : h * (((h⁻¹ : Γ) : Γ ⧸ W).out) ∈ W := by
      rw [hw, ← mul_assoc, mul_inv_cancel, one_mul]
      exact w.2
    change (if h * (((h⁻¹ : Γ) : Γ ⧸ W).out) ∈ W then F (((h⁻¹ : Γ) : Γ ⧸ W).out) else 0) = _
    rw [ite_eq_left hmem, hw, hF]
  · intro c _ hc
    rw [ite_eq_right]
    intro hmem
    apply hc
    rw [← QuotientGroup.out_eq' c]
    refine QuotientGroup.eq.2 ?_
    have := W.inv_mem hmem
    rwa [mul_inv_rev] at this
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem sum_coindSingle (f : Rep.coind W.subtype (Rep.trivial k W V)) :
    ∑ c : Γ ⧸ W, (Rep.coind W.subtype (Rep.trivial k W V)).ρ c.out
      ((coindSingle (k := k) W V).hom (f.1 c.out⁻¹)) = f := by
  classical
  refine Subtype.ext (funext fun h => ?_)
  rw [Submodule.coe_sum, Finset.sum_apply]
  have key := sum_ite_mul_out_mem W (fun x => f.1 x⁻¹) (fun x w => by
    rw [mul_inv_rev]
    exact coind_trivial_apply_mul W V f w⁻¹ x⁻¹) h
  rw [inv_inv] at key
  rw [← key]
  refine Finset.sum_congr rfl fun c _ => ?_
  change (W : Set Γ).indicator (fun _ => f.1 c.out⁻¹) (h * c.out) = _
  rw [Set.indicator_apply]
  rfl

def coindDualHom :
    Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V)) ⟶
      dualRep D (Rep.coind W.subtype (Rep.trivial k W V)) :=
  Rep.tensorHomEquiv _ _ _ (coindDualPairing W V D ≫ coindTrace W D)

theorem coindDualHom_hom_apply
    (μ : Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V)))
    (f : Rep.coind W.subtype (Rep.trivial k W V)) :
    ((coindDualHom W V D).hom μ : Rep.coind W.subtype (Rep.trivial k W V) →ₗ[k] D) f =
      (coindTrace W D).hom ((coindDualPairing W V D).hom (f ⊗ₜ[k] μ)) :=
  rfl

theorem tensorHom_coindDualHom_evalPairing :
    (𝟙 _ ⊗ₘ coindDualHom W V D) ≫ evalPairing D (Rep.coind W.subtype (Rep.trivial k W V)) =
      coindDualPairing W V D ≫ coindTrace W D := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul f μ => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

theorem coindDualInv_comp_coindDualHom :
    coindDualInv W V D ≫ coindDualHom W V D = 𝟙 _ := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun l => ?_))
  refine LinearMap.ext fun f => ?_
  change (coindTrace W D).hom ((coindDualPairing W V D).hom (f ⊗ₜ[k] (coindDualInv W V D).hom l)) =
    (l : Rep.coind W.subtype (Rep.trivial k W V) →ₗ[k] D) f
  rw [coindTrace_hom_apply]
  conv_rhs => rw [← sum_coindSingle W V f, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  change D.ρ c.out (D.ρ c.out⁻¹ (l ((Rep.coind W.subtype (Rep.trivial k W V)).ρ c.out⁻¹⁻¹
    ((coindSingle (k := k) W V).hom (f.1 c.out⁻¹))))) = _
  rw [inv_inv, Representation.self_inv_apply]

theorem coindDualHom_comp_coindDualInv :
    coindDualHom W V D ≫ coindDualInv W V D = 𝟙 _ := by
  classical
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun μ => ?_))
  refine Subtype.ext (funext fun h => ?_)
  change (((coindDualInv W V D).hom ((coindDualHom W V D).hom μ)).1 h : V →ₗ[k] D) =
    (μ.1 h : V →ₗ[k] D)
  refine LinearMap.ext fun a => ?_
  change D.ρ h ((coindTrace W D).hom ((coindDualPairing W V D).hom
    ((Rep.coind W.subtype (Rep.trivial k W V)).ρ h⁻¹ ((coindSingle (k := k) W V).hom a) ⊗ₜ[k] μ))) =
      (μ.1 h : V →ₗ[k] D) a
  rw [coindTrace_hom_apply, map_sum]
  have key := sum_ite_mul_out_mem W (fun x => D.ρ h (D.ρ x ((μ.1 x⁻¹ : V →ₗ[k] D) a)))
    (fun x w => by
      have hμ : μ.1 ((w⁻¹ : W) * x⁻¹) = _ := μ.2 w⁻¹ x⁻¹
      change D.ρ h (D.ρ (x * w) ((μ.1 (x * w)⁻¹ : V →ₗ[k] D) a)) = _
      rw [mul_inv_rev]
      change D.ρ h (D.ρ (x * w) ((μ.1 ((w⁻¹ : W) * x⁻¹) : V →ₗ[k] D) a)) = _
      rw [hμ]
      change D.ρ h (D.ρ (x * w) (D.ρ ((w⁻¹ : W) : Γ) ((μ.1 x⁻¹ : V →ₗ[k] D)
        ((Rep.trivial k W V).ρ (w⁻¹)⁻¹ a)))) = _
      rw [map_mul, Module.End.mul_apply]
      congr 2
      change D.ρ (w : Γ) (D.ρ (w : Γ)⁻¹ _) = _
      rw [Representation.self_inv_apply]
      rfl) h
  rw [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] at key
  rw [← key]
  refine Finset.sum_congr rfl fun c _ => ?_
  change D.ρ h (D.ρ c.out ((μ.1 c.out⁻¹ : V →ₗ[k] D)
    ((W : Set Γ).indicator (fun _ => a) (c.out⁻¹ * h⁻¹)))) = _
  by_cases hc : h * c.out ∈ W
  · rw [ite_eq_left hc, Set.indicator_of_mem]
    rw [← mul_inv_rev]
    exact W.inv_mem hc
  · rw [ite_eq_right hc, Set.indicator_of_notMem, map_zero, map_zero, map_zero]
    intro hmem
    apply hc
    have := W.inv_mem hmem
    rwa [mul_inv_rev, inv_inv, inv_inv] at this

def coindDualIso :
    Rep.coind W.subtype (dualRep (Rep.res W.subtype D) (Rep.trivial k W V)) ≅
      dualRep D (Rep.coind W.subtype (Rep.trivial k W V)) where
  hom := coindDualHom W V D
  inv := coindDualInv W V D
  hom_inv_id := coindDualHom_comp_coindDualInv W V D
  inv_hom_id := coindDualInv_comp_coindDualHom W V D

end Sum

end Module

end Langlands.ProfiniteCohomology

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory

universe u

section Finite

variable {k Γ : Type u} [CommRing k] [Group Γ] (W : Subgroup Γ) (V : Type u) [AddCommGroup V]
  [Module k V]

instance finite_coind_trivial [Finite V] [W.FiniteIndex] :
    Finite (Rep.coind W.subtype (Rep.trivial k W V)) := by
  refine Finite.of_injective (fun f : Rep.coind W.subtype (Rep.trivial k W V) =>
    fun c : Γ ⧸ W => f.1 c.out⁻¹) fun f f' hff' => Subtype.ext (funext fun x => ?_)
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W x⁻¹
  have h := congrFun hff' ((x⁻¹ : Γ) : Γ ⧸ W)
  simp only at h
  rw [hw, mul_inv_rev, inv_inv] at h
  rwa [← Subgroup.coe_inv, coind_trivial_apply_mul W V f w⁻¹ x,
    coind_trivial_apply_mul W V f' w⁻¹ x] at h

end Finite

section Formula

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] (W : OpenSubgroup Γ) (V : Type u) [AddCommGroup V] [Module k V] [Finite V]
  (D : Rep.{u} k Γ) [IsSmoothRep D]

instance isSmoothRep_coind_trivial :
    IsSmoothRep (Rep.coind (W : Subgroup Γ).subtype (Rep.trivial k (W : Subgroup Γ) V)) :=
  isSmoothRep_coind W _

instance isSmoothRep_dualRep_res_trivial :
    IsSmoothRep (dualRep (Rep.res (W : Subgroup Γ).subtype D) (Rep.trivial k (W : Subgroup Γ) V)) :=
  isSmoothRep_dualRep _ _

instance isSmoothRep_coind_dualRep_res_trivial :
    IsSmoothRep (Rep.coind (W : Subgroup Γ).subtype
      (dualRep (Rep.res (W : Subgroup Γ).subtype D) (Rep.trivial k (W : Subgroup Γ) V))) :=
  isSmoothRep_coind W _

instance isSmoothRep_dualRep_coind_trivial :
    IsSmoothRep (dualRep D (Rep.coind (W : Subgroup Γ).subtype (Rep.trivial k (W : Subgroup Γ) V))) :=
  isSmoothRep_dualRep _ _

theorem cupPairing_evalPairing_coindDualHom {r s m : ℕ} (h : r + s = m)
    (x : cohomology (Rep.coind.{u, u, u, u} (W : Subgroup Γ).subtype (Rep.trivial k (W : Subgroup Γ) V)) r)
    (y : cohomology (Rep.coind.{u, u, u, u} (W : Subgroup Γ).subtype
      (dualRep (Rep.res (W : Subgroup Γ).subtype D) (Rep.trivial k (W : Subgroup Γ) V))) s) :
    cupPairing (evalPairing D (Rep.coind.{u, u, u, u} (W : Subgroup Γ).subtype (Rep.trivial k (W : Subgroup Γ) V))) h x (coeffMap (coindDualHom (W : Subgroup Γ) V D) s y) =
      cores W D m (cupPairing (evalPairing (Rep.res (W : Subgroup Γ).subtype D)
        (Rep.trivial k (W : Subgroup Γ) V)) h (shapiroMap W (Rep.trivial k (W : Subgroup Γ) V) r x)
        (shapiroMap W (dualRep (Rep.res (W : Subgroup Γ).subtype D) (Rep.trivial k (W : Subgroup Γ) V)) s y)) := by
  have e1 := cupPairing_cohomologyMap
    (evalPairing D (Rep.coind.{u, u, u, u} (W : Subgroup Γ).subtype (Rep.trivial k (W : Subgroup Γ) V))) (𝟙 _) (coindDualHom (W : Subgroup Γ) V D)
    h x y
  rw [coeffMap_id] at e1
  change cupPairing (evalPairing D (Rep.coind.{u, u, u, u} (W : Subgroup Γ).subtype (Rep.trivial k (W : Subgroup Γ) V))) h x (coeffMap (coindDualHom (W : Subgroup Γ) V D) s y) =
    _ at e1
  rw [e1, tensorHom_coindDualHom_evalPairing, ← cohomologyMap_cupPairing,
    ← cores_shapiroMap]
  congr 1
  rw [cupPairing_apply, cupPairing_apply, shapiroMap_eq, shapiroMap_eq, shapiroMap_eq,
    ← map_resTensorHom_cup, cohomologyMap_map,
    map_coeffMap]
  erw [res_coindDualPairing_comp_coindEvalOne]
  rfl

end Formula

section Unit

variable {k H : Type u} [CommRing k] [Group H]

def unitHom (A : Rep.{u} k H) (a : A) (ha : ∀ g : H, A.ρ g a = a) : 𝟙_ (Rep.{u} k H) ⟶ A :=
  Rep.ofHom ⟨LinearMap.toSpanSingleton k A a, fun g => LinearMap.ext fun c => by
    change (c • a : A) = A.ρ g (c • a)
    rw [map_smul, ha]⟩

theorem unitHom_hom_apply (A : Rep.{u} k H) (a : A) (ha : ∀ g : H, A.ρ g a = a) (c : k) :
    (unitHom A a ha).hom c = c • a :=
  rfl

end Unit

section H0

theorem zmodRep_ρ_apply {H : Type u} [Monoid H] {n : ℕ} (g : H) (v : zmodRep.{u} H n) :
    (zmodRep.{u} H n).ρ g v = v :=
  rfl

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ}

def zmodH0Class (a : ZMod n) : cohomology (zmodRep.{u} H n) 0 :=
  coeffMap (unitHom (zmodRep.{u} H n) (ULift.up a) fun g => zmodRep_ρ_apply g _) 0 unitClass

theorem zmodH0Class_surjective : Function.Surjective (zmodH0Class (H := H) (n := n)) := by
  intro x
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 0 x
  refine ⟨(cochainOf _ (cocycleι _ 0 z) (fun i => i.elim0)).down, ?_⟩
  rw [zmodH0Class, unitClass, cohomologyMap_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_unitCocycle]
  funext σ
  have hσ : σ = fun i => i.elim0 := Subsingleton.elim _ _
  rw [hσ]
  exact one_smul _ _

variable [NeZero n] (D' : Rep.{u} (ULift.{u} ℤ) H) [IsSmoothRep D'] (hD : ∀ d : D', n • d = 0)

omit [TopologicalSpace H] [IsTopologicalGroup H] [IsSmoothRep D'] in

theorem unitHom_tensorHom_zmodMulPairing (a : ZMod n) :
    (unitHom (zmodRep.{u} H n) (ULift.up a) (fun g => zmodRep_ρ_apply g _) ⊗ₘ 𝟙 D') ≫ zmodMulPairing n D' hD =
      (λ_ D').hom ≫ (a.val • 𝟙 D') := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext
    (TensorProduct.ext' fun (c : ULift.{u} ℤ) d => ?_))
  change (zmodMulPairing n D' hD).hom
      ((unitHom (zmodRep.{u} H n) (ULift.up a) fun g => zmodRep_ρ_apply g _).hom c ⊗ₜ[ULift.{u} ℤ]
        d) =
    (a.val • 𝟙 D').hom ((λ_ D').hom.hom (c ⊗ₜ[ULift.{u} ℤ] d))
  rw [unitHom_hom_apply, ← TensorProduct.smul_tmul']
  change (zmodMulPairing n D' hD).hom.toLinearMap (_ • _) = _
  rw [LinearMap.map_smul, Representation.IntertwiningMap.toLinearMap_apply, zmodMulPairing_tmul,
    leftUnitor_hom_tmul, Rep.nsmul_hom, Representation.IntertwiningMap.coe_nsmul,
    Pi.smul_apply, ZMod.cast_eq_val, natCast_zsmul, smul_comm]
  rfl

theorem cupPairing_zmodH0Class (h : 0 + 2 = 2) (a : ZMod n) (y : cohomology D' 2) :
    cupPairing (zmodMulPairing n D' hD) h (zmodH0Class a) y = a.val • y := by
  have e := cupPairing_cohomologyMap (zmodMulPairing n D' hD)
    (unitHom (zmodRep.{u} H n) (ULift.up a) fun g => zmodRep_ρ_apply g _) (𝟙 D') h unitClass y
  rw [coeffMap_id] at e
  change cupPairing (zmodMulPairing n D' hD) h (zmodH0Class a) y = _ at e
  rw [e, unitHom_tensorHom_zmodMulPairing, ← cohomologyMap_cupPairing, cupPairing_apply,
    cohomologyMap_leftUnitor_unitClass_cup, cohomologyMap_nsmul_id]
  rfl

theorem bijective_zmodMulPairing_zero (T : cohomology D' 2 →+ ZMod n)
    (hT : Function.Bijective T) (h : 0 + 2 = 2) :
    Function.Bijective (fun x : cohomology (zmodRep.{u} H n) 0 =>
      T.comp (bilinAddHom (cupPairing (zmodMulPairing n D' hD) h) x)) := by
  obtain ⟨y₀, hy₀⟩ := hT.2 1
  have hF : ∀ (a : ZMod n) (y : cohomology D' 2),
      T.comp (bilinAddHom (cupPairing (zmodMulPairing n D' hD) h) (zmodH0Class a)) y =
        a.val • T y := by
    intro a y
    rw [AddMonoidHom.comp_apply, bilinAddHom_apply, cupPairing_zmodH0Class, map_nsmul]
  constructor
  · intro x x' hxx'
    obtain ⟨a, rfl⟩ := zmodH0Class_surjective x
    obtain ⟨a', rfl⟩ := zmodH0Class_surjective x'
    have key := DFunLike.congr_fun hxx' y₀
    beta_reduce at key
    rw [hF, hF, hy₀, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val] at key
    rw [key]
  · intro χ
    refine ⟨zmodH0Class (χ y₀), AddMonoidHom.ext fun y => ?_⟩
    beta_reduce
    rw [hF]
    have hy : y = (T y).val • y₀ :=
      hT.1 (by rw [map_nsmul, hy₀, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val])
    conv_rhs => rw [hy]
    rw [map_nsmul, nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      mul_comm]

end H0

section Transfer

variable {n : ℕ}

theorem bijective_of_bijective_comp {X X' Y Y' : Type*} [AddCommGroup Y] [AddCommGroup Y']
    {F : X → (Y →+ ZMod n)} (hF : Function.Bijective F) {α : X' → X} (hα : Function.Bijective α)
    {γ : Y' →+ Y} (hγ : Function.Bijective γ) {F' : X' → (Y' →+ ZMod n)}
    (hF' : ∀ x' y', F' x' y' = F (α x') (γ y')) : Function.Bijective F' := by
  let e := AddEquiv.ofBijective γ hγ
  have hP : Function.Bijective (fun χ : Y →+ ZMod n => χ.comp γ) := by
    refine ⟨fun χ χ' hχ => AddMonoidHom.ext fun y => ?_, fun ψ =>
      ⟨ψ.comp e.symm.toAddMonoidHom, AddMonoidHom.ext fun y' => ?_⟩⟩
    · obtain ⟨y', rfl⟩ := hγ.2 y
      exact DFunLike.congr_fun hχ y'
    · change ψ (e.symm (γ y')) = ψ y'
      rw [show γ y' = e y' from rfl, AddEquiv.symm_apply_apply]
  have hcomp : F' = (fun χ : Y →+ ZMod n => χ.comp γ) ∘ F ∘ α :=
    funext fun x' => AddMonoidHom.ext fun y' => hF' x' y'
  rw [hcomp]
  exact hP.comp (hF.comp hα)

/-- Bijectivity of a duality map `x ↦ T ∘ B(·, x)` is preserved by isomorphisms compatible with the
pairings and by multiplying the trace by a unit. -/
theorem bijective_of_transport {X X' Y Y' W W' : Type*} [AddCommGroup X] [AddCommGroup X']
    [AddCommGroup Y] [AddCommGroup Y'] [AddCommGroup W] [AddCommGroup W'] (B : Y →+ X →+ W)
    (B' : Y' →+ X' →+ W') (T : W →+ ZMod n) (f : W' →+ ZMod n) (eX : X ≃+ X') (eY : Y ≃+ Y')
    (eW : W ≃+ W') (hcup : ∀ y x, B' (eY y) (eX x) = eW (B y x)) (c : ZMod n) (hc : IsUnit c)
    (hf : ∀ w, f (eW w) = c * T w) (hbij : Function.Bijective fun x => T.comp (B.flip x)) :
    Function.Bijective fun x' => f.comp (B'.flip x') := by
  have hF : Function.Bijective fun x => (c • T).comp (B.flip x) := by
    refine ⟨fun x x' h => hbij.1 (AddMonoidHom.ext fun y => ?_), fun χ => ?_⟩
    · have e := DFunLike.congr_fun h y
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, AddMonoidHom.smul_apply,
        smul_eq_mul] at e ⊢
      exact hc.mul_left_cancel e
    · obtain ⟨x, hx⟩ := hbij.2 ((hc.unit⁻¹ : (ZMod n)ˣ) • χ)
      refine ⟨x, AddMonoidHom.ext fun y => ?_⟩
      have e := DFunLike.congr_fun hx y
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, AddMonoidHom.smul_apply,
        smul_eq_mul, Units.smul_def] at e ⊢
      rw [e, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  refine bijective_of_bijective_comp hF eX.symm.bijective (γ := eY.symm.toAddMonoidHom)
    eY.symm.bijective fun x' y' => ?_
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, AddMonoidHom.smul_apply, smul_eq_mul,
    AddEquiv.coe_toAddMonoidHom]
  conv_lhs => rw [← eX.apply_symm_apply x', ← eY.apply_symm_apply y']
  rw [hcup, hf]

end Transfer

section Main

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem bijective_cohomologyMap_of_comp_eq_id {A B : Rep.{u} k Γ} [IsSmoothRep A]
    [IsSmoothRep B] (f : A ⟶ B) (g : B ⟶ A) (hfg : f ≫ g = 𝟙 A) (hgf : g ≫ f = 𝟙 B) (m : ℕ) :
    Function.Bijective (coeffMap f m) := by
  refine Function.bijective_iff_has_inverse.2 ⟨coeffMap g m, fun x => ?_, fun y => ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← coeffMap_comp, hfg, coeffMap_id]
    rfl
  · rw [← ConcreteCategory.comp_apply, ← coeffMap_comp, hgf, coeffMap_id]
    rfl

variable [CompactSpace Γ] {n : ℕ} [NeZero n]

instance (priority := high) finite_uliftZMod : Finite (ULift.{u} (ZMod n)) :=
  Finite.of_equiv _ Equiv.ulift.symm

instance finite_coind_zmodRep (W : OpenSubgroup Γ) :
    Finite (Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) :=
  finite_coind_trivial _ _

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [NeZero n] in

theorem nsmul_coind_zmodRep_eq_zero (W : OpenSubgroup Γ)
    (f : Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) : n • f = 0 :=
  Subtype.ext (funext fun x => nsmul_zmodRep_eq_zero (W : Subgroup Γ) n (f.1 x))

instance isSmoothRep_coind_zmodRep (W : OpenSubgroup Γ) :
    IsSmoothRep (Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) :=
  isSmoothRep_coind W _

instance isSmoothRep_dualRep_coind_zmodRep (D : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep D]
    (W : OpenSubgroup Γ) :
    IsSmoothRep (dualRep D (Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n))) :=
  isSmoothRep_dualRep _ _

theorem bijective_dualityMap_coind (D : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep D]
    (hD : Nonempty (D ≃+ ZMod n)) (t : cohomology D 2 →+ ZMod n) (W : OpenSubgroup Γ)
    (hT : Function.Bijective (t.comp (cores W D 2).hom.toAddMonoidHom))
    (hP : IsPerfectPairing (bilinAddHom (cupPairing (zmodMulPairing n
      (Rep.res (W : Subgroup Γ).subtype D) (nsmul_eq_zero_of_nonempty_addEquiv hD))
      (show 1 + 1 = 2 from rfl))) (t.comp (cores W D 2).hom.toAddMonoidHom))
    {r s : ℕ} (h : r + s = 2) (hr : r ≤ 1) :
    Function.Bijective (dualityMap D h t
      (Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n))) := by
  have hD' : ∀ d : Rep.res (W : Subgroup Γ).subtype D, n • d = 0 :=
    nsmul_eq_zero_of_nonempty_addEquiv hD
  have hΨ : Function.Bijective (coeffMap (coindDualInv (W : Subgroup Γ)
      (ULift.{u} (ZMod n)) D) s) :=
    bijective_cohomologyMap_of_comp_eq_id _ _ (coindDualInv_comp_coindDualHom _ _ _)
      (coindDualHom_comp_coindDualInv _ _ _) s
  have hsh : ∀ (B : Rep.{u} (ULift.{u} ℤ) (W : Subgroup Γ)) [IsSmoothRep B] (m : ℕ),
      Function.Bijective (shapiroMap W B m) := fun B _ m =>
    Function.bijective_iff_has_inverse.2 ⟨inv (shapiroMap W B m), inv_shapiroMap_apply W m,
      shapiroMap_inv_apply W m⟩
  have he : Function.Bijective (coeffMap
      (zmodDualIso n (Rep.res (W : Subgroup Γ).subtype D) hD').hom s) :=
    bijective_cohomologyMap_of_comp_eq_id _ _ (Iso.hom_inv_id _) (Iso.inv_hom_id _) s
  let γ : cohomology (dualRep D (Rep.coind (W : Subgroup Γ).subtype
      (zmodRep.{u} (W : Subgroup Γ) n))) s →+ cohomology (Rep.res (W : Subgroup Γ).subtype D) s :=
    ((coeffMap (zmodDualIso n (Rep.res (W : Subgroup Γ).subtype D) hD').hom s).hom.comp
      ((shapiroMap W _ s).hom.comp (coeffMap (coindDualInv (W : Subgroup Γ)
        (ULift.{u} (ZMod n)) D) s).hom)).toAddMonoidHom
  have hγ : Function.Bijective γ := he.comp ((hsh _ s).comp hΨ)
  have key : ∀ x y, dualityMap D h t
      (Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) x y =
      t.comp (cores W D 2).hom.toAddMonoidHom
        (cupPairing (zmodMulPairing n (Rep.res (W : Subgroup Γ).subtype D) hD') h
          (shapiroMap W _ r x) (γ y)) := by
    intro x y
    have hy : coeffMap (coindDualHom (W : Subgroup Γ) (ULift.{u} (ZMod n)) D) s
        (coeffMap (coindDualInv (W : Subgroup Γ) (ULift.{u} (ZMod n)) D) s y) = y := by
      rw [← ConcreteCategory.comp_apply, ← coeffMap_comp, coindDualInv_comp_coindDualHom,
        coeffMap_id]
      rfl
    rw [dualityMap_apply]
    conv_lhs => rw [← hy]
    rw [cupPairing_evalPairing_coindDualHom]
    have e2 := cupPairing_cohomologyMap (zmodMulPairing n (Rep.res (W : Subgroup Γ).subtype D) hD')
      (𝟙 _) (zmodDualIso n (Rep.res (W : Subgroup Γ).subtype D) hD').hom h
      (shapiroMap W _ r x) (shapiroMap W _ s
        (coeffMap (coindDualInv (W : Subgroup Γ) (ULift.{u} (ZMod n)) D) s y))
    rw [coeffMap_id, tensorHom_zmodDualIso_zmodMulPairing] at e2
    change t (cores W D 2 _) = t (cores W D 2 _)
    congr 2
    exact e2.symm
  obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
  · obtain rfl : s = 2 := by omega
    exact bijective_of_bijective_comp
      (bijective_zmodMulPairing_zero (Rep.res (W : Subgroup Γ).subtype D) hD' _ hT h)
      (hsh _ 0) hγ key
  · obtain rfl : s = 1 := by omega
    exact bijective_of_bijective_comp hP.1 (hsh _ 1) hγ key

end Main

end Langlands.ProfiniteCohomology

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory Limits

universe u

section Helpers

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem injective_cohomologyMap_zero {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    (f : A ⟶ B) (hf : Function.Injective f.hom) : Function.Injective (coeffMap f 0).hom := by
  intro x y hxy
  have e := fun z => congrArg (fun φ => φ.hom z) (cohomologyMap_zero_comp_zeroIso_hom f)
  have hx := e x
  have hy := e y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx hy
  have h : ((Rep.invariantsFunctor k G).map f).hom ((zeroIso A).hom.hom x) =
      ((Rep.invariantsFunctor k G).map f).hom ((zeroIso A).hom.hom y) := by
    rw [← hx, ← hy, hxy]
  have h' : (zeroIso A).hom.hom x = (zeroIso A).hom.hom y :=
    Subtype.ext (hf (congrArg Subtype.val h))
  rw [← zeroIso_inv_hom_apply A x, ← zeroIso_inv_hom_apply A y, h']

end Helpers

section Naturality

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {D : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep D] {n : ℕ} {t : cohomology D 2 →+ ZMod n}

theorem dualityMap_δ {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} [IsSmoothRep S.X₁]
    [IsSmoothRep S.X₂] [IsSmoothRep S.X₃] [Finite S.X₁] [Finite S.X₂] [Finite S.X₃]
    (hS : S.ShortExact) (hT : (dualShortComplex D S).ShortExact) (x : cohomology S.X₃ 0)
    (y : cohomology (dualRep D S.X₁) 1) :
    dualityMap D (rfl : 1 + 1 = 2) t S.X₁ ((δ hS 0 1 rfl).hom x) y =
      -dualityMap D (rfl : 0 + 2 = 2) t S.X₃ x ((δ hT 1 2 rfl).hom y) := by
  rw [dualityMap_apply, dualityMap_apply, ← map_neg]
  congr 1
  have := cupPairing_δ_eq (S := S) (T := dualShortComplex D S) (p := 0) (p' := 1) (q := 1)
    (q' := 2) (n := 2) (evalPairing D S.X₁) (evalPairing D S.X₂) (evalPairing D S.X₃)
    (tensorHom_evalPairing D S.f) (tensorHom_evalPairing D S.g).symm hS hT rfl rfl rfl rfl x y
  have h1 : ((-1 : ULift.{u} ℤ) ^ (0 + 1)) = -1 := by norm_num
  rw [h1, neg_one_smul] at this
  exact this

end Naturality

section Core

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]

structure GroupDualityHypotheses (n : ℕ) (D : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep D]
    (t : cohomology D 2 →+ ZMod n) : Prop where
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  finite_two : ∀ (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → Finite (cohomology M 2)
  subsingleton_three : ∀ (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (cohomology M 3)
  bijective_cores : ∀ W : OpenSubgroup Γ,
    Function.Bijective (t.comp (cores W D 2).hom.toAddMonoidHom)
  isPerfectPairing : ∀ W : OpenSubgroup Γ,
    IsPerfectPairing
      (bilinAddHom (cupPairing (zmodMulPairing n (Rep.res (W : Subgroup Γ).subtype D)
        (nsmul_eq_zero_of_nonempty_addEquiv nonempty_addEquiv)) (show 1 + 1 = 2 from rfl)))
      (t.comp (cores W D 2).hom.toAddMonoidHom)

namespace GroupDualityHypotheses

variable {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) Γ} [IsSmoothRep D]
  {t : cohomology D 2 →+ ZMod n} (H : GroupDualityHypotheses n D t)

include H in
theorem finite_D : Finite D :=
  finite_of_nonempty_addEquiv H.nonempty_addEquiv

omit [NeZero n] in
include H in
theorem nsmul_D (d : D) : n • d = 0 :=
  nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv d

include H in

theorem exists_devissage (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    ∃ (I Q : Rep.{u} (ULift.{u} ℤ) Γ) (_ : IsSmoothRep I) (_ : IsSmoothRep Q) (_ : Finite I)
      (_ : Finite Q) (i : M ⟶ I) (p : I ⟶ Q) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧ (∀ x : I, n • x = 0) ∧ (∀ x : Q, n • x = 0) ∧
      Function.Bijective (dualityMap D (rfl : 0 + 2 = 2) t I) ∧
      Function.Bijective (dualityMap D (rfl : 1 + 1 = 2) t I) := by
  obtain ⟨W, J, _, i, hi⟩ := exists_injective_biproduct_coind (n := n) M hM
  have hφ : ∀ {r s : ℕ} (h : r + s = 2), r ≤ 1 → Function.Bijective (dualityMap D h t
      (⨁ fun _ : J => Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n) :
        Rep.{u} (ULift.{u} ℤ) Γ)) :=
    fun h hr => bijective_dualityMap_biproduct D _ h t fun _ =>
      bijective_dualityMap_coind D H.nonempty_addEquiv t W (H.bijective_cores W)
        (H.isPerfectPairing W) h hr
  have hnI : ∀ x : ((⨁ fun _ : J => Rep.coind (W : Subgroup Γ).subtype
      (zmodRep.{u} (W : Subgroup Γ) n) : Rep.{u} (ULift.{u} ℤ) Γ) : Type u), n • x = 0 := by
    intro x
    rw [biproduct_eq_sum _ x, Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← map_nsmul, nsmul_coind_zmodRep_eq_zero W, map_zero]
  have hmono : Mono i := (Rep.mono_iff_injective i).2 hi
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel (cokernelIsCokernel i)) hmono
      (inferInstance : Epi (cokernel.π i))
  have hQd : IsSmoothRep (cokernel i) := isSmoothRep_X₃_of_shortExact hS
  have hsurj : Function.Surjective (cokernel.π i).hom :=
    (Rep.epi_iff_surjective _).1 inferInstance
  have hQf : Finite ((cokernel i : Rep.{u} (ULift.{u} ℤ) Γ) : Type u) :=
    Finite.of_surjective _ hsurj
  refine ⟨_, cokernel i, inferInstance, hQd, inferInstance, hQf, i, cokernel.π i,
    cokernel.condition i, hS, hnI, fun x => ?_, hφ rfl (by norm_num), hφ rfl le_rfl⟩
  obtain ⟨y, rfl⟩ := hsurj x
  rw [← map_nsmul, hnI, map_zero]

end GroupDualityHypotheses

end Core

section Steps

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) Γ} [IsSmoothRep D]
  {t : cohomology D 2 →+ ZMod n}

namespace GroupDualityHypotheses

variable (H : GroupDualityHypotheses n D t)

include H in

theorem injective_zero (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Injective (dualityMap D (rfl : 0 + 2 = 2) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI0, hI1⟩ := H.exists_devissage M hM
  have hi : Function.Injective i.hom := (Rep.mono_iff_injective i).1 hS.mono_f
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : dualityMap D (rfl : 0 + 2 = 2) t I ((coeffMap i 0).hom x) = 0 := by
    ext y
    rw [dualityMap_cohomologyMap D (rfl : 0 + 2 = 2) t i x y, hx]
    rfl
  have h2 : (coeffMap i 0).hom x = 0 := (injective_iff_map_eq_zero _).1 hI0.1 _ h1
  exact (injective_iff_map_eq_zero _).1 (injective_cohomologyMap_zero i hi) x h2

include H in

theorem surjective_zero (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Surjective (dualityMap D (rfl : 0 + 2 = 2) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI0, hI1⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  have hsurj : Function.Surjective (coeffMap (dualMap D i) 2).hom := by
    intro y
    have : Subsingleton (cohomology (dualRep D Q) 3) :=
      H.subsingleton_three (dualRep D Q) (nsmul_dualRep_eq_zero H.nsmul_D)
    exact (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hT 2 3 rfl) y
      (Subsingleton.elim _ _)
  intro l
  obtain ⟨v, hv⟩ := hI0.2 (l.comp (coeffMap (dualMap D i) 2).hom.toAddMonoidHom)
  have hpv : (coeffMap p 0).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (H.injective_zero Q hnQ)
    ext y
    rw [dualityMap_cohomologyMap D (rfl : 0 + 2 = 2) t p v y, hv]
    change l ((coeffMap (dualMap D p) 2 ≫ coeffMap (dualMap D i) 2).hom y) = 0
    rw [← coeffMap_comp, ← dualMap_comp, w, dualMap_zero, coeffMap_zero]
    exact map_zero l
  obtain ⟨m, hm⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS 0) v hpv
  refine ⟨m, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := hsurj y
  rw [← dualityMap_cohomologyMap D (rfl : 0 + 2 = 2) t i m z]
  change dualityMap D (rfl : 0 + 2 = 2) t I ((coeffMap S.f 0).hom m) z = _
  rw [hm, hv]
  rfl

include H in
theorem bijective_zero (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Bijective (dualityMap D (rfl : 0 + 2 = 2) t M) :=
  ⟨H.injective_zero M hM, H.surjective_zero M hM⟩

include H in

theorem injective_one (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Injective (dualityMap D (rfl : 1 + 1 = 2) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI0, hI1⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : dualityMap D (rfl : 1 + 1 = 2) t I ((coeffMap i 1).hom x) = 0 := by
    ext y
    rw [dualityMap_cohomologyMap D (rfl : 1 + 1 = 2) t i x y, hx]
    rfl
  have hix : (coeffMap i 1).hom x = 0 := (injective_iff_map_eq_zero _).1 hI1.1 _ h1
  obtain ⟨q, hq⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS 0 1 rfl) x hix
  have hker : ((coeffMap (dualMap D p) 2).hom.toAddMonoidHom).ker ≤
      (dualityMap D (rfl : 0 + 2 = 2) t Q q).ker := by
    intro z hz
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hT 1 2 rfl) z hz
    rw [AddMonoidHom.mem_ker]
    rw [← hy]
    have e := dualityMap_δ (t := t) hS hT q y
    change dualityMap D (rfl : 1 + 1 = 2) t M ((δ hS 0 1 rfl).hom q) y = _ at e
    rw [hq, hx] at e
    exact neg_eq_zero.1 e.symm
  obtain ⟨ψ, hψ⟩ := zmod_exists_comp_eq_of_ker_le
    (nsmul_cohomology_eq_zero _ (nsmul_dualRep_eq_zero H.nsmul_D) 2) _ _ hker
  obtain ⟨v, hv⟩ := hI0.2 ψ
  have hpv : (coeffMap p 0).hom v = q := by
    apply H.injective_zero Q hnQ
    ext z
    rw [dualityMap_cohomologyMap D (rfl : 0 + 2 = 2) t p v z, hv, ← hψ]
    rfl
  rw [← hq, ← hpv]
  exact congrArg (fun φ => φ.hom v) (comp_δ hS 0 1 rfl)

include H in

theorem surjective_one (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Surjective (dualityMap D (rfl : 1 + 1 = 2) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI0, hI1⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  intro l
  obtain ⟨v, hv⟩ := hI1.2 (l.comp (coeffMap (dualMap D i) 1).hom.toAddMonoidHom)
  have hpv : (coeffMap p 1).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (H.injective_one Q hnQ)
    ext y
    rw [dualityMap_cohomologyMap D (rfl : 1 + 1 = 2) t p v y, hv]
    change l ((coeffMap (dualMap D p) 1 ≫ coeffMap (dualMap D i) 1).hom y) = 0
    rw [← coeffMap_comp, ← dualMap_comp, w, dualMap_zero, coeffMap_zero]
    exact map_zero l
  obtain ⟨x', hx'⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS 1) v hpv
  set ν := l - dualityMap D (rfl : 1 + 1 = 2) t M x' with hν
  have hker : ((δ hT 1 2 rfl).hom.toAddMonoidHom).ker ≤ ν.ker := by
    intro y hy
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hT 1 2 rfl) y hy
    rw [AddMonoidHom.mem_ker, ← hz, hν, AddMonoidHom.sub_apply, sub_eq_zero]
    change l ((coeffMap (dualMap D i) 1).hom z) =
      dualityMap D (rfl : 1 + 1 = 2) t M x' ((coeffMap (dualMap D i) 1).hom z)
    rw [← dualityMap_cohomologyMap D (rfl : 1 + 1 = 2) t i x' z]
    change _ = dualityMap D (rfl : 1 + 1 = 2) t I ((coeffMap S.f 1).hom x') z
    rw [hx', hv]
    rfl
  obtain ⟨ψ, hψ⟩ := zmod_exists_comp_eq_of_ker_le
    (nsmul_cohomology_eq_zero _ (nsmul_dualRep_eq_zero H.nsmul_D) 2) _ _ hker
  obtain ⟨q, hq⟩ := (H.bijective_zero Q hnQ).2 ψ
  refine ⟨x' - (δ hS 0 1 rfl).hom q, ?_⟩
  ext y
  have e := dualityMap_δ (t := t) hS hT q y
  change dualityMap D (rfl : 1 + 1 = 2) t M ((δ hS 0 1 rfl).hom q) y = _ at e
  rw [map_sub, AddMonoidHom.sub_apply, e, hq, sub_neg_eq_add]
  have hψy : ψ ((δ hT 1 2 rfl).hom y) = ν y := congrArg (fun f => f y) hψ
  change _ + ψ ((δ hT 1 2 rfl).hom y) = l y
  rw [hψy, hν, AddMonoidHom.sub_apply, add_sub_cancel]

include H in
theorem bijective_one (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Bijective (dualityMap D (rfl : 1 + 1 = 2) t M) :=
  ⟨H.injective_one M hM, H.surjective_one M hM⟩

end GroupDualityHypotheses

end Steps

section Generic

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (D : Rep.{u} k Γ) [IsSmoothRep D]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [IsSmoothRep D] in

theorem tensorHom_toDualDual_evalPairing (M : Rep.{u} k Γ) :
    (𝟙 (dualRep D M) ⊗ₘ toDualDual D M) ≫ evalPairing D (dualRep D M) =
      (β_ (dualRep D M) M).hom ≫ evalPairing D M := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul f m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cupPairing_toDualDual (M : Rep.{u} k Γ) [IsSmoothRep M] [IsSmoothRep (dualRep D M)]
    [IsSmoothRep (dualRep D (dualRep D M))] (x : cohomology M 2)
    (y : cohomology (dualRep D M) 0) :
    cupPairing (evalPairing D (dualRep D M)) (rfl : 0 + 2 = 2) y
        ((coeffMap (toDualDual D M) 2).hom x) =
      cupPairing (evalPairing D M) (rfl : 2 + 0 = 2) x y := by
  calc cupPairing (evalPairing D (dualRep D M)) (rfl : 0 + 2 = 2) y
        ((coeffMap (toDualDual D M) 2).hom x)
      = cupPairing (evalPairing D (dualRep D M)) (rfl : 0 + 2 = 2)
          (coeffMap (𝟙 (dualRep D M)) 0 y) (coeffMap (toDualDual D M) 2 x) := by
        rw [coeffMap_id]
        rfl
    _ = cupPairing ((𝟙 (dualRep D M) ⊗ₘ toDualDual D M) ≫ evalPairing D (dualRep D M))
          (rfl : 0 + 2 = 2) y x := cupPairing_cohomologyMap _ _ _ _ _ _
    _ = cupPairing ((β_ (dualRep D M) M).hom ≫ evalPairing D M) (rfl : 0 + 2 = 2) y x := by
        rw [tensorHom_toDualDual_evalPairing]
    _ = coeffMap (evalPairing D M) 2
          (coeffMap (β_ (dualRep D M) M).hom 2 (cup (rfl : 0 + 2 = 2) y x)) := by
        rw [cupPairing_apply, coeffMap_comp]
        rfl
    _ = cupPairing (evalPairing D M) (rfl : 2 + 0 = 2) x y := by
        rw [coeffMap_braiding_cup (rfl : 0 + 2 = 2) (rfl : 2 + 0 = 2) y x, zero_mul, pow_zero,
          one_smul]
        rfl

end Generic

section Two

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) Γ} [IsSmoothRep D]
  {t : cohomology D 2 →+ ZMod n}

omit [NeZero n] in

theorem dualityMap_two_eq (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M]
    [IsSmoothRep (dualRep D (dualRep D M))] (x : cohomology M 2)
    (y : cohomology (dualRep D M) 0) :
    dualityMap D (rfl : 2 + 0 = 2) t M x y =
      dualityMap D (rfl : 0 + 2 = 2) t (dualRep D M) y
        ((coeffMap (toDualDual D M) 2).hom x) := by
  rw [dualityMap_apply, dualityMap_apply, cupPairing_toDualDual]

namespace GroupDualityHypotheses

variable (H : GroupDualityHypotheses n D t)

include H in

theorem bijective_two (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : Function.Bijective (dualityMap D (rfl : 2 + 0 = 2) t M) := by
  have := H.finite_D
  have : Finite (cohomology M 2) := H.finite_two M hM
  have hbij := bijective_toDualDual H.nonempty_addEquiv hM
  have : IsSmoothRep (dualRep D (dualRep D M)) := isSmoothRep_dualRep _ _
  let e : M ≅ dualRep D (dualRep D M) := repIsoOfBijective (toDualDual D M) hbij
  have he1 : ∀ z, (coeffMap e.inv 2).hom ((coeffMap (toDualDual D M) 2).hom z) = z :=
    fun z => by
      change (coeffMap e.hom 2 ≫ coeffMap e.inv 2).hom z = z
      rw [← coeffMap_comp, e.hom_inv_id, coeffMap_id]
      rfl
  have he2 : ∀ z, (coeffMap (toDualDual D M) 2).hom ((coeffMap e.inv 2).hom z) = z :=
    fun z => by
      change (coeffMap e.inv 2 ≫ coeffMap e.hom 2).hom z = z
      rw [← coeffMap_comp, e.inv_hom_id, coeffMap_id]
      rfl
  have h0 := H.bijective_zero (dualRep D M) (nsmul_dualRep_eq_zero H.nsmul_D)
  refine bijective_of_bijective_flip (nsmul_cohomology_eq_zero _ hM 2)
    (bilinAddHom (cupPairing (evalPairing D M) (rfl : 2 + 0 = 2))) t ?_
  let c := (coeffMap (toDualDual D M) 2).hom.toAddMonoidHom
  let c' := (coeffMap e.inv 2).hom.toAddMonoidHom
  have hpre : Function.Bijective fun χ : cohomology (dualRep D (dualRep D M)) 2 →+ ZMod n =>
      χ.comp c := by
    constructor
    · intro χ χ' h
      ext z
      have := congrArg (fun f : cohomology M 2 →+ ZMod n => f ((c' z))) h
      simpa [c, c', he2] using this
    · intro ξ
      refine ⟨ξ.comp c', ?_⟩
      ext z
      simp [c, c', he1]
  have hfun : (fun y => t.comp ((bilinAddHom (cupPairing (evalPairing D M)
      (rfl : 2 + 0 = 2))).flip y)) =
      fun y => (dualityMap D (rfl : 0 + 2 = 2) t (dualRep D M) y).comp c := by
    funext y
    ext x
    exact dualityMap_two_eq M x y
  rw [hfun]
  exact hpre.comp h0

include H in

theorem bijective_dualityMap (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 2) :
    Function.Bijective (dualityMap D h t M) := by
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (r = 0 ∧ s = 2) ∨ (r = 1 ∧ s = 1) ∨ (r = 2 ∧ s = 0) := by omega
  · exact H.bijective_zero M hM
  · exact H.bijective_one M hM
  · exact H.bijective_two M hM

end GroupDualityHypotheses

end Two

end Langlands.ProfiniteCohomology

namespace Langlands.ProfiniteCohomology

open CategoryTheory

universe u

section FixedVector

variable {W : Type u} [Group W]

/-- A group acting on a nonzero finite module killed by `2` through elements of `2`-power order fixes
a nonzero vector. -/
theorem exists_ne_zero_forall_ρ_eq (N : Rep.{u} (ULift.{u} ℤ) W) [Finite N] [Nontrivial N]
    (h2 : ∀ m : N, 2 • m = 0) (hN : ∀ w : W, ∃ k : ℕ, N.ρ (w ^ 2 ^ k) = 1) :
    ∃ m : N, m ≠ 0 ∧ ∀ w : W, N.ρ w m = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup (N →ₗ[ULift.{u} ℤ] N)ˣ := N.ρ.asGroupHom.range
  have hR : IsPGroup 2 R := by
    rintro ⟨x, w, rfl⟩
    obtain ⟨k, hk⟩ := hN w
    refine ⟨k, Subtype.ext (Units.ext ?_)⟩
    change ((N.ρ.asGroupHom w ^ 2 ^ k : (N →ₗ[ULift.{u} ℤ] N)ˣ) : N →ₗ[ULift.{u} ℤ] N) = 1
    rw [← map_pow, Representation.asGroupHom_apply, hk]
  have hcard := hR.card_modEq_card_fixedPoints N
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : N)
  have hord : addOrderOf m₀ = 2 := addOrderOf_eq_prime (h2 m₀) hm₀
  have h2N : 2 ∣ Nat.card N := hord ▸ addOrderOf_dvd_natCard m₀
  have h2F : 2 ∣ Nat.card (MulAction.fixedPoints R N) := (hcard.dvd_iff (dvd_refl 2)).1 h2N
  have h0 : (0 : N) ∈ MulAction.fixedPoints R N := fun r => smul_zero r
  have hF : Finite (MulAction.fixedPoints R N) := Subtype.finite
  have hlt : 1 < Nat.card (MulAction.fixedPoints R N) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints R N) :=
      Nat.card_pos_iff.2 ⟨⟨⟨0, h0⟩⟩, hF⟩
    obtain ⟨c, hc⟩ := h2F
    omega
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := Finite.one_lt_card_iff_nontrivial.1 hlt |>.exists_pair_ne
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_or, not_not] at h
    exact hab (Subtype.ext (h.1.trans h.2.symm))
  have key : ∀ c ∈ MulAction.fixedPoints R N, ∀ w : W, N.ρ w c = c := fun c hc w =>
    hc ⟨N.ρ.asGroupHom w, w, rfl⟩
  rcases hne with h | h
  · exact ⟨a, h, key a ha⟩
  · exact ⟨b, h, key b hb⟩

end FixedVector

section ZModTwo

variable {W : Type u} [Group W]

/-- The homomorphism `ℤ/2 → N` sending `1` to an element `m` with `2m = 0`. -/
def zmodTwoAddHom {N : Type*} [AddCommGroup N] (m : N) (hm : 2 • m = 0) : ZMod 2 →+ N :=
  ZMod.lift 2 ⟨zmultiplesHom N m, by
    change ((2 : ℕ) : ℤ) • m = 0
    rw [natCast_zsmul]
    exact hm⟩

theorem zmodTwoAddHom_intCast {N : Type*} [AddCommGroup N] (m : N) (hm : 2 • m = 0) (k : ℤ) :
    zmodTwoAddHom m hm (k : ZMod 2) = k • m :=
  ZMod.lift_coe _ _ k

theorem zmodTwoAddHom_one {N : Type*} [AddCommGroup N] (m : N) (hm : 2 • m = 0) :
    zmodTwoAddHom m hm 1 = m := by
  have h := zmodTwoAddHom_intCast m hm 1
  rwa [Int.cast_one, one_zsmul] at h

theorem zmodTwoAddHom_injective {N : Type*} [AddCommGroup N] {m : N} (hm : 2 • m = 0)
    (hm0 : m ≠ 0) : Function.Injective (zmodTwoAddHom m hm) :=
  (injective_iff_map_eq_zero _).2 fun a ha => by
    fin_cases a
    · rfl
    · exact absurd ((zmodTwoAddHom_one m hm).symm.trans ha) hm0

/-- The morphism `ℤ/2 → N` of `W`-modules sending `1` to a fixed vector `m` with `2m = 0`. -/
def zmodTwoHom (N : Rep.{u} (ULift.{u} ℤ) W) (m : N) (hm : 2 • m = 0)
    (hfix : ∀ w : W, N.ρ w m = m) : zmodRep.{u} W 2 ⟶ N :=
  Rep.ofHom ⟨(uliftIntLinearEquivAddHom (zmodRep.{u} W 2) N).symm
    ((zmodTwoAddHom m hm).comp (AddEquiv.ulift : ULift.{u} (ZMod 2) ≃+ ZMod 2).toAddMonoidHom),
    fun w => by
      refine LinearMap.ext fun a => ?_
      obtain ⟨a⟩ := a
      obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
      change zmodTwoAddHom m hm (k : ZMod 2) = N.ρ w (zmodTwoAddHom m hm (k : ZMod 2))
      rw [zmodTwoAddHom_intCast, map_zsmul, hfix]⟩

theorem zmodTwoHom_hom_apply (N : Rep.{u} (ULift.{u} ℤ) W) (m : N) (hm : 2 • m = 0)
    (hfix : ∀ w : W, N.ρ w m = m) (a : zmodRep.{u} W 2) :
    (zmodTwoHom N m hm hfix).hom a = zmodTwoAddHom m hm (ULift.down a) :=
  rfl

end ZModTwo

end Langlands.ProfiniteCohomology
