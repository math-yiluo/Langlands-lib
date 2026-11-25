/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafStalkComparison
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorQuotientKernel
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Stalk generators of an exterior tensor quotient kernel
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem tuple_germs {X : Scheme.{v}} (M : X.Modules) (n : ℕ) (x : X)
    (a : Fin n → M.presheaf.stalk x) (U : X.Opens) (hxU : x ∈ U) :
    ∃ (V : X.Opens) (_hVU : V ≤ U) (hxV : x ∈ V) (b : Fin n → M.val.obj (op V)),
      ∀ i, M.presheaf.germ V x hxV (b i) = a i := by
  induction n generalizing U with
  | zero => exact ⟨U, le_rfl, hxU, Fin.elim0, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨V, hVU, hxV, b, hb⟩ := M.presheaf.exists_le_germ_eq (a 0) hxU
    obtain ⟨W, hWV, hxW, c, hc⟩ := ih (fun i ↦ a i.succ) V hxV
    refine ⟨W, hWV.trans hVU, hxW,
      Fin.cons (M.presheaf.map (homOfLE hWV).op b) c, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact (M.presheaf.germ_res_apply (homOfLE hWV) x hxW b).trans hb
    · exact hc j

set_option backward.isDefEq.respectTransparency false in
private theorem shortExact_stalk {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (x : X) :
    LinearMap.range (S.f.stalkLinearMap x) = LinearMap.ker (S.g.stalkLinearMap x) ∧
      Function.Surjective (S.g.stalkLinearMap x) := by
  let T := SheafOfModules.toSheaf X.ringCatSheaf
  let F := TopCat.Sheaf.forget Ab.{v} X.toTopCat ⋙ TopCat.Presheaf.stalkFunctor Ab.{v} x
  have : CategoryTheory.Limits.PreservesFiniteLimits T :=
    (CategoryTheory.moduleSheaves_colimits_forgetful X.ringCatSheaf).2.1
  have : CategoryTheory.Limits.PreservesFiniteColimits T :=
    (CategoryTheory.moduleSheaves_colimits_forgetful X.ringCatSheaf).2.2.1
  have : F.Additive := inferInstanceAs
    (TopCat.Sheaf.forget Ab.{v} X.toTopCat ⋙
      TopCat.Presheaf.stalkFunctor Ab.{v} x).Additive
  have : CategoryTheory.Limits.PreservesFiniteLimits F := inferInstanceAs
    (CategoryTheory.Limits.PreservesFiniteLimits
      (TopCat.Sheaf.forget Ab.{v} X.toTopCat ⋙ TopCat.Presheaf.stalkFunctor Ab.{v} x))
  have : CategoryTheory.Limits.PreservesFiniteColimits F := inferInstanceAs
    (CategoryTheory.Limits.PreservesFiniteColimits
      (TopCat.Sheaf.forget Ab.{v} X.toTopCat ⋙ TopCat.Presheaf.stalkFunctor Ab.{v} x))
  have H := (hS.map_of_exact T).map_of_exact F
  have he := H.exact
  have hg := H.ab_surjective_g
  constructor
  · apply le_antisymm
    · rintro _ ⟨d, rfl⟩
      exact ((S.map T).map F).ab_zero_apply d
    · intro b hb
      obtain ⟨d, hd⟩ := ((S.map T).map F).ab_exact_iff.mp he b hb
      exact ⟨d, hd⟩
  · exact hg

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_exterior_stalk {X : Scheme.{v}} (A B : X.Modules)
    (r s : ℕ) (x : X) :
    ∃ e : (exteriorPower A r ⊗ exteriorPower B s).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
        TensorProduct (X.presheaf.stalk x)
          (⋀[X.presheaf.stalk x]^r (A.presheaf.stalk x))
          (⋀[X.presheaf.stalk x]^s (B.presheaf.stalk x)),
      ∀ (U : X.Opens) (hx : x ∈ U) (a : Fin r → A.val.obj (op U))
        (b : Fin s → B.val.obj (op U)),
        e ((exteriorPower A r ⊗ exteriorPower B s).presheaf.germ U x hx
          (tmulSection (wedge (M := A) (r := r) (U := U) a) (wedge (M := B) (r := s) (U := U) b))) =
        exteriorPower.ιMulti (X.presheaf.stalk x) r
          (fun i ↦ A.presheaf.germ U x hx (a i)) ⊗ₜ[X.presheaf.stalk x]
        exteriorPower.ιMulti (X.presheaf.stalk x) s
          (fun i ↦ B.presheaf.germ U x hx (b i)) := by
  obtain ⟨eA, hA⟩ := exteriorSheaf_stalk_comparison A r x
  obtain ⟨eB, hB⟩ := exteriorSheaf_stalk_comparison B s x
  obtain ⟨Φ, hΦ, _⟩ := SheafOfModules.stalkTensorIso X.toRingedSpace x
  let e := (Φ (exteriorPower A r) (exteriorPower B s)).toLinearEquiv.trans
    (TensorProduct.congr eA eB)
  refine ⟨e, ?_⟩
  intro U hx a b
  change TensorProduct.congr eA eB
    ((Φ (exteriorPower A r) (exteriorPower B s)).hom
      ((exteriorPower A r ⊗ exteriorPower B s).presheaf.germ U x hx _)) = _
  have h := hΦ (exteriorPower A r) (exteriorPower B s) U hx
    (wedge (M := A) (r := r) (U := U) a) (wedge (M := B) (r := s) (U := U) b)
  change (Φ (exteriorPower A r) (exteriorPower B s)).hom
    ((exteriorPower A r ⊗ exteriorPower B s).presheaf.germ U x hx
      (tmulSection (wedge (M := A) (r := r) (U := U) a)
        (wedge (M := B) (r := s) (U := U) b))) = _ at h
  rw [h]
  simp only [TensorProduct.congr_tmul]
  exact congrArg₂ (TensorProduct.tmul (X.presheaf.stalk x)) (hA U hx a) (hB U hx b)

/-- The sectionwise span of the relations added by quotienting the second factor. -/
noncomputable def exteriorTensorRelationSpan {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (A : X.Modules) (r s : ℕ) (V : X.Opens) :
    Submodule (X.presheaf.obj (op V))
      ((exteriorPower A r ⊗ exteriorPower S.X₂ s).val.obj (op V)) :=
  Submodule.span (X.presheaf.obj (op V))
    {z | ∃ (a : Fin r → A.val.obj (op V))
      (c : Fin s → S.X₂.val.obj (op V)) (j : Fin s)
      (d : S.X₁.val.obj (op V)), c j = S.f.val.app (op V) d ∧
        z = tmulSection (M := exteriorPower A r) (N := exteriorPower S.X₂ s)
          (wedge (M := A) (r := r) (U := V) a) (wedge (M := S.X₂) (r := s) (U := V) c)}

/-- The stalk submodule generated by germs of local quotient relations. -/
noncomputable def exteriorTensorRelationStalkSpan {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (A : X.Modules) (r s : ℕ) (x : X) :
    Submodule (X.presheaf.stalk x)
      ((exteriorPower A r ⊗ exteriorPower S.X₂ s).presheaf.stalk x) :=
  Submodule.span (X.presheaf.stalk x)
    {z | ∃ (V : X.Opens) (hxV : x ∈ V)
      (t : (exteriorPower A r ⊗ exteriorPower S.X₂ s).val.obj (op V)),
      t ∈ exteriorTensorRelationSpan S A r s V ∧
        (exteriorPower A r ⊗ exteriorPower S.X₂ s).presheaf.germ V x hxV t = z}

-- Transporting the tensor and exterior comparisons requires extra elaboration fuel.
set_option backward.isDefEq.respectTransparency false in
/-- The stalk kernel of the exterior tensor quotient is generated by local relations. -/
theorem exteriorTensor_stalk_kernel_le_relationSpan {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (A : X.Modules) (r s : ℕ) (hs : s ≠ 0)
    (q : exteriorPower A r ⊗ exteriorPower S.X₂ s ⟶
      exteriorPower A r ⊗ exteriorPower S.X₃ s)
    (hq : ∀ (U : X.Opens) (a : Fin r → A.val.obj (op U))
      (c : Fin s → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := S.X₂) (r := s) (U := U) c)) =
        tmulSection (M := exteriorPower A r) (N := exteriorPower S.X₃ s)
          (wedge (M := A) (r := r) (U := U) a)
          (wedge (M := S.X₃) (r := s) (U := U) (fun i ↦ S.g.val.app (op U) (c i))))
    (x : X) :
    LinearMap.ker (q.stalkLinearMap x) ≤ exteriorTensorRelationStalkSpan S A r s x := by
  classical
  have _hs : s ≠ 0 := hs
  obtain ⟨eB, heB⟩ := tensor_exterior_stalk A S.X₂ r s x
  obtain ⟨eC, heC⟩ := tensor_exterior_stalk A S.X₃ r s x
  let L := TensorProduct.map
    (LinearMap.id : (⋀[X.presheaf.stalk x]^r (A.presheaf.stalk x)) →ₗ[X.presheaf.stalk x]
      (⋀[X.presheaf.stalk x]^r (A.presheaf.stalk x)))
    (exteriorPower.map s (S.g.stalkLinearMap x))
  have hcomm : eC.toLinearMap ∘ₗ q.stalkLinearMap x ∘ₗ eB.symm.toLinearMap = L := by
    apply TensorProduct.ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro c
    obtain ⟨U, _, hxU, aU, haU⟩ := tuple_germs A r x a ⊤ (by simp)
    obtain ⟨V, hVU, hxV, cV, hcV⟩ := tuple_germs S.X₂ s x c U hxU
    let aV := fun i ↦ A.presheaf.map (homOfLE hVU).op (aU i)
    have haV : (fun i ↦ A.presheaf.germ V x hxV (aV i)) = a := by
      funext i
      exact (A.presheaf.germ_res_apply (homOfLE hVU) x hxV (aU i)).trans (haU i)
    have hc : (fun i ↦ S.X₂.presheaf.germ V x hxV (cV i)) = c := funext hcV
    have hb := heB V hxV aV cV
    rw [haV, hc] at hb
    have hb' := eB.symm_apply_eq.mpr hb.symm
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.compr₂ₛₗ_apply,
      TensorProduct.mk_apply, LinearMap.comp_apply]
    change eC (q.stalkLinearMap x (eB.symm
      (exteriorPower.ιMulti (X.presheaf.stalk x) r a ⊗ₜ[X.presheaf.stalk x]
        exteriorPower.ιMulti (X.presheaf.stalk x) s c))) = L _
    rw [hb', Hom.stalkLinearMap_germ]
    change eC ((exteriorPower A r ⊗ exteriorPower S.X₃ s).presheaf.germ V x hxV
      (q.val.app (op V) _)) = _
    rw [hq V aV cV, heC V hxV]
    simp only [L, TensorProduct.map_tmul, LinearMap.id_apply, exteriorPower.map_apply_ιMulti]
    rw [haV]
    congr 2
    funext i
    exact (S.g.stalkLinearMap_germ x hxV (cV i)).symm.trans
      (congrArg (S.g.stalkLinearMap x) (hcV i))
  obtain ⟨hfg, hg⟩ := shortExact_stalk S hS x
  have hker := exteriorPower.tensor_quotient_kernel_le_span
    (A := A.presheaf.stalk x) (S.f.stalkLinearMap x) (S.g.stalkLinearMap x) hfg hg r s
  intro m hm
  have hLm : eB m ∈ LinearMap.ker L := by
    rw [← hcomm]
    change eC (q.stalkLinearMap x (eB.symm (eB m))) = 0
    rw [eB.symm_apply_apply, hm, map_zero]
  have hspan := hker hLm
  have hgen : ∀ z, z ∈ Submodule.span (X.presheaf.stalk x)
      {z | ∃ (a : Fin r → A.presheaf.stalk x) (c : Fin s → S.X₂.presheaf.stalk x)
        (j : Fin s) (d : S.X₁.presheaf.stalk x), c j = S.f.stalkLinearMap x d ∧
        z = exteriorPower.ιMulti (X.presheaf.stalk x) r a ⊗ₜ[X.presheaf.stalk x]
          exteriorPower.ιMulti (X.presheaf.stalk x) s c} →
      eB.symm z ∈ exteriorTensorRelationStalkSpan S A r s x := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, c, j, d, hj, rfl⟩ := hz
      obtain ⟨U, hxU, dU, hdU⟩ := S.X₁.presheaf.exists_germ_eq d
      obtain ⟨V, hVU, hxV, aV, haV⟩ := tuple_germs A r x a U hxU
      obtain ⟨W, hWV, hxW, cW, hcW⟩ := tuple_germs S.X₂ s x c V hxV
      let dW := S.X₁.presheaf.map (homOfLE (hWV.trans hVU)).op dU
      have hdW : S.X₁.presheaf.germ W x hxW dW = d :=
        (S.X₁.presheaf.germ_res_apply (homOfLE (hWV.trans hVU)) x hxW dU).trans hdU
      let aW := fun i ↦ A.presheaf.map (homOfLE hWV).op (aV i)
      have haW : (fun i ↦ A.presheaf.germ W x hxW (aW i)) = a := by
        funext i
        exact (A.presheaf.germ_res_apply (homOfLE hWV) x hxW (aV i)).trans (haV i)
      let cW' := Function.update cW j (S.f.val.app (op W) dW)
      have hcW' : (fun i ↦ S.X₂.presheaf.germ W x hxW (cW' i)) = c := by
        funext i
        by_cases hi : i = j
        · subst i
          simp only [cW', Function.update_self]
          exact (S.f.stalkLinearMap_germ x hxW dW).symm.trans
            ((congrArg (S.f.stalkLinearMap x) hdW).trans hj.symm)
        · simpa only [cW', Function.update_of_ne hi] using hcW i
      let t := tmulSection (M := exteriorPower A r) (N := exteriorPower S.X₂ s)
        (wedge (M := A) (r := r) (U := W) aW)
        (wedge (M := S.X₂) (r := s) (U := W) cW')
      have ht : t ∈ exteriorTensorRelationSpan S A r s W := by
        apply Submodule.subset_span
        exact ⟨aW, cW', j, dW, Function.update_self _ _ _, rfl⟩
      apply Submodule.subset_span
      refine ⟨W, hxW, t, ht, ?_⟩
      apply eB.injective
      rw [eB.apply_symm_apply]
      exact (heB W hxW aW cW').trans
        (congrArg₂ (fun a c ↦ exteriorPower.ιMulti (X.presheaf.stalk x) r a ⊗ₜ
          exteriorPower.ιMulti (X.presheaf.stalk x) s c) haW hcW')
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [LinearEquiv.map_smul]; exact Submodule.smul_mem _ c ha
  simpa only [eB.symm_apply_apply] using hgen (eB m) hspan

end AlgebraicGeometry.Scheme.Modules
