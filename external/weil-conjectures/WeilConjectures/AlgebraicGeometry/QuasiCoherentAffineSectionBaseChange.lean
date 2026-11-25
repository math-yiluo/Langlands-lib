/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine section base change for quasi-coherent modules

Source: Stacks Project, Constructions, Lemma 01LN, using Schemes Lemmas 01I9 and 01IA
(blueprint: lem-weil-pbc-quasi-coherent-affine-section-base-change).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- For affine opens `U ≤ V` of a scheme `X` and a quasi-coherent `F`, the canonical map
`F(V) ⊗[O(V)] O(U) → F(U)`, `m ⊗ r ↦ r • m|_U`, is a bijective linear map, linear also for
the action of `O(U)` on the second tensor factor (written, as in
lem-weil-pbc-module-pullback-affine-sections, by swapping to `O(U) ⊗[O(V)] F(V)`, acting on
the left factor and swapping back).
Source: Stacks Project, Constructions, Lemma 01LN, using Schemes Lemmas 01I9 and 01IA
(blueprint: lem-weil-pbc-quasi-coherent-affine-section-base-change).

Proof: (1) Take the canonical affine charts Spec R → X, Spec R' → X of U and V; the
restriction ρ : R' → R gives the open immersion j = Spec ρ with ι_V ∘ j = ι_U
(lem-weil-pbc-affine-open-spec-points, lem-weil-pbc-affine-open-inclusion-spec-map).
(2) The restriction of F to Spec R' is quasi-coherent, hence the tilde of M' = F(V) by the
affine tilde-Gamma counit ε (lem-weil-pbc-module-restriction-open-immersion-colimits,
lem-weil-pbc-affine-tilde-gamma-adjunction).
(3) Restricting further along j gives the restriction of F along ι_U, with sections F(U).
(4) Open-immersion pullback is restriction, and tilde commutes with pullback along Spec ρ
(lem-weil-pbc-open-immersion-module-pullback-restriction,
lem-weil-pbc-tilde-pullback-base-change); taking sections gives an R-linear isomorphism
Φ : R ⊗[R'] M' → F(U).
(5) Tracing m' through units and counits shows Φ(r ⊗ m') = r • m'|_U, so after swapping the
factors Φ is the canonical map, which is therefore bijective and R-linear. -/
theorem quasiCoherent_affine_section_baseChange
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U V : X.affineOpens) (hUV : U.1 ≤ V.1) :
    letI : Algebra Γ(X, V.1) Γ(X, U.1) :=
      (X.presheaf.map (homOfLE hUV).op).hom.toAlgebra
    letI : Module Γ(X, V.1) Γ(F, U.1) :=
      Module.compHom _ (X.presheaf.map (homOfLE hUV).op).hom
    ∃ c : (Γ(F, V.1) ⊗[Γ(X, V.1)] Γ(X, U.1)) →ₗ[Γ(X, V.1)] Γ(F, U.1),
      Function.Bijective c ∧
      (∀ (r : Γ(X, U.1)) (t : Γ(F, V.1) ⊗[Γ(X, V.1)] Γ(X, U.1)),
        c ((TensorProduct.comm Γ(X, V.1) Γ(F, V.1) Γ(X, U.1)).symm
          (r • TensorProduct.comm Γ(X, V.1) Γ(F, V.1) Γ(X, U.1) t)) = r • c t) ∧
      (∀ (m : Γ(F, V.1)) (r : Γ(X, U.1)),
        c (m ⊗ₜ[Γ(X, V.1)] r) = r • F.presheaf.map (homOfLE hUV).op m) := by
  classical
  dsimp only
  let : Algebra Γ(X, V.1) Γ(X, U.1) :=
    (X.presheaf.map (homOfLE hUV).op).hom.toAlgebra
  let : Module Γ(X, V.1) Γ(F, U.1) :=
    Module.compHom _ (X.presheaf.map (homOfLE hUV).op).hom
  let adj := Classical.choose (exists_tensorPullbackAdjunction (𝟙 X))
  let adj' := adj.ofNatIsoRight (pushforwardId X)
  let k : tensorPullback (𝟙 X) ≅ 𝟭 X.Modules := adj'.leftAdjointUniq Adjunction.id
  have hk (W : X.Opens) (s : Γ(F, W)) :
      (k.hom.app F).app W ((adj.unit.app F).val.app (.op W) s) = s := by
    have h := adj'.unit_leftAdjointUniq_hom_app Adjunction.id F
    have hv := congrArg (fun q ↦ q.val.app (.op W) s) h
    exact hv
  let : ∀ G : X.Modules, Module Γ(X, V.1) Γ((tensorPullback (𝟙 X)).obj G, U.1) :=
    fun G ↦ Module.compHom _ (Scheme.Hom.appLE (𝟙 X) V.1 U.1 hUV).hom
  obtain ⟨c, hc, hs, ht, _⟩ := exists_tensorPullback_affine_sections (𝟙 X) V U hUV
  let d : Γ((tensorPullback (𝟙 X)).obj F, U.1) →ₗ[Γ(X, V.1)] Γ(F, U.1) :=
    { toFun := (k.hom.app F).app U.1
      map_add' := map_add _
      map_smul' := by
        intro a s
        exact Hom.app_smul (k.hom.app F) _ _ }
  refine ⟨d.comp (c F inferInstance), ?_, ?_, ?_⟩
  · exact (ConcreteCategory.bijective_of_isIso ((k.hom.app F).app U.1)).comp
      (hc F inferInstance)
  · intro r t
    change d (c F inferInstance _) = r • d (c F inferInstance t)
    rw [hs]
    exact Hom.app_smul (k.hom.app F) r _
  · intro m r
    change d (c F inferInstance _) = _
    rw [ht]
    change (k.hom.app F).app U.1 (r • _) = _
    rw [Hom.app_smul]
    congr 1
    have hn := (k.hom.app F).val.naturality (homOfLE hUV).op
    have hv := congrArg (fun q ↦ q ((adj.unit.app F).val.app (.op V.1) m)) hn
    exact hv.trans (congrArg (fun z ↦ F.presheaf.map (homOfLE hUV).op z) (hk V.1 m))

end AlgebraicGeometry.Scheme.Modules
