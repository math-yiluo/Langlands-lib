/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.CoherentKernelConditionRestriction
import WeilConjectures.AlgebraicGeometry.CoherentKernelConditionDescent
import WeilConjectures.AlgebraicGeometry.CoherentModuleFiniteTypeLocalCore

/-! # Coherence of a module is local on an open covering

Source: Stacks Project, Modules, Definitions 01BV and 01B5; locality used in
Cohomology of Schemes, Lemma 0CYJ (blueprint: lemma-coherent-base-change-invertible-sheaves--1).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Coherence of a module is preserved by restriction to opens and is local on an open cover:
(1) if `F` is coherent then `F|_W` is a coherent `𝒪_W`-module for every open `W`; (2) if every
`F|_{U i}` is coherent and the `U i` cover `X`, then `F` is coherent. Restriction is Mathlib's
`Scheme.Modules.restrictFunctor` along the open immersion `W.ι`, coherence the project's
`RingedSpace.IsCoherent` (pqf-def-coherent).
Source: Stacks Project, Modules, Definitions 01BV and 01B5; the locality is used in
Cohomology of Schemes, Lemma 0CYJ (blueprint: lemma-coherent-base-change-invertible-sheaves--1).

Proof:
1. Restriction facts for opens `V ⊆ W ⊆ X`: `𝒪_X|_W = 𝒪_W` and `(G|_W)|_V = G|_V`
   (lem-weil-pbc-module-restriction-open-immersion-colimits); restriction is a left adjoint,
   so it preserves `𝒪^{⊕ n}` and epimorphisms; kernels are sectionwise, so restriction commutes
   with kernels (situation-conventions); finite type is invariant under isomorphism.
2. Finite type restricts: restrict a local surjection `𝒪_U^{⊕ n} → G|_U` to `U ∩ W`.
3. Part (1): `F|_W` is of finite type by 2; a map `𝒪_{W'}^{⊕ n} → (F|_W)|_{W'} = F|_{W'}`
   has kernel of finite type by the kernel condition for `F`, `W'` being open in `X`.
4. Finite type is local: a local surjection onto `G|_{W_i}` near `x` is one onto `G` near `x`.
5. Part (2): `F` is of finite type by 4. For `φ : 𝒪_W^{⊕ n} → F|_W` with kernel `K`, on
   `W_i = W ∩ U i` the restriction `K|_{W_i}` is the kernel of a map
   `𝒪_{W_i}^{⊕ n} → (F|_{U i})|_{W_i}`, of finite type by coherence of `F|_{U i}`; so `K` is of
   finite type by 4, and `F` is coherent (pqf-def-coherent).
-/
theorem coherent_module_local_on_open_cover
    (X : Scheme.{u}) (F : X.Modules) (I : Type u)
    (U : I → X.Opens)
    (hU : ⨆ i, U i = ⊤) :
    (RingedSpace.IsCoherent X.toRingedSpace F →
      ∀ (W : X.Opens),
        RingedSpace.IsCoherent W.toScheme.toRingedSpace
          ((Scheme.Modules.restrictFunctor W.ι).obj F)) ∧
      ((∀ (i : I),
          RingedSpace.IsCoherent (U i).toScheme.toRingedSpace
            ((Scheme.Modules.restrictFunctor (U i).ι).obj F)) →
        RingedSpace.IsCoherent X.toRingedSpace F) := by
  obtain ⟨hFT_restrict, hFT_cover⟩ :=
    coherent_module_finite_type_local_core X F I U hU
  constructor
  · intro hF W
    exact ⟨hFT_restrict hF W,
      coherent_kernel_condition_restriction X F hF.2 W⟩
  · intro hF
    exact ⟨hFT_cover hF,
      coherent_kernel_condition_descent X F I U hU (fun i ↦ (hF i).2)⟩

end AlgebraicGeometry
