/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.AlgebraicGeometry.FormalCompletionPushforwardLimitIso
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleLimitFull
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleLimitProjectionEpi
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Lifting compatible maps through the formal-functions comparison

Source: Stacks Project, Lemma 088B, construction of alpha from the inverse limit of gamma.
(blueprint: lem-weil-pbc-formal-completion-pushforward-lift)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Any compatible map from a coherent adic system lifts through the canonical completed
proper pushforward comparison.

Source: Stacks Project, Lemma 088B, first half of the proof, paragraphs constructing
alpha from the inverse limit of gamma; https://stacks.math.columbia.edu/tag/088B.
(blueprint: lem-weil-pbc-formal-completion-pushforward-lift)

Proof: The canonical comparison induces an isomorphism on inverse-limit sheaves:
on an affine basis this is the degree-zero theorem on formal functions, using the
ideal-product and quotient section formulas. Compose lim gamma with its inverse
to obtain beta: lim G -> lim H-completion. Reconstruction of coherent formal-system
maps from maps of limit sheaves descends beta to alpha. The defining equation of
alpha on limits and the inverse identities give lim(alpha kappa) = lim gamma.
Compose this equality with each target limit projection. Naturality of the limit
cones rewrites it as pi_G,n alpha_n kappa_n = pi_G,n gamma_n. The projections of
a coherent formal system's limit sheaf are epic: its transitions are surjective
on affine sections, and sequential limits of surjective module towers have
surjective projections. Cancel pi_G,n and apply natural-transformation
extensionality. Thus alpha kappa = gamma. The reconstruction lemma contains the
affine quotient descent and gluing; the comparison-isomorphism lemma contains
formal functions. No isomorphism hypothesis on gamma is used. Zero and unit ideals,
zero sheaves and the empty scheme satisfy the same construction.
-/
theorem formalCompletion_pushforward_lift {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) = (Scheme.Modules.pushforward f).map
          (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (γ : G.obj ⟶ formalCompletionSystem (J.comap f) F.obj ⋙
      Scheme.Modules.pushforward f) :
    ∃ α : G ⟶ (completion Y J).obj
        ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩,
      α.hom ≫ κ = γ := by
  have : IsIso (lim.map κ) := formalCompletion_pushforward_limit_isIso J f F h κ hκ
  let H : CoherentFormalModule Y J :=
    (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩
  let β : limit G.obj ⟶ limit H.obj := lim.map γ ≫ inv (lim.map κ)
  obtain ⟨α, hα⟩ := coherentFormalModule_limit_full J G H β
  refine ⟨α, ?_⟩
  have heq : lim.map (α.hom ≫ κ) = lim.map γ := by
    rw [Functor.map_comp, hα]
    simp [β]
  apply NatTrans.ext
  funext j
  obtain ⟨n⟩ := j
  have : Epi (limit.π G.obj (op n)) :=
    coherentFormalModule_limit_projection_epi J G n
  apply (cancel_epi (limit.π G.obj (op n))).1
  simpa only [lim_map, limMap_π] using
    congrArg (fun b ↦ b ≫ limit.π _ (op n)) heq

end AlgebraicGeometry
