/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.LerayAcyclicAdditiveNaturality
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural

/-! # Linear Leray comparison for an acyclic direct image

Source: Stacks Project, Tag 01F4 (1), Lemma 20.13.6.
(blueprint: lem-pc-m1-leray-acyclic-pushforward-linear-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The degenerate Leray comparison respects scalars from any scheme below the target.

Source: Stacks Project, Tag 01F4 (1), Lemma 20.13.6, and the naturality of its
spectral sequence in coefficient-module maps (Tag 01EY).
(blueprint: lem-pc-m1-leray-acyclic-pushforward-linear-comparison)

Proof: use the Leray spectral sequence for p and F. The assumed vanishing removes all
rows except higher-direct-image degree zero; the edge gives an additive isomorphism
between the cohomology of p_*F and F. Compare module-derived global sections with
abelian-sheaf cohomology, using injective modules being flasque. For every section
r of T, multiplication by f.appTop r on p_*F is the pushforward of multiplication
by (p followed by f).appTop r on F. Naturality of the spectral sequence therefore
makes the additive isomorphism commute with scalar multiplication. Equip it with
this linearity to obtain the displayed linear equivalence. This uses no coherence,
Noetherian, properness, or affine-base assumption. -/
theorem nonempty_linearEquiv_H_pushforward_of_higherDirectImage_vanishing
    {Y X T : Scheme.{u}} (p : Y ⟶ X) (f : X ⟶ T)
    [HasInjectiveResolutions Y.Modules] (F : Y.Modules)
    (hF : ∀ q : ℕ, 0 < q → IsZero ((higherDirectImage p q).obj F)) (q : ℕ) :
    letI : Module Γ(T, ⊤) (((pushforward p).obj F).H q) :=
      Module.compHom _ f.appTop.hom
    letI : Module Γ(T, ⊤) (F.H q) :=
      Module.compHom _ (p ≫ f).appTop.hom
    Nonempty (((pushforward p).obj F).H q ≃ₗ[Γ(T, ⊤)] F.H q) := by
  let : Module Γ(T, ⊤) (((pushforward p).obj F).H q) :=
    Module.compHom _ f.appTop.hom
  let : Module Γ(T, ⊤) (F.H q) := Module.compHom _ (p ≫ f).appTop.hom
  obtain ⟨e, he⟩ :=
    exists_addEquiv_H_pushforward_natural_of_higherDirectImage_vanishing p F hF q
  refine ⟨{ toAddEquiv := e, map_smul' := ?_ }⟩
  intro r x
  change e (H.map (((pushforward p).obj F).smulHom (f.appTop r)) q x) =
    H.map (F.smulHom ((p ≫ f).appTop r)) q (e x)
  rw [← pushforward_map_smulHom]
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
    he (F.smulHom (p.appTop (f.appTop r))) x

end AlgebraicGeometry.Scheme.Modules
