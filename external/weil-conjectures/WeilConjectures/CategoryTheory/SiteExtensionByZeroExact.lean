/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheafAdjoint
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Exactness of extension by zero on a localized site

Source: literature/stacks-project/sites-modules.tex, Modules on Sites, Lemma 03DJ
(blueprint: lem-weil-pbc-site-extension-by-zero-exact)

This statement asserts preservation of short exact sequences by the constructed left
adjoint to restriction recorded by the restriction-adjunction dependency.
The proof follows the direct-sum
presheaf construction of 03DH--03DJ, sectionwise injectivity, exact sheafification,
and right exactness from the adjunction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Componentwise injectivity implies injectivity of the direct-sum map (Stacks 03DJ). -/
private theorem presheaf_preserves_monomorphisms
    {C : Type u} [SmallCategory C] (W : C) :
    (siteExtensionByZeroPresheaf.{u, u, u} W).PreservesMonomorphisms where
  preserves {X Y} α hα := by
    classical
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro V
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    change Function.Injective (siteExtensionByZeroHomApp W α V).hom
    have hmap : (siteExtensionByZeroHomApp W α V).hom =
        DirectSum.map (fun φ : V.unop ⟶ W =>
          (α.app (Opposite.op (Over.mk φ))).hom) := by
      apply DirectSum.addHom_ext
      intro φ x
      dsimp [siteExtensionByZeroHomApp, siteExtensionByZeroSection]
      simp only [DirectSum.toAddMonoid_of, DirectSum.map_of, AddMonoidHom.comp_apply]
    rw [hmap]
    apply (DirectSum.map_injective _).mpr
    intro φ
    exact (AddCommGrpCat.mono_iff_injective _).mp (inferInstance)

/-- Sectionwise injectivity survives direct sums and sheafification. The explicit functor
and the chosen sheaf pullback are isomorphic by uniqueness of left adjoints (Stacks 03DI). -/
private theorem siteExtensionByZero_preserves_monomorphisms
    {C : Type u} [SmallCategory C]
    (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (W : C) :
    (Functor.sheafPullbackConstruction.sheafPullback
      (Over.forget W) AddCommGrpCat.{u} (J.toGrothendieck.over W)
      J.toGrothendieck).PreservesMonomorphisms := by
  have : (siteExtensionByZeroPresheaf.{u, u, u} W).PreservesMonomorphisms :=
    presheaf_preserves_monomorphisms W
  have : (sheafToPresheaf (J.toGrothendieck.over W)
      AddCommGrpCat.{u}).PreservesMonomorphisms := inferInstance
  have : (presheafToSheaf J.toGrothendieck
      AddCommGrpCat.{u}).PreservesMonomorphisms := inferInstance
  have : (siteExtensionByZeroSheaf J W).PreservesMonomorphisms := by
    unfold siteExtensionByZeroSheaf
    infer_instance
  obtain ⟨adj, _⟩ := siteExtensionByZeroPresheaf_adjunction J W
  exact Functor.PreservesMonomorphisms.of_iso (adj.leftAdjointUniq
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Over.forget W) AddCommGrpCat.{u} (J.toGrothendieck.over W) J.toGrothendieck))

/-- Extension by zero from the localized site is exact.

Source: literature/stacks-project/sites-modules.tex, Modules on Sites, Lemma 03DJ
(blueprint: lem-weil-pbc-site-extension-by-zero-exact).

The site is the precoverage encoding of `def-weil-pbc-sites-and-cohomology`.
Extension by zero is the constructed left adjoint recorded by
`lem-weil-pbc-site-restriction-adjunction`. The zero-morphism witness permits mapping
short complexes; it is a conclusion, not an additional hypothesis.

Proof:
1. Rewrite the component map of the explicit presheaf construction as `DirectSum.map`.
   Evaluation sends a monomorphism of presheaves to an injective homomorphism, so
   `DirectSum.map_injective` proves that presheaf extension by zero preserves monos.
2. The sheaf inclusion and sheafification preserve finite limits, hence monos.
   Thus the sheafified direct-sum functor preserves monos as well.
3. The existing presheaf adjunction and `sheafAdjunctionContinuous` identify the
   explicit functor and the chosen pullback by uniqueness of left adjoints. Transfer
   preservation of monos along this natural isomorphism.
4. Restriction is additive by its sectionwise formula. Its left adjoint is additive,
   so it preserves zero morphisms. The adjunction also gives preservation of colimits.
5. The final map of a short exact sequence is a cokernel of the first. Map its
   cokernel cofork using colimit preservation; the mapped complex is exact and its
   final map is epic. Its first map is monic by Steps 1--3. These three properties
   give the required short exact sequence.
-/
theorem site_extensionByZero_exact
    {C : Type u} [SmallCategory C]
    (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (W : C) :
    ∃ (hL : (Functor.sheafPullbackConstruction.sheafPullback
      (Over.forget W) AddCommGrpCat.{u} (J.toGrothendieck.over W)
      J.toGrothendieck).PreservesZeroMorphisms),
      ∀ (S : ShortComplex (Sheaf (J.toGrothendieck.over W) AddCommGrpCat.{u})),
        S.ShortExact →
          (@ShortComplex.map _ _ _ _ _ _ S
            (Functor.sheafPullbackConstruction.sheafPullback
              (Over.forget W) AddCommGrpCat.{u} (J.toGrothendieck.over W)
              J.toGrothendieck) hL).ShortExact := by
  let F := Functor.sheafPullbackConstruction.sheafPullback
    (Over.forget W) AddCommGrpCat.{u} (J.toGrothendieck.over W)
    J.toGrothendieck
  have : ((Over.forget W).sheafPushforwardContinuous AddCommGrpCat.{u}
      (J.toGrothendieck.over W) J.toGrothendieck).Additive := ⟨by
    intro X Y f g
    ext V
    rfl⟩
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Over.forget W) AddCommGrpCat.{u} (J.toGrothendieck.over W) J.toGrothendieck
  have : F.Additive := adj.left_adjoint_additive
  have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
  have : F.PreservesMonomorphisms := siteExtensionByZero_preserves_monomorphisms J W
  have : PreservesFiniteColimits F := inferInstance
  refine ⟨inferInstance, ?_⟩
  intro S hS
  have : Mono S.f := hS.mono_f
  have hright : (S.map F).Exact ∧ Epi (S.map F).g :=
    (S.map F).exact_and_epi_g_iff_g_is_cokernel.mpr
      ⟨CokernelCofork.mapIsColimit _ hS.gIsCokernel F⟩
  have : Mono (S.map F).f := F.map_mono S.f
  have : Epi (S.map F).g := hright.2
  exact ⟨hright.1⟩

end CategoryTheory
