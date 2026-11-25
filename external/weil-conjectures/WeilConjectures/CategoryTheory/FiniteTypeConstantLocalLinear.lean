/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective

/-! # Local linearity of maps between finite constant module sheaves

Source: Stacks Project, Modules on Sites, Tags 093T and 093U (3).
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (B : Type u) [CommRing B] [IsNoetherianRing B]

/-- A morphism between restricted constant module sheaves, with finite source, is locally
induced by a linear map over the original coefficient ring.
Source: Stacks Project, Modules on Sites, Tags 093T and 093U (3).
(auxiliary; not a blueprint node).

Proof: Over a Noetherian ring the finite source module is finitely presented. The two
constant-module sheafification constructions agree definitionally. Apply local
surjectivity of the constant local-Hom comparison to the given map on the slice.
Its image sieve covers the base object. On a member of this sieve, the resulting
linear map induces the restriction of the original map, by the local-Hom equivalence.
This also handles empty-cover members without a nondegeneracy assumption. -/
theorem exists_cover_constant_linearMap (M N : ModuleCat.{u} B) [Module.Finite B M] (U : C)
    (a : ((strictPerfectConstantSheaf J B).obj M).over U ⟶
      ((strictPerfectConstantSheaf J B).obj N).over U) :
    ∃ S ∈ J U, ∀ (V : C) (f : V ⟶ U), S f → ∃ g : M ⟶ N,
      (overFunctorMap _ f).inv.app ((strictPerfectConstantSheaf J B).obj M) ≫
        (overMap _ f).map a ≫
        (overFunctorMap _ f).hom.app ((strictPerfectConstantSheaf J B).obj N) =
          ((strictPerfectConstantSheaf J B).map g).over V := by
  let F := siteConstantModuleFunctor J B
  have : Module.FinitePresentation B M := Module.finitePresentation_of_finite B M
  have : Presheaf.IsLocallySurjective J (constantLocalHom F M N) :=
    siteConstantModuleHom_locallySurjective J B M N
  let x := (localHomEquiv (F.obj M) (F.obj N) (op U)).symm a
  refine ⟨Presheaf.imageSieve (constantLocalHom F M N) x,
    Presheaf.imageSieve_mem J (constantLocalHom F M N) x, ?_⟩
  intro V f hf
  obtain ⟨g, hg⟩ := hf
  refine ⟨g, ?_⟩
  have h := congrArg (localHomEquiv (F.obj M) (F.obj N) (op V)) hg
  rw [constantLocalHom_equiv] at h
  exact h.symm

end SheafOfModules
