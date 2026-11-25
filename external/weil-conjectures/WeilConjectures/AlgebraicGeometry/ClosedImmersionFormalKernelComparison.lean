/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Whiskering

import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalenceTermwise
import WeilConjectures.AlgebraicGeometry.FormalSystemsPullback

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Closed pushforward identifies the underlying inverse system of a categorical
formal kernel, without asserting that evaluation preserves kernels.

Source: Stacks Project, Tags 087T, 088A and 0887.
(blueprint: aux-closed-immersion-formal-kernel-comparison)

Proof: The termwise closed-pushforward equivalence gives a functor R into coherent
formal modules on X, with its specified underlying-system comparison. Termwise
pullback along j sends coherent formal modules on X to those on Z (Tag 0887).
Whisker the module pullback-pushforward adjunction with the inverse-system index,
then restrict it along the fully faithful formal-system inclusions. This makes R
a right adjoint, so it preserves limiting kernel forks. Lift e and d to the full
subcategory and use naturality of the underlying-system comparison to obtain a
commuting square between a and R.map alpha. The uniqueness isomorphism for the two
limiting kernel forks, followed by the underlying-system comparison at k.pt, gives
the required isomorphism. No evaluation functor is asserted to preserve kernels,
and no particular choice of Abelian structure is used beyond existence of kernel a. -/
theorem closedImmersion_formalKernel_comparison
    {X Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z]
    (j : Z ⟶ X) [IsClosedImmersion j] (Q : X.IdealSheafData)
    [Abelian (CoherentFormalModule X Q)]
    (M N : CoherentFormalModule X Q)
    (G D : CoherentFormalModule Z (Q.comap j))
    (a : M ⟶ N) (α : G ⟶ D)
    (e : M.obj ≅ G.obj ⋙ Scheme.Modules.pushforward j)
    (d : N.obj ≅ D.obj ⋙ Scheme.Modules.pushforward j)
    (hsquare : a.hom ≫ d.hom =
      e.hom ≫ Functor.whiskerRight α.hom (Scheme.Modules.pushforward j))
    (k : KernelFork α) (hk : IsLimit k) :
    Nonempty ((kernel a).obj ≅ k.pt.obj ⋙ Scheme.Modules.pushforward j) := by
  classical
  let U := ObjectProperty.ι (IsCoherentFormalModule Q)
  obtain ⟨E, ⟨θ⟩⟩ := closedImmersion_coherentFormal_equivalence_termwise j Q
  let R := E.functor ⋙ ObjectProperty.ι
    (fun F : CoherentFormalModule X Q ↦ SupportedOn Q F j)
  obtain ⟨P, _, hP, _, _⟩ := (exists_formalSystemsPullback j Q).1
  let adj := (Scheme.Modules.nonempty_tensorPullbackAdjunction j).some
  let formalAdj : P ⊣ R :=
    (adj.whiskerRight ℕᵒᵖ).restrictFullyFaithful
      (ObjectProperty.fullyFaithfulι (IsCoherentFormalModule Q))
      (ObjectProperty.fullyFaithfulι (IsCoherentFormalModule (Q.comap j)))
      (eqToIso hP.symm) θ.symm
  have : R.IsRightAdjoint := formalAdj.isRightAdjoint
  have : R.PreservesZeroMorphisms := inferInstance
  let e' : M ≅ R.obj G := ObjectProperty.isoMk _ (e ≪≫ (θ.app G).symm)
  let d' : N ≅ R.obj D := ObjectProperty.isoMk _ (d ≪≫ (θ.app D).symm)
  have hw : a ≫ d'.hom = e'.hom ≫ R.map α := by
    apply U.map_injective
    apply (cancel_mono (θ.hom.app D)).mp
    change a.hom ≫ (d.hom ≫ θ.inv.app D) ≫ θ.hom.app D =
      (e.hom ≫ θ.inv.app G) ≫ (R.map α).hom ≫ θ.hom.app D
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
      ObjectProperty.ι_obj, Functor.whiskeringRight, Category.comp_id]
    rw [show (R.map α).hom ≫ θ.hom.app D =
      θ.hom.app G ≫ Functor.whiskerRight α.hom (Scheme.Modules.pushforward j) from
        θ.hom.naturality α]
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Category.comp_id] using hsquare
  let q : kernel a ≅ R.obj k.pt := KernelFork.mapIsoOfIsLimit
    (kernelIsKernel a) (k.mapIsLimit hk R) (Arrow.isoMk e' d' hw.symm)
  exact ⟨U.mapIso q ≪≫ θ.app k.pt⟩

end AlgebraicGeometry
