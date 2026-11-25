/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel

/-!
# Pushforward along a closed immersion is fully faithful

Source: Stacks Project, Modules, Lemma 08KS (modules-lemma-i-star-equivalence),
quoted for schemes in Morphisms, Lemma 01QY
(blueprint: lem-weil-pbc-closed-immersion-pushforward-fully-faithful).
-/

@[expose] public section

universe w

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- For a closed immersion, pullback followed by pushforward has invertible counit,
and pushforward is fully faithful
(blueprint: lem-weil-pbc-closed-immersion-pushforward-fully-faithful).
Proof: compute the counit on stalks using the quotient description of a closed
immersion and the tensor pullback stalk formula; then apply the adjunction theorem
that an isomorphism counit makes the right adjoint fully faithful.
-/
theorem closedImmersion_pushforward_fullyFaithful
    {X Z : Scheme.{w}} (i : Z ⟶ X) [IsClosedImmersion i] :
    let e : Scheme.Modules.tensorPullback i ⊣ Scheme.Modules.pushforward i :=
      Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)
    (∀ (G : Z.Modules), IsIso (e.counit.app G)) ∧
      ∀ (G G' : Z.Modules),
        Function.Bijective (fun (φ : G ⟶ G') => (Scheme.Modules.pushforward i).map φ) := by
  dsimp
  let e : Scheme.Modules.tensorPullback i ⊣ Scheme.Modules.pushforward i :=
    Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)
  have hc : ∀ (G : Z.Modules), IsIso (e.counit.app G) := by
    intro G
    -- The unit is epi and the triangle identity supplies a retraction.
    have hη : Epi (e.unit.app ((Scheme.Modules.pushforward i).obj G)) :=
      (Scheme.Modules.closedImmersion_unit_kernel i _).1
    have hs : IsSplitMono (e.unit.app ((Scheme.Modules.pushforward i).obj G)) :=
      IsSplitMono.mk' ⟨(Scheme.Modules.pushforward i).map (e.counit.app G),
        e.right_triangle_components G⟩
    have hunit : IsIso (e.unit.app ((Scheme.Modules.pushforward i).obj G)) :=
      isIso_of_epi_of_isSplitMono _
    have hmap : IsIso ((Scheme.Modules.pushforward i).map (e.counit.app G)) := by
      rw [← IsIso.inv_eq_of_hom_inv_id (e.right_triangle_components G)]
      infer_instance
    -- Closed pushforward stalks identify its counit map with the original stalk map.
    let a := (SheafOfModules.toSheaf Z.ringCatSheaf).map (e.counit.app G)
    have hi (z : Z) : IsIso ((TopCat.Presheaf.stalkFunctor Ab z).map a.hom) := by
      have hcG := (closedImmersion_pushforward_stalks i i.isClosedEmbedding G).2.1 z |>.2.1
      let P := ((Scheme.Modules.tensorPullback i).obj
        ((Scheme.Modules.pushforward i).obj G))
      have hcP := (closedImmersion_pushforward_stalks i i.isClosedEmbedding P).2.1 z |>.2.1
      have hn := (closedImmersion_pushforward_stalks i i.isClosedEmbedding P).2.2
        G (e.counit.app G) z
      have hh : IsIso ((TopCat.Presheaf.stalkFunctor Ab (i.base z)).map
          ((Scheme.Modules.pushforward i).map (e.counit.app G)).mapPresheaf) :=
        (TopCat.Presheaf.stalkFunctor Ab (i.base z)).map_isIso
          ((Scheme.Modules.toPresheaf X).map
            ((Scheme.Modules.pushforward i).map (e.counit.app G)))
      have hccomp : IsIso (TopCat.Presheaf.stalkPushforward Ab i.base P.presheaf z ≫
          (TopCat.Presheaf.stalkFunctor Ab z).map (e.counit.app G).mapPresheaf) := by
        rw [← hn]
        infer_instance
      change IsIso ((TopCat.Presheaf.stalkFunctor Ab z).map
        (e.counit.app G).mapPresheaf)
      exact IsIso.of_isIso_comp_left
        (TopCat.Presheaf.stalkPushforward Ab i.base P.presheaf z) _
    let := hi
    have := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso a
    have : IsIso ((Scheme.Modules.toPresheaf Z).map (e.counit.app G)) :=
      (TopCat.Sheaf.forget Ab Z.toTopCat).map_isIso a
    exact isIso_of_reflects_iso (e.counit.app G) (Scheme.Modules.toPresheaf Z)
  have : IsIso e.counit := NatIso.isIso_of_isIso_app _
  let ff := e.fullyFaithfulROfIsIsoCounit
  refine ⟨hc, ?_⟩
  intro G G'
  let : (Scheme.Modules.pushforward i).Full := ff.full
  let : (Scheme.Modules.pushforward i).Faithful := ff.faithful
  exact ⟨Functor.Faithful.map_injective, Functor.Full.map_surjective⟩

end AlgebraicGeometry
