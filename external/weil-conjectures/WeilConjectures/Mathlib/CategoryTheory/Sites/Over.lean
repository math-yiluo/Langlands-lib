/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Over

/-!
# Sheafification of a site from its localization at a terminal object

For a Grothendieck topology `J` on `C` and a terminal object `W : C`, the equivalence
`Over W ≌ C` given by `CategoryTheory.Over.equivalenceOfIsTerminal` identifies the
localized site `J.over W` with `J` itself. This file records:

- `CategoryTheory.isCocontinuous_equivalenceOfIsTerminal_inverse`: the canonical section
  `C ⥤ Over W` of `Over.forget W` is cocontinuous for the localized topology.
- `CategoryTheory.GrothendieckTopology.hasWeakSheafify_of_over_isTerminal`:
  sheafification for `J.over W` gives sheafification for `J`.
-/

@[expose] public section

universe v u'

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v} A] {W : C}

/-- The canonical section `C ⥤ Over W` of `Over.forget W` for a terminal object `W` is
cocontinuous for the localized topology: under `Over.forget W` its pullback of a sieve
identifies with `CategoryTheory.Sieve.overEquiv`. -/
lemma isCocontinuous_equivalenceOfIsTerminal_inverse (hW : IsTerminal W) :
    (Over.equivalenceOfIsTerminal hW).inverse.IsCocontinuous J (J.over W) where
  cover_lift {U S} hS := by
    rw [GrothendieckTopology.mem_over_iff] at hS
    refine J.superset_covering (fun Z f hf ↦ ?_) hS
    rw [Sieve.overEquiv_iff] at hf
    have : (Over.equivalenceOfIsTerminal hW).inverse.map f =
        (Over.homMk (𝟙 Z) (hW.hom_ext _ _) :
          Over.mk (hW.from Z) ⟶ Over.mk (f ≫ hW.from U)) ≫
          (Over.homMk f : Over.mk (f ≫ hW.from U) ⟶ Over.mk (hW.from U)) := by
      ext
      exact (Category.id_comp f).symm
    change S ((Over.equivalenceOfIsTerminal hW).inverse.map f)
    rw [this]
    exact S.downward_closed hf _

/-- Sheafification for the localization of a site at a terminal object gives
sheafification for the site itself, along the equivalence `Over W ≌ C` given by
`CategoryTheory.Over.equivalenceOfIsTerminal`. Compare
`CategoryTheory.Equivalence.hasSheafify`, which assumes the strong `HasSheafify`. -/
lemma GrothendieckTopology.hasWeakSheafify_of_over_isTerminal (hW : IsTerminal W)
    [HasWeakSheafify (J.over W) A] : HasWeakSheafify J A := by
  let e : C ≌ Over W := (Over.equivalenceOfIsTerminal hW).symm
  have : e.functor.IsCocontinuous J (J.over W) :=
    isCocontinuous_equivalenceOfIsTerminal_inverse J hW
  have : e.inverse.IsCocontinuous (J.over W) J :=
    inferInstanceAs ((Over.forget W).IsCocontinuous (J.over W) J)
  have : e.inverse.IsDenseSubsite (J.over W) J :=
    Equivalence.isDenseSubsite_inverse_of_isCocontinuous J (J.over W) e
  exact ⟨_, ⟨((e.op.congrLeft.toAdjunction.comp (sheafificationAdjunction (J.over W) A)).comp
      (e.sheafCongr J (J.over W) A).symm.toAdjunction).ofNatIsoRight
    (NatIso.ofComponents (fun F ↦ Functor.isoWhiskerRight e.op.unitIso.symm F.obj))⟩⟩

end CategoryTheory
