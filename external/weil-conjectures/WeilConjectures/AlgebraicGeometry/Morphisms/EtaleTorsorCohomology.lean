/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorH1Functoriality

/-!
# Naturality of the torsor attached to an étale `H¹`-class

Let `M` be a finite abelian group and `Y` a scheme. Every class `ξ ∈ H¹(Y_ét, M)` of the
constant sheaf `M` is the class of an `M`-torsor `t` over `Y`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_quotientEquivSheafH`), and the classification
is natural in `Y`: the pullback of `ξ` along a morphism `f : Y' ⟶ Y` is the class of the
pulled-back torsor `t ×_Y Y'`. Since a torsor has class zero exactly when it has a section,
the pullback of `ξ` along `f` vanishes exactly when `f` lifts to the total space of `t`.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_forall_cohomologyMap_eq_zero_iff`: a class of
  `H¹(Y_ét, M)` is represented by an `M`-torsor `t`, in the sense that it dies after pullback
  along `f` exactly when `f` lifts to `t`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleTorsor

variable (M : Type (u + 1)) [AddCommGroup M] [Finite M]

/-- Let `M` be a finite abelian group and `ξ ∈ H¹(Y_ét, M)` a class of the constant sheaf `M` on a
scheme `Y`. Then there is an `M`-torsor `t` over `Y` representing `ξ` naturally: for every
morphism `f: Y' ⟶ Y`, the pullback of `ξ` along `f` vanishes exactly when `f` lifts to the
total space of `t`, that is, exactly when the pulled-back torsor `t ×_Y Y'` is trivial. -/
@[stacks 02NE]
theorem exists_forall_cohomologyMap_eq_zero_iff {Y : Scheme.{u}}
    (ξ : Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1) :
    ∃ t : EtaleTorsor M Y, ∀ ⦃Y' : Scheme.{u}⦄ (f : Y' ⟶ Y),
      Etale.cohomologyMap f _ 1 ξ = 0 ↔ ∃ s : Y' ⟶ t.P, s ≫ t.π = f := by
  obtain ⟨q, hq⟩ := (bijective_classH1 (M := M) (Y := Y)).2 ξ
  induction q using Quotient.inductionOn with | h t => ?_
  refine ⟨t, fun {Y'} f ↦ ?_⟩
  obtain ⟨T', eT, _, hclass⟩ :=
    Sheaf.Torsor.etale_torsor_h1_functoriality.1 Y Y' f _ t.toSheafTorsor
  rw [← hq, classH1_mk, hclass, Sheaf.Torsor.classH1_eq_zero_iff]
  let F := MorphismProperty.Over.pullback @Etale ⊤ f
  let e : (Scheme.etaleSetPullback f).obj t.toSheafTorsor.sheaf ≅
      Y'.smallEtaleTopology.uliftYoneda.{u + 1}.obj (F.obj t.toEtale) :=
    (presheafToSheaf Y'.smallEtaleTopology (Type (u + 1))).mapIso
      ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u + 1} F).app t.toEtale).symm ≪≫
    (sheafificationIso (Y'.smallEtaleTopology.uliftYoneda.{u + 1}.obj
      (F.obj t.toEtale))).symm
  have e' := ((sheafSections Y'.smallEtaleTopology (Type (u + 1))).obj
    (Opposite.op (⊤_ Y'.Etale))).mapIso (eT.symm ≪≫ e)
  let e₀ := terminalIsTerminal.uniqueUpToIso
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y')
  constructor
  · rintro ⟨x⟩
    let φ := e₀.inv ≫ (e'.hom x).down
    have hφ : φ.left ≫ pullback.snd t.π f = 𝟙 Y' :=
      MorphismProperty.Over.w φ
    exact ⟨φ.left ≫ pullback.fst t.π f, by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hφ, Category.id_comp]⟩
  · rintro ⟨s, hs⟩
    let ψ : Etale.mk (𝟙 Y') ⟶ F.obj t.toEtale :=
      MorphismProperty.Over.homMk
        (pullback.lift s (𝟙 Y') (by change s ≫ t.π = 𝟙 Y' ≫ f; rw [hs, Category.id_comp]))
        (pullback.lift_snd _ _ _)
    exact ⟨e'.inv ⟨e₀.hom ≫ ψ⟩⟩

end AlgebraicGeometry.Scheme.EtaleTorsor
