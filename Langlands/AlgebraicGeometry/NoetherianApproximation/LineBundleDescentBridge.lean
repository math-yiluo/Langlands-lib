import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

/-! # Shared lemmas for the line bundle descent bridges

The ported FLT descent theorems for line bundles are stated for an arbitrary directed system of
rings with a direct limit, and for the FLT notion `Scheme.Modules.IsInvertible`. This module
supplies the system of finitely generated `A₀`-subalgebras of an `A₀`-algebra `A`, the comparison
between `IsInvertible` and the Library's `IsLocallyFreeRankOne`, and the formal lemmas on
pullbacks of modules that the bridges use.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

open Langlands.AlgebraicGeometry.Picard

/-- A module that is invertible in the sense of the FLT port is locally free of rank one. -/
theorem isLocallyFreeRankOne_of_isInvertible {X : Scheme.{u}} {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) : IsLocallyFreeRankOne M := fun x => by
  obtain ⟨U, hx, ⟨e⟩⟩ := hM.exists_trivialization x
  exact ⟨U, hx, ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e⟩⟩

/-- If the pullbacks of `M` and `N` along `b` are isomorphic, so are their pullbacks along any
morphism `a` that factors through `b`. -/
theorem nonempty_iso_pullback_of_fac {X Y Z : Scheme.{u}} {a : X ⟶ Z} {b : Y ⟶ Z} (c : X ⟶ Y)
    (hc : c ≫ b = a) {M N : Z.Modules}
    (h : Nonempty ((Scheme.Modules.pullback b).obj M ≅ (Scheme.Modules.pullback b).obj N)) :
    Nonempty ((Scheme.Modules.pullback a).obj M ≅ (Scheme.Modules.pullback a).obj N) := by
  obtain ⟨e⟩ := h
  subst hc
  exact ⟨((Scheme.Modules.pullbackComp c b).app M).symm ≪≫
    (Scheme.Modules.pullback c).mapIso e ≪≫ (Scheme.Modules.pullbackComp c b).app N⟩

/-- Iterated pullbacks are isomorphic exactly when the pullbacks along the composite are. -/
theorem nonempty_iso_pullback_pullback_iff {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M N : Z.Modules) :
    Nonempty ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅
        (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)) ↔
      Nonempty ((Scheme.Modules.pullback (f ≫ g)).obj M ≅
        (Scheme.Modules.pullback (f ≫ g)).obj N) :=
  ⟨fun ⟨e⟩ => ⟨((Scheme.Modules.pullbackComp f g).app M).symm ≪≫ e ≪≫
      (Scheme.Modules.pullbackComp f g).app N⟩,
    fun ⟨e⟩ => ⟨(Scheme.Modules.pullbackComp f g).app M ≪≫ e ≪≫
      ((Scheme.Modules.pullbackComp f g).app N).symm⟩⟩

/-- Let `e' : X ⟶ P` be a section of `e : P ⟶ X`. If the pullback of `L` along `e ≫ w` is
isomorphic to the pullback of `M` along `e`, then the pullback of `L` along `w` is isomorphic
to `M`. -/
theorem nonempty_iso_pullback_of_section {P X Q : Scheme.{u}} {e : P ⟶ X} {e' : X ⟶ P}
    (he : e' ≫ e = 𝟙 X) (w : X ⟶ Q) {L : Q.Modules} {M : X.Modules}
    (h : Nonempty ((Scheme.Modules.pullback (e ≫ w)).obj L ≅ (Scheme.Modules.pullback e).obj M)) :
    Nonempty ((Scheme.Modules.pullback w).obj L ≅ M) := by
  obtain ⟨i⟩ := h
  have hw : e' ≫ e ≫ w = w := by rw [← Category.assoc, he, Category.id_comp]
  exact ⟨((Scheme.Modules.pullbackCongr hw).app L).symm ≪≫
    ((Scheme.Modules.pullbackComp e' (e ≫ w)).app L).symm ≪≫
    (Scheme.Modules.pullback e').mapIso i ≪≫ (Scheme.Modules.pullbackComp e' e).app M ≪≫
    (Scheme.Modules.pullbackCongr he).app M ≪≫ (Scheme.Modules.pullbackId X).app M⟩

/-- The finitely generated `A₀`-subalgebras of `A`, ordered by inclusion. -/
abbrev FGIndex (A₀ A : Type u) [CommRing A₀] [CommRing A] [Algebra A₀ A] : Type u :=
  {T : Subalgebra A₀ A // T.FG}

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]

/-- The ring at an index: the subalgebra itself. -/
abbrev FGStage (T : FGIndex A₀ A) : Type u := ↥T.1

instance FGIndex.instNonempty : Nonempty (FGIndex A₀ A) :=
  ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

instance FGIndex.instIsDirected : IsDirected (FGIndex A₀ A) (· ≤ ·) :=
  ⟨fun S T => ⟨⟨S.1 ⊔ T.1, S.2.sup T.2⟩, (le_sup_left : S.1 ≤ S.1 ⊔ T.1),
    (le_sup_right : T.1 ≤ S.1 ⊔ T.1)⟩⟩

/-- The inclusion of a finitely generated subalgebra into a larger one. -/
def fgTransition (S T : FGIndex A₀ A) (h : S ≤ T) : FGStage S →+* FGStage T :=
  (Subalgebra.inclusion (show S.1 ≤ T.1 from h)).toRingHom

/-- The inclusion of a finitely generated subalgebra into `A`. -/
def fgToLimit (T : FGIndex A₀ A) : FGStage T →+* A :=
  T.1.val.toRingHom

instance fgDirectedSystem :
    DirectedSystem (FGStage (A₀ := A₀) (A := A)) fun S T h => ⇑(fgTransition S T h) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- `A` is the direct limit of its finitely generated `A₀`-subalgebras. -/
theorem fgIsDirectLimit :
    IsDirectLimit (fun S T h => ⇑(fgTransition (A₀ := A₀) (A := A) S T h))
      fun T => ⇑(fgToLimit T) where
  surj m := ⟨⟨Algebra.adjoin A₀ ↑({m} : Finset A), Subalgebra.fg_adjoin_finset _⟩,
    ⟨m, Algebra.subset_adjoin (by simp)⟩, rfl⟩
  inj S T x y h := ⟨⟨S.1 ⊔ T.1, S.2.sup T.2⟩, (le_sup_left : S.1 ≤ S.1 ⊔ T.1),
    (le_sup_right : T.1 ≤ S.1 ⊔ T.1), Subtype.ext h⟩
  compatibility _ _ _ _ := rfl

/-- The inclusion of a stage into `A` is its structure map as an `A`-subalgebra. -/
theorem algebraMap_fgStage (T : FGIndex A₀ A) : algebraMap (FGStage T) A = fgToLimit T :=
  rfl

theorem spec_map_fgToLimit_comp (T : FGIndex A₀ A) :
    Spec.map (CommRingCat.ofHom (fgToLimit T)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A₀ (FGStage T))) =
      Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem spec_map_fgTransition_comp (S T : FGIndex A₀ A) (h : S ≤ T) :
    Spec.map (CommRingCat.ofHom (fgTransition S T h)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A₀ (FGStage S))) =
      Spec.map (CommRingCat.ofHom (algebraMap A₀ (FGStage T))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem spec_map_fgToLimit_fgTransition (S T : FGIndex A₀ A) (h : S ≤ T) :
    Spec.map (CommRingCat.ofHom (fgToLimit T)) ≫
        Spec.map (CommRingCat.ofHom (fgTransition S T h)) =
      Spec.map (CommRingCat.ofHom (fgToLimit S)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end Langlands.AlgebraicGeometry.NoetherianApproximation
