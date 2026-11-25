/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import WeilConjectures.Compactification.BaseChange

/-!

# Compactifications of morphisms over a base scheme

Let `S` be a scheme and `f : X ⟶ Y` a morphism of `S`-schemes. A compactification
`c : X ⟶[i] Z ⟶[p] Y` of `f` makes `Z` an `S`-scheme through `p ≫ (Y ↘ S)`, for which `p` and
`i` are morphisms over `S`. If `Y` is separated and of finite type over `S`, so is `Z`, the
structure morphism `p` being proper. The same applies to the base change
`Z ×_Y Y' ⟶[snd] Y'` of a compactification along a morphism of `S`-schemes `g : Y' ⟶ Y`, and
the projection `Z ×_Y Y' ⟶ Z` is a morphism over `S`.

These instances let the compactifications of morphisms between separated `S`-schemes of finite
type be used in statements on such schemes, without any hypothesis on `Z`.

The same is done in the category `Over S`: for a morphism `f : X ⟶ Y` of `Over S` and a
compactification `c` of the underlying morphism of schemes `f.left`, `Z` is an object
`c.overObj` of `Over S`, and `i` and `p` are morphisms `c.overI : X ⟶ c.overObj` and
`c.overG : c.overObj ⟶ Y` of `Over S`, with `c.overI ≫ c.overG = f`. For a cartesian square
`sq : IsPullback g' f' f g` of `Over S`, the square of underlying schemes is cartesian
(`CategoryTheory.IsPullback.overLeft`), and the proper and open-immersion squares of the base
change `c.ofIsPullback sq.overLeft` are cartesian squares of `Over S`
(`Compactification.overBaseChange_isPullback_g`, `Compactification.overBaseChange_isPullback_i`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {S X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The compactification `Z` of a morphism of `S`-schemes is an `S`-scheme, through the structure
morphism `p : Z ⟶ Y` followed by `Y ↘ S`. -/
instance overZ [Y.Over S] : c.Z.Over S :=
  OverClass.ofHom (c.g ≫ Y ↘ S)

instance isOver_g [Y.Over S] : c.g.IsOver S :=
  ⟨rfl⟩

instance isOver_i [X.Over S] [Y.Over S] [f.IsOver S] : c.i.IsOver S :=
  ⟨by
    change c.i ≫ c.g ≫ Y ↘ S = X ↘ S
    rw [← Category.assoc, ← c.comm]
    exact comp_over f S⟩

instance locallyOfFiniteType_over [Y.Over S] [LocallyOfFiniteType (Y ↘ S)] :
    LocallyOfFiniteType (c.Z ↘ S) :=
  inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y ↘ S))

instance quasiCompact_over [Y.Over S] [QuasiCompact (Y ↘ S)] : QuasiCompact (c.Z ↘ S) :=
  inferInstanceAs (QuasiCompact (c.g ≫ Y ↘ S))

instance isSeparated_over [Y.Over S] [IsSeparated (Y ↘ S)] : IsSeparated (c.Z ↘ S) :=
  inferInstanceAs (IsSeparated (c.g ≫ Y ↘ S))

section BaseChange

variable {Y' : Scheme.{u}} (g : Y' ⟶ Y)

/-- The fibre product `Z ×_Y Y'` underlying the base change of a compactification along a
morphism `g : Y' ⟶ Y` of `S`-schemes is an `S`-scheme through the second projection, as the
compactification scheme of the base change (`Compactification.overZ`). -/
noncomputable instance overPullback [Y'.Over S] : (pullback c.g g).Over S :=
  OverClass.ofHom (pullback.snd c.g g ≫ Y' ↘ S)

/-- The projection `Z ×_Y Y' ⟶ Z` is a morphism over `S`. -/
instance isOver_pullback_fst [Y.Over S] [Y'.Over S] [g.IsOver S] :
    (pullback.fst c.g g).IsOver S :=
  ⟨by
    change pullback.fst c.g g ≫ c.g ≫ Y ↘ S = pullback.snd c.g g ≫ Y' ↘ S
    rw [pullback.condition_assoc, comp_over g S]⟩

instance locallyOfFiniteType_pullback_over [Y'.Over S] [LocallyOfFiniteType (Y' ↘ S)] :
    LocallyOfFiniteType (pullback c.g g ↘ S) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd c.g g ≫ Y' ↘ S))

instance quasiCompact_pullback_over [Y'.Over S] [QuasiCompact (Y' ↘ S)] :
    QuasiCompact (pullback c.g g ↘ S) :=
  inferInstanceAs (QuasiCompact (pullback.snd c.g g ≫ Y' ↘ S))

instance isSeparated_pullback_over [Y'.Over S] [IsSeparated (Y' ↘ S)] :
    IsSeparated (pullback c.g g ↘ S) :=
  inferInstanceAs (IsSeparated (pullback.snd c.g g ≫ Y' ↘ S))

end BaseChange

/-! ### Compactifications of morphisms in the category over `S` -/

section OverCategory

variable {S : Scheme.{u}} {X Y : Over S} {f : X ⟶ Y} (c : Compactification f.left)

/-- The compactification `Z` of a morphism `f` of `Over S` as an object of `Over S`, through the
structure morphism `p : Z ⟶ Y` followed by `Y ⟶ S`. -/
noncomputable def overObj : Over S :=
  Over.mk (c.g ≫ Y.hom)

/-- The open immersion `i : X ⟶ Z` of a compactification of a morphism `f` of `Over S`, as a
morphism of `Over S`. -/
noncomputable def overI : X ⟶ c.overObj :=
  Over.homMk c.i (by
    change c.i ≫ c.g ≫ Y.hom = X.hom
    rw [← Category.assoc, ← c.comm, Over.w])

/-- The proper morphism `p : Z ⟶ Y` of a compactification of a morphism `f` of `Over S`, as a
morphism of `Over S`. -/
noncomputable def overG : c.overObj ⟶ Y :=
  Over.homMk c.g rfl

@[simp] lemma overObj_left : c.overObj.left = c.Z := rfl

@[simp] lemma overObj_hom : c.overObj.hom = c.g ≫ Y.hom := rfl

@[simp] lemma overI_left : c.overI.left = c.i := rfl

@[simp] lemma overG_left : c.overG.left = c.g := rfl

@[reassoc]
lemma overI_overG : c.overI ≫ c.overG = f :=
  Over.OverMorphism.ext c.comm.symm

instance isOpenImmersion_overI : IsOpenImmersion c.overI.left :=
  c.isOpenImmersion

instance isProper_overG : IsProper c.overG.left :=
  c.isProper

instance locallyOfFiniteType_overObj [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType c.overObj.hom :=
  inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y.hom))

instance quasiCompact_overObj [QuasiCompact Y.hom] : QuasiCompact c.overObj.hom :=
  inferInstanceAs (QuasiCompact (c.g ≫ Y.hom))

instance isSeparated_overObj [IsSeparated Y.hom] : IsSeparated c.overObj.hom :=
  inferInstanceAs (IsSeparated (c.g ≫ Y.hom))

section BaseChange

variable {X' Y' : Over S} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The square of underlying schemes of a cartesian square in `Over S` is cartesian. -/
theorem _root_.CategoryTheory.IsPullback.overLeft (sq : IsPullback g' f' f g) :
    IsPullback g'.left f'.left f.left g.left :=
  sq.map (Over.forget S)

variable (sq : IsPullback g' f' f g)

/-- The projection `Z ×_Y Y' ⟶ Z` from the base change of a compactification along a cartesian
square of `Over S`, as a morphism of `Over S`. -/
noncomputable def overBaseChangeFst : (c.ofIsPullback sq.overLeft).overObj ⟶ c.overObj :=
  Over.homMk (pullback.fst c.g g.left) (by
    change pullback.fst c.g g.left ≫ c.g ≫ Y.hom = pullback.snd c.g g.left ≫ Y'.hom
    rw [pullback.condition_assoc, Over.w])

@[simp] lemma overBaseChangeFst_left :
    (c.overBaseChangeFst sq).left = pullback.fst c.g g.left := rfl

/-- The proper square of the base-changed compactification is cartesian in `Over S`. -/
theorem overBaseChange_isPullback_g :
    IsPullback (c.overBaseChangeFst sq) (c.ofIsPullback sq.overLeft).overG c.overG g :=
  IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext pullback.condition)
    (c.isPullback_g_ofIsPullback sq.overLeft).flip

/-- The open-immersion square of the base-changed compactification is cartesian in `Over S`. -/
theorem overBaseChange_isPullback_i :
    IsPullback g' (c.ofIsPullback sq.overLeft).overI c.overI (c.overBaseChangeFst sq) :=
  IsPullback.of_map (Over.forget S)
    (Over.OverMorphism.ext (c.isPullback_i_ofIsPullback sq.overLeft).w)
    (c.isPullback_i_ofIsPullback sq.overLeft)

end BaseChange

end OverCategory

end AlgebraicGeometry.Compactification
