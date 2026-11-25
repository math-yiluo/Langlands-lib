/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!

# Left Kan extensions for presheaves on the small sites

Left Kan extensions along the opposites of base change and of the localization functors
exist for `A`-valued presheaves on the small étale and the small pro-étale sites, for a
Grothendieck abelian category `A` with `Hom`-types in the universe `u + 1`, one above the
universe `u` of the base schemes.

The instances for the localization functors are proved from the scheme-side combinatorics
below, namely the type `AlgebraicGeometry.SmallSite.LiftIndex` of factorizations of the
structure morphism of `W : P.Over ⊤ U` through `f`, which governs the indexing comma
category of the pointwise left Kan extension along the localization functor of `h : P f`,
and the dichotomy `SmallSite.mem_essImage_or_isEmpty_costructuredArrow_op_overMap`: for a
monomorphism `f`, every `W` either lies in the essential image of the localization functor
(a lift induces a terminal object of the comma category) or has empty indexing comma
category. That dichotomy is what makes the pointwise left Kan extensions exist over a
category with an initial object (`SmallSite.hasPointwiseLeftKanExtension_op_overMap`) and
makes the presheaf-level left Kan extension left exact
(`SmallSite.preservesFiniteLimits_op_lan_overMap`), being pointwise either an evaluation or
a zero object. The cancellation `P (α ≫ f) → P f → P α` it uses is
`MorphismProperty.HasOfPostcompProperty P P`, available both for `P = @Etale` and for
`P = @WeaklyEtale`.

For an arbitrary `f` the indexing comma category at `W` is the disjoint union, over the
lifts `α` of `W` through `f`, of categories with terminal object: the inclusion of the
discrete category of lifts is final
(`SmallSite.exists_final_discrete_costructuredArrow_overMap`). The presheaf-level left Kan
extension is then pointwise the direct sum `⨁_α F(α)`, hence left exact when direct sums in
`A` are exact
(`SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian`). This is the
left exactness of extension by zero along an étale morphism.

Base change `MorphismProperty.Over.pullback P ⊤ g` along an *arbitrary* morphism
`g : Z ⟶ Y` sends `W : P.Over ⊤ Y` to the left edge of the cartesian square

```
  W ×[Y] Z ---> W
      |         |
      v         v
      Z ---g--> Y
```

and has no monomorphism to exploit, so neither the existence of the left Kan extensions
along its opposite nor their left exactness comes from the combinatorics above:

- existence is the general `Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize` of
  `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`: the indexing comma
  categories have objects in `Type (u + 1)` and `Hom`-types in `Type u`, so they are
  essentially `u + 1`-small and `A` has colimits over them. No smallness of the small sites
  themselves is needed. That instance applies to the small sites as it stands, so nothing is
  restated for it here;
- left exactness is the slice-level statement
  `MorphismProperty.Over.preservesFiniteLimits_op_lan_pullback` of
  `WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty`, at `P = @Etale` and
  `P = @WeaklyEtale` over `Scheme.{u}`: base change preserves the finite limits of the
  slice, hence is representably flat, so the indexing comma categories are filtered and the
  Kan extension is computed by filtered colimits, which are exact in `A` by AB5. It is
  restated for each of the two sites below.

For an étale `g` both are also proved in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and for a weakly étale `g` in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`, via the adjunction
`MorphismProperty.Over.mapPullbackAdj`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.SmallSite

section LiftIndex

variable {P : MorphismProperty Scheme.{u}} {V U : Scheme.{u}}

/-- The type of lifts of `W : P.Over ⊤ U` through `f : V ⟶ U`: factorizations of the
structure morphism of `W` through `f`. It indexes the colimit computing the presheaf-level
left Kan extension along the localization functor of `h : P f`. -/
private def LiftIndex (f : V ⟶ U) (W : P.Over ⊤ U) : Type u :=
  {α : W.left ⟶ V // α ≫ f = W.hom}

namespace LiftIndex

variable [P.IsMultiplicative] [P.HasOfPostcompProperty P] {f : V ⟶ U} {W : P.Over ⊤ U}

omit [P.IsMultiplicative] in
/-- The lift of a `P`-scheme over `U` through `f` with `P f` satisfies `P`, by the
cancellation property `MorphismProperty.HasOfPostcompProperty P P`. -/
private lemma prop_val (h : P f) (α : LiftIndex f W) : P α.1 :=
  MorphismProperty.of_postcomp (W := P) (W' := P) α.1 f h (by rw [α.2]; exact W.prop)

/-- The `P`-scheme over `V` determined by a lift of `W : P.Over ⊤ U` through `f`. -/
private def toOver (h : P f) (α : LiftIndex f W) : P.Over ⊤ V :=
  MorphismProperty.Over.mk ⊤ α.1 (α.prop_val h)

/-- The comparison morphism from `W` to the image of `α.toOver` in `P.Over ⊤ U`; its
underlying morphism is the identity. -/
private def homToComp (h : P f) (α : LiftIndex f W) :
    W ⟶ (MorphismProperty.Over.map ⊤ h).obj (α.toOver h) :=
  MorphismProperty.Over.homMk (𝟙 W.left) ((Category.id_comp _).trans α.2)

/-- A lift of `W` through `f` identifies `W` with the image of a `P`-scheme over `V`
under the localization functor: the comparison morphism `LiftIndex.homToComp` is the
identity on underlying schemes. -/
private def isoComp (h : P f) (α : LiftIndex f W) :
    W ≅ (MorphismProperty.Over.map ⊤ h).obj (α.toOver h) where
  hom := α.homToComp h
  inv := MorphismProperty.Over.homMk (𝟙 W.left) ((Category.id_comp _).trans α.2.symm)
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _

/-- The object of the comma category indexing the pointwise left Kan extension at `W`
associated with a lift `α`; for a monomorphism `f` it is terminal, see
`LiftIndex.isTerminalCostructuredArrow`. -/
private def costructuredArrow (h : P f) (α : LiftIndex f W) :
    CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W) :=
  CostructuredArrow.mk (α.homToComp h).op

/-- The lift of `W` extracted from an object of the indexing comma category. -/
private def ofCostructuredArrow (h : P f) (W : P.Over ⊤ U)
    (s : CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W)) :
    LiftIndex f W :=
  ⟨s.hom.unop.left ≫ s.left.unop.hom, by
    have hw : s.hom.unop.left ≫
        ((MorphismProperty.Over.map ⊤ h).obj s.left.unop).hom = W.hom :=
      MorphismProperty.Over.w s.hom.unop
    rw [Category.assoc]
    exact hw⟩

omit [P.HasOfPostcompProperty P] in
/-- If `W` has no lift through `f`, the indexing comma category is empty. -/
private lemma isEmpty_costructuredArrow (h : P f) (W : P.Over ⊤ U)
    (hempty : IsEmpty (LiftIndex f W)) :
    IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W)) :=
  ⟨fun s => hempty.elim (ofCostructuredArrow h W s)⟩

/-- For a monomorphism `f`, the comma object associated with a lift `α` of `W` is
terminal: the pointwise left Kan extension formula collapses to a single value. -/
private noncomputable def isTerminalCostructuredArrow (h : P f) [Mono f]
    (α : LiftIndex f W) :
    IsTerminal (α.costructuredArrow h) :=
  IsTerminal.ofUniqueHom
    (fun s =>
      CostructuredArrow.homMk
        (Quiver.Hom.op
          (MorphismProperty.Over.homMk s.hom.unop.left
            (by
              have hs : s.hom.unop.left ≫ s.left.unop.hom ≫ f = W.hom :=
                MorphismProperty.Over.w s.hom.unop
              exact (cancel_mono f).mp
                (((Category.assoc _ _ _).trans hs).trans α.2.symm)) :
            α.toOver h ⟶ s.left.unop))
        (by
          apply Quiver.Hom.unop_inj
          apply MorphismProperty.Over.Hom.ext
          exact Category.id_comp _))
    (fun s m => by
      ext
      have hw := m.w
      apply_fun (fun z => z.unop.left) at hw
      exact (Category.id_comp _).symm.trans hw)

omit [P.HasOfPostcompProperty P] in
/-- The lift of `W` extracted from an object of the indexing comma category is constant along
the morphisms of the comma category. -/
private lemma ofCostructuredArrow_eq_of_hom (h : P f)
    {s t : CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W)} (m : s ⟶ t) :
    ofCostructuredArrow h W s = ofCostructuredArrow h W t := by
  apply Subtype.ext
  have hw : s.hom.unop.left = t.hom.unop.left ≫ m.left.unop.left := by
    have := congrArg (fun z ↦ z.unop.left) (CostructuredArrow.w m)
    exact this.symm
  change s.hom.unop.left ≫ s.left.unop.hom = t.hom.unop.left ≫ t.left.unop.hom
  rw [hw, Category.assoc, MorphismProperty.Over.w m.left.unop]

/-- The lift of `W` extracted from the comma object associated with a lift `α` is `α`. -/
private lemma ofCostructuredArrow_costructuredArrow (h : P f) (α : LiftIndex f W) :
    ofCostructuredArrow h W (α.costructuredArrow h) = α :=
  Subtype.ext (Category.id_comp _)

/-- A morphism of the indexing comma category into the comma object associated with a lift
`α`, from an object inducing the lift `α`. -/
private def homCostructuredArrow (h : P f) (α : LiftIndex f W)
    (s : CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W))
    (hs : ofCostructuredArrow h W s = α) : s ⟶ α.costructuredArrow h :=
  CostructuredArrow.homMk
    (Quiver.Hom.op
      (MorphismProperty.Over.homMk s.hom.unop.left (congrArg Subtype.val hs) :
        α.toOver h ⟶ s.left.unop))
    (by
      apply Quiver.Hom.unop_inj
      apply MorphismProperty.Over.Hom.ext
      exact Category.id_comp _)

/-- There is at most one morphism of the indexing comma category into the comma object
associated with a lift. -/
private lemma subsingleton_hom_costructuredArrow (h : P f) (α : LiftIndex f W)
    (s : CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W)) :
    Subsingleton (s ⟶ α.costructuredArrow h) := by
  refine ⟨fun m m' ↦ ?_⟩
  ext
  have hw := congrArg (fun z ↦ z.unop.left) m.w
  have hw' := congrArg (fun z ↦ z.unop.left) m'.w
  exact ((Category.id_comp _).symm.trans hw).trans
    (((Category.id_comp _).symm.trans hw').symm)

/-- The functor sending a lift `α` of `W` through `f` to the associated object of the indexing
comma category. -/
private def discreteFunctor (h : P f) :
    Discrete (LiftIndex f W) ⥤ CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W) :=
  Discrete.functor (costructuredArrow h)

/-- The functor sending an object of the indexing comma category to the lift of `W` it
induces. -/
private def toDiscrete (h : P f) :
    CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W) ⥤ Discrete (LiftIndex f W) where
  obj s := ⟨ofCostructuredArrow h W s⟩
  map m := Discrete.eqToHom (ofCostructuredArrow_eq_of_hom h m)

/-- The indexing comma category is the disjoint union, over the lifts `α` of `W` through `f`,
of categories with terminal object `α.costructuredArrow h`: sending an object to its lift is
left adjoint to `LiftIndex.discreteFunctor`. -/
private def toDiscreteAdjunction (h : P f) :
    toDiscrete (W := W) h ⊣ discreteFunctor h :=
  Adjunction.mkOfHomEquiv
    { homEquiv s α :=
        have := subsingleton_hom_costructuredArrow h α.as s
        { toFun e := homCostructuredArrow h α.as s (Discrete.eq_of_hom e)
          invFun m := Discrete.eqToHom ((ofCostructuredArrow_eq_of_hom h m).trans
            (ofCostructuredArrow_costructuredArrow h α.as))
          left_inv _ := Subsingleton.elim _ _
          right_inv _ := (subsingleton_hom_costructuredArrow h α.as s).elim _ _ }
      homEquiv_naturality_left_symm _ _ := Subsingleton.elim _ _
      homEquiv_naturality_right {s _ α} _ _ :=
        (subsingleton_hom_costructuredArrow h α.as s).elim _ _ }

/-- The inclusion of the lifts of `W` into the indexing comma category is final. -/
private lemma final_discreteFunctor (h : P f) : (discreteFunctor (W := W) h).Final :=
  Functor.final_of_adjunction (toDiscreteAdjunction h)

end LiftIndex

end LiftIndex

section Final

variable {P : MorphismProperty Scheme.{u}} {V U : Scheme.{u}}
  [P.IsMultiplicative] [P.HasOfPostcompProperty P] {f : V ⟶ U}

/-- The comma category indexing the pointwise left Kan extension along the opposite of the
localization functor of `h : P f` at `W` receives a final functor from a discrete category,
namely the lifts of `W` through `f`, whose comma objects have invertible structure maps. -/
theorem exists_final_discrete_costructuredArrow_overMap (h : P f) (W : P.Over ⊤ U) :
    ∃ (ι : Type u) (s : Discrete ι ⥤ CostructuredArrow (MorphismProperty.Over.map ⊤ h).op (op W)),
      s.Final ∧ ∀ i, IsIso (s.obj i).hom :=
  ⟨_, LiftIndex.discreteFunctor h, LiftIndex.final_discreteFunctor h, fun i ↦
    inferInstanceAs (IsIso (i.as.isoComp h).hom.op)⟩

end Final

section OverMap

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {P : MorphismProperty Scheme.{u}} [P.IsMultiplicative] [P.HasOfPostcompProperty P]
  {V U : Scheme.{u}} {f : V ⟶ U}

/-- Along the localization functor of `h : P f` with `f` a monomorphism, all pointwise
left Kan extensions with values in a category with an initial object exist: the indexing
comma categories are either empty or admit a terminal object. -/
instance hasPointwiseLeftKanExtension_op_overMap (h : P f) [Mono f]
    (F : (P.Over ⊤ V)ᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasPointwiseLeftKanExtension F := by
  intro W
  by_cases hn : Nonempty (LiftIndex f W.unop)
  · obtain ⟨α⟩ := hn
    have : HasTerminal (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op W) :=
      (α.isTerminalCostructuredArrow h).hasTerminal
    infer_instance
  · have : IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op W) :=
      LiftIndex.isEmpty_costructuredArrow h W.unop (not_nonempty_iff.mp hn)
    have : HasColimitsOfShape
        (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op W) A :=
      hasColimitsOfShape_of_equivalence (equivalenceOfIsEmpty (Discrete PEmpty.{1}) _)
    infer_instance

/-- Every `P`-scheme over `U` either lies in the essential image of the localization
functor of `h : P f`, or has empty indexing comma category: a lift of `W` through `f`
identifies `W` with the image of a `P`-scheme over `V`, and if no lift exists the comma
category is empty. This is the dichotomy underlying the left exactness of the
presheaf-level lower shriek. -/
lemma mem_essImage_or_isEmpty_costructuredArrow_op_overMap (h : P f) (W : (P.Over ⊤ U)ᵒᵖ) :
    (MorphismProperty.Over.map ⊤ h).op.essImage W ∨
      IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op W) := by
  by_cases hn : Nonempty (LiftIndex f W.unop)
  · obtain ⟨α⟩ := hn
    exact Or.inl ⟨op (α.toOver h), ⟨(α.isoComp h).op⟩⟩
  · exact Or.inr (LiftIndex.isEmpty_costructuredArrow h W.unop (not_nonempty_iff.mp hn))

/-- The presheaf-level left Kan extension along the opposite of the localization functor
of `h : P f` with `f` a monomorphism is left exact: by the dichotomy
`mem_essImage_or_isEmpty_costructuredArrow_op_overMap` it is pointwise either an evaluation
or a zero object. -/
lemma preservesFiniteLimits_op_lan_overMap (h : P f) [Mono f] :
    PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ h).op.lan :
      ((P.Over ⊤ V)ᵒᵖ ⥤ A) ⥤ (P.Over ⊤ U)ᵒᵖ ⥤ A) :=
  Functor.preservesFiniteLimits_lan_of_essImage_or_isEmpty _
    (mem_essImage_or_isEmpty_costructuredArrow_op_overMap h)

/-- The presheaf-level left Kan extension along the opposite of the localization functor
of `h : P f`, for an arbitrary `f`, is left exact: at `W` it is the direct sum, over the lifts
`α` of `W` through `f`, of the values at `α`, because the indexing comma category is a
disjoint union of categories with terminal objects; direct sums are exact in the Grothendieck
abelian category `A`. -/
lemma preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian (h : P f)
    [∀ F : (P.Over ⊤ V)ᵒᵖ ⥤ A,
      (MorphismProperty.Over.map ⊤ h).op.HasPointwiseLeftKanExtension F] :
    PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ h).op.lan :
      ((P.Over ⊤ V)ᵒᵖ ⥤ A) ⥤ (P.Over ⊤ U)ᵒᵖ ⥤ A) :=
  have : HasCoproducts.{u} A := hasCoproducts_shrink.{u, u + 1}
  have : AB4OfSize.{u} A := AB4OfSize_shrink.{u, u + 1} A
  Functor.preservesFiniteLimits_lan_of_final.{u} _
    fun W ↦ ⟨_, _, LiftIndex.final_discreteFunctor (W := W.unop) h⟩

end OverMap

end AlgebraicGeometry.SmallSite

/-! ### The small étale site -/

namespace AlgebraicGeometry.Etale

instance (priority := 10) hasLeftKanExtension_op_overPullback (A : Type u') [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (F : Y.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasLeftKanExtension F :=
  inferInstance

/-- Along the localization functor of `h : Etale f` with `f` a monomorphism, all pointwise
left Kan extensions with values in a category with an initial object exist: the indexing
comma categories are either empty or admit a terminal object. -/
instance hasPointwiseLeftKanExtension_op_overMap (A : Type u') [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {V U : Scheme.{u}} {f : V ⟶ U}
    (h : Etale f) [Mono f] (F : V.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasPointwiseLeftKanExtension F :=
  SmallSite.hasPointwiseLeftKanExtension_op_overMap A h F

/-- Left Kan extensions along the opposite of the localization functor of `h : Etale f`
with `f` a monomorphism exist for `A`-valued presheaves on the small étale sites: the
indexing comma categories are either empty or admit a terminal object, see
`hasPointwiseLeftKanExtension_op_overMap`. -/
instance hasLeftKanExtension_op_overMap (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {V U : Scheme.{u}} {f : V ⟶ U} (h : Etale f) [Mono f]
    (F : V.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasLeftKanExtension F :=
  inferInstance

/-- Every étale scheme over `U` either lies in the essential image of the localization
functor of `h : Etale f`, or has empty indexing comma category. -/
lemma mem_essImage_or_isEmpty_costructuredArrow_op_overMap {V U : Scheme.{u}} {f : V ⟶ U}
    (h : Etale f) (W : U.Etaleᵒᵖ) :
    (MorphismProperty.Over.map ⊤ h).op.essImage W ∨
      IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op W) :=
  SmallSite.mem_essImage_or_isEmpty_costructuredArrow_op_overMap h W

/-- The presheaf-level left Kan extension along the opposite of the localization functor
of `h : Etale f` with `f` a monomorphism is left exact: by the dichotomy
`mem_essImage_or_isEmpty_costructuredArrow_op_overMap` it is pointwise either an evaluation
or a zero object. -/
instance preservesFiniteLimits_op_lan_overMap (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {V U : Scheme.{u}} {f : V ⟶ U} (h : Etale f) [Mono f] :
    PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ h).op.lan :
      (V.Etaleᵒᵖ ⥤ A) ⥤ U.Etaleᵒᵖ ⥤ A) :=
  SmallSite.preservesFiniteLimits_op_lan_overMap A h

/-- The left Kan extension along the opposite of base change by an *arbitrary* morphism
`g : Z ⟶ Y` is left exact for a Grothendieck abelian coefficient category: base change
preserves the finite limits of the étale slice, hence is representably flat, so the indexing
comma categories of the pointwise left Kan extensions are filtered and the Kan extension is
computed by filtered colimits, which are exact in `A` by AB5. This is the case `P = @Etale`
of `MorphismProperty.Over.preservesFiniteLimits_op_lan_pullback`. For an étale `g` it is
also proved in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` via the adjunction
with the localization functor. -/
instance preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan :
      (Y.Etaleᵒᵖ ⥤ A) ⥤ Z.Etaleᵒᵖ ⥤ A) :=
  MorphismProperty.Over.preservesFiniteLimits_op_lan_pullback A @Etale g

end AlgebraicGeometry.Etale

/-! ### The small pro-étale site -/

namespace AlgebraicGeometry.ProEtale

instance (priority := 10) hasLeftKanExtension_op_overPullback (A : Type u') [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (F : Y.ProEtᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.HasLeftKanExtension F :=
  inferInstance

/-- Along the localization functor of `h : WeaklyEtale f` with `f` a monomorphism, all
pointwise left Kan extensions with values in a category with an initial object exist: the
indexing comma categories are either empty or admit a terminal object. -/
instance hasPointwiseLeftKanExtension_op_overMap (A : Type u') [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {V U : Scheme.{u}} {f : V ⟶ U}
    (h : WeaklyEtale f) [Mono f] (F : V.ProEtᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasPointwiseLeftKanExtension F :=
  SmallSite.hasPointwiseLeftKanExtension_op_overMap A h F

/-- Left Kan extensions along the opposite of the localization functor of
`h : WeaklyEtale f` with `f` a monomorphism exist for `A`-valued presheaves on the small
pro-étale sites, see `hasPointwiseLeftKanExtension_op_overMap`. -/
instance hasLeftKanExtension_op_overMap (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {V U : Scheme.{u}} {f : V ⟶ U} (h : WeaklyEtale f)
    [Mono f] (F : V.ProEtᵒᵖ ⥤ A) :
    (MorphismProperty.Over.map ⊤ h).op.HasLeftKanExtension F :=
  inferInstance

/-- Every weakly étale scheme over `U` either lies in the essential image of the
localization functor of `h : WeaklyEtale f`, or has empty indexing comma category. -/
lemma mem_essImage_or_isEmpty_costructuredArrow_op_overMap {V U : Scheme.{u}} {f : V ⟶ U}
    (h : WeaklyEtale f) (W : U.ProEtᵒᵖ) :
    (MorphismProperty.Over.map ⊤ h).op.essImage W ∨
      IsEmpty (CostructuredArrow (MorphismProperty.Over.map ⊤ h).op W) :=
  SmallSite.mem_essImage_or_isEmpty_costructuredArrow_op_overMap h W

/-- The presheaf-level left Kan extension along the opposite of the localization functor
of `h : WeaklyEtale f` with `f` a monomorphism is left exact: by the dichotomy
`mem_essImage_or_isEmpty_costructuredArrow_op_overMap` it is pointwise either an evaluation
or a zero object. -/
instance preservesFiniteLimits_op_lan_overMap (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {V U : Scheme.{u}} {f : V ⟶ U} (h : WeaklyEtale f)
    [Mono f] :
    PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ h).op.lan :
      (V.ProEtᵒᵖ ⥤ A) ⥤ U.ProEtᵒᵖ ⥤ A) :=
  SmallSite.preservesFiniteLimits_op_lan_overMap A h

/-- The left Kan extension along the opposite of base change by an *arbitrary* morphism
`g : Z ⟶ Y` is left exact for a Grothendieck abelian coefficient category: base change
preserves the finite limits of the pro-étale slice, hence is representably flat, so the
indexing comma categories of the pointwise left Kan extensions are filtered and the Kan
extension is computed by filtered colimits, which are exact in `A` by AB5. This is the case
`P = @WeaklyEtale` of `MorphismProperty.Over.preservesFiniteLimits_op_lan_pullback`. For a
weakly étale `g` it is also proved in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs` via the adjunction with
the localization functor. -/
instance preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    PreservesFiniteLimits ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op.lan :
      (Y.ProEtᵒᵖ ⥤ A) ⥤ Z.ProEtᵒᵖ ⥤ A) :=
  MorphismProperty.Over.preservesFiniteLimits_op_lan_pullback A @WeaklyEtale g

end AlgebraicGeometry.ProEtale
