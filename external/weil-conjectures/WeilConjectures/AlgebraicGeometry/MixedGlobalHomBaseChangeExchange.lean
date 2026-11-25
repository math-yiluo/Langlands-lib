/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatAffineGlobalHomComparison
public import WeilConjectures.AlgebraicGeometry.MixedGlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.MixedInternalHomBaseChangeExchange
import WeilConjectures.AlgebraicGeometry.MixedGlobalSectionsBaseChangeMate

/-!
# The exchange square for global Hom comparisons

Source: Stacks Project, duality.tex, Tag 0AA8, final commutative diagrams.
(blueprint: lem-sc-mixed-global-hom-base-change-exchange).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry

private theorem globalMate_postcomp
    {C D B V : Type*} [Category C] [Category D] [Category B] [Category V]
  {F : C ⥤ D} {R : D ⥤ C} (adj : F ⊣ R)
  (G : C ⥤ B) (T : D ⥤ V) (S : V ⥤ B) (e : R ⋙ G ≅ T ⋙ S)
    {A : C} {P Q : D}
    (a : F.obj A ⟶ P) (b : P ⟶ Q) :
    G.map (adj.homEquiv _ _ a) ≫ e.hom.app P ≫ S.map (T.map b) =
      G.map (adj.homEquiv _ _ (a ≫ b)) ≫ e.hom.app Q := by
  rw [adj.homEquiv_naturality_right, G.map_comp, Category.assoc]
  have hn := e.hom.naturality b
  dsimp only [Functor.comp_map] at hn
  rw [hn]

private theorem globalMate_exchange
    {C D B V : Type*} [Category C] [Category D] [Category B] [Category V]
  {F : C ⥤ D} {R : D ⥤ C} (adj : F ⊣ R)
  (G : C ⥤ B) (T : D ⥤ V) (S : V ⥤ B) (e : R ⋙ G ≅ T ⋙ S)
    {A A' : C} {P Q Q' : D} {Z : B}
    (l : Z ⟶ G.obj A) (s : Z ⟶ S.obj (T.obj P))
    (a : F.obj A ⟶ P) (b : P ⟶ Q') (u : A ⟶ A')
    (v : F.obj A' ⟶ Q) (d : Q ⟶ Q')
    (hs : s = l ≫ G.map (adj.homEquiv _ _ a) ≫ e.hom.app P)
    (hi : a ≫ b = F.map u ≫ v ≫ d) :
    s ≫ S.map (T.map b) =
      l ≫ G.map u ≫ G.map (adj.homEquiv _ _ v) ≫ e.hom.app Q ≫ S.map (T.map d) := by
  rw [hs]
  simp only [Category.assoc]
  rw [globalMate_postcomp adj G T S e a b, hi,
    adj.homEquiv_naturality_left, G.map_comp]
  simp only [Category.assoc]
  rw [← globalMate_postcomp adj G T S e v d]

/-- The evaluation-mate pullback and direct-image comparisons satisfy the exchange
square, with the canonical base-change map in each Hom entry. No invertibility,
counit equation, or additional morphisms are assumed.

Source: Stacks Project, duality.tex, Tag 0AA8, final commutative diagrams;
cohomology.tex, Tag 08I3, and duality.tex, Tag 0B6I, evaluation-mate comparisons.
(blueprint: lem-sc-mixed-global-hom-base-change-exchange).

Proof: expand both comparison maps as the transposes of evaluation under the
fixed tensor-Hom bijections and pullback/direct-image adjunctions. Transpose the
two paths once more. Naturality of evaluation identifies the occurrence of
base change in the second entry with postcomposition by its evaluation mate;
in the first entry, contravariance identifies it with precomposition by the
same mate. Expand that mate as the canonical pullback-composition comparison
followed by the adjunction counit. The counit naturality square and triangle
identity make the two resulting tensor-evaluation composites equal. The pinned
pullback tensor comparisons respect composition: on K-flat representatives both
are the ordinary tensor-pullback comparison, and their derived universal
properties transport this equality to all objects. Apply derived global sections.
The Leray comparisons respect composition by uniqueness of the comparison with
the same right-derived unit; the underived global-sections/scalar comparison is
the identity on sections. Thus its two scalar paths are identified by exactly
schemeGlobalScalarSquareIso. This gives the displayed equality. -/
theorem mixedGlobalHom_baseChange_exchange
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (M N : schemeDerivedCategory X) :
    (schemeGlobalScalarRestriction f).map
        (mixedGlobalHomPullbackComparison (pullback.fst f g) M N) ≫
      (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition).hom.app
          ((schemeGlobalDerivedHom (pullback f g)).obj
            (op ((derivedPullback (pullback.fst f g)).obj M),
              (derivedPullback (pullback.fst f g)).obj N)) ≫
      (schemeGlobalScalarRestriction g).map
        (mixedGlobalHomDirectImageMap (pullback.snd f g)
          ((derivedPullback (pullback.fst f g)).obj M)
          ((derivedPullback (pullback.fst f g)).obj N)) ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeGlobalDerivedHom Y').map
          (X := (op ((schemeDerivedDirectImage (pullback.snd f g)).obj
            ((derivedPullback (pullback.fst f g)).obj M)),
            (schemeDerivedDirectImage (pullback.snd f g)).obj
              ((derivedPullback (pullback.fst f g)).obj N)))
          (Y := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M)),
            (schemeDerivedDirectImage (pullback.snd f g)).obj
              ((derivedPullback (pullback.fst f g)).obj N)))
          ((schemeDerivedBaseChangeMap f (pullback.snd f g) g
            (pullback.fst f g) pullback.condition M).op, 𝟙 _)) =
    mixedGlobalHomDirectImageMap f M N ≫
      mixedGlobalHomPullbackComparison g
        ((schemeDerivedDirectImage f).obj M) ((schemeDerivedDirectImage f).obj N) ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeGlobalDerivedHom Y').map
          ((𝟙 _).op, schemeDerivedBaseChangeMap f (pullback.snd f g) g
            (pullback.fst f g) pullback.condition N)) := by
  let H := fun Z : Scheme.{u} ↦
    derivedInternalHom (Opens.grothendieckTopology Z) Z.sheaf
  let c := fun {S T : Scheme.{u}} (h : T ⟶ S) ↦
    mixedHomDirectImageComparison h
  let p := fun {S T : Scheme.{u}} (h : T ⟶ S) (P Q : schemeDerivedCategory S) ↦
    ((schemeDerivedTensorHomEquiv T)
      ((derivedPullback h).obj
        ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q)))
      ((derivedPullback h).obj P) ((derivedPullback h).obj Q)).symm
        ((mixedHomTensorPullbackIso h).inv.app
          ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q), P) ≫
          (derivedPullback h).map
            ((schemeDerivedTensorHomEquiv S)
              ((derivedInternalHom (Opens.grothendieckTopology S) S.sheaf).obj (op P, Q))
              P Q (𝟙 _)))
  let E := (H X).obj (op M, N)
  let E' := (H (pullback f g)).obj
    (op ((derivedPullback (pullback.fst f g)).obj M),
      (derivedPullback (pullback.fst f g)).obj N)
  let a := p (pullback.fst f g) M N
  let b₁ := (H Y').map
      (X := (op ((schemeDerivedDirectImage (pullback.snd f g)).obj
        ((derivedPullback (pullback.fst f g)).obj M)),
        (schemeDerivedDirectImage (pullback.snd f g)).obj
          ((derivedPullback (pullback.fst f g)).obj N)))
      (Y := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M)),
        (schemeDerivedDirectImage (pullback.snd f g)).obj
          ((derivedPullback (pullback.fst f g)).obj N)))
      ((schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition M).op, 𝟙 _)
  let b := (c (pullback.snd f g)).app
      (op ((derivedPullback (pullback.fst f g)).obj M),
        (derivedPullback (pullback.fst f g)).obj N) ≫ b₁
  let d := (H Y').map
    (X := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M)),
      (derivedPullback g).obj ((schemeDerivedDirectImage f).obj N)))
    (Y := (op ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M)),
      (schemeDerivedDirectImage (pullback.snd f g)).obj
        ((derivedPullback (pullback.fst f g)).obj N)))
    ((𝟙 ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj M))).op,
      schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition N)
  have hi := mixedInternalHom_baseChange_exchange f g M N
  change schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition E ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map a ≫ b =
    (derivedPullback g).map ((c f).app (op M, N)) ≫
      p g ((schemeDerivedDirectImage f).obj M) ((schemeDerivedDirectImage f).obj N) ≫ d
    at hi
  have hs := mixedGlobalSections_baseChange_mate f g E E' a
  have ht := globalMate_exchange (schemeHomPullbackAdjunction g)
    (schemeDerivedGlobalSections Y) (schemeDerivedGlobalSections Y')
    (schemeGlobalScalarRestriction g) (mixedGlobalSectionsDirectImageIso g)
    ((mixedGlobalSectionsDirectImageIso f).inv.app E) _
    (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition E ≫ (schemeDerivedDirectImage (pullback.snd f g)).map a)
    b ((c f).app (op M, N))
    (p g ((schemeDerivedDirectImage f).obj M) ((schemeDerivedDirectImage f).obj N))
    d hs (by simpa only [Category.assoc] using hi)
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  simpa only [schemeGlobalDerivedHom, mixedGlobalHomDirectImageMap,
    mixedGlobalHomPullbackComparison, Functor.comp_map, Functor.comp_obj,
    b, b₁, d, E, E', a, p, H, c, Functor.prod_obj, Functor.op_obj,
    Functor.map_comp, Category.assoc] using ht

end AlgebraicGeometry
