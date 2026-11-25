/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # SchemeDerivedMateEvaluation

Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-scheme-derived-mate-evaluation).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

private theorem evaluation {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {M : C} {N : D}
    (t : F.obj M ⟶ N) : F.map (adj.homEquiv M N t) ≫ adj.counit.app N = t :=
  (adj.homEquiv M N).symm_apply_apply t

private theorem evaluation_factors {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {M : C} {N P Q Z : D}
    (a : F.obj M ⟶ P) (b : P ⟶ Q) (c : Q ⟶ Z) (d : Z ⟶ N)
    (beta : M ⟶ G.obj N) (hbeta : beta = adj.homEquiv M N (a ≫ b ≫ c ≫ d)) :
    F.map beta ≫ adj.counit.app N = (a ≫ b ≫ c) ≫ d := by
  rw [hbeta]
  simpa only [Category.assoc] using evaluation adj (a ≫ b ≫ c ≫ d)

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The adjunction choice already used by `schemeDerivedBaseChangeMap`, pinned to the
selected left-derived counit and the recorded right-derived unit.
Source: Stacks Project, Tag 08HY.
(blueprint: lem-pc-scheme-derived-mate-evaluation). -/
noncomputable def canonicalSchemeDerivedAdjunction {P Q : Scheme.{u}} (k : P ⟶ Q) :
    derivedPullback k ⊣ schemeDerivedDirectImage k :=
  Classical.choose (exists_schemeDerivedAdjunction k
    (hAdd := (Classical.choose exists_derivedPullbackComposition) k)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) k))

/-- The composition choice already used by `schemeDerivedBaseChangeMap`, determined
by the left-derived universal property in `exists_derivedPullbackComposition`.
Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-scheme-derived-mate-evaluation). -/
noncomputable def canonicalDerivedPullbackComposition {P Q Z : Scheme.{u}}
    (k : P ⟶ Q) (l : Q ⟶ Z) :
    derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
  (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) k l

/-- The square comparison already used in the defining transpose of base change.
Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-scheme-derived-mate-evaluation). -/
noncomputable def canonicalDerivedSquareComparison {P Q P' Q' : Scheme.{u}}
    (l : P ⟶ Q) (l' : P' ⟶ Q') (r : Q' ⟶ Q) (r' : P' ⟶ P)
    (hh : r' ≫ l = l' ≫ r) (M : schemeDerivedCategory Q) :
    (derivedPullback l').obj ((derivedPullback r).obj M) ⟶
      (derivedPullback r').obj ((derivedPullback l).obj M) :=
  (canonicalDerivedPullbackComposition l' r).hom.app M ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj M) hh.symm) ≫
      (canonicalDerivedPullbackComposition r' l).inv.app M

/-- Evaluating the counit-defined mate recovers its defining transpose.
Proof: unfold the mate, apply the inverse-forward identity for the pinned
adjunction Hom equivalence, and reassociate the defining square comparison.
Source: Stacks Project, Tag 08HY.
(blueprint: lem-pc-scheme-derived-mate-evaluation). -/
theorem schemeDerivedMate_evaluation
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (K : schemeDerivedCategory X) :
  (derivedPullback f').map (schemeDerivedBaseChangeMap f f' g g' h K) ≫
      (canonicalSchemeDerivedAdjunction f').counit.app ((derivedPullback g').obj K) =
    canonicalDerivedSquareComparison f f' g g' h ((schemeDerivedDirectImage f).obj K) ≫
      (derivedPullback g').map ((canonicalSchemeDerivedAdjunction f).counit.app K) := by
  delta canonicalDerivedSquareComparison
  exact evaluation_factors (canonicalSchemeDerivedAdjunction f')
    ((canonicalDerivedPullbackComposition f' g).hom.app
      ((schemeDerivedDirectImage f).obj K))
    (eqToHom (congrArg (fun k ↦
      (derivedPullback k).obj ((schemeDerivedDirectImage f).obj K)) h.symm))
    ((canonicalDerivedPullbackComposition g' f).inv.app
      ((schemeDerivedDirectImage f).obj K))
    ((derivedPullback g').map ((canonicalSchemeDerivedAdjunction f).counit.app K))
    (schemeDerivedBaseChangeMap f f' g g' h K) rfl

end AlgebraicGeometry
