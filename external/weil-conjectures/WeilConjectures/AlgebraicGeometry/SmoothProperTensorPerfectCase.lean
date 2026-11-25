/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.AlgebraicGeometry.PerfectTensorHomDuality
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.SmoothProperTensorPerfectCaseData
import WeilConjectures.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore

/-! # Projection comparison for perfect complexes

Source: Stacks Project, Duality for Schemes, Tag 0A9T
(blueprint: lem-sc-smooth-proper-tensor-perfect-case).
-/

@[expose] public section

set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- The projection-formula mate `Lf^*K ⊗ c(𝒪_Y) → c(K)` is invertible for perfect `K`.
The displayed equation specifies the inverse of `pf` as the canonical projection map:
its pullback-adjoint is the inverse tensor comparison followed by the pullback counit.
Thus `pf.hom`, followed by the right-adjoint counit and the right unitor, has exactly
its prescribed mate under `Rf_* ⊣ c`. Full-subcategory morphisms are formed by `homMk`.

The existential witnesses are bookkeeping for restriction of `Rf_*` to quasi-coherent
objects, the quasi-coherence of the unit and the tensor source, and the derived pullback's
monoidal adjunction. They are conclusions, not additional geometric hypotheses. The
formula is stated for every choice of monoidal pullback and its adjunction: in particular
for their canonical K-flat constructions. These choices do not change invertibility.
Finite Tor dimension is stated directly using Tor of the actual stalk-map restriction
of scalars; the bound may depend on the point, but not on the test module.

Source: Stacks Project, Duality for Schemes, Tag 0A9T
(blueprint: lem-sc-smooth-proper-tensor-perfect-case).
Proof (the node's two steps):
1. Properness implies quasi-compactness and quasi-separatedness. The projection formula
   (lem-pc-projection-formula) gives `pf`; the displayed adjunction equation specifies
   its canonical direction. Composing with the counit at the unit gives the comparison.
   Restriction to quasi-coherent derived categories and the K-flat tensor construction
   give the bookkeeping witnesses.
2. By lem-pc-perfect-tensor-hom-duality, K has a dual Kdual, and Lf*K has dual Lf*Kdual.
   For every quasi-coherent E, use tensor-Hom duality on X, then Rf_* ⊣ c, then the
   projection formula for Kdual, then tensor-Hom duality on Y, then Rf_* ⊣ c again.
   This identifies Hom(E,Lf*K ⊗ c(O_Y)) naturally with Hom(E,c(K)). Naturality and the
   two adjunction counits identify the induced map with the displayed comparison.
   Yoneda makes that comparison invertible. Monoidal coherence and the triangle
   identities make the same argument independent of choices of presentation data. -/
theorem smoothProper_tensor_perfect_case
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hTor : ∀ x : X, ∃ n : ℕ,
      ∀ (M : ModuleCat.{u} (Y.presheaf.stalk (f x))) (i : ℕ), n < i →
        IsZero (((Tor' (ModuleCat.{u} (Y.presheaf.stalk (f x))) i).obj
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
            (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)))).obj M)) :
    ∃ (hRf : ∀ E : schemeDerivedQCohCategory X,
        schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
      (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
      (hTensor : ∀ (K : schemeDerivedQCohCategory Y) (E : schemeDerivedQCohCategory X),
        schemeDerivedQCohProperty X (((derivedPullback f).obj K.obj) ⊗ E.obj)),
      Nonempty (Functor.Monoidal (derivedPullback f)) ∧
      Nonempty (derivedPullback f ⊣ schemeDerivedDirectImage f) ∧
      ∀ (_ : Functor.Monoidal (derivedPullback f))
        (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
        (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
        (adj : (schemeDerivedQCohProperty Y).lift
          ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
        (K : schemeDerivedQCohCategory Y), Scheme.IsPerfect Y K.obj →
        ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback f) K.obj
              ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom)))  := by
  obtain ⟨hRf, hO, hTensor, ⟨hm⟩, ⟨ha⟩⟩ :=
    smoothProper_tensor_perfect_case_data f hTor
  refine ⟨hRf, hO, hTensor, ⟨hm⟩, ⟨ha⟩, ?_⟩
  exact smoothProper_tensor_perfect_case_core f hRf hO hTensor

end AlgebraicGeometry
