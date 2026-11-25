/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.AffineScheme

import WeilConjectures.AlgebraicGeometry.AffineBasisAcyclicSectionsPreservesHomology
import WeilConjectures.AlgebraicGeometry.AffineBasisKInjectiveSectionsPreservesHomology
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Epi part of affine-basis section resolution comparison

Source: Stacks Project, Tag 08C2, singleton cover; Tag 071B, compatible resolution tower.
(blueprint: lem-sc-affine-basis-sections-resolution-homology-epi).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option linter.unusedVariables false in
/-- The section resolution map induces a epimorphism on homology in each degree.
Source: Stacks Project, Tag 08C2, lemma-alternating-cech-complex-complex-ss,
and Tag 071B, lemma-K-injective.
(blueprint: lem-sc-affine-basis-sections-resolution-homology-epi).

Proof: Restrict to V, where affine opens form a basis including V itself. Restriction is
exact and preserves K-injectives, so i restricts to a K-injective resolution. On the
singleton cover of V the alternating Cech total complex is the ordinary section complex.
For each good truncation tau_ge(-m) of F, the terms above -m are the original terms and
the term in degree -m is a differential cokernel. The first two vanishing assumptions
therefore give the bounded-below Cech comparison on every truncation. The homology-sheaf
vanishing gives the compatible resolution tower of 071B with cohomological bound zero.
Sections commute with the inverse limit of this tower. In degree n the section complexes
of the good truncations eventually agree in degrees n-1, n and n+1; hence their degree-n
homology is eventually constant. The resolution-tower transition maps are degreewise
surjective, and the Milnor sequence with vanishing first derived limit identifies the
homology of its section limit with this stable homology. Naturality identifies the map
from F with the canonical resolution map. This proves the desired assertion for the
special tower resolution. Compare that resolution with J over F: K-injectivity gives
comparison maps whose compositions are homotopic to the identities, since both maps
from F are quasi-isomorphisms. Additive evaluation preserves homotopies, so the induced
homology maps agree with those of i. Injective module sheaves are flasque, so the
abelian-sheaf computation in 08C2 computes module-valued section cohomology; the exact
forgetful functor to abelian groups reflects the assertion. When V is empty all section
modules are zero, and the assertion follows as well.
Every cohomology class of the resolution section limit comes from the stable truncation
homology, and hence has a representative in the ordinary section complex. -/
theorem affineBasisSections_resolution_homology_epi
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    (F J : CochainComplex X.Modules ℤ) [J.IsKInjective]
    (i : F ⟶ J) [QuasiIso i]
    (hterms : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.X n).restrict W.ι).H (q + 1)))
    (hcokernels : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((cokernel (F.d (n - 1) n)).restrict W.ι).H (q + 1)))
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1))) (n : ℤ) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    Epi (HomologicalComplex.homologyMap
      ((S.mapHomologicalComplex (ComplexShape.up ℤ)).map i) n) := by
  clear hterms
  dsimp
  let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
  let : S.Additive := inferInstanceAs
    ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
  have hJ : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (r : ℤ) (q : ℕ),
      Subsingleton (((J.homology r).restrict W.ι).H (q + 1)) := by
    intro W hW hWV r q
    let := hhomology W hW hWV r q
    let e := (Scheme.Modules.restrictFunctor W.ι).mapIso
      (asIso (HomologicalComplex.homologyMap i r))
    exact (Scheme.Modules.H.mapLinearEquiv e (q + 1)).symm.injective.subsingleton
  let := affineBasisAcyclicSections_preservesLeftHomology X V hV F
    hcokernels hhomology n
  let := affineBasisKInjectiveSections_preservesLeftHomology X V hV J hJ n
  let φ := (HomologicalComplex.shortComplexFunctor X.Modules (.up ℤ) n).map i
  change Epi (ShortComplex.homologyMap (S.mapShortComplex.map φ))
  have : IsIso (ShortComplex.homologyMap φ) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap i n))
  have h := ShortComplex.mapHomologyIso_hom_naturality φ S
  have : IsIso (ShortComplex.homologyMap (S.mapShortComplex.map φ) ≫
      ((J.sc n).mapHomologyIso S).hom) := by
    rw [h]
    infer_instance
  have : IsIso (ShortComplex.homologyMap (S.mapShortComplex.map φ)) :=
    IsIso.of_isIso_comp_right _ ((J.sc n).mapHomologyIso S).hom
  infer_instance

end AlgebraicGeometry
