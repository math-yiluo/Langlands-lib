/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.UniformFiniteFilteredLocalization
public import WeilConjectures.CategoryTheory.UniformFilteredHomotopy
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Quotient
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Abelian.Filtration
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.Algebra.Homology.FlatCoverFunctor
import WeilConjectures.Algebra.Homology.CyclePullbackResolution
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.KFlatTelescopeClosure
import WeilConjectures.CategoryTheory.Right.RightFractionDenseSubcategory
import WeilConjectures.CategoryTheory.UniformFilteredHomotopy
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-! # Split flat models with a fixed finite filtration

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/
sec-additivity-of-trace-classes/sk-i-additivity/sk-i-additivity.proof.md,
Filtered operations, paragraphs 1–3
(blueprint: lem-trf-finite-filtered-flat-model).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe uC vC w

namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})

/-- The module sheaves over the coefficient sheaf on the given site.
Source: blueprint sk-i-additivity.proof.md, Filtered operations, coefficient category
(blueprint: lem-trf-finite-filtered-flat-model). -/
abbrev finiteFilteredModules (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} ((sheafCompose J
    (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

/-- Cochain complexes of the module sheaves, with the coefficient universe explicit.
Source: blueprint sk-i-additivity.proof.md, Filtered operations, complexes
(blueprint: lem-trf-finite-filtered-flat-model). -/
abbrev finiteFilteredComplex (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{w}) :=
  CochainComplex (finiteFilteredModules J R) ℤ

/-- The split-flat and K-flat hypotheses used for a resolving filtered complex.
Splitting is imposed on module-sheaf maps in each degree, not on chain maps.
For a finite filtration the successor inclusions split exactly when the whole
filtration is degreewise a sum of its graded pieces.
Source: blueprint sk-i-additivity.proof.md, Filtered operations, flat resolutions
(blueprint: lem-trf-finite-filtered-flat-model). -/
def IsSplitFlatFiltered
    (K : WeilFilteredObject (finiteFilteredComplex J R)) : Prop :=
  (∀ p n : ℤ,
    IsSplitMono ((Subobject.ofLE (K.filtration.F (p + 1)) (K.filtration.F p)
      (K.filtration.F_succ_le p)).f n)) ∧
  (∀ p n : ℤ,
    SheafOfModules.IsFlatOnSite.{uC, vC, w, w} (J := J) (R := R)
      ((K.filtration.gradedPiece p).X n)) ∧
  CochainComplex.IsKFlatIndependentCoefficients (R := R) K.obj ∧
  (∀ p : ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      (K.filtration.F p : finiteFilteredComplex J R) ∧
      CochainComplex.IsKFlatIndependentCoefficients (R := R) (K.filtration.gradedPiece p))

/-- The split-flat property on objects of the actual filtered homotopy category.
The homotopy quotient has the same objects as the complex category. Its full
subcategory on these objects is the homotopy category of split-flat complexes.
Source: blueprint sk-i-additivity.proof.md, Filtered operations, resolving models
(blueprint: lem-trf-finite-filtered-flat-model). -/
def finiteFilteredSplitFlatProperty (a b : ℤ) :
    ObjectProperty (UniformFilteredHomotopyCategory (finiteFilteredModules J R)
      (some (a, b)) (CochainComplex.minus (finiteFilteredModules J R))) :=
  fun K => IsSplitFlatFiltered (J := J) R K.as.obj

/-- The canonical localization functor induced by the split-flat inclusion.
This is the localization lift of the inclusion of actual filtered homotopy
categories, at graded quasi-isomorphisms on both sides.
Source: blueprint sk-i-additivity.proof.md, Filtered operations, deriving tensor
(blueprint: lem-trf-finite-filtered-flat-model). -/
def finiteFilteredLocalizationComparison (a b : ℤ) :
    ((uniformFilteredHomotopyQuasiIso (some (a, b))
      (CochainComplex.minus (finiteFilteredModules J R))).inverseImage
        (finiteFilteredSplitFlatProperty (J := J) R a b).ι).Localization ⥤
    (uniformFilteredHomotopyQuasiIso (some (a, b))
      (CochainComplex.minus (finiteFilteredModules J R))).Localization :=
  Localization.Construction.lift
    ((finiteFilteredSplitFlatProperty (J := J) R a b).ι ⋙
      (uniformFilteredHomotopyQuasiIso (some (a, b))
        (CochainComplex.minus (finiteFilteredModules J R))).Q)
    (fun _ _ f hf =>
      (uniformFilteredHomotopyQuasiIso (some (a, b))
        (CochainComplex.minus (finiteFilteredModules J R))).Q_inverts
        ((finiteFilteredSplitFlatProperty (J := J) R a b).ι.map f) hf)

/-- The sum of the images defining the convolution filtration at weight `r`.
The image of the coproduct map is the sum of the images. Indexing by `p`
with second index `r-p` is exactly the condition `p+q=r`.
Source: blueprint sk-i-additivity.proof.md, Filtered operations, convolution tensor
(blueprint: lem-trf-finite-filtered-flat-model). -/
def finiteFilteredConvolutionStep
    (P Q : WeilFilteredObject (finiteFilteredComplex J R)) (r : ℤ) :
    Subobject (HomologicalComplex.tensorObj P.obj Q.obj) :=
  imageSubobject (Sigma.desc (fun p : ℤ =>
    HomologicalComplex.tensorHom (P.filtration.F p).arrow
      (Q.filtration.F (r - p)).arrow))

/--
Every bounded-above fixed-interval filtered complex admits a split-flat model,
the corresponding localized filtered homotopy categories are equivalent, and
ordinary total tensor with the model preserves graded quasi-isomorphisms for any
uniformly finite filtration on the right.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/
sec-additivity-of-trace-classes/sk-i-additivity/sk-i-additivity.proof.md,
Filtered operations, paragraphs 1–3
(blueprint: lem-trf-finite-filtered-flat-model).

Proof:
1. Induct downwards from `b+1` to `a`. Resolve the bounded-above cone of the
   already constructed `P_(p+1) → F^p M` by a flat complex `G_p`, using
   lem-pc-sites-modules-functorial-flat-cover,
   lem-pc-functorial-cycle-pullback-construction, and
   lem-pc-kflat-bounded-flat-replacement. The map from this cone to `gr^p M`
   is a quasi-isomorphism since the previously constructed filtered map is a
   quasi-isomorphism on its finitely many grades. Decompose the replacement
   map into `g_p : G_p → F^p M` in degree zero and
   `h_p : G_p → P_(p+1)[1]`. With cone differential `(d,u;0,-d)`, they satisfy
   `d h_p + h_p d = 0` and `d g_p - g_p d = -u h_p`.
   The negatives of the components of `h_p` give the twisting maps. Their
   Maurer--Cartan identities make `G_p ⊕ P_(p+1)` a complex with a split
   filtration (lem-trf-filtered-mapping-cylinder-step); `(g_p,f_(p+1))` is
   its augmentation. Its grade `p` is the replacement of the cone followed
   by the quasi-isomorphism to `gr^p M`, and the higher graded maps are the
   old ones. Finite direct sums keep the common upper cochain bound.
   The total complex, its steps and grades have flat terms and are K-flat
   by lem-pc-bounded-above-flat-kflat-site and lem-pc-kflat-closure.
2. In the actual filtered homotopy category use the right calculus from
   lem-trf-uniform-filtered-homotopy-calculus. Step 1 supplies a denominator
   from the full split-flat subcategory into every object. Apply
   lem-trf-right-fraction-dense-subcategory to the canonical inclusion and
   the two localizations. Its right-roof argument gives the equivalence
   of the canonical localization lift used here, including faithfulness.
3. The convolution graded quotient is naturally the finite sum of
   `gr^p P ⊗ gr^q Q` for `p+q=r`
   (lem-trf-filtered-convolution-graded-quotient). Each grade of `P` is
   K-flat. The cone of each graded map on `Q` is acyclic, and tensoring it
   with `gr^p P` remains acyclic. Tensor commutes with cones, so each
   summand map is a quasi-isomorphism; finite sums preserve this property.
4. The two filtration intervals make the convolution finite even when
   `Q` is unbounded in cochain degree. Inclusions induce the ordinary
   total-tensor map, and the quotient identification respects the signed
   total differential. Filtration weights introduce no additional signs.
-/
theorem finiteFilteredFlatModel
    (a b : ℤ) (hab : a ≤ b)
    (M : UniformFilteredComplexes (finiteFilteredModules J R) (some (a, b))
      (CochainComplex.minus (finiteFilteredModules J R))) :
    (∃ K : UniformFilteredComplexes (finiteFilteredModules J R) (some (a, b))
        (CochainComplex.minus (finiteFilteredModules J R)),
      IsSplitFlatFiltered (J := J) R K.obj ∧
      ∃ f : K.obj ⟶ M.obj,
        (∀ p : ℤ, QuasiIso (WeilFilteredObject.gradedMapSteps f p))) ∧
    (finiteFilteredLocalizationComparison (J := J) R a b).IsEquivalence ∧
    (∀ (P : UniformFilteredComplexes (finiteFilteredModules J R) (some (a, b))
          (CochainComplex.minus (finiteFilteredModules J R))),
      IsSplitFlatFiltered (J := J) R P.obj →
      ∀ {Q Q' : WeilFilteredObject (finiteFilteredComplex J R)},
        Q.filtration.IsFinite → Q'.filtration.IsFinite →
        ∀ g : Q ⟶ Q',
          (∀ p : ℤ, QuasiIso (WeilFilteredObject.gradedMapSteps g p)) →
          ∃ (FT : DecreasingFiltration (HomologicalComplex.tensorObj P.obj.obj Q.obj))
            (FT' : DecreasingFiltration (HomologicalComplex.tensorObj P.obj.obj Q'.obj))
            (t : (⟨HomologicalComplex.tensorObj P.obj.obj Q.obj, FT⟩ :
                WeilFilteredObject (finiteFilteredComplex J R)) ⟶
              ⟨HomologicalComplex.tensorObj P.obj.obj Q'.obj, FT'⟩),
            (∀ r : ℤ, FT.F r = finiteFilteredConvolutionStep (J := J) R P.obj Q r) ∧
            (∀ r : ℤ, FT'.F r = finiteFilteredConvolutionStep (J := J) R P.obj Q' r) ∧
            FT.IsFinite ∧ FT'.IsFinite ∧
            t.hom = HomologicalComplex.tensorHom (𝟙 P.obj.obj) g.hom ∧
            (∀ r : ℤ, QuasiIso (WeilFilteredObject.gradedMapSteps t r))) := by
  sorry

end CategoryTheory
