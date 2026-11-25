/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionTransfer
public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison

/-!
# Canonical comparison specified on resolution cocycles

Source: Stacks Project, Tags 0A50 and 03F3, and the Ext/injective-resolution comparison.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Comparison equivalences with their normalization on representing cocycles.
The normalization uses the independently constructed `InjectiveResolution.extMk` and
`etaleOpenObjectCohomologyMap`; it asserts no restriction or transfer identity.
Source: Stacks Project, Tag 0A50 (resolution sections), Tag 03F3 (localization).
(blueprint: def-weil-pbc-etale-resolution-section-canonical-comparison) -/
structure ResolutionSectionCanonicalComparison {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G) where
  globalEquiv : ∀ q : ℕ,
    (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).homology q ≃+ Sheaf.H G q
  openEquiv : ∀ (W : X.Opens) (q : ℕ),
    (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).homology q ≃+
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj G) q
  global_cocycle : ∀ (q : ℕ)
    (f : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ I.cocomplex.X q)
    (hf : f ≫ I.cocomplex.d q (q + 1) = 0)
    (z : (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).cycles q),
    ((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).iCycles q) z =
      (((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (MorphismProperty.Over.mkIdTerminal @Etale X)).homAddEquiv _
          (I.cocomplex.X q)).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)) f →
    globalEquiv q (((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).homologyπ q) z) = I.extMk f (q + 1) rfl hf
  open_cocycle : ∀ (W : X.Opens) (q : ℕ)
    (f : (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι) ⟶ I.cocomplex.X q)
    (hf : f ≫ I.cocomplex.d q (q + 1) = 0)
    (z : (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).cycles q),
    ((((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).iCycles q) z =
      EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk W.ι)
        (I.cocomplex.X q) f →
    openEquiv W q (((((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).homologyπ q) z) =
        etaleOpenObjectCohomologyMap G q W (I.extMk f (q + 1) rfl hf)

end AlgebraicGeometry.Etale
