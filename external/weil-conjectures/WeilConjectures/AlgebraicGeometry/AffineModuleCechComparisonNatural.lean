/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.AlgebraicGeometry.ModuleCechComparisonIsoAffine
import WeilConjectures.AlgebraicGeometry.CechComparisonMapNaturality

/-! # Naturality of the affine-cover Čech comparison isomorphisms

Source: Stacks Project, Cohomology of Sheaves, Tag 01EQ; Cohomology of Schemes, Tag 01XD
(blueprint: lem-sc-cech-comparison-natural).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The canonical Čech comparison isomorphisms transport the map of cochains obtained by
applying a quasi-coherent module morphism componentwise to the induced cohomology map.
Source: Stacks 01EQ and 01XD (blueprint: lem-sc-cech-comparison-natural).
Proof:
1. By lem-sc-cech-comparison-map-naturality, lift the morphism to injective resolutions.
The resulting map of Čech double complexes commutes with both alpha and beta. Taking
cohomology and inverting H(alpha) gives the commuting comparison square.
2. By lem-sc-cech-comparison-map-iso-affine, affine-intersection acyclicity makes these
canonical comparisons the isomorphisms of lem-pc-cech-computes. Compose the square with
the inverse of the source comparison to obtain the displayed conjugation formula. -/
theorem moduleCechComparison_natural_affine (X : Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens)
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤) (F F' : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F']
    (φ : F ⟶ F') (p : ℕ) :
    ∃ (e : ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology p ≅
          (RingedSpace.moduleCohomology X.toRingedSpace p).obj F)
      (e' : ((CategoryTheory.cechComplexFunctor U).obj F'.presheafModuleCat).homology p ≅
          (RingedSpace.moduleCohomology X.toRingedSpace p).obj F'),
      IsModuleCechComparison U F p e.hom ∧
      IsModuleCechComparison U F' p e'.hom ∧
      e.inv ≫ HomologicalComplex.homologyMap ((CategoryTheory.cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map φ.val)) p ≫
          e'.hom =
        (RingedSpace.moduleCohomology X.toRingedSpace p).map φ := by
  classical
  obtain ⟨hexists, hnatural⟩ := (cechComparisonMapNaturality X U hcover).2 p
  choose c hc using hexists
  let cF := c F
  let cF' := c F'
  have hF : IsIso cF := moduleCechComparison_isIso_of_affine X U hU hcover F p cF (hc F)
  have hF' : IsIso cF' :=
    moduleCechComparison_isIso_of_affine X U hU hcover F' p cF' (hc F')
  let e : ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology p ≅
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F := asIso cF
  let e' : ((CategoryTheory.cechComplexFunctor U).obj F'.presheafModuleCat).homology p ≅
      (RingedSpace.moduleCohomology X.toRingedSpace p).obj F' := asIso cF'
  refine ⟨e, e', hc F, hc F', ?_⟩
  have hn := hnatural F F' φ cF cF' (hc F) (hc F')
  change inv cF ≫ _ ≫ cF' = _
  have hn' := congrArg (fun k => inv cF ≫ k) hn
  simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hn'

end AlgebraicGeometry.Scheme.Modules
