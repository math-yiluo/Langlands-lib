/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
import WeilConjectures.AlgebraicGeometry.DerivedTensorSymmetry
import WeilConjectures.AlgebraicGeometry.ProjectionFormulaLocality
import WeilConjectures.AlgebraicGeometry.QCqsDerivedProjectionMate
import WeilConjectures.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison

/-! # The derived qcqs projection isomorphism in fixed localizations

Source: Stacks Project, Tag 08EU, Lemma 36.22.1.
(blueprint: lem-pc-qcqs-derived-projection-iso-universes).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The qcqs projection formula for quasi-coherent derived objects.
Source: Stacks Project, Tag 08EU, Lemma 36.22.1.
(blueprint: lem-pc-qcqs-derived-projection-iso-universes).

Proof: use the derived pullback/direct-image adjunction and the K-flat tensor
comparison to form the canonical projection map. Its isomorphy is local on Y,
since the three derived operations commute with restriction to target opens.
On an affine target Spec A, fix E and consider those K for which this map is
invertible. Pullback and tensor preserve coproducts, and qcqs direct image preserves
coproducts on quasi-coherent objects; hence the class is closed under coproducts.
Exactness of these functors and compatibility of the canonical map with translation
make it closed under distinguished triangles. For every shift of A the projection
map is the unit and shift comparison and is invertible. The equivalence between
D(A) and D_QCoh(Spec A), and generation by the shifts of A, prove invertibility
for every K. Detect it on an affine cover of Y and take the associated isomorphism.
Perform the argument in standard localizations and transport along the unique
localization equivalences to the supplied source and target categories. The
K-flat tensor, derived pullback and K-injective direct-image comparisons identify
the transported objects with exactly the displayed objects. No Noetherianity,
coherence, support condition or bound is required. Zero factors and empty schemes
are included by the same unit, coproduct and restriction computations. -/
theorem nonempty_qcqs_derivedProjection_iso_universes
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (K : schemeDerivedCategory Y) (hK : schemeDerivedQCohProperty Y K) :
    Nonempty (((schemeDerivedDirectImage f).obj E) ⊗ K ≅
      (schemeDerivedDirectImage f).obj (E ⊗ (derivedPullback f).obj K)) := by
  classical
  obtain ⟨p⟩ := nonempty_derivedPullbackAdjunction f
  obtain ⟨m, _⟩ := exists_derivedPullbackMonoidalModel f
  let := m.toMonoidal
  let t := (Functor.Monoidal.μNatIso (derivedPullback f)).symm
  obtain ⟨sX, _⟩ := exists_schemeDerivedTensorSymmetry X
  obtain ⟨sY, _⟩ := exists_schemeDerivedTensorSymmetry Y
  let φ := p.homEquiv (K ⊗ (schemeDerivedDirectImage f).obj E)
    ((derivedPullback f).obj K ⊗ E)
      (t.hom.app (K, (schemeDerivedDirectImage f).obj E) ≫
        (𝟙 ((derivedPullback f).obj K) ⊗ₘ p.counit.app E))
  let ψ := (sY ((schemeDerivedDirectImage f).obj E) K).hom ≫ φ ≫
    (schemeDerivedDirectImage f).map (sX ((derivedPullback f).obj K) E).hom
  have hcover : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 := by
    intro y
    obtain ⟨U, hU, hy, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := y) (by trivial)
    exact ⟨⟨U, hU⟩, hy⟩
  have hψ : IsIso ψ := by
    apply (projectionFormula_isIso_iff_openCover f E K Y.affineOpens
      (fun U ↦ U.1) hcover ψ).mpr
    intro U
    let Z := (f ⁻¹ᵁ U.1).toScheme
    let g := f ∣_ U.1
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
    have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated g
    obtain ⟨q, s, N, L, ⟨a⟩⟩ :=
      exists_derivedProjectionMate_openRestriction_comparison f p t ⟨K, hK⟩ ⟨E, hE⟩
        U.1 Z g rfl HEq.rfl
    have hlocal := qcqsDerivedProjectionMate_isIso.{u, u} Z U.1.toScheme g q s N L
    have hφ : IsIso ((schemeOpenRestriction Y U.1).mapDerivedCategory.map φ) :=
      (Arrow.isIso_iff_isIso_of_isIso a.hom).mpr hlocal
    dsimp only [ψ]
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  exact ⟨asIso ψ⟩

end AlgebraicGeometry
