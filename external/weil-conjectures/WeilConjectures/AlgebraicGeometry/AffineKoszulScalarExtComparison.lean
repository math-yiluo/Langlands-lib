/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.RingTheory.KoszulDualComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.RingTheory.KoszulRegularSequenceDualComplex
import WeilConjectures.AlgebraicGeometry.LocalFiniteFreeScalarHomology
import WeilConjectures.AlgebraicGeometry.AffineKoszulFiniteFreeResolution
import WeilConjectures.AlgebraicGeometry.AffineKoszulHomCoordinates

/-! # Affine scalar Ext and dual Koszul cohomology

Source: Stacks Project, Tag 0BQZ, local finite free Hom computation.
(blueprint: lem-sc-affine-koszul-scalar-ext-comparison). -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Restriction of scalar Ext to an affine Koszul chart is the associated sheaf
of the cohomology of the integer-indexed dual Koszul complex.

Source: Stacks Project, Tag 0BQZ, proof of Lemma 48.15.5, the displayed finite
free Hom computation; Tag 08DM, Lemma 20.46.9.
(blueprint: lem-sc-affine-koszul-scalar-ext-comparison).

Proof: Put A = O_Y(U) and I = i.ker.ideal U. The closed immersion identifies
its inverse image over U with Spec(A/I) over Spec(A). Koszul regularity makes
the quotient augmentation a quasi-isomorphism. Exact associated-module
sheafification and transport along U.isoSpec sheafify this augmentation to a
resolution of the restricted i_* O_Z, by the affine quotient resolution lemma.
The terms are finite free exterior powers and vanish above the sequence length;
extension to integer cochain degrees makes a bounded finite free resolution.
Restrict derived internal Hom to U, and use the bounded finite free Hom model
into O_U in degree zero. In finite free coordinates, sheaf Hom into O_U is the
associated sheaf of module Hom into A. These coordinate maps commute with
localization on standard opens, with the Koszul differentials, and hence glue
to an isomorphism of complexes with the sheafified dual Koszul complex.
In degree k >= 0, only the target degree-zero term contributes, and the Hom
differential is (-1)^(k+1) times precomposition with the Koszul boundary; this
is exactly koszulDualBoundary. Negative degrees have zero terms.
Associated sheafification and open restriction are exact, so their homology
is the associated sheaf of the module homology. The equivalence between the
over-U module site and U.toScheme.Modules gives the stated form.
For an arbitrary supplied derived universe compute both representations using
the same K-injective Hom complex in the standard derived universe and transport
its homology comparison. Thus no derived-category instance on U in universe w
is assumed. Empty sequences give the degree-zero structure sheaf; an empty
chart gives the zero sheaf category. There is no rank or degree exclusion here,
and no tensor pullback or derived base-change assertion. -/
theorem affine_koszul_scalar_ext_comparison
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (U : Y.affineOpens) (n : ℕ) (f : Fin n → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (q : ℤ) :
    let F : Y.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf)))
    Nonempty (F.over U.1 ≅
      (Scheme.Modules.overEquiv U.1).inverse.obj
        ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj
          ((ExteriorAlgebra.koszulDualCochainComplex (Γ(Y, U.1) : Type u) n f).homology q)))
    := by
  obtain ⟨ε, hε, _⟩ := ExteriorAlgebra.exists_koszul_quotient_augmentation
    (Γ(Y, U.1) : Type u) (i.ker.ideal U) n f hreg hf
  let := hε
  obtain ⟨hbounded, hfree, a, ha⟩ :=
    affine_koszul_finite_free_resolution i U n f ε
  let := ha
  obtain ⟨e⟩ := local_finite_free_scalar_homology U.1
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    _ hbounded hfree a q
  obtain ⟨c⟩ := affine_koszul_hom_coordinates U n f q
  exact ⟨e ≪≫ (Scheme.Modules.overEquiv U.1).inverse.mapIso c⟩

end AlgebraicGeometry
