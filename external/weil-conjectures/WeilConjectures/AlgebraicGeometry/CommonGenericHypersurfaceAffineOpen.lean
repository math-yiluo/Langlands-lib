/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.MvPolynomial.Basic

import WeilConjectures.AlgebraicGeometry.GenericFibreBirationalHypersurfaceModel
import WeilConjectures.AlgebraicGeometry.GenericFibrePartialIsoSpreadOpen

/-! # A common affine open with a generic hypersurface model

Source: Stacks Project, Tag 0559, first proof, and Tag 0552.
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A generically geometrically integral affine family has a common affine open
with a hypersurface over its original base. The generic fibre of this open is
nonempty. No assertion about special fibres is made here.

Source: Stacks Project, Tag 0559, first proof, the separating transcendence basis
and common-open construction; Tag 0552, birational finite type schemes.
Proof: Apply the generic-fibre birational hypersurface model theorem to obtain
P over Gamma(S, O_S), a geometrically integral generic hypersurface, and a partial
isomorphism of the two generic fibres over kappa(eta). The hypersurface map is
locally of finite presentation: a polynomial algebra in finitely many variables
is finitely presented, and quotienting by one equation preserves finite
presentation. Geometric irreducibility makes the source generic fibre nonempty.
Apply the generic-fibre partial-isomorphism spreading theorem to obtain an open
V in X meeting the generic fibre and an open immersion V -> H over S. Choose a
point v in V above eta and an affine open neighbourhood W of v contained in V.
Compose W -> V with V -> H. The composite is an open immersion over S, and v
witnesses that eta is in the image of W -> S. Retain the geometric properties
of the hypersurface generic fibre supplied by the model theorem.

(blueprint: lem-sbc-common-generic-hypersurface-affine-open) -/
theorem exists_common_generic_hypersurface_affine_open
    {X S : Scheme.{u}} [IsAffine X] [IsReduced X] [IsAffine S] [IsIntegral S]
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (hred : GeometricallyReduced (f.fiberToSpecResidueField η)) :
    ∃ W : X.Opens, IsAffineOpen W ∧ η ∈ Set.range (W.ι ≫ f) ∧
      ∃ (n : ℕ) (P : MvPolynomial (Fin n) Γ(S, ⊤)),
        let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
        let g : H ⟶ S := Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
        ∃ i : W.toScheme ⟶ H, IsOpenImmersion i ∧ i ≫ g = W.ι ≫ f ∧
          GeometricallyIrreducible (g.fiberToSpecResidueField η) ∧
          GeometricallyReduced (g.fiberToSpecResidueField η) := by
  obtain ⟨n, P, hgeomH, hredH, p, hp⟩ :=
    exists_generic_fibre_birational_hypersurface_model f η hη hgeom hred
  let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
  let g : H ⟶ S := Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
  have hg : LocallyOfFinitePresentation g := by
    have hfp : Algebra.FinitePresentation Γ(S, ⊤)
        (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton P)
    have hspec : LocallyOfFinitePresentation
        (Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C))) := by
      rw [LocallyOfFinitePresentation.SpecMap_iff]
      exact RingHom.finitePresentation_algebraMap.mpr hfp
    infer_instance
  have := hgeom
  have : IrreducibleSpace (f.fiber η) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (f := f.fiberToSpecResidueField η)
  obtain ⟨V, hηV, i, hi, hif⟩ := exists_open_of_generic_fibre_partial_iso f g η hη p hp
  obtain ⟨v, hv⟩ := hηV
  obtain ⟨W, hW, hvW, hWV⟩ := exists_isAffineOpen_mem_and_subset v.property
  let j : W.toScheme ⟶ V.toScheme := X.homOfLE hWV
  have := hi
  refine ⟨W, hW, ?_, n, P, j ≫ i, inferInstance, ?_, hgeomH, hredH⟩
  · refine ⟨⟨v.val, hvW⟩, ?_⟩
    exact hv
  · change (j ≫ i) ≫ g = W.ι ≫ f
    rw [Category.assoc, hif, ← Category.assoc, X.homOfLE_ι hWV]

end AlgebraicGeometry
