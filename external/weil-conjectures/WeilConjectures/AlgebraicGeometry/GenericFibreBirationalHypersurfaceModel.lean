/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.MvPolynomial.Basic

import WeilConjectures.AlgebraicGeometry.GenericFibreHypersurfaceFunctionFieldModel
import WeilConjectures.AlgebraicGeometry.AffineBirationalOfFractionRingEquiv

/-! # A birational hypersurface model of a geometrically integral generic fibre

Source: Stacks Project, Tag 0559, first proof, field generators and polynomial numerator;
Tag 0552, the function-field criterion for birationality.
(blueprint: lem-sbc-generic-fibre-birational-hypersurface-model)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- The generic fibre, without any spreading of its common opens, has a birational
geometrically integral hypersurface model whose equation has coefficients on the base.

Source: Stacks Project, Tag 0559, first proof, the paragraphs beginning with the generic
point of the generic fibre and ending with the polynomial quotient; Tag 0552.
Proof: Put A = Gamma(S, O_S) and K = kappa(eta) = Frac(A). The affine generic fibre
has a finitely generated geometrically integral K-algebra B. Its fraction field L
is separably generated over K and remains a domain after extension to an algebraic
closure of K. A separating transcendence basis t_1,...,t_r and a primitive element z
present L as the fraction field of K[t_1,...,t_r,T]/(Q), where Q is the primitive
numerator of the minimal polynomial of z. Gauss's lemma and geometric integrality
of L show that Q stays irreducible over an algebraic closure, and the resulting
hypersurface is geometrically integral. Clear the finitely many coefficient
denominators in K = Frac(A) by a nonzero scalar from A, obtaining P over A. This
scalar is a unit on the generic fibre, so it does not change the generic quotient.
The two generic integral affine schemes have isomorphic function fields over K;
express the finite sets of algebra generators as fractions in L and invert their
nonzero denominators to obtain isomorphic dense opens over K (Tag 0552).
These opens give the required generic-fibre partial isomorphism. The case of a
purely transcendental L uses Q = T in one additional variable, including L = K.
No flatness or reducedness away from the generic fibre is required.

(blueprint: lem-sbc-generic-fibre-birational-hypersurface-model) -/
theorem exists_generic_fibre_birational_hypersurface_model
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (hred : GeometricallyReduced (f.fiberToSpecResidueField η)) :
    ∃ (n : ℕ) (P : MvPolynomial (Fin n) Γ(S, ⊤)),
      let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
      let g : H ⟶ S := Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
      GeometricallyIrreducible (g.fiberToSpecResidueField η) ∧
        GeometricallyReduced (g.fiberToSpecResidueField η) ∧
        Scheme.BirationalOver (f.fiberToSpecResidueField η)
          (g.fiberToSpecResidueField η) := by
  obtain ⟨n, P, hgeomH, hredH, hX, hH, hft, e, he⟩ :=
    exists_generic_fibre_hypersurface_function_field_model f η hη hgeom hred
  let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
  let g : H ⟶ S := Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
  have : IsIntegral (f.fiber η) := hX
  have : IsIntegral (g.fiber η) := hH
  have : LocallyOfFiniteType (g.fiberToSpecResidueField η) := hft
  have : LocallyOfFiniteType (f.fiberToSpecResidueField η) :=
    show LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField η)) from
      inferInstance
  refine ⟨n, P, hgeomH, hredH, ?_⟩
  exact birationalOver_of_fractionRing_equiv
    (f.fiberToSpecResidueField η) (g.fiberToSpecResidueField η) e he

end AlgebraicGeometry
