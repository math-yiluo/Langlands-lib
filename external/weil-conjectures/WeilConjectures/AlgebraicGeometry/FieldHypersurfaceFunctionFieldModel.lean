/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import WeilConjectures.AlgebraicGeometry.FieldHypersurfaceIntegralPresentation
import WeilConjectures.AlgebraicGeometry.FieldFractionRingGeometricIntegrality

/-! # Hypersurface function-field presentation over a field

Source: Stacks Project, Tag 0559, first proof, separating generators and minimal polynomial.
(blueprint: lem-sbc-field-hypersurface-function-field-model)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A geometrically integral affine scheme of finite type over a field has the function
field of a geometrically integral hypersurface over that field.

Source: Stacks Project, Tag 0559, first proof, paragraphs beginning with the generic
point and the separating generators.
Proof: The affine section algebra is a finitely generated geometrically integral
K-algebra, so its fraction field L is finitely generated and separably generated over K.
Choose a separating transcendence basis and a primitive element for the remaining finite
separable extension. Take the primitive numerator Q of its minimal polynomial. Gauss's
lemma identifies the quotient with a subalgebra of L having fraction field L. After any
field extension, the same injection into the localization of the geometrically integral
section algebra shows that the quotient is still a domain. Its spectrum is therefore
geometrically irreducible and reduced, and both schemes are integral. A finite polynomial
algebra and its principal quotient are finitely presented, giving local finite type.
The two inclusions in L induce the fraction-ring equivalence, and both fix K; composing
with the canonical global-section identification of Spec K gives the displayed equality.
When L is purely transcendental use one extra variable with equation T; this includes L=K.

(blueprint: lem-sbc-field-hypersurface-function-field-model) -/
theorem exists_field_hypersurface_function_field_model
    {K : Type u} [Field K] {Y : Scheme.{u}} [IsAffine Y]
    (p : Y ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (hgeom : GeometricallyIrreducible p) (hred : GeometricallyReduced p) :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin n) K),
      let Z := Spec (.of (MvPolynomial (Fin n) K ⧸ Ideal.span {Q}))
      let q : Z ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {Q})).comp MvPolynomial.C))
      GeometricallyIrreducible q ∧ GeometricallyReduced q ∧
        ∃ e : FractionRing Γ(Y, ⊤) ≃+* FractionRing Γ(Z, ⊤),
          ∀ a : Γ(Spec (.of K), ⊤),
            e (algebraMap Γ(Y, ⊤) (FractionRing Γ(Y, ⊤)) (p.appTop.hom a)) =
              algebraMap Γ(Z, ⊤) (FractionRing Γ(Z, ⊤)) (q.appTop.hom a) := by
  have : GeometricallyIrreducible p := hgeom
  have : GeometricallyReduced p := hred
  have : IrreducibleSpace Y := GeometricallyIrreducible.irreducibleSpace_of_subsingleton p
  have : IsReduced Y := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian p
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  obtain ⟨n, Q, hZ, e, he⟩ := exists_integral_field_hypersurface_presentation p hred
  let Z := Spec (.of (MvPolynomial (Fin n) K ⧸ Ideal.span {Q}))
  let q : Z ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span {Q})).comp MvPolynomial.C))
  have : IsIntegral Z := hZ
  obtain ⟨hgeomZ, hredZ⟩ := geometrically_integral_of_fractionRing_equiv p q hgeom hred e he
  exact ⟨n, Q, hgeomZ, hredZ, e, he⟩

end AlgebraicGeometry
