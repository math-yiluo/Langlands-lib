/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.FieldTheory.Finite.UniqueSubfieldOfClosure
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiber

/-!
# Global finite-field datum and geometric base change

Source: Weil conjectures blueprint, `chap-Nagata-compactification-and-Chows-lemma`,
`sk-prop-nagata-sketch-comp-category/def-weil-finite-field-fiber.md`, order 411
(blueprint: def-weil-finite-field-fiber).

The global datum permits any field with the specified cardinality and any fixed algebraic
closure. Its inclusion is `algebraMap D.k₀ D.k`. Closed points and residue fields use the
existing `closedPoints S` and `S.residueField s`, without new definitions.

For a finite-type object `Y₀` over `Spec D.k₀`, `D.geometricFiber Y₀` is the geometric
base change as an object over `Spec D.k`; its `.hom` is the structure morphism `a_Y`.
`D.extensionPoints Y₀ n hn` and `D.pointCount Y₀ n hn` give the extension-valued points
and their number. Finiteness of the point set is a separate theorem, not assumed here.

For a prime `l` distinct from `D.p`, the coefficient conventions reuse `Padic l`,
`PadicInt l`, and a field `Qbar` with `[Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]`;
`AlgebraicClosure (Padic l)` is one possible fixed choice. For every finite-dimensional
extension `E` the ring, chosen uniformizer and quotients are exactly
`Padic.coefficientExtensionIntegers l E`, `Padic.coefficientExtensionUniformizer l E`,
and `Padic.coefficientExtensionRing l E n`. These notions are not defined again here.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

attribute [instance] FiniteFieldDatum.field_base FiniteFieldDatum.finite_base
  FiniteFieldDatum.field_closure FiniteFieldDatum.algebra_closure FiniteFieldDatum.isAlgClosure

namespace FiniteFieldDatum

/-- `F_{q^n}` is the unique subfield supplied by the dependency theorem. Its uniqueness
fixes the data up to equality of subfields, even before that theorem is proved.
Source: blueprint order 411, `def-weil-finite-field-fiber.md`
(blueprint: def-weil-finite-field-fiber). -/
noncomputable def extensionSubfield (D : FiniteFieldDatum.{u}) (n : ℕ) (hn : 1 ≤ n) :
    Subfield D.k :=
  (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
    D.cardinality_eq D.k₀ D.card_base D.k n hn).choose

/-- The inclusion `k₀ → F_{q^n}` is the corestriction of the structure homomorphism.
The dependency specifies its composite with the injective subfield inclusion, so this
homomorphism is uniquely determined.
Source: blueprint order 411, `def-weil-finite-field-fiber.md`
(blueprint: def-weil-finite-field-fiber). -/
noncomputable def extensionEmbedding (D : FiniteFieldDatum.{u}) (n : ℕ) (hn : 1 ≤ n) :
    D.k₀ →+* D.extensionSubfield n hn :=
  (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
    D.cardinality_eq D.k₀ D.card_base D.k n hn).choose_spec.2.2.2.2.2.2.choose

/-- `Y₀ ×_{k₀} k`, bundled with its second projection `a_Y` to `Spec k`.
The finite-type condition means locally of finite type and quasi-compact.
Source: blueprint order 411, `def-weil-finite-field-fiber.md`
(blueprint: def-weil-finite-field-fiber). -/
noncomputable def geometricFiber (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] : Over (Spec (CommRingCat.of D.k)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj Y₀

/-- The `F_{q^n}`-valued points are precisely morphisms over `Spec k₀`.
Source: blueprint order 411, `def-weil-finite-field-fiber.md`
(blueprint: def-weil-finite-field-fiber). -/
noncomputable def extensionPoints (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (n : ℕ) (hn : 1 ≤ n) : Type u :=
  Over.mk (Spec.map (CommRingCat.ofHom (D.extensionEmbedding n hn))) ⟶ Y₀

/-- A single choice of coefficient prime `l ≠ p` and algebraic closure of `ℚ_[l]`.
The base coefficient field and its valuation ring are the existing `Padic l` and
`PadicInt l`. Finite extensions use the existing coefficient-extension constructions.
Source: blueprint order 411, `def-weil-finite-field-fiber.md`
(blueprint: def-weil-finite-field-fiber). -/
structure CoefficientDatum (D : FiniteFieldDatum.{u}) where
  l : ℕ
  [prime : Fact l.Prime]
  different : l ≠ D.p
  Qbar : Type u
  [field : Field Qbar]
  [algebra : Algebra (Padic l) Qbar]
  [isAlgClosure : IsAlgClosure (Padic l) Qbar]

attribute [instance] CoefficientDatum.prime CoefficientDatum.field CoefficientDatum.algebra
  CoefficientDatum.isAlgClosure

end FiniteFieldDatum
end WeilConjectures
