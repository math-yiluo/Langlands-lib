# Finite stages inside a chosen fraction field

This internal algebraic adapter prepares finite data over a chosen fraction
field for noetherian approximation. Its provenance is composition of Mathlib's
fraction representations, fraction-field lifting and range equivalence with
the separately published `NormalFiniteTypeSubalgebraStatement`. It introduces
no new translation from the literature.

Fix a commutative domain `R : Type u` and any chosen fraction field
`K : Type v`, with its given `Algebra R K` and `IsFractionRing R K`.
The two universes are independent. No valuation or characteristic assumption
is needed. For an actual integer subalgebra `T` of `R`,
`stageFractionFieldMap R K T : FractionRing T →+* K` lifts the composite
injection `T → R → K`. Its algebra-map lemma states that an element of `T`
is sent to its image under the original `algebraMap R K`. The map is
injective because its source is a field.

`exists_finset_fractionFieldData` starts with finite sets `sR` in `R` and
`sK` in `K`. Mathlib's `IsFractionRing.div_surjective` represents each
element of `sK` by a numerator and a nonzero denominator in `R`. Their
finitely many numerators and denominators, together with `sR`, form a
finite set `t`. For every integer subalgebra `T` containing `t`, the
fraction formed from those two elements of `T` maps to the prescribed
element of `K`. Thus `sK` lies in the actual field image of
`stageFractionFieldMap R K T`.

`exists_fg_fractionFieldStage` takes `T = ℤ[t]`. It proves finite
generation and preserves both the prescribed elements of `R` and the
prescribed field elements. This result has no normality assumption.

`exists_normal_fractionFieldStage` additionally assumes
`IsIntegrallyClosed R` and takes an explicit proof of
`NormalFiniteTypeSubalgebraStatement.{u}`. Apply that statement to `t`
and use the universal conclusion of the finite-data lemma. The resulting
actual subalgebra `T` is finitely generated, contains `sR`, is integrally
closed in its own fraction field and is noetherian; its fraction-field
image contains `sK`.

For an actual `B : Subalgebra ℤ K` contained in this field image,
`factorToStageFractionField` restricts `B → K` to that image and composes
with the inverse of Mathlib's `RingHom.rangeRestrictFieldEquiv`. It gives
an actual ring map `B →+* FractionRing T`. The evaluation lemma proves
that its composite with `stageFractionFieldMap` is exactly `B → K`;
this also proves injectivity.

`exists_normal_fractionFieldFactor` applies the normal-stage result to
a finite set of algebra generators of `B`. The image of a field is an
integer subalgebra, so containment of those generators implies containment
of all of `B`. The factor map then yields an injective ring map
`B →+* FractionRing T` whose composite with the displayed embedding
into `K` equals the original inclusion, as an equality of ring maps.
The finite subset `sR` remains in `T`.

The normal-stage conclusions explicitly depend on the separately stated
normal-subalgebra theorem; this file does not prove that theorem.
These are algebraic finite-data and factorization results. They do not
descend a generic line bundle, its axes, a scheme or a morphism property.
They do not construct or compare a correspondence representer, and do not
prove the arbitrary-valuation two-axis extension statement.
