# Basic open subschemes and points over a topological ring

Author: Worker 3519.

This module states the general criteria in the opening discussion of Section 3 of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, printed pp.3–4. It
contains one auxiliary map and one Prop-valued statement, and no proof.

## Source

Printed pp.3–4: "More generally, if `X = Spec A` and `U = Spec A_f` with `f ∈ A`, then the
subset `U(R) ⊆ X(R)` is the locus where the continuous map `f : X(R) → R` is unit-valued – the
preimage of the subset `R^×` – and this preimage might not be open. Such openness in general
(for a fixed `R`) is equivalent to the set of non-units in `R` being closed […]. Regardless of
whether or not `R^×` is open in `R`, since `A_f = A[T]/(fT − 1)` we see that `U(R) → X(R)` is a
topological embedding onto its image if and only if `1/f : U(R) → R` is continuous when `U(R)`
is given the subspace topology from `X(R)`. Taking `X` to be the affine line and `U` to be the
multiplicative group, such an embedding property for general affine finite type `R`-schemes
would force `R^×` to be a topological group with its subspace topology from `R` […]. We
conclude that the failure of openness of `R^×` in `R` or the failure of `R^×` to be a
topological group with its subspace topology from `R` are the only obstacles to basic open
affine immersions inducing open embeddings on spaces of `R`-points."

## Objects

`R` and `S` are commutative rings in one universe `u`, `S` an `R`-algebra and a topological
ring (Conrad's topological ring `R` is the value ring `S` here; the base `R` is arbitrary).
Points of `Spec A` with values in `S` are the Library's algebra points `AlgPoint R A S`
(`A →ₐ[R] S`) with the evaluation topology of Proposition 2.1; `AlgPoint` is the Library's
model for affine points, and `spectrumAlgebraPointHomeomorph` identifies it with points of the
actual relative spectrum.

`basicOpenPointMap R S A f` is the map induced by the basic open `Spec A_f → Spec A`, for
`A_f = Localization.Away f`: precomposition with the localization map `A → A_f`.

`Sˣ` carries Mathlib's units topology, induced by `u ↦ (u, u⁻¹)` into `S × Sᵐᵒᵖ`, so
inversion on `Sˣ` is continuous. Thus `Units.val : Sˣ → S` is a topological embedding exactly
when inversion is continuous for the subspace topology from `S`, that is, when `S^×` with its
subspace topology is a topological group; it is an open embedding when moreover `S^×` is open.

## Statement

`AffineBasicOpenPointCriteria` asserts, for all such `R` and `S`:

1. for every `R`-algebra `A` and `f ∈ A`, the image of `basicOpenPointMap R S A f` is
   `{p | IsUnit (p f)}`, the unit locus of `f`;
2. the image is open for every finite-type `A` and every `f` iff `{s : S | IsUnit s}` is open;
3. `basicOpenPointMap R S A f` is a topological embedding for every finite-type `A` and every
   `f` iff `Units.val : Sˣ → S` is a topological embedding;
4. `basicOpenPointMap R S A f` is an open embedding for every finite-type `A` and every `f` iff
   `Units.val : Sˣ → S` is an open embedding.

Clauses 2 and 3 are Conrad's two equivalences: openness of the non-units' complement, and the
embedding property (continuity of `1/f`, forced on the multiplicative group). Clause 4 is his
conclusion that these are the only obstacles to open embeddings.

## Provenance

Derived formulation of the source discussion. Conrad states clause 3 pointwise, for a fixed
`U ⊆ X`, as continuity of `1/f`; the statement uses the uniform form "for all finite-type `A`
and all `f`", which is the form of his conclusion. The quantification over all finite-type
`A` in clauses 2–4 matches his "in general (for a fixed `R`)" and "for general affine finite
type `R`-schemes". The algebra-point formulation, the names and the conjunction are this
formalization's.

Why it holds: (1) by the universal property of localization. In (2)–(4) the backward
directions follow from (1) and continuity of evaluation at `f`, and, in (3), from writing every
element of `A_f` as `a · (1/f)^n`. The forward directions take `A = R[X]` and `f = X`, where
the points are `S` and `S^×` and the map is `Units.val`.
