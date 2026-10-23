# Compatible finite-tower descent along a directed union of fields

Authors: Worker 29; Worker 60 supplied the compatible-tower formulation.

`Langlands.FieldTheory.FiniteTowerDirectedUnionDescent.{u,v}` is a
proposition definition. This module states the descent assertion; it does
not prove it or assume a certificate of its conclusion.

## Exact quantifiers and witnesses

Let `U`, `E`, and `L` be fields in a common arbitrary universe `u`. The
quantified structures are `Algebra U E`, `FiniteDimensional U E`,
`Algebra.IsSeparable U E`, `Algebra E L`, `FiniteDimensional E L`, and
`IsGalois E L`. The `U`-algebra on `L` is defined as the composite through
`E`, rather than quantified independently.

Let `I : Type v` be nonempty, with `v` independent of `u`, and let
`A : I → Subfield U` satisfy `Directed (· ≤ ·) A` and
`∀ x : U, ∃ i : I, x ∈ A i`. There is no order on `I` and no common
smaller ground field or finite-dimensionality hypothesis on its stages.
For every `i₀ : I`, `sE : Finset E`, and `sL : Finset L`, there exist
one index `i`, one `B : IntermediateField (A i) E`, and one
`C : IntermediateField B L` satisfying all of the following together:

1. `A i₀ ≤ A i`.
2. `B` is finite dimensional and separable over `A i`, with
   `Module.finrank (A i) B = Module.finrank U E`.
3. `C` is finite dimensional and Galois over `B`, with
   `Module.finrank B C = Module.finrank E L`.
4. `C` is finite dimensional over `A i`, with
   `Module.finrank (A i) C = Module.finrank U L`.
5. `B.LinearDisjoint U` and
   `IntermediateField.adjoin U (B : Set E) = ⊤`.
6. `(C.restrictScalars (A i)).LinearDisjoint U` and
   `IntermediateField.adjoin U (C : Set L) = ⊤`.
7. `C.LinearDisjoint E` and
   `IntermediateField.adjoin E (C : Set L) = ⊤`.
8. Every element of `sE` belongs to `B`, and every element of `sL`
   belongs to `C`.
9. As ring homomorphisms from `B` to `L`,
   `(algebraMap C L).comp (algebraMap B C) =
   (algebraMap E L).comp (algebraMap B E)`.

All of these clauses occur within the same existential quantifiers. There
is no nontriviality assumption on either extension degree: degree-one
extensions and empty finite sets are included. The fields may have any
characteristic. Separability of `E/U` and Galoisness of `L/E` are explicit
hypotheses; Galoisness of `L/U` is not assumed or asserted. The proposition
has no term parameters outside its definition, only the universe levels.

## Literal maps and linear disjointness

The `U`-algebra on `L` is
`((algebraMap E L).comp (algebraMap U E)).toAlgebra`, and its
`IsScalarTower U E L` is installed by reflexivity of the algebra-map
equality. For a selected stage, `Algebra.ofSubsemiring (A i)` gives the
algebras from `A i` to `U`, `E`, and `L`. Their maps are the subfield
inclusion followed by the specified tower maps. The compatible scalar
towers through `U` and `E` are installed explicitly.

The intermediate field `B` has its canonical `A i`-algebra and inclusion
into `E`. `Algebra.ofSubsemiring B` installs its algebra on `L`, whose
map is exactly `B → E → L`; `IsScalarTower B E L` is installed explicitly.
The `A i → B → L` tower is inherited from these structures.

The intermediate field `C` is defined over this specific `B`-algebra on
`L`. Its canonical `B`-algebra therefore puts the image of `B` inside
`C`, and its inclusion into `L` is the subtype inclusion. Its `A i`-algebra
is inherited from the compatible tower, with `IsScalarTower (A i) C L`
installed by reflexivity of the map equality. The final equality in the
statement also exposes the commuting square through `B`, `E`, `C`, and
`L` directly. There is no separately chosen embedding of `B` into `C`.

`C.restrictScalars (A i)` has the same underlying subset of `L` as `C`;
it changes only the displayed intermediate base field. Mathlib's
`IntermediateField.LinearDisjoint` compares the intermediate field's
subalgebra with the range of `IsScalarTower.toAlgHom` for the other field.
Thus the three disjointness clauses concern, respectively, the actual
images of `B` and `U` in `E` over `A i`, of `C` and `U` in `L` over
`A i`, and of `C` and `E` in `L` over `B`. The three `adjoin` clauses
express the corresponding literal composita in `E` and `L`.

## Source and derived scope

Source: Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, Graduate Texts in Mathematics 67, Springer, 1979, Chapter V,
§4, Lemma 6 and its proof, printed page 89 (PDF page 96), and the
simultaneous-model step in the proof of Proposition 7, printed page 90
(PDF page 97). The registered source is `serre-1979-local-fields`, at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The original printed pages 88–90 were read. No project errata note for
this source was found.

Lemma 6 supplies single-extension descent by retaining finitely many
basis multiplication coefficients, including separable and Galois
refinements. Proposition 7 uses compatible finite models of two nested
extensions, with the upper finite model Galois over the lower one. This
module isolates a generic compatible-tower strengthening with an
explicit separability hypothesis on the lower extension. It is a derived
interface, not a verbatim statement of either result, and does not assert
the local-field conclusions used in Proposition 7.

The mathematical rationale is simultaneous finite-coefficient descent.
One may choose a `U`-basis of `E` and an `E`-basis of `L`, each containing
`1`, and use their products as a `U`-basis of `L`. A sufficiently large
stage can contain coefficients for multiplication in both bases, the
prescribed finite subsets, separable polynomial relations for the lower
basis, and the images of the upper basis under the finite group
`Gal(L/E)`. The intended lower and upper spans then retain the inclusion
of the lower span, all three bases, and the Galois action. Basis
independence explains the degrees and disjointness conclusions, and
basis spanning explains the composita. This describes the provenance of
the requested strengthening; it is not an implemented Lean proof. In
particular, producing both spans as fields and proving every simultaneous
refinement remain obligations of the future proof.

## Difference from single-extension descent

The published `Langlands.FieldTheory.FiniteExtensionDirectedUnionDescent`
in `Langlands.FieldTheory.FiniteExtensionDescentStatement` has one finite
extension, one descended intermediate field, one prescribed finite set,
and conditional separable and Galois refinements for that one witness.
It applies without assuming separability of its extension.

The present target has two given finite extensions and two compatible
witness fields at one common stage. It assumes the lower extension is
separable and the upper extension is Galois, and demands those properties
for `B/(A i)` and `C/B`, respectively. It simultaneously retains the
lower, upper, and total degrees; all three disjointness and compositum
pairs; two prescribed finite sets; and the literal inclusion square.
Two independent applications of the single-extension assertion do not
by themselves align these witnesses or supply these compatibility clauses.
The existing single-extension statement and proof are left unchanged.

## Dependencies and remaining work

The sole Lean import is `Mathlib.FieldTheory.LinearDisjoint` in the pinned
Lean 4.34.0 / Mathlib `5ed2965256430c3649e86755f9576b54eca72435`
environment. Existing intermediate-field, scalar-tower, separability,
Galois, and finite-dimensional APIs express the target directly.

This module contains no descent theorem, norm theorem, ramification
argument, maximal-unramified-field identification, fixed-field comparison,
or cohomology assertion. Independent acceptance of the statement leaves
its exact proof as a separate task.
