# Finite length of normalized products of smooth GL factors

Author: Worker 118.

This pair states two finite-length assertions for actual normalized upper
parabolic induction. All three declarations in the namespace
`Langlands.Classification` are `Prop` definitions; none proves the assertions.

| Declaration | Assertion and provenance |
| --- | --- |
| `IrreducibleProductFiniteLength F T` | A finite family of arbitrary irreducible smooth complex positive-rank GL representations has normalized product induction of finite length. Henniart 2002, §2.5, pp.594–595. |
| `AdmissibleFiniteLengthProductPreservation F T` | The same conclusion holds if each smooth block factor is admissible and of finite length. Derived block-factor specialization of Casselman 1995, Corollary 6.3.8, p.60, using the external tensor-product translation below. |
| `PadicNormalizedProductFiniteLengthTheorems` | The conjunction of these two assertions for every prime, every actual finite extension of its p-adic field, and every compatible topological realization. This is only an organizational aggregate. |

## Quantifiers and actual objects

`F : PadicField.{uF} p` is an actual finite extension of `ℚ_p`, for
`p : ℕ` with `[Fact p.Prime]`. There is no restriction on its degree,
ramification or Galois group. `T : F.TopologicalData` supplies its compatible
topology and normalized absolute value. The canonical realization exists in
the Library, so this quantification applies to every such algebraic field.

Each component quantifies over `n : ℕ` with the explicit premise `0 < n`,
then over `B : GeneralLinear.BlockShape n`. The fields of `B` supply
`B.positive : ∀ i, 0 < B.size i` and
`B.sum_eq : ∑ i, B.size i = n`. The finite ordered index set is
`Fin B.length`; positive total rank excludes the empty family. Arbitrary
finite ordered families of positive ranks are represented by this data.

The factors are actual objects

```lean
A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)
```

Smoothness is part of these objects. The field universe `uF` and common
factor-carrier universe `uV` are independent. All factors have carriers in
`Type uV`, with no topology or finite-dimensionality condition on those
carriers. The external tensor carrier lies in `Type uV`; the actual
induced function carrier lies in `Type (max uF uV)`. The conclusion uses
that induced object directly and does not resize it to `Type uV`.

The first component assumes only `∀ i, (A i).IsIrreducible`.
This is simplicity of the actual invariant-submodule lattice and includes
nonzeroness. In particular, it assumes neither supercuspidality nor
admissibility, unitarity, temperedness or a chosen central character.
Admissibility of irreducible factors is a mathematical input to a possible
proof, not a hidden hypothesis.

The second component explicitly assumes, for every factor, both
`(A i).IsAdmissible` and
`IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear (B.size i) F.Carrier))
(A i).representation.asModule`.
`IsAdmissible` uses the existing all-open-subgroups convention: smoothness
and finite-dimensional fixed vectors for every open subgroup. On these
groups it agrees with the compact-open convention by the compact-open
neighborhood basis. This comparison is not a new assumption in the clause.
The factors may be reducible or zero. No conclusion of irreducibility or
numerical length bound is asserted.

In both clauses the conclusion is the existing `IsFiniteLength` predicate
on the induced representation's actual group-algebra module. Mathlib's
`isFiniteLength_iff_exists_compositionSeries` identifies it with a finite
composition series from bottom to top in the group-algebra submodule
lattice. Mathlib's `Subrepresentation.subrepresentationSubmoduleOrderIso` identifies
these with the complex subspaces invariant under all group elements. Thus this is finite representation length, including the
zero module, and not finite complex dimension. The existing
`SmoothRep.HasFiniteLength` is the wrapper for this same predicate;
the clauses display the predicate itself.

## Tensor product, parabolic and normalization

The induced object is exactly
`(T.normalizedProductInductionFunctor B).obj A` from
`Langlands.Representation.Induction.BlockFactors`.
Its Levi representation is the external tensor product
`B.blockTensor (fun i => (A i).representation)` on
`PiTensorProduct ℂ (fun i => A i)`. Here
`B.Levi F.Carrier = ∀ i, GeneralLinear (B.size i) F.Carrier`,
with the actual standard block-diagonal embedding. The action on a pure
tensor is the tensor of the individual block actions, as recorded by
`BlockShape.blockTensor_tprod`.

The parabolic `B.parabolic F.Carrier` consists of upper block-triangular
invertible matrices, with block sizes in the given order.
`normalizedProductInductionFunctor_obj` identifies the underlying action
with `T.normalizedProductInduced`. For `q` in the parabolic and
`m = B.leviProjection F.Carrier q`, its covariance is

```text
f(q g) = δ_P(m)^(1/2) (⊗_i A_i(m_i)) f(g),
(g · f)(x) = f(x g).
```

The factor is the positive real square root, embedded in `ℂ`, of
`T.leviModulus B`; the normalizing character is `T.leviHalfCharacter B`.
The explicit upper-block modulus is
`∏_{i<j} |det m_i|_F^(B.size j) / |det m_j|_F^(B.size i)`,
with normalized absolute value `|ϖ|_F = q_F^(-1)`.
The covariance is proved by `normalizedProductInduced_covariant`, and
right translation is `BlockShape.productInducedOf_apply`.
No opposite-parabolic or negative-half-modulus convention is used.

Casselman §2.4, p.26, defines induction by this right action and untwisted
left covariance. His §3.1, p.32, defines normalized induction by twisting
with `δ_P^(1/2)`, where `δ_P(m) = |det Ad(m)|` on the unipotent Lie algebra.
For an upper GL block pair, conjugation sends `X` to `m_i X m_j^(-1)`;
its determinant absolute value is the corresponding factor in the displayed
formula. This identifies the intended normalizations. Formal comparison
with the Haar modulus remains a proof obligation, not an extra premise.

## Casselman's Levi hypothesis and the derived factor clause

Corollary 6.3.8 concerns one **admissible finite-length representation of
the Levi**. It does not state a theorem with only admissibility as input.
The factor version here has the following mathematical translation.

1. The finite external tensor product of smooth admissible factors is a
   smooth admissible representation of the product Levi. For product
   compact open subgroups, invariants identify with the tensor product
   of the finite-dimensional factor invariant spaces. Any open subgroup
   of the finite product contains such a product of compact open subgroups;
   its invariants form a subspace of that finite-dimensional space.
2. Tensor the factors' finite composition series, using exactness of
   tensoring over `ℂ`. This gives a finite filtration whose successive
   factors are external tensor products of irreducible admissible
   representations of the individual GL groups. Such external tensor
   products are irreducible representations of the product group
   (the product-group assertion recorded in BZ77 §2.7, p.447).
   Hence the Levi representation has finite length. A zero factor gives
   the zero tensor module and causes no exception.
3. Apply Casselman Corollary 6.3.8 to this Levi representation and the
   actual upper block parabolic. The functor identity above gives precisely
   the conclusion in `AdmissibleFiniteLengthProductPreservation`.

These steps explain the derived specialization; they are not Lean proofs
in this pair. For the first clause, Henniart directly asserts the result.
Alternatively, BZ77 Theorem 2.5, p.447, supplies admissibility of each
irreducible smooth GL factor; each has length one, and the preceding route
then applies. Neither route assumes that the factors are supercuspidal.

## Boundaries and remaining proofs

The published
`Langlands.CuspidalSupport.CuspidalInductionLengthTheorem`
states the stronger bound by `B.length!` for **irreducible cuspidal Levi
data**, following BZ77 Theorem 2.8, pp.447–448. That hypothesis is
essential for that bound; BZ77 Remark 2.10, p.448, explicitly warns that
the corresponding bound can fail without cuspidality. This pair adds
the general finite-length assertion and does not duplicate the
cuspidal-support, association or multiplicity statements.

The neighboring published `Langlands.GLAdmissibleFiniteLengthStatement`
in `Classification.FiniteLengthStatement` requires **both admissibility
and finite generation over the group algebra**. Its predicate is the same
`IsFiniteLength`. It is neither an admissibility-only implication nor an
induction theorem. This pair reuses the common predicates and adds no
replacement for that statement. A proof route through it would also need
to prove finite generation of the induced module; admissibility alone
would not suffice.

Remaining proof obligations include irreducible admissibility (already
part of the published `CuspidalEmbeddingTheorem` statement), product
admissibility and its invariant-space comparison, tensor exactness and
irreducibility for the product-group factors, construction of the Levi
composition filtration, and finite-length preservation by actual
normalized induction. Casselman proves the latter via the preceding
cuspidal case, exactness and induction transitivity, citing §§2.4.4–2.4.5,
p.28. The actual induction exactness/transitivity and the normalization
comparisons must be proved when implementing that route.
This pair introduces no classification constructor, new axiom, abstract
replacement predicate, or proof of any of these substantive assertions.

## Retained sources and reading extent

All page numbers below are printed pages; PDF numbers are one-based.
The stated passages were independently read in the retained originals.
No whole-book or whole-paper reading is claimed. No source-specific
errata file was present under the project's `notes/errata` at this check.

- **H02:** Guy Henniart, *Une caractérisation de la correspondance de
  Langlands locale pour GL(n)*, Bull. Soc. Math. France 130 (2002),
  587–602. §2.5, pp.594–595 (PDF 8–9), specifies the upper parabolic and
  arbitrary irreducible smooth factors and asserts finite length.
  Registered ID `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
  Retained file:
  `/home/taskhub/central-library/Henniart--Une caracterisation de la correspondance de Langlands locale pour GL(n)--2002.pdf`.
- **Ca95:** W. Casselman, *Introduction to the theory of admissible
  representations of p-adic reductive groups*, draft of 1 May 1995.
  Corollary 6.3.8, p.60 (PDF 60); §2.4, pp.26–28, and §3.1, p.32,
  for the action, exactness/transitivity and normalization.
  Registered ID `casselman-1995-admissible-representations`, SHA-256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
  Retained file:
  `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
- **BZ77:** I. N. Bernstein and A. V. Zelevinsky, *Induced representations
  of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472.
  §§2.1–2.10, pp.446–448 (PDF 7–9), read for the block Levi, irreducible
  admissibility, product-group tensor assertion, and the cuspidal bound.
  Registered ID `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Retained file:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

## Exact declaration dependencies

The direct imports are `Langlands.Representation.Induction.BlockFactors`
and `Langlands.Representation.Category.Subquotients`. Their dependency versions are
pinned by Library commit `01a58491bc71539f1ecd3d5f0eec6ab8eae20fed`.
The relevant definitions and paired explanations were read. No draft
dependency is used.

| Module | Reused declarations and role |
| --- | --- |
| `Langlands.LocalField.Definitions` and the canonical topological realization imported by `Group.GL.BlockModulus` | `PadicField`, `PadicField.TopologicalData`, compatible topology and normalized absolute value |
| `Langlands.Group.GL.Blocks` | `BlockShape`, `positive`, `sum_eq`, `Levi`, `parabolic`, `leviProjection` |
| `Langlands.Group.GL.BlockModulus` | `leviModulus`, `leviHalfModulus`, `parabolicHalfModulus` |
| `Langlands.Representation.Induction.Parabolic` | `leviHalfCharacter`, normalized induction of the actual Levi representation |
| `Langlands.Representation.Tensor.Finite` | `FiniteTensor.external`, `externalFunctor`, actual smooth Levi tensor product |
| `Langlands.Representation.Induction.BlockFactors` | `normalizedProductInductionFunctor`, `normalizedProductInductionFunctor_obj`, `normalizedProductInduced_covariant`, `blockTensor_tprod`, `productInducedOf_apply` |
| `Langlands.Representation.Category.Basic` | `SmoothRep`, `representation`, `IsIrreducible`, `IsAdmissible`, `HasFiniteLength` |
| `Langlands.Representation.Category.Subquotients` | Actual smooth invariant submodules and quotients for the composition-series interpretation; no abstract chosen constituent |
| `Mathlib.RepresentationTheory.Subrepresentation` | `Subrepresentation.subrepresentationSubmoduleOrderIso`, invariant subspaces as group-algebra submodules |
| `Mathlib.RingTheory.FiniteLength` | `IsFiniteLength`, `isFiniteLength_iff_exists_compositionSeries` |

The pinned environment uses Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
Successful elaboration and inspection as `Prop` check the formulation,
not its mathematical truth; independent semantic review and publication
are separate requirements.
