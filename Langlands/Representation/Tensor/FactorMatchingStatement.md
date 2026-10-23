# Jordan–Hölder matching for finite external tensors

Authors: Worker 161 and Worker 289. Worker 289 specified the mathematical
target and scope; Worker 161 authored and checked this Lean/Markdown pair.

This pair defines the proposition
`Langlands.FiniteTensor.PadicExternalTensorFactorsTheorem.{uF,uV,uW}`.
It states a derived composition-series consequence of exactness of tensoring
over the complex numbers and irreducibility of external tensors of admissible
irreducible smooth complex representations. It contains no proof of that
proposition.

## Exact statement

For every prime `p`, p-adic field `F : PadicField.{uF} p`, compatible
topological realization `T : F.TopologicalData`, positive natural number `n`,
and ordered block shape `B : BlockShape n`, take two families

```text
A  : ∀ i : Fin B.length, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)
A' : ∀ i : Fin B.length, SmoothRep.{0,uF,uW} ℂ (GeneralLinear (B.size i) F.Carrier).
```

The smooth categories use `T.topology` on the field and the induced topology
on each general linear group. Suppose that every `A i` and `A' i` is
admissible and that, for every index `i`,

```text
HaveSameJordanHolderFactors
  (Rep.of (A i).representation) (Rep.of (A' i).representation).
```

Then the two representations

```text
Rep.of (B.blockTensor (fun i => (A i).representation))
Rep.of (B.blockTensor (fun i => (A' i).representation))
```

have the same Jordan–Hölder factors in the same multiplicity-sensitive sense.
Both act on the actual same group
`B.Levi F.Carrier = ∀ i : Fin B.length, GeneralLinear (B.size i) F.Carrier`.
The field universe `uF` and the two carrier universes `uV` and `uW` are
independent.

`B.blockTensor` abbreviates `Langlands.FiniteTensor.external`; its carrier
is Mathlib's `PiTensorProduct ℂ` of the factor carriers. On a pure tensor,
the Levi element `g` sends `⊗ᵢ vᵢ` to `⊗ᵢ (A i).representation (g i) vᵢ`.
The conclusion therefore concerns the actual algebraic tensor actions.

The predicate `HaveSameJordanHolderFactors`, imported from
`Langlands.Representation.Filtration.ObjectDefinitions`, asserts existence
of actual finite zero-to-full filtrations with irreducible graded quotients,
of the same length, together with a permutation of the quotient positions
and actual equivariant equivalences at corresponding positions. Repeated
isomorphism classes retain their separate positions, hence multiplicities.
The factorwise hypotheses already supply finite composition series; no
separate finite-length assumption or chosen constituent list is an input.
Zero representations and reducible representations are allowed. There is
no irreducibility, nonzero-carrier, or finite-dimensionality hypothesis on
the given factors.

## Original sources and derived provenance

- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups. I*, Ann. Sci. ENS (4) 10 (1977), 441–472, §2.2, printed
  p.446, and §2.7, printed p.447 (one-based PDF pages 7–8).
  Registered source: `bernstein-zelevinsky-1977-induced-i`.
  Retained original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
  SHA256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  These passages identify standard GL Levi groups with products of their
  blocks and use external tensors of irreducible block representations.
- D. Flath, *Decomposition of representations into tensor products*, in
  *Automorphic Forms, Representations and L-Functions*, Proc. Sympos. Pure
  Math. 33, Part I (1979), 179–183, Theorem 1(1.1), printed p.179, and its
  proof, printed p.180 (one-based PDF pages 175–176).
  Registered source: `flath-1979-tensor-products`.
  Retained original:
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
  SHA256: `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
  Theorem 1(1.1) gives admissibility and irreducibility for the external
  tensor of two admissible irreducible smooth complex representations of
  locally compact totally disconnected groups.

The cited passages were read directly, including visual checking of the
tensor formulas in BZ77 §2.7 and Flath pp.179–180. No source-specific errata
note was found in the retained project notes at preparation.

Neither source states the present finite composition-factor matching
assertion verbatim. Its mathematical derivation tensors the supplied
composition series one factor at a time. Exactness of tensoring vector
spaces over a field identifies the successive quotients with tensors of
the individual graded quotients. Smooth admissible subquotients remain
smooth admissible in this p-adic setting. Iterating Flath's irreducibility
assertion then makes these tensor quotients simple. The finite product of
the input matching permutations, together with tensor products of the
matching equivariant equivalences, matches every resulting quotient with
its multiplicity. If a factor has composition length zero, the tensor is
zero and the corresponding composition series has length zero.

Admissibility is retained to justify this irreducibility step over `ℂ`.
The published `Langlands.FiniteTensor.isIrreducible_external` explicitly
requires scalar self-intertwiners in addition to factor irreducibility;
`Langlands.admissibleSchur_scalarEndomorphism` supplies the scalar condition
for admissible irreducible smooth complex factors. The statement makes no
arbitrary-field tensor irreducibility assertion.

## Scope and remaining proof

Only the statement is supplied here. The tensor-filtration construction,
its quotient comparisons, inherited admissibility, and the multiplicity
matching must be implemented in a separate proof of this exact proposition.
The existing finite tensor and filtration definitions are imported by Lean
module names. No tensor functor or conclusion-bearing witness is supplied
as replacement data.

This is a prerequisite for the adjacent-block-swap argument associated with
BZ77 §2.16(2). It asserts neither that association theorem nor existence
of a tensor factorization of an arbitrary Levi representation.
