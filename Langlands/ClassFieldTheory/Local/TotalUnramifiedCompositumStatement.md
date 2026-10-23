# Finite totally ramified and unramified composita

Authors: Worker 27 (the Lean statement and the first Markdown draft, shared as
revision 1 of the draft record of task `7ef970ee-f3a3-4328-9aea-62e67c0ff666`)
and Worker 231 (source and map audit, this Markdown and the submission). The
Lean file is Worker 27's draft without changes.

## Exact proposition and scope

`Langlands.LocalClassField.TotalUnramifiedCompositum.{u}` is a
proposition definition, not a proved theorem. Fix a prime `p`, given as
`p : ℕ` with `[Fact p.Prime]`, a p-adic field `F : PadicField.{u} p`, and
two finite intermediate fields
`E K' : FiniteIntermediateExtension F.Carrier` of the specified algebraic
closure `AlgebraicClosure F.Carrier`. Assume `[IsGalois F.Carrier E.field]`,

```lean
(E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
    Module.finrank F.Carrier E.field * F.canonicalTopologicalData.ramificationIndex
```

and

```lean
(K'.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
    F.canonicalTopologicalData.ramificationIndex
```

Write `e(X)` for the canonical absolute ramification index of `X` over
`Padic p`. The two hypotheses say `e(E) = [E:F]·e(F)` and `e(K') = e(F)`.
Since absolute ramification indices multiply in towers and
`e·f = [E:F]` for `E/F`, they mean that `E/F` is totally ramified and
`K'/F` is unramified. That reading is the mathematical meaning; the
proposition uses only the two displayed equalities.

The conclusion is `E.field.LinearDisjoint K'.field` together with a finite
intermediate field `M` such that `M.field = E.field ⊔ K'.field`, and
inclusions `hE : E.field ≤ M.field` and `hK : K'.field ≤ M.field`, for which
the following six clauses hold:

1. `Module.finrank K'.field M.field = Module.finrank F.Carrier E.field`,
   that is `[M:K'] = [E:F]`;
2. `e(M) = e(E)`, with the canonical absolute indices of `M` and `E`;
3. `IsGalois K'.field M.field`;
4. `Function.Bijective` holds for the canonical relative residue map
   `PadicField.TopologicalData.relativeResidueMap` from the canonical
   residue field of `K'` to that of `M`;
5. for every `z : E.field`, the canonical order of
   `IntermediateField.inclusion hE z` in `M` equals the canonical order of
   `z` in `E`;
6. for every `z : E.field`,
   `Algebra.norm K'.field (IntermediateField.inclusion hE z) =
   algebraMap F.Carrier K'.field (Algebra.norm F.Carrier z)`.

The universe `u` is arbitrary. `E/F` may have any finite degree; it is not
restricted to prime degree. `K'/F` is not assumed Galois. The degree-one
cases `E = F` and `K' = F` are included. No clause asserts anything about
ramification breaks, norm surjectivity or norm polynomials.

## Fields, inclusions and scalar structures

`FiniteIntermediateExtension F.Carrier` is the subtype of intermediate fields
of `F.Carrier ⊆ AlgebraicClosure F.Carrier` that are finite-dimensional over
`F.Carrier`; `.field` is the underlying intermediate field. All three fields
`E`, `K'` and `M` lie in this one closure, and `E.field ⊔ K'.field` is the
supremum in the lattice of intermediate fields, the compositum. Because the
conclusion fixes `M.field`, the field `M` is unique; `hE` and `hK` are
proofs of the two inclusions and carry no data.

`E.field.LinearDisjoint K'.field` is Mathlib's
`IntermediateField.LinearDisjoint`, with the inherited algebras of `K'.field`
over `F.Carrier` and into the closure. It is linear disjointness of the two
corresponding subalgebras of the closure.

`X.asPadicField` repackages the same field `X.field` as a `PadicField.{u} p`
whose `Padic p`-algebra is the composite
`(algebraMap F.Carrier X.field).comp (algebraMap (Padic p) F.Carrier)`.
`canonicalTopologicalData` is the canonical local-field structure of a
p-adic field, built from the spectral norm. All ramification indices,
orders and residue fields in the statement use this canonical data of the
`asPadicField` repackagings and of `F`.

Inside the conclusion the statement installs, by `letI`:

- the `asPadicField` `Padic p`-algebras of `E`, `K'` and `M`;
- `Algebra E.field M.field` and `Algebra K'.field M.field` given by
  `(IntermediateField.inclusion hE).toAlgebra` and
  `(IntermediateField.inclusion hK).toAlgebra`;
- the scalar towers `F.Carrier → E.field → M.field`,
  `F.Carrier → K'.field → M.field`, `Padic p → E.field → M.field` and
  `Padic p → K'.field → M.field`, each by
  `IsScalarTower.of_algebraMap_eq' rfl`, so each holds definitionally for
  these inclusions;
- `FiniteDimensional K'.field M.field`, from
  `FiniteDimensional.right F.Carrier K'.field M.field`.

The degree, the Galois property, the residue map and the norm in clauses 1,
3, 4 and 6 use the inclusion algebra `K'.field → M.field`. Mathlib has no
global algebra instance between two intermediate fields, so this is the only
algebra available there. The `Padic p`-algebra installation is needed:
Mathlib's global instance `IntermediateField.algebra'` also gives a
`Padic p`-algebra on `E.field`, through the algebra of `Padic p` on the
closure, but it is not definitionally the `asPadicField` composite. With the
installation, the tower `Padic p → K'.field → M.field` required by
`relativeResidueMap` is stated for the same structures as the canonical data
of `K'.asPadicField` and `M.asPadicField`.

`relativeResidueMap T S`, in `Langlands.LocalField.RelativeIntegers`, is
`IsLocalRing.ResidueField.map` of `relativeIntegerMap T S`, the restriction
of the field map `K'.field → M.field` to the canonical integer rings. Here
that field map is the inclusion `hK`, so on residue classes it sends the
class of `x` to the class of `x` viewed in `M`.

`Algebra.norm` is Mathlib's determinant of multiplication. In clause 6 it is
taken for `M.field` over `K'.field` on the left and for `E.field` over
`F.Carrier` on the right. `algebraMap F.Carrier K'.field` is the inherited
inclusion of `F.Carrier` into `K'.field`.

## Conventions

The canonical order `ord` of `Langlands.LocalField.Normalization.Definitions`
is the normalized additive valuation, with value group `ℤ`, and
`ord 0 = 0` by convention. The absolute ramification index is
`(ord (p : X)).toNat`. Clause 5 covers every `z`, including `z = 0`, where
both sides are `0` by that convention. Taking `z` to be any element of order
`1` in `E` shows that every uniformizer of `E` remains a uniformizer of `M`.
No other uniformizer is chosen.

## Source and provenance

The source is Serre, *Local Fields*, English translation by Marvin Jay
Greenberg, Graduate Texts in Mathematics 67, Springer (1979), registered as
`serre-1979-local-fields`, file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf` with SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 231 read Chapter V, §4, "Extension of the Residue Field in a Totally
Ramified Extension", printed pages 87–88 (PDF pages 94–95), through the
statement of Proposition 6 and its corollary. No errata note exists for this
source in the Library.

Serre's `K`, `L`, `K'`, `L'` correspond here to `F`, `E`, `K'`, `M`. Serre
takes `L/K` finite and totally ramified with perfect residue field. Here that
residue field is finite, so it is perfect. He lets `K'` be the unramified
extension of `K` corresponding to a finite residue extension (Chapter III,
§5); here `K'` is any finite unramified intermediate field. The source
states directly that:

- `L/K` and `K'/K` are linearly disjoint, with compositum `L' = K' ⊗_K L`;
- `L'/L` is unramified, with residue extension that of `K'/K`;
- a uniformizer of `L` is also a uniformizer of `L'`;
- if `L/K` is Galois with group `G`, then `L'/K'` is Galois, and the
  ramification groups of `G` are the same for both extensions.

Serre's own sentence covers linear disjointness, the compositum and the
Galois clause 3. The other clauses are derived from Serre's facts:

- Clause 1 follows from the identification `M ≅ K' ⊗_F E`.
- Clause 2 is the statement that `M/E` is unramified, written with absolute
  indices.
- Clause 5 is a strengthening of the uniformizer sentence: since `M/E` is
  unramified, the normalized order of `M` restricts to that of `E` on all of
  `E`.
- Clause 4 is the residue-degree-one consequence. By clauses 1 and 2,
  `e(M/K') = e(M)/e(K') = e(E)/e(F) = [E:F] = [M:K']`, so the residue degree
  of `M/K'` is `1`. The injective map between finite residue fields of equal
  cardinality is then bijective. In Serre's terms, `L'/K'` is totally
  ramified: its inertia group `G_0` equals `G`, because its ramification
  groups are those of the totally ramified `L/K`.
- Clause 6 is the determinant base-change consequence of `M ≅ K' ⊗_F E`.
  A basis of `E` over `F` is a basis of `M` over `K'`, and multiplication by
  `z ∈ E` has the same matrix in both bases. Mathlib's
  `IntermediateField.LinearDisjoint.norm_algebraMap` and
  `Subalgebra.LinearDisjoint.norm_algebraMap` state this identity.

These derived clauses are precise targets for a proof. The statement does
not claim that the quoted paragraph proves them verbatim. The arbitrary
finite Galois `E/F` and the canonical fields and maps are a derived
interface for this setup. Serre's subsequent use, for `G` cyclic of prime
degree with the norm polynomials `N_n` and `N'_n` and Proposition 6, is not
part of this statement.

## What is not asserted

The statement does not assert norm surjectivity, Serre's Proposition 6 or
its corollary, preservation of ramification breaks or of the homomorphisms
`θ_i`, compatibility of the norm polynomials, or the passage to the maximal
unramified extension. Those need separate statements and proofs. A proof of
this statement must give the actual compositum and the displayed equalities
for the actual inclusion maps. An unrelated isomorphism of residue fields, or
a different uniformizer, is not enough.

## Checks

`lean_check` diagnostic `bfb21cba-194d-48df-943a-0d707c1eae34` compiled the
module with zero diagnostics. It reports `statement_returns_prop: true`,
universe parameter `u`, and only the axioms `propext`, `Classical.choice`
and `Quot.sound`. A private audit check confirmed three points: no
`Algebra K'.field M.field` instance can be synthesized without the
installation; the global `IntermediateField.algebra'` structure is not
definitionally the `asPadicField` composite; and `relativeIntegerMap` acts
as the inclusion on underlying elements by `rfl`. Worker 27's earlier
development check `89f96e1e-5967-48e9-8394-761618739bd3` reported the same
result for this Lean file. These checks are not evidence for the arithmetic.
