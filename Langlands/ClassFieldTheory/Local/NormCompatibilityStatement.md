# Relative norms and arithmetic normalization

Author: Worker 10.

This module defines the proposition
`Langlands.LocalClassField.RelativeNormCompatibility`. It states the norm and
embedding compatibility needed to transport the absolute-value character in
local reciprocity. It contains no theorem proof or constructed reciprocity map.

## Fields, hypotheses and actual objects

Both component propositions quantify every prime `p`, finite extensions
`F : PadicField.{u} p` and `E : PadicField.{v} p` in independent universes,
an `Algebra F.Carrier E.Carrier`, the compatible
`IsScalarTower (Padic p) F.Carrier E.Carrier`, and
`FiniteDimensional F.Carrier E.Carrier`. They then quantify every supplied
`TF : F.TopologicalData` and `TE : E.TopologicalData`.
No Galois, abelian, unramified, or reciprocity hypothesis is imposed.

The norm is Mathlib's determinant field norm `Algebra.norm F.Carrier`.
The embedding is the specified `algebraMap`. On multiplicative groups, the
norm is exactly `Units.map (Algebra.norm F.Carrier (S := E.Carrier))`.
The additive orders, residue degrees, ramification indices and normalized
absolute values are the accepted constructions on these supplied valuation
integer rings and residue fields. The canonical norm is the accepted spectral
norm extending that of `Padic p`; no alternative field or norm is defined here.

The all-fields realization obligation for an interface using `TopologicalData`
is precisely that for every prime `p` and every `F : PadicField.{u} p`,
`Nonempty F.TopologicalData` holds. The existing, separately published
`Langlands.PadicField.canonicalTopologicalData` in
`Langlands.LocalField.Canonical` constructs such data for every field.
This module works for every supplied choice, without assuming any of the
normalization identities it concludes.

## Exact conclusions

Write `n = [E : F]`, `N = N_{E/F}`, and `i : F → E` for the given embedding.
Write `|x|_F` for the residue-cardinality normalized absolute value and
`s_F(x)` for the base-extending spectral norm.

`RelativeAbsoluteValueLaws` states, including at zero:

- `|N(x)|_F = |x|_E` for every `x ∈ E`.
- `|i(x)|_E = |x|_F^n` for every `x ∈ F`.
- `s_F(N(x)) = s_E(x)^n` for every `x ∈ E`.
- `s_E(i(x)) = s_F(x)` for every `x ∈ F`.

The degree power therefore occurs on different sides for the two
normalizations. In particular, residue-normalized absolute values need not
extend each other under a nontrivial finite extension.

`RelativeNormOrderLaws` uses the actual absolute residue degrees `f_F,f_E`
and absolute ramification indices `e_F,e_E`. It states

- `f_F * ord_F(N(x)) = f_E * ord_E(x)` for every `x ∈ E`.
- `e_F * ord_E(i(x)) = e_E * ord_F(x)` for every `x ∈ F`.
- For every `x ∈ Eˣ`, its field norm has order zero if and only if `x`
  has order zero.

The first two formulas avoid introducing separate relative-index definitions
or division in the statement. They are the usual relative residue-degree and
ramification formulas after multiplying by the absolute indices. Each
natural-number index is explicitly cast to `ℤ`. The orders use the existing
convention `ord(0)=0`; at zero both sides of each order formula are zero.
The last clause is stated on field units, so it concerns nonzero elements.
Order zero characterizes the units of the valuation integer ring; this clause
does not claim that every element of the field's multiplicative group has
order zero, or that every integer-ring unit is a norm.

## Original-source correspondence and scope

Jean-Pierre Serre, *Local Fields*, English translation by Marvin Jay Greenberg,
Springer GTM 67 (1979), Chapter II, section 1, printed pages 26–28
(PDF pages 34–36), and section 2, Proposition 3 and Corollaries 1–4,
printed pages 28–30 (PDF pages 36–38); also Chapter I, section 4,
printed pages 14–15 (PDF pages 22–23), and Chapter II, section 5,
printed page 36 (PDF page 44), for the actual indices and their absolute
specialization.
Registered source `serre-1979-local-fields`, retained at
`C:/Central-Library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 10 read these original pages.

Section 1 fixes `q^(-ord x)` away from zero and zero at zero. Corollary 4
gives `ord_F(N(x)) = f(E/F) * ord_E(x)`, and the paragraph at the top of
printed page 30 states the norm identity for normalized absolute values.
Corollaries 1–3 give the degree relation, uniqueness of the prolonged valuation
and equality of the valuations of conjugates. Applying the field norm to a
base scalar gives its `n`th power, yielding the embedding formula.

The spectral-norm clauses and the cross-multiplied absolute-index order
clauses are derived interface formulations of those results, not verbatim
theorem statements from Serre. The unique base-extending spectral norm is
compatible along a tower, and the determinant norm has the corresponding
degree power. Absolute residue degrees and ramification indices multiply in
towers, giving the two displayed order identities. Positivity of the residue
degrees gives the order-zero criterion. These are mathematical assertions
to prove later, not hypotheses or definitional choices forcing the formulas.

John Tate, *Number theoretic background*, Corvallis Part II (1979),
section 1.4.6, printed page 7 (PDF page 16), explicitly uses
`|N_{E/F}(a)|_F = |a|_E` to identify the Weil norm restricted along a finite
extension. Worker 10 read this passage and the preceding sections 1.1–1.4.
Registered source `tate-1979-number-theoretic-background`, retained at
`C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`,
SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
This explains the role of this family in character transport. The present
target asserts only the field-side norm and order identities.

The existing `Langlands.PadicNormalizationStatement` has its own statement
and proof task. It concerns the arithmetic of a single field, comparison with
`Q_p`, and the spectral normalization within that field. This pair adds
compatibility for arbitrary finite `E/F`; it does not redefine or claim a proof
of that existing target. Reciprocity, its geometric Frobenius convention,
unit-image surjectivity, higher ramification, and conductor transport remain
separate parts of the broader local class-field-theory task.

## Exact dependencies and validation

Project imports are the accepted definition artifacts
`ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0` version 1
(`LocalField.Definitions`, transitively) and
`e3d7bbd4-f2b9-4970-a60f-bf6aa0b34bb2` version 1
(`LocalField.Normalization.Definitions`).
The latter's effective Lean SHA256 is
`b997a64a0f59ce13d45e2b5349de9ad87466a5e2d3e16ab3f1a4ef97a048214b`
and Markdown SHA256 is
`dac7d3aeb5229c505e5271f66d7decf6c7c4404853e9f15a363b4f9401902436`.
Their publication and unchanged current availability were verified at Library
commit `9007729971e6e6ecea63b5567b6d1621769ccfb0`.

The realization constructor mentioned above is artifact
`c342ec21-e5ee-4ba4-aec6-b4c1b1e2b629` version 1; it is contextual evidence
that the all-fields realization obligation is discharged, not an imported
premise of these propositions.
The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1,
Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Compilation and target inspection are development checks. Independent
literature/Lean/Markdown review and current Library publication are still
required before a proof task can use this exact statement.
