# Unramified norm membership by normalized order

Worker 90 proves `Langlands.LocalClassField.unramifiedNormMembership.{u,v}`
with exactly the published type
`Langlands.LocalClassField.UnramifiedNormMembership.{u,v}`. For every prime,
finite p-adic fields in independent universes, their compatible finite
extension, and arbitrary supplied `TopologicalData T,S` with equal absolute
ramification indices, the theorem states

\[
a\in N_{E/F}(E^\times)\quad\Longleftrightarrow\quad
[E:F]\mid\operatorname{ord}_F(a).
\]

Divisibility is in the integers. The norm, its image subgroup, and the orders
are the published `normUnits`, `normSubgroup`, and supplied normalized `ord`.
The final theorem has no Galois hypothesis or additional proof premise.

## Implemented proof

The public helper
`Langlands.PadicField.TopologicalData.mem_unitFiltration_zero_of_ord_eq_zero` constructs an
integer-ring unit from a field unit of order zero. The element and its inverse
have normalized absolute value one, so both belong to the supplied integer
ring. Their inverse identities construct the integer-ring unit. Reduction
modulo the zeroth power of the maximal ideal is reduction modulo the whole
ring; thus the unit lies in the actual reduction kernel at level zero. Its
inclusion is the original field unit, proving membership in `T.unitFiltration 0`.

The general helper `normMembership_of_order_and_unitNorms` assumes the
norm-order formula and norm surjectivity at level zero. For the forward
implication, a witness `b` for membership in the norm image gives

\[
\operatorname{ord}_F(N_{E/F}(b))=[E:F]\operatorname{ord}_E(b),
\]

which exhibits the required divisibility. Conversely, write
`T.ord a = [E:F] * k`. The published `S.ord_surjective_nonzero` supplies a
nonzero element of order `k`, hence a field unit `b` of that order.
Multiplicativity of order, its inverse formula, and the norm-order identity
show that `a / N(b)` has order zero. The helper places this quotient
in `T.unitFiltration 0`. Surjectivity on that group supplies a unit `c` with
`N(c) = a / N(b)`, and multiplicativity gives `N(c * b) = a`.

The closing theorem discharges both premises of the general helper. It uses
`ord_normUnits_of_unramified F E T S he`, imported from
`Langlands.ClassFieldTheory.Local.NormOrderProof`, for the displayed genuine
norm-order formula. It specializes `unramifiedUnitNorms p F E T S he` from
`Langlands.ClassFieldTheory.Local.UnitNormProof` at `n = 0` for unit-norm
surjectivity. Both imported results are independently accepted and published.
They retain the supplied data and independent field universes. The statement
pair and all existing imported pairs are unchanged.

## Provenance and dependencies

This is a derived kernel formulation of Jean-Pierre Serre, *Local Fields*,
Greenberg English translation, GTM 67 (1979), Chapter V introduction,
printed p.80 (PDF p.87), and Section 2, Proposition 3(c), corollary,
finite-residue-field remark and non-Galois exercise, printed p.82 (PDF p.89).
Worker 90 read PDF pp.87–89. The general norm-order equation is in the chapter
introduction; Lemma 2 on printed p.81 (PDF p.88) is the filtered-group lifting
result used in the unit-norm argument. The membership proof here chooses an
arbitrary source element of order `k` and takes a quotient; it does not require
compatible uniformizers. The order-zero integer-unit construction is a derived
bridge to the Library's actual filtration definitions.

Registered source: `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
No source-specific errata file was found in the project notes.

The norm-order proof was authored by Worker 110; the unit-norm proof was
authored by Worker 26. This module imports their published declarations and
reuses the published normalization and filtration API. Their proofs are not
copied or reproved here. No local reciprocity or local invariant theorem is
used. The implementation uses Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
