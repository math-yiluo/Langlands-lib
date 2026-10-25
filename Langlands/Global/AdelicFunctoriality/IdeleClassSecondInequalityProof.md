# The second inequality for actual idele classes

Author: Worker 123.

`Langlands.Global.AdelicFunctoriality.ideleClassSecondInequality.{u,v}`
proves exactly the published proposition
`Langlands.Global.AdelicFunctoriality.IdeleClassSecondInequality.{u,v}`.
For every Galois extension of number fields `L/K`, it gives

\[
 [C_K : N_{L/K}(C_L)] \mid [L:K].
\]

The carriers `K : Type u` and `L : Type v` have independent universes.
The statement includes nonabelian Galois extensions and the degree-one case.
The map is the unchanged actual `ideleClassNorm`; its range index is
`(ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index`.
Since the degree is positive, divisibility also entails that the index is
finite. There are no additional arithmetic or cohomological assumptions
on the final theorem.

The helper lemmas are in the namespace `SecondInequalityProof`.
`dvd_of_primewise_coprime_factor` proves a natural-number divisibility
prime power by prime power. For each prime `p`, suppose `d` divides
`a * b`, `p` is coprime to `a`, and `b` divides `n`. Every power of `p`
dividing `d` must then divide `b`, hence `n`. Mathlib's
`Nat.dvd_iff_prime_pow_dvd_dvd` gives `d ∣ n`.

The proof reuses the published
`ideleClassNorm_range_index_dvd_mul_of_tower`. For a compatible tower
`M/L/K`, norm transitivity identifies the top norm with a composite.
The subgroup-image index formula then gives

\[
 [C_K:N_{M/K}C_M] \mid
 [C_K:N_{L/K}C_L]\,[C_L:N_{M/L}C_M].
\]

This helper retains Mathlib's zero convention for infinite index; it does
not assume finiteness. Its implementation and provenance are described
in `CyclotomicSecondInequalityReduction.md`.

`ideleClassNorm_index_dvd_of_isPGroup` proves the result for a Galois
p-group extension by strong induction on its degree, keeping the base
field fixed. In degree one the degree-power bound gives index dividing
one. Otherwise the Galois group has order divisible by `p`. A finite
p-group is nilpotent, so Mathlib supplies a normal subgroup `H` of order
`p`. For its fixed field `E`, the extension `L/E` has degree `p`, while
`E/K` is Galois of smaller degree and its Galois group is a p-group by
the quotient equivalence. The induction hypothesis for `E/K`, the
prime-degree inequality for `L/E`, and the tower index divisibility
prove the result, using multiplicativity of extension degrees.

`ideleClassNorm_index_dvd_of_sylow_cases` handles a general Galois
extension. For each prime `p`, choose a Sylow p-subgroup of `Gal(L/K)`
and let `E` be its fixed field. The subgroup index `[E:K]` is coprime
to `p`, and `Gal(L/E)` is a p-group. The degree-power bound applies to
`E/K` even though this intermediate extension need not be Galois.
Together with the p-group result and the tower lemma, it yields

\[
 [C_K:N_{L/K}C_L] \mid [E:K]^r [L:E].
\]

The first factor is coprime to `p`; the second divides `[L:K]`.
The numerical lemma therefore proves the desired divisibility.

`secondInequality_of_inputs` assembles these reductions using the tower
proposition at universes `(u,v,v)` and `(v,v,v)`, the finite-index and
degree-power proposition at `(u,v)` and `(v,v)`, and the prime-degree
proposition at `(v,v)`. It uses the second conjunct of each degree-power
input. Intermediate fields are subtypes of the upper field, so these
specializations preserve the independent universes of the conclusion.
The final theorem discharges all five premises with the published
`ideleClassNormTower`, `ideleClassNormIndexFinite`, and
`ideleClassPrimeDegreeSecondInequality` theorems. The conditional helper
is not the submitted target; the final unconditional theorem is.

The provenance is Artin and Tate, *Class Field Theory* (2009), Chapter
VI §1, printed pp.19–20 (PDF pp.28–29): the second fundamental
inequality, the degree-power and tower-index lemmas, and Reduction 1.
The registered original is `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The original passage was read directly during development, and its
errata were checked. The implemented proof makes the prime tower
explicit through normal subgroups of order `p`, then applies the
source's Sylow reduction using Mathlib's Galois correspondence.

This module develops Worker 123's earlier private reduction and imports
published arithmetic proofs by name. The norm tower, finite-index,
prime-degree and cyclotomic modules retain their own authorship and
proof explanations. No private work by another worker is copied.
The prime-degree theorem contains the separately established arithmetic
and first-inequality inputs. This general reduction uses no global
reciprocity, global fundamental class, or global idele-class H¹
vanishing as a premise. The target pair and all imported definitions
remain unchanged; no new axiom or proof hole is introduced.
