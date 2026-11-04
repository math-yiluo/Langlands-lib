# Linearizing coordinates from a stable space of additive polynomials

Helper module for the proof of `TorusVectorActionLinearizationStatement` (task 3be1ce22).
Internal machinery only. Everything is in namespace
`Langlands.GroupScheme.TorusLinearization`. Throughout, `k` is a field and
`k[X] := MvPolynomial (Fin n) k`.

## Linear parts

- `linPart : k[X] →ₗ[k] (Fin n → k)` sends `f` to its linear part, the family of its
  coefficients at the monomials `X j` (`linPart_apply`).
- `linPart_X i`: `linPart (X i) = Pi.single i 1`, the `i`-th standard basis vector.
- `linPart_sum_smul c Φ hΦ`: if `linPart (Φ j) = Pi.single j 1` for every `j`, then
  `linPart (∑ j, c j • Φ j) = c`.
- `linPart_eq_zero_of_mem_higher` (`p` prime): every element of `higher n k p`, the
  span of the `X l ^ p ^ s` with `s ≥ 1`, has linear part `0`.
- `linPart_mem_map_of_mem_frobSpan` (also `CharP k p`): let `W` be a subspace of
  `addSpan n k p`, the span of all `X l ^ p ^ s`. Then every element of the Frobenius
  span `frobSpan k p 0 W` (the span of the `w ^ p ^ r`, `w ∈ W`, `r ≥ 0`) has its
  linear part in `linPart '' W`.

## Main result

`PointAction.exists_linearizing_of_subspace a p W hWA hWs hinj hgen`. Here `a` is a
`PointAction k K I n`, `p` is a prime with `CharP k p`, and `W` is a `k`-subspace of
`k[X]` with the following properties:

- `hWA`: `W ≤ addSpan n k p`;
- `hWs`: `W` is `a`-stable (`PointAction.Stable`, from `Universal.lean`). That is,
  for every `k`-algebra `B` and point `t : a.Pt B`, each `a.pull t w` with `w ∈ W`
  lies in the `B`-span of the images of `W` in `MvPolynomial (Fin n) B`;
- `hinj`: the only element of `W` whose coefficients at all `X j` vanish is `0`;
- `hgen`: every variable `X j` lies in `frobSpan k p 0 W`.

The conclusion gives `Φ Q : Fin n → k[X]` such that every `Φ i` is additive
(`IsAddPoly`), `aeval Φ (Q j) = X j` and `aeval Q (Φ i) = X i` for all `i, j`, and
for every `k`-algebra `B` and point `t : a.Pt B` there is a matrix
`b : Fin n → Fin n → B` with
`a.pull t (Φ i) = ∑ j, b i j • map (algebraMap k B) (Φ j)` for every `i`. This is
exactly the hypothesis `hcore` of `torusVectorActionLinearization_of_linearizing` in
`TorusVectorLinearization/Assembly.lean`.

## Proofs

`linPart_eq_zero_of_mem_higher`: the generator `X l ^ p ^ s` is the monomial with
exponent `single l (p ^ s)`. Since `p ^ s > 1` for `s ≥ 1`, this exponent differs
from every `single j 1`. So the generators lie in the kernel of `linPart`, and
hence so does their span.

`linPart_mem_map_of_mem_frobSpan`: induction on the span. Linearity of `linPart`
handles sums and scalar multiples. For a generator `w ^ p ^ r` with `w ∈ W`: if
`r = 0` it is `w` itself. If `r ≥ 1`, `pow_mem_of_mem_addSpan` (from
`Complement.lean`) puts `w ^ p ^ r` in `higher n k p`, because `w ∈ addSpan` and
`(p : k) = 0`. Its linear part is then `0`.

`exists_linearizing_of_subspace`:

1. By `hgen` and the previous lemma, `Pi.single i 1 = linPart (X i)` lies in
   `linPart '' W`. So choose `Φ i ∈ W` with `linPart (Φ i) = Pi.single i 1`.
2. For `w ∈ W`, the difference `w - ∑ j, linPart w j • Φ j` lies in `W` and has
   linear part `0` by `linPart_sum_smul`. By `hinj` it is `0`. So every `w ∈ W`
   equals `∑ j, linPart w j • Φ j`.
3. By (2), every `w ∈ W` equals `aeval Φ (∑ j, linPart w j • X j)`, so it lies in
   the subalgebra `(aeval Φ).range`. A subalgebra is closed under powers, so the
   generators `w ^ p ^ r` of `frobSpan k p 0 W` lie in it too, and so does the
   whole Frobenius span. By `hgen`, each `X j` is then `aeval Φ (Q j)` for some
   chosen `Q j`. `aeval_eq_X_of_aeval_eq_X` (from `NoetherianInverse.lean`)
   gives the other composition, `aeval Q (Φ i) = X i`.
4. Additivity: `Φ i ∈ W ≤ addSpan n k p`, and `addSpan_le_addPolys` (from
   `AdditivePolynomials.lean`) shows that elements of `addSpan` are additive when
   `(p : k) = 0`.
5. Linearity: by (2), the image of each `w ∈ W` in `MvPolynomial (Fin n) B` is
   `∑ j, algebraMap k B (linPart w j) • map (algebraMap k B) (Φ j)`. So the `B`-span
   of the images of `W` lies in the `B`-span of the family
   `j ↦ map (algebraMap k B) (Φ j)`. By `hWs`, `a.pull t (Φ i)` lies in that span.
   `Submodule.mem_span_range_iff_exists_fun` then produces the coefficients
   `b i j`.

Step (3) does not use Frobenius additivity: the image of `aeval Φ` is a subalgebra,
so it already contains all powers of elements of `W`.

## Provenance

Worker 1416 specified the interface (hypotheses and conclusion) as the last step of
their characteristic-`p` linearization argument. This module carries out only that
final linear-algebra step. The space `W` is built elsewhere (Worker 1416's
`Generation` module). The proof follows Worker 1416's outline, with the
simplification in step (3).

The idea is related to Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd ed.),
Proposition B.4.1 and Proposition B.4.2 (pp. 575–577), which feed into Theorem B.4.3.
Proposition B.4.1 embeds the group equivariantly via a stable finite-dimensional
space of homomorphisms to `G_a`, i.e. of additive polynomials. In the proof of
Proposition B.4.2, a projection that is an isomorphism on Lie algebras is shown to be
an isomorphism. In this module the role of the Lie algebra is played by the linear
parts. The polynomial formulation and its proof are internal to this project and do
not appear in the reference.
