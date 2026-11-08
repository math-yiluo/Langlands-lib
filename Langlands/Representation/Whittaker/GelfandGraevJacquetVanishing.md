# Jacquet vanishing for compact induction detected by a scalar

Draft by Worker 1832 for task `d7c75f29-8641-4f6e-9a08-aaa69f1db69c`. This is a generic lemma
used in the computation of the Jacquet module of the Gelfand–Graev representation
(`GelfandGraevJacquetStatement`). It discards the non-open `N`–`P` double cosets.

## Setting

`P` is a locally compact topological group. `U` is a normal subgroup of `P` in which every compact
subset lies in a compact open subgroup of `U`. `S` is a closed subgroup of `P`, and `σ` is a
complex representation of `S` on `W`. `compactInduced S σ` is the compact induction
`c-Ind_S^P σ` with right translation. Its vectors are functions with `f(s g) = σ(s) f(g)` whose
support has compact image in `S \ P`.

## Results

- `exists_isCompact_support_subset_mul`: every `f` in `c-Ind_S^P σ` has a compact set `C ⊆ P` such
  that every `g` with `f(g) ≠ 0` can be written as `s c` with `s ∈ S` and `c ∈ C`.
- `subsingleton_coinvariants_compactInduced_of_scalar`: suppose some `x ∈ S` with `x ∈ U` acts on
  `W` by a scalar `c ≠ 1`, that is, `σ(x) w = c • w` for all `w`. Then the actual `U`-coinvariants
  `Jacquet.Coinvariants (compactInduced S σ) U` form a subsingleton, that is, they are zero.

## Proof

Fix `f` and take `C` as above. The conjugates `c⁻¹ x c` for `c ∈ C` form a compact subset of `U`
(`U` is normal). So they lie in one compact open subgroup `K` of `U`. Let `h` be the average of `f`
over `K`; it is `K`-fixed. The average is a finite mean of `K`-translates of `f`.

- If every `K`-translate of `f` vanishes at `g`, then `h(g) = 0`.
- At `q ∈ C` we have `q⁻¹ x q ∈ K`. Hence `h(x q) = h(q (q⁻¹ x q)) = h(q)`, and covariance
  gives `h(x q) = c • h(q)`. Since `c ≠ 1`, `h(q) = 0`.
- Otherwise `f(g k) ≠ 0` for some `k ∈ K`, so `g k = s q` with `s ∈ S`, `q ∈ C`. Then
  `h(g) = h(g k) = σ(s) h(q) = 0`.

So `h = 0`. By `Compact.averageMap_eq_zero_iff`, `f` lies in the coinvariant kernel for `K`, and
hence in the kernel for `U`. Its class in the `U`-coinvariants is zero.

## Provenance

This is the standard averaging argument behind the Bernstein–Zelevinsky geometric lemma
(Bernstein–Zelevinsky 1977, §5, and the analogous vanishing in Bushnell–Henniart's treatment of
Whittaker models). The formulation here is internal.
