# Proof that unnormalized `Φ⁻` sends irreducibles to irreducibles or zero

Author: Worker 806.

This module proves `Langlands.Derivative.Mirabolic.phiMinusIrreducible`, of type
`PhiMinusIrreducibleStatement.{uF, uV} F T m`, for every p-adic field `F`, topological
data `T` and `m : ℕ`.

## Route

The source (Bernstein–Zelevinsky 1976, Proposition 5.12 and the proof of Corollary
5.13 b), pp.46–48) deduces the result from the equivalence `Φ⁺Φ⁻ ≅ id` on
representations with `Ψ⁻ = 0`. The Lean proof does not use that equivalence. It uses a
direct averaging argument over a finite quotient of radical lattices.

### Abstract lemma

`eq_bot_or_eq_top_of_radicalQuotient` works with any linear surjection `q : V → W` and
any subspace `σ ⊆ W`. It assumes the following:

- `ξ` is a smooth irreducible representation of `mirabolic (m + 1) F`;
- `q (ξ (u c) v) = ψ(c_last) q v` for the radical element `u c`, where `c_last` is the
  last coordinate of `c ∈ F^(m+1)`;
- `q v ∈ σ` implies `q (ξ (successor h) v) ∈ σ` for every `h ∈ mirabolic m F`.

It concludes `σ = ⊥ ∨ σ = ⊤`. Suppose `σ ≠ ⊥` and pick `x` with `q x ∈ σ`,
`q x ≠ 0`.

1. **Reduction (`hred`).** Let `x'` satisfy `q x' ≠ 0` and `q (ξ (levi g) x') ∈ σ` for
   every `g ∈ GL_(m+1)(F)`. The vectors `v` with `q (ξ g v) ∈ σ` for all `g` in the
   mirabolic group form a subrepresentation `S`. Every mirabolic element is
   `u(c) · levi g` (`eq_radicalElement_mul_levi`), so `x' ∈ S`. Because `q x' ≠ 0`,
   `S ≠ ⊥`, so `S = ⊤` by irreducibility. Since `q` is surjective, `σ = ⊤`.
2. **Lattices.** Smoothness gives an open subgroup `K` fixing `x`. Let
   `J = levi⁻¹ K`. The last-row image of `J` is a neighbourhood of the last row `e` of
   the identity (`lastRow_image_mem_nhds`). So some box `(π^(-n₀) O)^(m+1)` of
   increments `d` has `e + d` in that image. Some box `(π^(-l) O)^(m+1)` of radical
   coordinates has `u(d) ∈ K`, so `u(d)` fixes `x`. From `q x ≠ 0` this gives
   `ψ(d_last) = 1` on that box. The boxes are the `latticeBox` subgroups, built from
   the Library lattices `T.additiveLattice`.
3. **Average.** Let `M = max l (n(ψ) − n₀)`, where `n(ψ)` is `T.additiveConductor ψ`.
   Let `Q` be the quotient of the `M`-box by the `l`-box. It is finite, because an
   open subgroup of a compact group has finite index. Put
   `x' = Σ_{c ∈ Q} ψ(−c_last) ξ(u c) x`, with fixed coset representatives.
4. **Key identity (`hkey`).** By `levi_mul_radicalElement`,
   `q (ξ (levi g) x') = (Σ_{c ∈ Q} χ_g(c)) · q (ξ (levi g) x)`, where
   `χ_g(c) = ψ((g c)_last − c_last)` is an additive character of the `M`-box. For
   `g = 1` the sum is `|Q|`, so `q x' = |Q| q x ≠ 0`.
5. **Each Levi translate lies in `σ`.** Fix `g` and let `r` be the last row of `g`.
   - Suppose `ψ((r − e)_j t) = 1` for every `j` and every `t ∈ π^(-M) O`. Then, by
     `mem_additiveLattice_of_forall_mul_eq_one`, `r − e` lies in the `n₀`-box. So `r`
     is the last row of some `j ∈ J`, and `g = a j` with `a` mirabolic
     (`lastRow_mem_image_iff`). Then `ξ (levi g) x = ξ (successor a) x`, which `q` maps
     into `σ`.
   - Otherwise some `j₀` and `t` give `χ_g(t e_(j₀)) ≠ 1`. If `q (ξ (levi g) x) = 0`
     the translate is `0 ∈ σ`. If not, `χ_g` is trivial on the `l`-box: there `u(d)`
     fixes `x` and `ψ(d_last) = 1`. Then the character sum over `Q` vanishes
     (`sum_out_eq_zero`), and again the translate is `0 ∈ σ`.

Step 1 then gives `σ = ⊤`.

### Final theorem

`phiMinusIrreducible` applies the abstract lemma to the Library quotient
`phiMinusQuotient T ψ m (SmoothRep.of ξ hs)`. It is surjective
(`phiMinusQuotient_surjective`) and the radical acts through `θ_ψ`
(`phiMinusQuotient_radical`, `theta_radicalElement`). Take `σ` to be the underlying
submodule of a subrepresentation of `Φ⁻ ξ`. It is stable under the successor action,
because `Φ⁻ ξ` acts through `successor`.

## Auxiliary declarations

The proof uses these lemmas from the helper module
`Langlands.Representation.Derivative.MirabolicLatticeBox`:

- `sum_out_eq_zero`: a character sum over a finite quotient `G ⧸ L` vanishes if the
  character is trivial on `L` and not identically one.
- `eq_one_of_smul_eq_self`: `a • v = v` with `v ≠ 0` forces `a = 1`.
- `latticeBox T k N`: the product lattice `(π^(-N) O)^k`, with lemmas that it is open,
  compact and monotone in `N`, that it is cofinal at `0`
  (`exists_latticeBox_subset`), and that quotients of boxes are finite.
