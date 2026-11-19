# The Laumon–Deligne count for p-adic fields

For every prime \(p\), every p-adic field \(E\), and all integers \(d\ge 1\)
and \(1\le s<d\,e_E\), the proposition (LD) states
\[
T_E(d,s)=T_E(d+s,s).
\]
Here \(e_E=v_E(p)\) is the absolute ramification index. The count \(T_E(d,s)\)
is the number of unramified-twist orbits of irreducible complex Weil
representations of dimension \(d\) and Swan exponent \(s\) whose restriction
to inertia is irreducible.

`Langlands.Henniart.LaumonDeligneCountStatement.{uK, uW}` uses the canonical
absolute ramification index `K.canonicalTopologicalData.ramificationIndex`
for each `K : PadicField.{uK} p`. The count
`Numerical.weilTwistIrreducibleCount.{uK, uW} K k s` represents \(T_E(k+1,s)\)
by the extended cardinality in `ℕ∞` of the torsion-number-one Weil stratum.
Thus the right side uses rank index `k + s`, representing \(d+s\). The field
universe `uK` and Weil representation universe `uW` are independent.
[Refined orbit strata](HenniartRefinedStrata.md)

## Provenance

The operator's route note `operator-numerical-llc-route-2026-11-16` formulates
the combined p-adic statement as Proposition `prop:LD` in
`numerical-LLC-route.tex`, lines 820–830. This formulation and its numbering
come from the route note, where (LD) is input (I2) of Option II. It combines
two inputs from the literature.

- **E1a (close fields).** For \(E'=\mathbb F_{q_E}((t))\), with \(q_E\) the
  residue field cardinality of \(E\), the comparison of ramification quotients
  preserves the rank, Swan exponent and unramified twists. It gives
  \(T_E(d,s)=T_{E'}(d,s)\) for \(s<d\,e_E\). Deligne (1984),
  *Les corps locaux de caractéristique p, limites de corps locaux de
  caractéristique 0*, §3.5, p. 144 (`bdkv-1984-representations-local-field`).
  [Henniart (1988), §5.1, p. 512](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=17)
- **E1b (local Fourier transform).** In characteristic \(p\), the numerical
  consequence of Laumon's local Fourier transform is
  \(T_{E'}(d,s)=T_{E'}(d+s,s)\) for \(d,s\ge 1\). The transform raises the rank
  by the Swan exponent and preserves that exponent. The orbit-count form
  uses compatibility with unramified twists.
  [`laumon-1987-fourier-weil`, Théorème (2.4.3)(i) b), c), p. 163](https://www.numdam.org/item/10.1007/BF02698937.pdf#page=34)
  · [`henniart-1988-numerical`, §4.3, pp. 510–511](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=15)

The route note applies E1a in ranks \(d\) and \(d+s\), since
\(s<d\,e_E\le(d+s)e_E\), and uses E1b for the intervening equality over \(E'\).
