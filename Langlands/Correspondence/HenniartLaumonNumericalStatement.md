# Laumon's numerical rank shift in equal characteristic

Let \(X=k((t))\) for a finite field \(k=\mathbb F_q\). For every rank
\(n\ge 1\), Swan exponent \(s\ge 1\), and \(f\mid\gcd(n,s)\), the
proposition `Langlands.Henniart.LaumonNumericalStatement` states
\[
  |W_X(n,s,f)|=|W_X(n+s,s,f)|.
\]
Here \(W_X(n,s,f)\) is the set of unramified-twist orbits of continuous
irreducible \(n\)-dimensional complex representations of the Weil group
of \(X\) with Swan exponent \(s\) and torsion number \(f\). The torsion
number is the cardinality of the unramified-twist stabilizer of a
representation class. The counts are extended cardinalities in `ℕ∞`.
At \(f=1\) the equality is \(T_X(n,s)=T_X(n+s,s)\).

Every nonarchimedean local field of characteristic \(p\) with residue
field \(\mathbb F_q\) is isomorphic as a valued field to
\(\mathbb F_q((t))\). Hensel's lemma lifts the roots of \(x^q-x\) to a
coefficient field and completeness gives expansions in a uniformizer.
The Laurent-series formulation thus covers every such field.

Lean writes \(n=d+1\), so the right-hand rank index `d + s` represents
\(n+s\). Both sides use `LocalNumerical.weilRefinedStratum` over
`X := LaurentSeries k` and `SeparableClosure X`. The coefficient field
and separable closure have universe `uK`, and both strata use the same
independent representation-carrier universe `uW`. The proposition installs
`Langlands.LocalField.Laurent.valuativeRel k` locally. Inference supplies
`Langlands.LocalField.Laurent.localField`, Mathlib's X-adic topology
and its `IsSepClosure` instance. [Refined strata](HenniartLocalNumerical.md)

## Provenance

This is E1b of input (I2) in Option II, Corollary `cor:Laumon` of the
numerical local Langlands route note (`operator-numerical-llc-route-2026-11-16`,
`numerical-LLC-route.tex`, lines 794–802). It is the refined orbit-count
form of Henniart (1988), §4.3. Laumon (1987), Théorème (2.4.3)(i) b), c),
gives the rank increase by the Swan exponent, preservation of that
exponent, and the equivalence onto the subcategory of slopes below one
for the local Fourier transform \(F^{(0,\infty')}\). Compatibility with
unramified twists makes the resulting bijection on irreducible classes
preserve stabilizers and descend to the refined orbit sets.
[Henniart, pp. 510–511](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=15)
· [Laumon, p. 163](https://www.numdam.org/item/10.1007/BF02698937.pdf#page=34)

Henniart cites “[Lm] 2.5.2 et 3.6.3” for twist compatibility. The route
note's Theorem `thm:Laumon` repeats the citation. In the published
Laumon paper, (2.5.2) concerns base change of the residue field, and §3.6
ends at Théorème (3.6.2). Définition (2.4.2.3) expresses the local
transform using vanishing cycles. An unramified character is pulled
back from a rank-one lisse sheaf on the common residue field. The
projection formula lets tensoring by this locally free sheaf pass
through the derived pushforward in nearby cycles and hence through the
vanishing-cycle triangle. This uses the definitions in SGA 7 II, Exposé
XIII, (2.1.1). [Source map, §2](../../notes/henniart/laumon-local-fourier-source-map.md#2-laumons-theorem-and-the-locators-henniart-cites)

Laumon's theorem concerns continuous \(\ell\)-adic representations of
the absolute Galois group for \(\ell\ne p\). The comparison with the
complex Weil representations in the Lean proposition belongs to the
proof of `cor:Laumon`. Its last paragraph passes between the two types
of orbit via finite-image representatives using Henniart (1988),
§§4.1–4.2. [Henniart, pp. 509–510](https://www.numdam.org/article/ASENS_1988_4_21_4_497_0.pdf#page=14)

## Sources

- `operator-numerical-llc-route-2026-11-16`, directory SHA-256
  `faece16e4d4722c37c1ba0e7ebba30a11d94b64639f20f19a6aa7ccff3faba3f`.
  `numerical-LLC-route.tex`, §2.2 and lines 784–802.
- `henniart-1988-numerical`, SHA-256
  `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.
  Sections 4.1–4.3, pp. 509–511.
- `laumon-1987-fourier-weil`, SHA-256
  `c666e214ae586651b9f171f6a39d755e58f96379970ffa98bafb2d9be591fc8e`.
  Définition (2.4.2.3) and Théorème (2.4.3)(i) b), c), p. 163.
  Section (2.5.2), p. 165, and §3.6, pp. 200–203, locate the citation discrepancy.
- `deligne-1973-sga7-xiii-cycles-evanescents`, SHA-256
  `898f984a6010f8088537f6cb3d4fe9d8b20d5a4ffb43e258f613dc35e97f7b2a`.
  SGA 7 II, Exposé XIII, (1.4.2.2) and (2.1.1)–(2.1.2), pp. 97–99.
  [SGA 7 II](https://link.springer.com/book/10.1007/BFb0060505)
