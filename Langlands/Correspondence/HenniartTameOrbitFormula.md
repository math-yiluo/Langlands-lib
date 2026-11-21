# Wild inertia orbits and the tame conductor counts

This module states the two representation-theoretic counting inputs of the
fixed-cutoff tame average, and the implication that assembles them.

## Definitions

- `weilWildInertia K` is the preimage in the actual local Weil group
  `W_K` of the published absolute wild inertia subgroup
  `Ramification.Padic.wildInertia K`, under `localProjection K`. It is normal,
  as the preimage of a normal subgroup.
- `WildClasses K` is `OpenKernelIrreducibleClasses (weilWildInertia K)`: actual
  isomorphism classes of finite-dimensional irreducible complex representations
  of wild inertia `P` with open kernel, with carriers in `Type uW`. `W_K` acts
  on these classes by the published inverse-conjugation action.
- `WildTrivialAt K v A` says that `A` is trivial on every element of `P` that
  lies in the actual Weil upper group `W_K^v`
  (`VirtualRepresentation.LocalWeil.Ramification.upperGroup K v`).
  `wildClassTrivialAt` is the same condition on classes; it is invariant
  under intertwining isomorphisms.
- `tameOrbitClasses K J r m j` is the set of wild classes that are fixed by
  every element of `J`, have dimension dividing `p^r`, and are trivial at
  every index `v > j / (p^r m)`. The last condition says that the slope of
  the class is at most `j / (p^r m)`.
- `frobeniusStableTameOrbits K J r m j φ` is the set of orbits of inertia
  `I_K = localInertia K` on wild classes that contain a member `c` of
  `tameOrbitClasses` such that `φ • c` lies in the same orbit.

## Statements

`WeilTameOrbitFormulaStatement.{uK,uW}`: let `p ∤ m`, let `J` be an open normal
subgroup of `W_K` with `J ≤ I_K` and `[I_K : J] = m`, and let `φ ∈ W_K` have
geometric degree `1`. Then
\[
  C_K(p^r m, j) = (q_K - 1)\,\#\{\text{$\varphi$-stable $I_K$-orbits of
  tame classes}\}
\]
in `ℕ∞`, where `C_K` is the published `Numerical.weilConductorCount`.

`WeilTameFieldFixedPointStatement.{uK,uW}`: let `p ∤ m` and `φ` have degree
`1`, and let `D : TameWeilFrobeniusData K m φ` be a Frobenius coset
parametrization with kernel `J`. For `g ∈ I_K` and `E` the field indexed by the
coset of `g`,
\[
  C_E(p^r, j) = (q_K - 1)\,\#\{c \in \text{tame classes for $J$} :
  (g\varphi)\cdot c = c\}.
\]

`WeilTameAveragingFromOrbitFormulasStatement.{uK,uW}` is the implication from
the parametrization statement and these two formulas to the published
`WeilTameAveragingStatement`. This module proves none of these statements.

## Provenance (derived)

H. Koch, *Bemerkungen zur numerischen lokalen Langlands-Vermutung* (1984),
registered as `koch-1984-numerical-langlands-remarks`, §8, printed p. 113
(PDF p. 6), Lemmas 6–8: pairs are counted with a fixed restriction to the
first ramification group `V₁` (wild inertia), and Lemma 7 gives `2n(q-1)`
pairs for each such restriction. G. Henniart, *La conjecture de Langlands
locale numérique pour GL(n)* (1988), registered as `henniart-1988-numerical`,
§2.1, printed p. 503 (PDF p. 8), relates the Swan exponent to the slope by
`s(ρ) = n λ(ρ)`; Proposition 2.2(c), printed p. 504 (PDF p. 9), identifies
torsion number one with irreducible restriction to inertia.

The statements replace Koch's determinant-normalized pairs by the
Library's unramified-twist orbits. A torsion-one irreducible `σ` of `W_K`
has irreducible restriction to `I_K`. Its restriction to `P` is a sum over
one `I_K`-orbit of wild classes. The orbit length is prime to `p`, divides
`m` exactly when the classes are `J`-fixed (here `I_K/J` is the cyclic
quotient of order `m`), and the rank is that length times a power of `p`.
Over each `φ`-stable orbit there are exactly `q_K - 1` such `σ` up to
unramified twist; this is Koch's factor `q - 1` in Lemmas 7 and 8. The slope
is computed on `P`, since `W_K^v ⊆ P` for `v > 0`. In a tame totally
ramified field `E` of degree `m`, `W_E ∩ I_K = J`, an element `gφ` of
`W_E` has degree one for `E`, `q_E = q_K`, and upper indices are multiplied by
`m`. The two formulas make these counts explicit at the fixed cutoff `j`.
