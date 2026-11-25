# A spherical lower bound in the actual standard Levi

The module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviXiLowerBoundStatement`
states the proof target `RationalLeviXiLowerBoundStatement.{u}`, at arbitrary
field universe `u`. This module contains no proof of the estimate.

Let `F` be a nonarchimedean local field, `G` a connected reductive affine
group of finite type, `i : S → G` a maximal split torus, `ν` generic, and
`J` a subset of the simple relative roots. Assume that a compact open `K0`
has the supplied structural property `SimultaneousStandardBasisAt i ν K0`.
Let `K` be any compact open subgroup with the minimal Levi Iwasawa
decomposition

```
M_J(F) = (P₀(F) ∩ M_J(F)) (K ∩ M_J(F)).
```

For every finite family `F0` of points of the torus centralizer, the
proposition asks for one positive constant `C` such that

```
φ_K^M(m) ≤ C Ξ_K^M(m),     m = f i(a), f ∈ F0, a ∈ CAplus(F,S,J).
```

The Levi Iwasawa weight `φ_K^M` is
`iwasawaWeight hM (standardLeviMinimalModulusOf i ν J)` and the spherical
function is `rationalLeviXi hKc hM`. For these representatives,
`m ∈ P₀(F) ∩ M_J(F)`, so the left side is
`δ₀^{M_J}(m)^(1/2)`. The chamber only requires dominance against the
roots in `J`; it imposes no dominance condition on the other ambient
simple roots. `F0` is arbitrary and need not itself lie in that chamber.
The constant can depend on this finite family. There is no ambient or
Levi Cartan covering, matrix representation or analytic estimate among the
premises.

The source is the lower bound in Waldspurger's Lemma II.1.1, printed p.251,
applied within `M_J`, as used in the proof of II.4.5, printed pp.262–263.
The compact and chamber adaptation and the finite translates are derived
content: the Library uses an arbitrary compact Iwasawa factor, while its
structural basis is supplied at `K0`. The usual proof chooses one
sufficiently small basis member, factors it relative to the minimal
parabolic in the Levi, and uses contraction on the Levi chamber. The
already published ambient `rationalXi_lowerBound` treats only the ambient
minimal split-component chamber; applying it directly does not establish
the present larger Levi chamber. The needed restriction and contraction
arguments remain part of the proof obligation, not hypotheses here.

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra* (2003), literature ID
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
Lemma II.1.1 and proof, printed p.251; Proposition II.4.5 and proof,
printed pp.262–263.
