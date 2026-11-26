# Simple characters with their domains

The domain `H^{m+1}(β,𝔄)` can vary with `β`. The pair `(H^{m+1}(β,𝔄), θ)`
records the subgroup on which each `θ` is defined, so equality and intersection
of character sets in the ambient group have their ordinary set-theoretic
meaning. In particular, a common pair certifies that the domains coincide.

In the source, `F` is a nonarchimedean local field, `V` is finite-dimensional
over `F`, and `𝔄` is the hereditary order represented by the chain `L`.
The additive character `ψ_F` satisfies `IsBKAdditiveCharacter`, so it is
trivial on `𝔭_F` and nontrivial on `𝔬_F`.

For a simple stratum `S` with element `β` and order `𝔄`,
`simpleCharacterPairs ψF S m` forms `Ĉ(𝔄,m,β)` in this setting at depths
`0 ≤ m < n` for which `[𝔄,n,m,β]` is simple. This includes the stratum's own
nonnegative depth and every lower nonnegative depth. The definition takes the
union of the pairs computed using `simpleHGroup` and `simpleCharacters` over
all `DefiningSequenceChoice`s for `S`. The source identifies the sets obtained
from different defining sequences at these inputs.

`SimpleStratumAt L n m` uses the existing `Stratum` and `IsSimple` on the
fixed lattice chain `L` representing `𝔄`. `simpleCharacterPairsAt ψF L n m`
forms `S^m_n(𝔄)` by taking the union over those strata. Repetitions in this
union have no effect.

Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy classes*
(1994), conventions on printed pp. 109–110 (PDF pp. 122–123) and §2, the
definition of `S^m_n(𝔄)` and (2.1), printed p. 118 (PDF p. 131).
Literature ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
The choice independence of the character construction is Bushnell and Kutzko,
*The admissible dual of GL(N) via compact open subgroups* (1993), (3.3.20),
printed p. 113 (PDF p. 125). Literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
