# Henniart's characterization of the full correspondence at one character

`Langlands.Correspondence.fullCharacterization` proves the published
proposition `Langlands.Correspondence.FullCharacterizationStatement.{uF, uP, uA} F`
for every prime `p`, every `F : PadicField.{uF} p` and independent parameter
and automorphic carrier universes `uP` and `uA`. This is Henniart, *Une
caractérisation de la correspondance de Langlands locale pour GL(n)*, Bull. SMF
130 (2002), Corollary 1.8 (printed p. 592; proof in Section 4.5, printed
p. 600), registered as `henniart-2002-characterization`.

For a supercuspidal map `c0`, a full map `τ`, a nontrivial additive character
`ψ` and a reciprocity candidate `e`, the hypotheses are exactly those of the
statement:

- `IsSupercuspidalCorrespondence F c0`;
- `IsGeometricReciprocity F e`;
- `RankOneCompatibility F e τ`;
- `FullFactorCompatibilityAt F e ψ τ`: pair L-factor compatibility of `τ` at
  `ψ` for all ranks and all parameter classes, and pair epsilon-factor
  compatibility at `ψ` for some system with base component `e`.

The conclusion is `IsAssemblyOf F c0 τ`, together with `c = τ` for every full
map `c` with `IsAssemblyOf F c0 c`.

## The implemented proof

The theorem combines two published theorems:

- Henniart 2002, Corollary 1.6: `fullCharacterizationExtends F :
  FullCharacterizationExtendsStatement.{uF, uP, uA} F`
  (module `Langlands.Correspondence.FullCharacterizationExtendsProof`). Under
  the four hypotheses above, it gives `ExtendsSupercuspidal F c0 τ`: `τ` sends
  the zero-monodromy class of every irreducible Weil class `σ` to `c0 σ`.
- Henniart 2002, Theorem 1.8: `assemblyLCharacterization F :
  AssemblyLCharacterizationStatement.{uF, uP, uA} F`
  (module `Langlands.Correspondence.AssemblyLCharacterizationProof`). Given
  `IsSupercuspidalCorrespondence F c0`, `ExtendsSupercuspidal F c0 τ` and the
  pair L-factor identities at `ψ`, it gives both required conclusions. The L
  identities are needed only for ranks `j + 1 < k + 1`, for each class `D` of
  rank `k + 1` that is not an irreducible Weil parameter, and for each
  indecomposable class `D'` of rank `j + 1`.

The Lean proof introduces the data and the four hypotheses
`hc0 he hRankOne hFactors`. It applies `assemblyLCharacterization F c0 τ ψ hc0`
to the extension `fullCharacterizationExtends F c0 τ ψ e hc0 he hRankOne
hFactors`. That leaves the restricted lower-rank L-tests. For given
`k`, `j`, `D` and `D'`, the test is `hFactors.1 k j D D'`, because the
first component `hFactors.1 : FullPairLCompatibilityAt F ψ τ` covers all ranks
and all pairs of parameter classes. The rank inequality, the non-irreducibility
of `D` and the indecomposability of `D'` are not needed for it.

The hypotheses `IsGeometricReciprocity F e` and `RankOneCompatibility F e τ`, and
the epsilon component of `FullFactorCompatibilityAt`, are used only as inputs to
the extension theorem. This follows Henniart's route in Section 4.5: Corollary 1.6 gives the extension, and
Theorem 1.8 identifies `τ` with the assembly. The composition is the adapter
that Worker 1652 designed in the previous project instance (shared draft
revision 1 of this task). The axioms of the theorem are `propext`,
`Classical.choice` and `Quot.sound`.
