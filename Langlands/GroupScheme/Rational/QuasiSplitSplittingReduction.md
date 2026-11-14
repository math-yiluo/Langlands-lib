# Reducing quasi-split splitting to actual relative-root irreducibility

This internal derived unit constructs the source root-system input needed by
the preceding rational-restriction splitting argument. It proves the
implication
`RelativeRootSystemIrreducibleStatement.{u} →
QuasiSplitSimplyLacedSplittingStatement.{u}` at every universe `u`, without
excluding any field characteristic. The irreducibility statement remains an
explicit hypothesis, so this is a reduction, not an unconditional proof of
either published target.

First,
`IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension` proves absolute
almost-simplicity after any algebraic field extension `K/k`. The algebraic
closures of `k` and `K`, viewed as algebraic closures of `k`, are
`k`-isomorphic. Almost-simplicity transports along the corresponding base
isomorphism. The two published pullback comparisons identify the resulting
group with the algebraic-closure base change of `G_K`. The published
field-extension reflection theorem then supplies almost-simplicity of
`G_K` itself. This proves both clauses of absolute almost-simplicity; no
perfectness or separability premise is added.

Next, `IsAlmostSimple.relativeRoots_nonempty_of_split_maximalTorus` proves
that a split maximal torus in an almost-simple group has an actual root.
If the roots were empty, the published connected-reductive rank-zero
theorem would make the torus inclusion an isomorphism. Transporting points
back into the commutative torus would make every test-point group
commutative, contradicting almost-simplicity.

The rational-restriction part takes a quasi-split absolutely almost-simple
affine, locally finite type group `G` over `k`; a maximal split torus
`a : S → G`; a containing maximal torus `j : T → G`; a supplied
factor `f : S → T`; and a finite Galois extension `L/k` splitting `T`.
It also takes the full-root predicate
`HasReducedSimplyLacedRelativeRootSystem a` and the published irreducibility
statement as an input. The construction proceeds as follows:

- Absolute almost-simplicity ascends to `L`, and maximality of `j` persists
  under base change. The split torus `T_L` is therefore a maximal split
  torus of the almost-simple group `G_L`.
- The published `relativeRootSystem` theorem constructs a finite actual
  root system `Q` on the rational span of the roots of `j_L`, paired with
  its rational dual by evaluation. Its entire root image equals the
  rationalized actual roots.
- The nonemptiness lemma and the explicit
  `RelativeRootSystemIrreducibleStatement` premise establish irreducibility
  of this `Q`. No choice of root system or irreducibility witness remains
  as an additional premise of the resulting theorem.
- Unpacking the full reduced simply-laced predicate gives the symmetric
  target root system `P`. The preceding rational-restriction injectivity
  theorem applies to `P` and `Q`.

This proves
`IsQuasiSplit.rationalRootRestriction_injective_of_relativeRootSystemIrreducible`.
The injectivity result uses the Galois hypothesis and does not itself
require finite degree; the subsequent torus descent uses the stated
finite-dimensional hypothesis.
`IsQuasiSplit.torusFactorIsoOfRelativeRootSystemIrreducible` then constructs
`S.toGrp ≅ T.toGrp` from the preceding torus-splitting module. Its homomorphism
is exactly `CommGroupScheme.groupHom f`, as its `_hom` theorem records.
The corresponding maximality theorem proves `IsMaximalTorus a`.

Finally,
`quasiSplitSimplyLacedSplitting_of_relativeRootSystemIrreducible`
chooses a containing maximal torus using the published extension theorem
for affine groups locally of finite type. It chooses a finite Galois
splitting extension using the published theorem for every field torus,
then applies the construction above. The conclusion is exactly the
published `QuasiSplitSimplyLacedSplittingStatement.{u}`.

The provenance is the composition of the named Library constructions,
the algebraic-closure transport argument, and the preceding internal
rational-restriction units. No external source is newly transcribed here.
The module does not prove
`RelativeRootSystemIrreducibleStatement`, construct a stable chamber, or
prove the host `LocalAnisotropicAffineDiagramStatement`.
