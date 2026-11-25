# The exact marked vertex and quaternionic model in local rank-one type C

This internal module constructs an actual quaternionic
symplectic presentation and determines the distinguished vertex of a local
rank-one group supplied with a type-C Cartan numbering. It does not prove the
upper bound on the absolute rank or the full local rank-one enumeration.

## Definitions and conclusion

`Langlands.GroupScheme.LocalRankOneTypeCPresentation K G n` stores a central
finite-dimensional division algebra `D : Type u` with `dim_K D = 4`, a
first-kind involution whose symmetric subspace has dimension three, and an
invertible trace-valued antihermitian form in `n` variables of Witt index one.
It includes an isomorphism of actual group schemes from `G` to the symplectic
group of the form, and a proof that `n` is nonzero.

`localRankOneTypeC_presentation_and_marking` applies over every nonarchimedean
local field `K : Type u`, without any field or residue characteristic
restriction. Its inputs are an affine locally finite type group scheme `G`,
actual `d : TitsIndexData G`, a numbering `e : d.Vertex ≃ Fin n` preserving
every entry of the type-C Cartan matrix, `2 ≤ n`, simple connectedness,
absolute almost simplicity, and `splitRank G = 1`. It concludes:

- the presentation data above exist;
- a vertex `a` is distinguished exactly when `(e a).val = 1`, that is, its
  one-based number is two;
- every element of the full absolute Galois group fixes every actual vertex.

`localRankOneTypeCPresentation` chooses the constructed presentation. This is
data containing an actual group-scheme isomorphism, rather than a type label.

## Implemented proof

The helper
`Quaternionic.FirstKindInvolution.exists_nonzero_alternating_of_wittIndex_one`
works over any division algebra with a first-kind involution. For a
nondegenerate trace-valued antihermitian form of Witt index one in `m ≥ 3`
variables, it constructs a nonzero alternating element. Published hyperbolic
pair existence gives vectors `e,f` with `h(e,e)=0` and `h(e,f)=1`. The kernel
of `x ↦ (h(x,e),h(x,f))` has positive dimension because the codomain has
dimension two. Choose a nonzero `w` in that kernel. If `h(w,w)=0`, then
`e,w` are independent and span a totally isotropic plane, contradicting Witt
index one. The nonzero value `h(w,w)` is alternating by the trace-valued
condition. This generalizes the orthogonal-vector argument in the published
`Quaternionic/HyperbolicBasis.exists_gramThree`; no normal-form conclusion in
arbitrary dimension is claimed.

For the local group, the unconditional published `typeCDivisionForm` produces
a degree `degree > 0`, size `m`, division algebra `D`, first-kind involution
`σ`, and form `H`, with
`m * degree = 2 * n`, `dim_K D = degree^2`, Witt index equal to the split
rank, an actual group-scheme isomorphism, and the exact marked-position
formula `(e a).val + 1 = j * degree` for `1 ≤ j ≤ splitRank G`.

The published
`Langlands.UnitaryInvolution.reducedDegree_dvd_two` applies with scalar
endomorphism `RingHom.id K` and involution `σ`. Its actual
`IsUnitaryInvolution` predicate requires additivity, reversed
multiplication, involutivity, and compatibility with that scalar map; it does
not require a nonidentity scalar map. A first-kind involution satisfies all
four conditions, and the identity preserves the valuation. The identity
`reducedDegree K D = Nat.sqrt (dim_K D)` identifies this degree with the
supplied `degree`, so `degree` divides two.

If `degree=1`, then `dim_K D=1`; the algebra map from `K` is surjective and
`σ` fixes every element of `D`. But `m=2*n≥4` and the preceding helper gives a
nonzero element `c=a-σ(a)`, a contradiction. Therefore `degree=2` and `m=n`.
The dimension and symmetric-subspace formulas become four and three.
Split rank one makes `j=1` in the marked-position formula, giving exactly
zero-based position one. Published type-C Cartan rigidity, via
`TypeCQuasiSplitInnerFormProof.star_eq_self`, gives triviality of the entire
star action.

## Provenance and scope

This is an internal composition of published Library theorems and elementary
linear algebra. It introduces no additional literature translation. Its
geometric input is `SimplyConnected/TypeCDivisionFormProof`, its arithmetic
input is `Algebra/LocalUnitaryResidue`, and its form lemmas come from
`Quaternionic/HyperbolicBasis`. All characteristics and universe `u` are
retained.

The theorem does not show `n=2` or `n=3`. In particular it does not prove
the published predicate `HasRankOneCIndex n`, which also requires that rank
bound; `localRankOneTypeC_index` (module `LocalRankOneCIndex`) proves it. It neither settles the other classical, exceptional or trialitarian
possibilities nor proves `LocalRankOneTitsIndexStatement`.
