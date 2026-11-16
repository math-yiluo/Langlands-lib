# Consequences of rank-one normalization

This module draws one consequence of the third condition of
`LocalSplitCell.RankOneNormal`, `N² = a^∨(-1)`: conjugation by `N²` acts on every root group
by a sign. It imports `Langlands.GroupScheme.Reductive.LocalSplitRankOneNormalStatement`. It
contains no `Prop`-valued statement.

## Results (namespace `Langlands.GroupScheme.LocalSplitCell`)

The setting is a commutative ring `R`, a group scheme `G` over `Spec R` with affine structure
morphism, a coordinate split torus `i : T_I → G` with `I` finite, and
`P : RootDatum J (I → ℤ) (I → ℤ)`.

- `coPairing_root_coroot`: if `R` is local and `P` is a fibrewise root datum of `(G, i)`
  (`IsFibrewiseRootDatumOf`), then for all indices `β`, `a`, the coordinate pairing
  `coPairing (P.root β) (P.coroot a) = ∑ⱼ (P.root β) j · (P.coroot a) j` equals
  `P.pairingIn ℤ β a`.
- `conj_sq_rootPoint`: in the same setting, let `N` be a global point of `G` with
  `N · N = a^∨(-1)`, that is, `cocharPoint (P.coroot a) (𝟙_) (-1) ≫ i.hom.hom`. Let `w` be a
  root parametrization of `i` for `P.root β` (`IsRootParametrization`). Then over every
  `Z` over `Spec R` and for every global function `x` on `Z`,
  `(N N) w(x) (N N)⁻¹ = w(σ • x)`. Here `N` stands for its pull-back
  `G.constantPoint N Z`, and `σ = (P.pairingIn ℤ β a).negOnePow ∈ ℤˣ` is the sign
  `(-1)^⟨β, a^∨⟩`.

## Proof

**The pairing.** The pairing of the root datum is recovered on a residue-field fibre by the
imported `IsFibrewiseRootDatumOf.pairing`, applied to the residue field of `R`. There it is
the coordinate pairing `coPairing`, and Mathlib's `algebraMap_pairingIn` identifies it with
`P.pairingIn ℤ`.

**The square.** `N N` is the image under `i` of the torus point `a^∨(-1)`. Write it as a
pull-back of a global torus point (imported `GroupScheme.constantPoint_mul` and
`toUnit_comp_eq_constantPoint`). The equivariance of the root parametrization `w`
(`IsRootParametrization.equivariant`) turns conjugation by it into multiplication of `x` by
the character `β` evaluated at `a^∨(-1)`. The imported `torusChar_cocharPoint` and
`VectorGroup.charValue_comp` compute this value as `(-1)^{coPairing (P.root β) (P.coroot a)}`,
which is `(-1)^⟨β, a^∨⟩` by `coPairing_root_coroot`. A parity split
(`Int.even_or_odd`) gives `1` or `-1`, matching `Int.negOnePow`.

## Provenance and scope

This is internal derived content toward the Isomorphism Theorem over an arbitrary local
ring. It is the computation `int(w_α²) x_β = (-1)^{⟨β, α^∨⟩} x_β`, used in SGA 3, Exp. XXIII,
3.1.1 and in Conrad, *Reductive group schemes* (2014), Corollary 5.1.9, for
`w_α² = α^∨(-1)`. The hypothesis `N · N = a^∨(-1)` is the third condition of
`RankOneNormal`. The module does not prove that condition.
