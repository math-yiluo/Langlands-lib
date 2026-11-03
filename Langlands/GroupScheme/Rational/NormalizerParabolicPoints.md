# Normalizing points in dynamic and standard parabolics

This internal auxiliary module proves that a rational point normalizing a
split subtorus `i : T ⟶ G` and lying in a dynamic parabolic `P_G(ζ)` of a
cocharacter `ζ` of `T` already lies in the dynamic centralizer `Z_G(ζ)`.
It follows that the normalizing points of the standard parabolic `P_J(k)`
lie in the standard Levi `L_J(k)`, and that their classes lie in the
standard relative Weyl group `W_J`. The module introduces no definitions; it
only proves theorems about the published `normalizerPoints`,
`centralizerPoints`, `relativeWeylGroup`, `Dynamic.parabolic`,
`Dynamic.centralizer`, `standardParabolicPoints`, `standardLeviPoints` and
`standardRelativeWeylGroup`.

## Results

- `Gm.eq_zero_of_zpow_extension`: over a domain `k`, if a morphism
  `e : Spec k ⊗ 𝔸¹_k ⟶ 𝔾_{m,k}` restricts along the unit inclusion
  `𝔾_{m,k} ⊆ 𝔸¹_k` to the power map `t ↦ t ^ m`, then `m = 0`.
- `IsSplitTorus.cocharacter_eq_zero`: over a field, a cocharacter `δ` of a
  split torus with `latticePairing T α δ = 0` for every character `α` is
  zero.
- `IsSplitSubtorus.mem_centralizer_of_mem_parabolic`: for a split subtorus
  `i`, a cocharacter `ζ` of `T`, and a rational point `n` in
  `normalizerPoints i` and in the rational points of
  `Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)`, the point `n` lies in
  the rational points of `Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)`.
- `IsSplitSubtorus.normalizerPoints_inf_standardParabolicPoints_le`:
  `normalizerPoints i ⊓ standardParabolicPoints i ν J ≤
  standardLeviPoints i ν J`, for every cocharacter `ν` and every set `J` of
  characters (with `[IsAffineHom G.X.hom]`, the hypothesis under which the
  published standard-parabolic definitions are made; this and the following
  results carry it).
- `IsSplitSubtorus.mem_standardParabolicPoints_iff`: for `n` in
  `normalizerPoints i`, membership of `n` in `P_J(k)`, membership of `n` in
  `L_J(k)`, and membership of its class `QuotientGroup.mk n` in
  `standardRelativeWeylGroup i ν J` are equivalent (stated as two
  equivalences).
- `IsSplitSubtorus.mk_mem_standardRelativeWeylGroup`: if `n` in
  `normalizerPoints i` lies in `P_J(k)`, then its class lies in `W_J`.

No hypothesis on `ν` (genericity) or on `J` (being a set of simple roots) is
needed. When `i` is a maximal split torus, `IsMaximalSplitTorus.isSplitSubtorus`
supplies the `IsSplitSubtorus i` hypothesis.

## Proof

`Gm.eq_zero_of_zpow_extension`. Precompose `e` with the canonical point of
`𝔸¹_k` over the polynomial ring and restrict to the Laurent-polynomial point.
By naturality of `Gm.affinePointsEquiv` along `k[t] → k[t, t⁻¹]`, the unit of
`k[t]` given by `e` maps to the unit `t ^ m` of `k[t, t⁻¹]`. Over a domain,
every unit of `k[t]` is a nonzero constant (`Polynomial.isUnit_iff`), so it
has Laurent degree `0`, while `T m` has degree `m`.

`IsSplitTorus.cocharacter_eq_zero`. Transport `δ` along the splitting
isomorphism to a standard split torus, where `latticePairing` is a perfect
pairing (`splitTorus.isPerfPair_latticePairing`); `latticePairing_congr`
moves the pairing along the isomorphism, and right injectivity of the perfect
pairing gives `δ = 0`.

`IsSplitSubtorus.mem_centralizer_of_mem_parabolic`. Let `σ : T ≅ T` be the
automorphism through which `n` normalizes `i`, so that conjugation by `n`
carries `i(y)` to `i(σ y)`. Put `δ := ζ ≫ σ⁻¹ − ζ`, a cocharacter of `T`.
On `𝔾_m`-points, `n⁻¹ · ζ(t) n ζ(t)⁻¹ = i(σ⁻¹ ζ(t)) · i(ζ(t))⁻¹ = i(δ(t))`; the
private lemma `comp_groupHom_sub` evaluates the difference of cocharacters,
and `comp_innerIso_hom` together with `constantPoint_naturality` and
`constantPoint_self` expresses conjugation by `n`. Membership of `n` in the
dynamic parabolic gives an extension `e` of the orbit map
`t ↦ ζ(t) n ζ(t)⁻¹` to `𝔸¹_k`; the translate `n⁻¹ · e` therefore extends
`t ↦ i(δ(t))`. Since `i` is a closed immersion (the second conjunct of
`IsSplitSubtorus`), `AffineLine.exists_lift_of_unitInclusion` lifts this
extension through `i` to a morphism `e' : Spec k ⊗ 𝔸¹_k ⟶ T` extending `δ`.
For each character `α`, the composite `e' ≫ α` extends
`t ↦ t ^ latticePairing T α δ` (by `latticePairing_apply` and
`gmEndEquiv_symm_comp`), so the pairing is `0` by
`Gm.eq_zero_of_zpow_extension`. Hence `δ = 0` by
`IsSplitTorus.cocharacter_eq_zero`, so `n⁻¹ · orbit(n) = 1`, that is, the
orbit map of `n` is the constant map `n`; `Dynamic.mem_centralizer` turns
this into membership in the dynamic centralizer.

`IsSplitSubtorus.normalizerPoints_inf_standardParabolicPoints_le` applies the
previous result to each standard cocharacter `ζ` in the defining
intersections (`mem_standardParabolic`, `mem_standardLevi`).

`IsSplitSubtorus.mem_standardParabolicPoints_iff`. The first equivalence
combines the previous inclusion with `standardLevi_le_standardParabolic`. For
the second, `QuotientGroup.mk n ∈ W_J` holds for `n ∈ L_J(k)` by
`mem_standardRelativeWeylGroup_iff`. Conversely, if the class of `n` equals
the class of some `m ∈ L_J(k)`, then `m⁻¹ n` centralizes `i`, so it lies in
`L_J(k)` (by `mem_centralizerPoints`, `mem_torusCentralizer_base_iff` and the
published `torusCentralizer_le_standardLevi`), and
`n = m · (m⁻¹ n) ∈ L_J(k)`. `IsSplitSubtorus.mk_mem_standardRelativeWeylGroup`
chains the two equivalences.

## Provenance

These are internal, derived results supporting the proof of
`Langlands.GroupScheme.StandardParabolicPointsStatement`; they make no
literal claim of a source. The classical counterpart is the step
`N(S) ∩ P = Z(S)` for a minimal parabolic `P` containing a maximal split
torus `S`, in the proof of Borel–Tits, *Groupes réductifs* (1965), source
`borel-tits-1965-groupes-reductifs`, §5.3 (printed p.97). Borel–Tits
argue there through the Levi decomposition and the equality of normalizer
and centralizer of a torus in a connected solvable group. The Lean proof
instead uses the dynamic description of parabolics: it shows that the
cocharacter `σ⁻¹ ζ − ζ` extends to `𝔸¹` and therefore pairs trivially with
every character. The results here hold for every dynamic parabolic of a
cocharacter of a split subtorus, not only minimal ones.
