# The Chevalley root function family of a Chevalley group

This internal unit defines the root function family of Kaletha–Prasad's
Chevalley valuation (*Bruhat–Tits Theory: A New Approach*, §6.1(a), the
functions `φ_{o, a}` before Lemma 6.1.1) for the Chevalley groups of the split
existence construction. It proves every axiom of the Library's
`IsRootDatumValuation` that concerns one root at a time, together with
split-torus compatibility. Reflections (V 2), commutators (V 3) and opposite
root elements (V 5) are not treated here.

## Setting

Let `D` be Chevalley data of a reduced root datum `P` with finite index type
and finite free weight lattice, `k` a field, and `G : D.ChevGroup k` a
Chevalley group whose underlying group scheme `G.H` is affine and locally of
finite type over `k`. Let `omega : AddValuation k (WithTop ℝ)`.

## Preliminary identities

- `gaRationalEquiv_eq_scalarPoint`: the rational point of `𝔾ₐ` attached to
  `x : k` is the published scalar point of the global function corresponding
  to `x` under `Scheme.ΓSpecIso`.
- `charValue_eq_rationalCharacterEval`: for a commutative group scheme `T`,
  a character `χ` and a rational point `z`, the published global value
  `VectorGroup.charValue χ` at `z` corresponds to the rational value
  `rationalCharacterEval` of `χ` at `z`.
- `rootCoord G j` is the published field coordinate `rootCoordEquiv` of the
  root group of `j`, regarded as an equivalence onto `rootGroupPoints`. The
  definition `coordOfEq` transfers it to any character equal to the root
  character.
- `charOf_root_injective`: distinct roots have distinct characters.
- `mem_relativeRoots_iff`: the relative roots of the torus `G.t` are exactly the
  root characters, by the published `roots_t`.

## The family

`family G omega` sends a root character `charOf k (P.root j)` to the published
`additiveRootValue` of `omega` along the coordinate of its root group, and
sends every other character to the constant `∞`. `family_root` and
`family_of_not_root` record these two cases.

The following theorems are exactly the corresponding fields of
`IsRootDatumValuation G.t (family G omega)`:

- `eq_top_of_not_mem_roots` and `eq_top_of_not_mem`: the normalizations off the
  roots and off the root groups;
- `three_le_encard`: V 0, under the hypothesis that the range of `omega` has at
  least three elements;
- `one_mem`, `mul_mem` and `inv_mem`: V 1, the filtration sets are subgroups;
- `eq_top_iff`: on a root group the value is infinite only at the identity;
- `double`: V 4, which holds vacuously because no root is twice a root, by the
  published `hasNoHigherRoots_charOf`.

These follow from the published laws of `additiveRootValue`.

## Split-torus compatibility

`conj_rootCoordEquiv` states that conjugation by the inverse of the image of a
rational torus point `s` multiplies the coordinate by the inverse of the root
value at `s`. It is the base-point instance of the published torus
equivariance `u_isTorusEquivariant`.

`isSplitTorusCompatible ω hω` proves the published
`IsSplitTorusCompatible G.t ω (family G omega)` for any function
`ω : kˣ → ℝ` with `omega x = ω x` on units. The value shift is
`omega(a(s)⁻¹) = -ω(a(s))`, which follows from multiplicativity of `omega`.

## Scope

This unit does not prove V 2, V 3 or V 5. It does not prove normalizer
stability, and it does not transport the family to other split groups. All
results are uniform in the universe and the characteristic.
