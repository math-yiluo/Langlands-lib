# Local smooth duality for every pair of cuspidal contragredient presentations

Author: Worker 818.

`Langlands.Automorphic.cuspidalContragredientLocalCompatibility` proves the
published proposition
`Langlands.Automorphic.CuspidalContragredientLocalCompatibilityStatement.{uF, uP, uQ}`
from [CuspidalContragredientStatement](CuspidalContragredientStatement.md),
with its three independent universes and exactly its hypotheses. This is an
internal derivation from the Library's actual operator realizations, the
published smooth invariant-pairing duality
`Langlands.smoothInvariantPairingDuality` and compact-open cofinality
`Langlands.GeneralLinear.compactOpen_cofinal`. It has no external source
attribution.

The proof does not follow the factorization route sketched in the statement's
Markdown. It uses no finite/infinite or all-place factorization, no
multiplicity projection and no restricted-dual comparison. It also does not
claim that the full pairing restricted to the two embedded slices is perfect.
Instead, the full pairing is first composed with an actual operator that
commutes with the local group at `v`. Full-operator irreducibility guarantees
that some such composite is nonzero on the two local components.

## Notation

Fix the data of the statement: `T`, `T'`, the full-operator pairing
`B : T.Space →ₗ[ℂ] T'.Space →ₗ[ℂ] ℂ` from `IsContragredientOf`, presentations
`P` and `P'`, a finite place `v` and the four irreducibility and admissibility
proofs at `v`. Put `S = T.realization`, `S' = T'.realization`,
`W = P.localComponent v` and `W' = P'.localComponent v`. Write `G_v` for
`FiniteLocalGL F (r + 1) v` and `ι_v` for `localInclusion`. Both `W` and `W'`
are nonzero (`localComponent_ne_bot`) and lie in the finite images of `S` and
`S'`. This holds because `localComponent_le` places each local component in its
finite slice, and the slice field `le_image` places the slice in the finite
image.

## Group splitting

Two lemmas at the start of the module concern the finite adelic group.
`localInclusion_commute_of_localProjection_eq_one` shows that an adelic matrix
with identity `v`-component commutes with every `ι_v g`. It compares all local
projections through `ext_localProjection`. By `exists_localSplit`, every
finite adelic `d` can be written as `ι_v g * d'` with `d'` having identity
`v`-component. Here `g` is the `v`-projection of `d`, and `d'` is
`(ι_v g)⁻¹ * d`.

## Twisting by the local centralizer

`localCentralizer n v` is the subalgebra centralizer, in the endomorphisms of
the ambient finite-smooth space, of all finite translations `ι_v g`. Three
kinds of operator lie in it:

- finite translations by matrices with identity `v`-component;
- every standard infinite compact translation
  (`AdelicGL.ofFinite_commute_ofInfinite`);
- every enveloping-algebra operator
  (`finiteSmoothFiniteRightAction_envelopingAction`).

An operator of the concrete automorphic operator algebra whose ambient value
lies in this centralizer commutes with the local translations of `S`
(`OperatorRealization.representation_commute`).

`OperatorRealization.localLift` reads `W` back inside `S`. It combines the
inclusion of `W` into the finite image with the inverse of `S.finiteEquiv`.
The lift is injective and has the same underlying form
(`formInclusion_localLift`). It intertwines the action of `G_v` on `W` with the
finite operators `finiteOperator (ι_v g)` on `S` (`localLift_representation`).

`twistedLocalSpan` is the span of all vectors `a (localLift x)` with `x ∈ W`
and `a` an algebra operator whose ambient value lies in the centralizer.
`representation_mem_twistedLocalSpan` shows that every operator of the
algebra preserves this span. The proof is by induction on `Algebra.adjoin`;
inside the generator case it is an induction on the span.

- A compact or enveloping generator `b` multiplies `a` to `b * a`, which is
  again in the centralizer.
- A finite generator `d` is split as `ι_v g * d'` (`finite_twisted_mem`). Then
  `d · a (localLift x) = (d' * a) (localLift (g · x))`. The proof moves
  `ι_v g` past `a` and past `d'` and uses the intertwining property of the
  lift. The operator `d' * a` lies in the centralizer.
- The scalar, sum and product cases are checked on ambient functions.

Since `S` is irreducible for the full algebra and the span contains the
nonzero lifted vectors, `twistedLocalSpan_eq_top` shows that the span is all
of `S`. Consequently a nonzero linear functional on `S` is nonzero on some
twisted vector `a (localLift x)` (`exists_twist_ne_zero`).

## A nonzero invariant local pairing

In `exists_localInvariantPairing`, choose a nonzero `x' ∈ W'`. The partial map
`B.flip` is injective, and so is the lift, so `B (·) (localLift x')` is a
nonzero functional on `S`. The previous step gives `a` in the centralizer and
`x ∈ W` with `B (a (localLift x)) (localLift x') ≠ 0`. Define

```text
b x' y = B (a (localLift y)) (localLift x')     for x' ∈ W', y ∈ W.
```

It is built as `(B.compl₁₂ (a ∘ localLift) localLift).flip`, so `b ≠ 0`.
For `g ∈ G_v`, the lift sends `g · y` to `ι_v g · localLift y`. The operator
`a` commutes with `ι_v g`. Hence `b (g · x') (g · y) = b x' y` by the finite
invariance of `B` at `ι_v g`, which is the first component of
`IsInvariantPairing`. Only finite invariance, injectivity of `B.flip` and
full-operator irreducibility of `S` are used. Irreducibility of `S'` is not
needed.

## Nondegeneracy and smooth duality

`invariantPairing_left_nondegenerate` and
`invariantPairing_right_nondegenerate` are generic lemmas for any group and
complex vector spaces. Each kernel of an invariant pairing is a
subrepresentation. Hence a nonzero invariant pairing has zero left kernel when
its left representation is irreducible, and zero right kernel when its right
representation is irreducible. Applied to `b` with the supplied
irreducibility of `W'` and `W`, both kernels vanish.

The final theorem installs the statement's canonical p-adic topology on the
local field and the canonical matrix topology and topological-group structure
on `GL_(r+1)`. It then applies `smoothInvariantPairingDuality` to the two
`padicObject` actions. The left representation is the `T'` side and the
right is the `T` side. The hypotheses are as follows:

- compact-open cofinality comes from
  `GeneralLinear.compactOpen_cofinal (padicField v)` with
  `canonicalTopologicalData`;
- admissibility of the `T` side is the admissibility field of its
  `padicObject`;
- smoothness of the `T'` side is the smoothness of its `padicObject` carrier;
- the remaining inputs are `b`, its invariance and the two nondegeneracy
  facts.

The resulting `Representation.Equiv` from the `T'` action to
`smoothContragredient` of the `T` action proves the `Nonempty` conclusion.

## Scope

The statement's hypotheses are used as given. Irreducibility and admissibility
are needed only at the given `v`. Admissibility of the `T'` component enters
only through the construction of its `padicObject`, which the statement
requires. There is no restriction to unexceptional places and no unitarity or
association premise. The proof does not use the compact-translation or Lie
algebra parts of the invariance of `B`, nor the surjectivity part of
`IsContragredientPairing`. The module adds the group-splitting,
centralizer, lift, twisted-span and generic pairing lemmas described above. It
proves no factorization of `T` or `T'`, and no comparison between different
presentations of one realization.

The underlying-function abbreviation `OperatorRealization.ambient` is reused from `Langlands.Automorphic.CuspidalL2.Representation`.
