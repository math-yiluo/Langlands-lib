# Actual commutator bounds under restriction between split tori

This internal construction proves axiom V3 for the actual scalar family
`torusRestrictedRootFunctionFamily`. It starts with an upper root datum
valuation and uses the canonical subgroups already constructed in
`RootDepthTorusRestriction`. All groups in the argument are subgroups of the
unchanged group `rationalPoints G`.

Let `k : Type u` be any field, let `S` and `T` be commutative group schemes over
`k`, let `G` be an affine group scheme, and let `i : T.toGrp ⟶ G` have
monomorphic underlying scheme map. Write `f : S ⟶ T` and
`j = CommGroupScheme.groupHom f ≫ i`. The upper family `φ` is assumed to satisfy
`IsRootDatumValuation i φ`. The construction does not require `j` to be
monomorphic. Additional splitness and smoothness assumptions enter only where
specified below.

## The mixed subgroup

For lower characters `a, b` and real depths `r, s`, define

\[
 K(a,b;r,s)=\bigvee_{\substack{\chi\in\Phi(T,G),\ p,q\in\mathbb N_{>0}\\
                       f^*\chi=pa+qb}}
                     U_{\chi,\,pr+qs}.
\]

Here `U` is the actual subgroup `hφ.filtrationSubgroup`. The Lean definition
`torusRestrictedMixedRootDepthSubgroup` uses a subtype of triples `(χ,p,q)`
recording exactly these conditions. The positive coefficients are natural
numbers; the real depths may have either sign. This definition chooses no
cocharacter or coordinate ordering.

The canonical lower subgroup is

\[
 H(a,r)=\bigvee_{\substack{\chi\in\Phi(T,G),\ m\in\mathbb N_{>0}\\
                          f^*\chi=ma}}U_{\chi,mr}.
\]

The private `rootDepth_eq_iSup` just flattens its nested supremum into one
subtype-indexed supremum. It does not alter the subgroup.

## Upper V3 and normalization

Suppose a supplied cocharacter `ν` of `S` has strictly positive integral
pairing with both `a` and `b`.
`latticePairing_comp_torusHom_of_restrict_eq_combination` proves that

\[
 \langle\chi,\nu\circ f\rangle
   =m\langle a,\nu\rangle+n\langle b,\nu\rangle
 \quad\text{when }f^*\chi=ma+nb.
\]

In particular, if `m,n` are nonnegative integers with `m+n>0`, this upper
pairing is positive. Two such upper roots are outside opposite real rays by
the existing `KPApartmentData.positiveRoots_nonopposite` theorem.

`filtrationSubgroup_commutator_le_torusRestrictedMixed` considers roots
restricting to `ma+nb` and `pa+qb`, with each sum nonzero and with
`m+p>0`, `n+q>0`. Upper V3 bounds their filtration commutator by the upper
mixed-root factors. Each factor `vχ+wθ`, for positive integers `v,w`, restricts
to

\[
 (vm+wp)a+(vn+wq)b.
\]

Both coefficients are positive, and its depth is exactly
`(vm+wp)r+(vn+wq)s`. Thus every upper V3 factor lies in `K`.

`filtrationSubgroup_le_normalizer_torusRestrictedMixed` applies this bound
against every mixed generator. It uses the independently developed generic
`Langlands.GroupTheory.le_normalizer_iSup_of_commutator_le` to prove that any
positive-cone filtration normalizes `K`. In particular each generator of
`H(a,r)` and of `H(b,s)` normalizes `K`.

`torusRestrictedRootDepthSubgroup_commutator_le_mixed` then applies
`Langlands.GroupTheory.commutator_iSup_le_of_normalizes` to these two families.
The pairwise bound is the case of coefficient pairs `(m,0)` and `(0,n)` above.
This proves

\[
 [H(a,r),H(b,s)]\ \leq\ K(a,b;r,s).
\]

Normalization is proved before applying this generated-subgroup lemma; no
unrestricted distribution of commutators over subgroup suprema is used.
These steps require the supplied common positive cocharacter and upper
valuation, but no splitness, smoothness, opposite-factor-pair or lower valuation
assumption.

## Exact lower mixed target

`torusRestrictedMixedRootDepthSubgroup_le` puts `K` inside

\[
 L=\bigvee_{\substack{p,q>0\\pa+qb\in\Phi(S,G)}}H(pa+qb,pr+qs).
\]

For an upper mixed generator, positivity of the pairing shows that `pa+qb` is
nonzero. The actual adjoint-weight restriction map `rootRestriction` then
proves that this restriction is an actual lower root. The upper filtration is
a generator of its canonical lower filtration with multiplier one.

Conversely, `iSup_torusRestrictedRootDepthSubgroup_le_mixed` expands every
lower filtration in `L`. A factor with positive multiplier `m` has restriction
`(mp)a+(mq)b` and depth `(mp)r+(mq)s`, so it is a generator of `K`. This
inclusion requires no cocharacter hypothesis.
`torusRestrictedMixedRootDepthSubgroup_eq_iSup` combines the two inclusions
under a common positive cocharacter.

For actual lower roots outside opposite real rays and split `S`, the existing
`IsSplitTorus.exists_cocharacter_pos_pair_of_not_opposite` supplies the needed
cocharacter. The theorem `torusRestrictedRootDepthSubgroup_commutator_le`
therefore proves the full canonical subgroup V3 bound with exactly the positive
integral combinations and lower-root tests appearing in the valuation axiom.
Neither splitness of `T` nor smoothness of `G` is needed for this subgroup
conclusion.

## Scalar V3 and scope

The final theorem `torusRestrictedRootFunctionFamily_commutator` additionally
assumes smooth `G`, split `S` and `T`, and
`RelativeRoot.HasOppositeFactorPairs i`. These are retained inputs to the
previously constructed actual scalar family. Its exact finite level sets are
the canonical `H` subgroups on actual lower roots. The proof rewrites the two
input filtrations using those identities, applies the canonical subgroup V3
bound, and rewrites each lower mixed filtration in the output. Mathlib's
`Subgroup.closure_iUnion` identifies the closure of the mixed union with the
supremum of its subgroup closures. The result is precisely the existing
`IsRootDatumValuation.commutator` field type for the constructed scalar family.

The argument is internal: it combines the explicit upper valuation axioms,
the published actual character/adjoint-weight restriction maps and the common
positive-cocharacter theorem, the canonical lower filtration construction and
its exact scalar level sets, and elementary subgroup algebra. It introduces no
new assertion from external literature.

This unit establishes V3 under the stated upper-valuation hypotheses. It does
not establish V2, V4 or V5 or assert a full lower root datum valuation. Initial
valuation existence, building geometry and metric construction, and the special
vertex and unique fixation for the original supplied integral model remain
outside this unit. In particular `BuildingComparisonStatement` remains open.
