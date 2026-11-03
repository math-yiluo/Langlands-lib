# Associated standard families under actual longest normalizer lifts

This is internal derived infrastructure for the rational structure of group
schemes. It specializes the generic character-image transport construction in
`StandardRestrictedConjugation` to a supplied finite actual relative Weyl
Coxeter realization. It uses the published scheme character action and the
literal standard subgroup functors. No new assertion is attributed to external
literature.

Let `k` be any field, `T` a commutative group scheme over `Spec k`, and `G` an
affine group scheme over `Spec k`. Let `i : T.toGrp ⟶ G` have monomorphic
underlying scheme map, and let `ν` be a cocharacter of `T`. Both the actual
simple-root type `SimpleRoot i ν` and the actual relative Weyl group
`relativeWeylGroup i` have supplied finite enumerations. A Coxeter system `cs`
on that quotient, labelled by those simple roots, and a proof of
`IsRelativeWeylCoxeterRealization i ν cs` are explicit inputs. The universe is
arbitrary. Reductivity, maximality or splitness of `T`, and genericity of `ν`
are not additional hypotheses of this construction.

For a finite subset `J` of the simple-root labels, write `A = associatedSubset
cs J` and `w = longestRep cs J`. The published equivalence
`associatedSimpleEquiv cs J : A ≃ J` induces `associatedFinsetEquiv cs J` on
finite subsets. If `I : Finset A`, write `I₀` for its image in the ambient
simple-root type and `I₁` for the ambient image of `associatedFinsetEquiv cs J
I`. The function `rootSet i ν` reads any such finite label set as the set of its
actual characters.

The root-image results identify these actual characters, including their signs:

- `schemeWeylCharacterAction_associatedSimpleEquiv` says that `w` sends each
  associated simple character to the character of its specified image in `J`.
- `schemeWeylCharacterAction_image_associatedSubset` identifies the image of
  `rootSet A` with `rootSet J`.
- `schemeWeylCharacterAction_image_associatedFinsetEquiv` identifies the image
  of `rootSet I₀` with `rootSet I₁`.
- `weylAction_image_associatedStandardFamily` gives both set-image identities
  for every actual normalizer point `n` whose quotient class is `w`. It retains
  that same point throughout the construction.

The theorem `associatedStandardSubgroups_eq_comap` proves both literal subgroup
functor equalities

\[
 L_A\cap P_{I_0}=\operatorname{Int}(n)^*(L_J\cap P_{I_1}),\qquad
 L_A\cap U_{I_0}=\operatorname{Int}(n)^*(L_J\cap U_{I_1}).
\]

Here every subscript denotes the corresponding actual `rootSet`; the displayed
meets are precisely `restrictedStandardParabolic` and
`restrictedStandardUnipotent` from
`StandardAssociatedParabolicTransportStatement`. The identities hold on every
scheme test, including nonreduced tests, with `Int(n)(x) = n*x*n⁻¹`.

For every `U : Over (Spec k)`, the definitions
`associatedStandardParabolicConjEquiv` and
`associatedStandardUnipotentConjEquiv` construct multiplicative equivalences
between the carriers of the corresponding source and target functors at `U`.
The four `apply` and `symm_apply` lemmas give their values in the original
ambient group of categorical points. Writing `n_U = G.constantPoint n U`, they
are

\[
 x\longmapsto n_U x n_U^{-1},\qquad
 y\longmapsto n_U^{-1} y n_U.
\]

The theorem `mem_associatedStandardParabolic_unipotent_inv_conj_iff` also applies
to any ambient point `x : U ⟶ G.X` in the target standard Levi `L_J(U)`. It
proves both

\[
 x\in P_{I_1}(U)\ \Longleftrightarrow\ n_U^{-1}xn_U\in P_{I_0}(U),\qquad
 x\in U_{I_1}(U)\ \Longleftrightarrow\ n_U^{-1}xn_U\in U_{I_0}(U).
\]

These assertions specialize to rational points but use no identification of
points of a sheaf quotient with a quotient of point groups.

The implemented proof first uses `positiveSimpleSet_longestRep` to identify
right ascents with the associated subset. The realization's length-sign clause
therefore makes each associated simple-root image positive. The published
`IsRelativeWeylCoxeterRealization.root_eq_of_conj_simple`, applied to
`associatedSimpleEquiv_conj`, identifies that positive character with the
specified target character. This theorem retains the possible double-root
case of a nonreduced relative root system. Surjectivity of the simple-label
equivalence gives the full set-image equality. Composition of set images gives
the finite-subset equality. The quotient action agrees with `weylAction i n`
on every actual representative, so no new lift is chosen.

The published theorem
`IsRelativeWeylCoxeterRealization.exists_standardCocharacter_finset` supplies
standard cocharacters for `A` and `J` from the realization's actual
standard-Levi parabolic clause. Finiteness of the simple roots follows from the
supplied finite enumeration. The two subtype-index inclusions give `I₀ ⊆ A`
and `I₁ ⊆ J`. These inputs and the two character-image identities instantiate
`restrictedStandardSubgroups_eq_comap_of_character_images`, which proves both
all-test equalities by the orbit-extension argument. The two equivalences and
the inverse membership laws specialize the corresponding generic
constructions. Their formulas follow from the actual inner isomorphism and its
inverse.

All subsets, including empty subsets, are retained; no nonempty-root or
positive-rank hypothesis occurs. The Coxeter realization remains an input.
This module does not establish its existence, the general intrinsic
standard-cocharacter theorem without a realization, the separate
minimum-source or ambient opposite-family identities, or a
representation-theoretic comparison.
