# Weyl-normalizing automorphisms of pinned groups are inner

Let `k` be a field in an arbitrary universe `u`, let `G` and `A` be group
schemes over `Spec k` with `G` affine over the base, let `p` be a supplied
split pinning of `G`, and let `q : G ⟶ A` satisfy `IsAdjointQuotient q`
(connected reductive source, adjoint target, flat, surjective and locally of
finite presentation, with kernel the actual scheme-theoretic centre, and the
universal property for maps killing the centre). This internal unit proves that
every automorphism of `G` which normalizes the pinned torus through an element
of the actual Weyl image is the inner action `hq.innerAction.basePointIso x`
of some ground-field point `x` of `A`.

## The simple-root torus maps to the adjoint quotient

`rootScalingProjection_kernel_comp_adjoint` shows that the actual
scheme-theoretic kernel of `p.rootScalingProjection` (the projection of the
pinned torus onto the split torus with one coordinate per simple root) maps
trivially to `A` through `p.inclusion ≫ q`. Its proof uses the imported fact
`rootScalingProjection_kernel_central` that this kernel is central in `G`,
and the centre characterization `IsAdjointQuotient.mem_center_iff_comp_eq_one`.

`rootScalingAdjointHom` is the group-scheme map from the simple-root torus to
`A` obtained by fpqc descent of homomorphisms (`FpqcHomDescent.hom`) along the
faithfully flat, finitely presented projection, using the previous vanishing.
`rootScalingProjection_comp_adjointHom` is its defining factorization
`rootScalingProjection ≫ rootScalingAdjointHom = p.inclusion ≫ q`.

`innerAction_restrict_rootScalingAdjointHom` proves that, on every test
scheme, the inner action of `A` restricted along `rootScalingAdjointHom` is
the existing descended conjugation action `p.rootScalingAction` of the
simple-root torus. Both actions are compared by
`AutomorphicAction.hom_ext_of_local_quotient_lift`: after a local lift of the
torus point through the projection, both reduce to conjugation by the lifted
torus point, using the factorization above and `innerAction_act_lift`.

## Evaluated automorphisms

`innerAction_basePointIso_lift` states that for a ground-field point `n` of
`G`, the automorphism given by the image point `n ≫ q` is the actual inner
automorphism `G.innerIso n`. `innerAction_basePointIso_rootScaling` states
that the image under `rootScalingAdjointHom` of the base point with
simple-root coordinates `c : p.base.support → kˣ` acts by the existing root
scaling automorphism `p.rootScalingIso c`. Both are proved by comparing the
automorphisms on all points of all test schemes.

## Automorphisms fixing the pinned torus

`exists_eq_rootScalingIso` proves that every automorphism `f` of `G` with
`p.inclusion ≫ f.hom = p.inclusion` equals `p.rootScalingIso c` for some
`c`. Because `f` fixes the torus, its differential preserves the weight space
of each simple root (`lieKernelHomLinear_mem_weightSpace`), so the pinning's
trivialization of that line yields a scalar `d a` with
`f_*(X_a) = d a • X_a`; this scalar is nonzero because the differential is
invertible and the pinned root vector is nonzero. With `c a = d a`, the
composite `f ≪≫ (p.rootScalingIso c).symm` fixes the torus and every simple
root vector (`rootScalingIso_inclusion`, `rootScalingIso_rootVector`), so it is
the identity by the Library theorem `pinnedAutomorphismRigidity`.

## Weyl-normalizing automorphisms

`exists_adjointPoint_of_weylImage` assumes the underlying scheme map of the
torus inclusion is a monomorphism (needed to define `weylImage`), an
automorphism `f : G ≅ G` and a torus automorphism `σ` with
`p.inclusion ≫ f.hom = groupHom σ.hom ≫ p.inclusion`, and
`characterAut σ ∈ weylImage p.inclusion`. It produces a ground-field point
`x` of `A` with `hq.innerAction.basePointIso x = f`.

The proof chooses a normalizer point `n` whose Weyl action is
`characterAut σ`. Equality of the character actions and character
extensionality of the split torus identify its normalizing automorphism with
`σ`, so `n` normalizes the torus through `σ`. Then `f` followed by the inverse
of `G.innerIso n` fixes the torus and is a root scaling `p.rootScalingIso c`.
Hence `f = p.rootScalingIso c ≪≫ G.innerIso n`, and the point
`x = (n ≫ q) * (rootScalingPoint c ≫ rootScalingAdjointHom)` works, by
multiplicativity of the action and the two evaluation lemmas.

## Scope and provenance

The provenance is internal: this is the standard argument that an
automorphism of a pinned split reductive group inducing a Weyl element on the
torus differs from an inner automorphism by a torus-fixing automorphism, which
is inner by an adjoint torus point. The Lean route combines
the imported pinned rigidity theorem, the descended simple-root torus action
and fpqc homomorphism descent. It assumes the pinning, the adjoint quotient
and the Weyl hypothesis; it does not construct a quasi-split inner form or any
Galois cocycle.
