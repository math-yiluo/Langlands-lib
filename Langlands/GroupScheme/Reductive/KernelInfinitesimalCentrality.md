# Kernel centrality through nilpotent thickenings

This is a derived internal construction for the kernel-centrality step of
Conrad's *Reductive group schemes*, Proposition 3.3.10, p.103. The source is
registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The module composes existing Library interfaces for infinitesimal lifting,
centrality, and the actual scheme-theoretic kernel. It does not prove either
infinitesimal input proposition.

All rings and schemes are in an arbitrary universe `u`. Put `S = Spec A`,
`S₀ = Spec (A/J)`, and let `r : S₀ → S` be the quotient closed immersion, where
`J` is a nilpotent ideal of a commutative ring `A`.

## The constructed object

`KernelInfinitesimalCentrality.centralKernelOfNilpotentReduction` takes:

- proofs of the published propositions
  `MultiplicativeTypeSubgroupInfinitesimalLiftStatement` and
  `MultiplicativeTypeInfinitesimalCentralityStatement`;
- group schemes `G,H` over `S`, with `G` smooth and `H` separated over `S`;
- a homomorphism `f : G → H` whose underlying scheme morphism is flat;
- multiplicative type of the full kernel of `f` after base change along `r`;
- centrality of the inclusion of that full base-changed kernel.

It returns a commutative group scheme over `S` whose underlying group scheme
is exactly `kernel f`. The simp theorem
`centralKernelOfNilpotentReduction_toGrp` records this equality by reflexivity.
The construction uses `IsCentral.commGroupScheme`, which obtains commutativity
from centrality of the monomorphic actual kernel inclusion. It retains the
underlying group object and its existing group operations.

## Implemented supporting proofs

`isCentral_kernel_baseChange_iff` identifies centrality of the actual kernel
inclusion of the base-changed map with centrality of the base change of
`kernelι f`. In each direction it precomposes by one side of
`kernelBaseChangeIso`; `kernelBaseChangeIso_hom_ι` and
`kernelBaseChangeIso_inv_ι` identify the resulting inclusion. Thus the comparison
uses full scheme-theoretic kernels on every test scheme.

`isMultiplicativeType_kernel_baseChange_iff` transports the relative
multiplicative-type predicate across the same isomorphism, using
`RelativeMultiplicativeType.IsMultiplicativeType.of_iso` in each direction.
Both equivalences hold over arbitrary base schemes, with arbitrary base change.

`quotient_locallyNilpotent` supplies the ideal-sheaf hypothesis required by the
centrality input. Naturality of `Scheme.ΓSpecIso` identifies the kernel of the
quotient map on global sections with the image of `J` under the canonical ring
isomorphism `A → Γ(Spec A, ⊤)`. The affine formula `Scheme.ker_of_isAffine`
identifies the ideal sheaf, and its formula on the top affine open makes the
relevant ideal another image of that global-section kernel. Applying
`Ideal.map_pow` twice carries an equation `J^n = 0` to this ideal. The top affine
open is a neighbourhood of every point, proving the required local condition.

`subgroup_of_nilpotent_reduction` treats a homomorphism `k : K → G` that is an
immersion, where `K` is flat over `S` and `G` is smooth over `S`. It assumes that
the base change of `K` is of multiplicative type and the base change of `k` is
central. Part (b) of the supplied infinitesimal subgroup-lifting proposition
gives multiplicative type of `K`. The quotient map is a closed immersion by
surjectivity of `A → A/J`. Smoothness of `G` supplies local finite presentation,
so the supplied infinitesimal centrality proposition, with
`quotient_locallyNilpotent`, gives centrality of `k`.

`kernel_of_nilpotent_reduction` applies that result to `kernelι f`. Separatedness
of `H` makes this inclusion a closed immersion, hence an immersion. The
kernel pullback square `kernel_isPullback_scheme f` transports flatness of `f`
to flatness of the kernel over `S`. The two base-change equivalences above
convert the hypotheses on the kernel of the base-changed homomorphism into the
hypotheses needed for this subgroup. Its conclusion is that the actual kernel
is of multiplicative type and its actual inclusion is central. The selected
definition bundles this kernel using that centrality proof.

## Scope

Conrad's argument on p.103 motivates an infinitesimal kernel-centrality step;
the implemented route uses part (b) of the Library's subgroup-lifting statement
and the separate infinitesimal centrality statement. Both remain explicit proof
arguments throughout. No existence or conjugacy clause of the lifting statement
is used.

This module assumes multiplicative type and centrality after a specified
nilpotent reduction. It does not deduce these hypotheses from residue-field
centrality, prove detection by artinian tests, justify noetherian approximation,
or establish the arbitrary-base fibrewise central-isogeny criterion.
