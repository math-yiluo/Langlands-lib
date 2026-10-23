# Coefficient automorphisms on affine group-scheme points

This is an internal construction from the actual algebra spectrum functor
and the group-valued point functor. No additional literature convention or
representability assumption is introduced.

Let R and S be commutative rings, with an R-algebra structure on S, and let
G be any group scheme over Spec R. Its S-points here are actual morphisms
from `algSpec (CommAlgCat.of R S)` to the underlying object `G.X` in the
category of schemes over Spec R. They carry the canonical group law of
`G.points`. No affineness hypothesis on G or finite-generation hypothesis
on S is required.

For an R-algebra automorphism s of S, `affinePointAut G s` is a
multiplicative equivalence of this point group. It is constructed by
applying `CommAlgCat.isoMk`, the contravariant spectrum functor, and the
contravariant point functor, and then converting the resulting group
isomorphism into a multiplicative equivalence. The evaluation identity
`affinePointAut_apply` is definitional:

\[
\alpha_s(x)=\operatorname{Spec}(s)\mathbin{\gg}x.
\]

The two contravariant functors give the original order of composition:
`affinePointAut_one` and `affinePointAut_mul` prove

\[
\alpha_1=1,\qquad \alpha_{st}=\alpha_s\alpha_t,
\]

where `(st)(a)=s(t(a))`. The proofs use the identity and composition laws
of the spectrum functor and associativity of composition. The construction
`affinePointAutHom G` packages these laws as a group homomorphism from
R-algebra automorphisms of S to group automorphisms of G(S).

For another commutative R-algebra T, automorphisms s of S and t of T,
and an R-algebra map f:S→T satisfying `t ∘ f = f ∘ s`, the theorem
`affinePointAut_naturality` proves

\[
\alpha_t(\operatorname{Spec}(f)\mathbin{\gg}x)
 =\operatorname{Spec}(f)\mathbin{\gg}\alpha_s(x).
\]

It combines spectrum maps using functoriality and applies the given
commuting equality. The theorem `affinePointAut_target` also proves
compatibility with a morphism of group schemes G→H defined over R, by
associativity of scheme composition.

These are coefficient actions on actual S-points. The module does not
assert that s induces an S-linear automorphism of a scalar-extended group
scheme or construct Galois transport of cocharacters.
