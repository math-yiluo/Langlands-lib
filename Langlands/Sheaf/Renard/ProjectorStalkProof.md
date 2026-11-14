# Renard II.2.5: proof of the original-module stalk description

The theorem `Langlands.Sheaf.Renard.ProjectorStalk.projectorStalkDescription.{u,v}`
proves the published proposition
`Langlands.Sheaf.Renard.ProjectorStalk.ProjectorStalkDescription.{u,v}`.
Its source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, II.2.5, printed pp.40–41 / PDF pp.46–47,
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These pages were read directly. The target and all its imported Lean/Markdown
pairs are unchanged.

The source describes the fibre as the direct limit of `χ_U M` over compact-open
neighborhoods of `x`, identifies equality with agreement after a neighborhood
projector, and identifies this space with `M/M(x)`, where a vector belongs to
`M(x)` when some test nonzero at `x` kills it. The proof here uses local
constancy near `x` instead of the source's finite disjoint expansion of the
witnessing test. The kernel and linear first-isomorphism formulations make
explicit the linear content of that identification.

For independent `X : Type u` and `M : Type v`, `annihilatorDescription` proves
the literal test condition is equivalent to being killed by a compact-open
neighborhood projector. Given a witness `f`, choose a compact-open neighborhood
`U` inside the open fibre `{y | f y = f x}`. For
`g = (f x)⁻¹ • χ_U`, pointwise evaluation gives `g * f = χ_U`, so
`χ_U • m = g • (f • m) = 0`. This only uses the original nonunital action.
Conversely, if `χ_U • m = 0` and `x ∈ U`, the test `χ_U` is nonzero at `x`
and witnesses membership in the published annihilator submodule.

`basisOriginalGerm` sends an original vector to its projected germ at a chosen
compact-open neighborhood in the existing
`rawStalk (rawPresheaf hX M) x`. This is the actual lifted abelian-group colimit,
with carrier universe `max u v`. `basisOriginalGerm_eq` proves that every
compact-open neighborhood computes the same map: on the intersection of two
neighborhoods both restrictions are the intersection projector of the original
vector. Thus the auxiliary choice does not affect the resulting germ.

The published `rawGerm_eq_iff` gives
`basisOriginalGerm_eq_iff`: two original vectors have the same germ exactly
when some compact-open neighborhood projectors agree. In the forward direction,
restrict equal representatives to a common refinement and absorb the larger
projector; in the reverse direction compute both germs on the witnessing
neighborhood. The published `rawStalk_representative` gives surjectivity:
a section of `χ_U M` is the projection of its own underlying original vector.
The annihilator description identifies the additive kernel. Applying
`QuotientAddGroup.liftEquiv` proves `basisStalkComparison`. Its quotient-class
formula is the neighborhood-independent germ formula, so it holds for every
neighborhood, membership proof and original vector required by the target.

For the all-open clauses, `X` and `M` lie in the same arbitrary universe `u`.
The sheaf is the published compatible-family vector sheaf
`ProjectorVectorSheaf.presheaf.{u,u} hX hM`, with the canonical recovered
complex scalars `originalModule hM`. Two private instances establish that the
forgetful functor from `ModuleCat.{u} ℂ` preserves filtered colimits at universe
`u`. Mathlib's default instance ties the module universe to the scalar universe;
its explicit `ModuleCat.FilteredColimits.colimitCoconeIsColimit` construction
already covers the required arbitrary module universe. The first instance uses
this construction and the corresponding additive-group colimit to prove
preservation by `forget₂`; the second composes it with the additive-group
forgetful functor. Thus Mathlib's actual-stalk representative and equality
lemmas apply without restricting `u` or changing the stalk.

`originalGerm_eq` computes the published
global original-vector germ on any open neighborhood using restriction
compatibility and Mathlib's germ-restriction identity.

`originalGerm_eq_iff` proves the projector criterion for equality in the actual
all-open stalk. Equal germs give an open neighborhood where their sections
agree. Shrink to a compact-open neighborhood and read its component to obtain
equality of the original projectors. Conversely, projector equality on `K`
gives equality of all components on compact opens inside `K`, since their
projectors absorb `χ_K`; hence the sections and germs agree.

`originalGerm_surjective` starts from Mathlib's representative theorem for the
actual stalk. Represent a germ by a section `s` on an open `U`, shrink to a
compact-open neighborhood `K ⊆ U`, and take the original vector underlying
`s`'s component at `K`. Compatibility of the family identifies its
original-vector section on `K` with the restriction of `s`; germ-restriction
compatibility gives the required original-vector preimage.

`originalGerm_ker` specializes the equality criterion to zero and uses
`annihilatorDescription` to identify the linear kernel with the literal
annihilator. `vectorStalkComparison` transports the quotient along this equality and applies
`LinearMap.quotKerEquivOfSurjective` to give the complex-linear equivalence
with its representative formula. The closing theorem assembles the two
independent-universe basis clauses and the four all-open clauses into the
exact aggregate proposition.

No compactness of the space, finite-dimensionality, supplied comparison map
or additional action is assumed. The original action, recovered complex
structure, published annihilator and both actual colimit stalks are retained.
The all-open clauses apply at every common universe `u`; only that part uses
a common universe, while the basis clauses keep independent `u` and `v`.
The construction works pointwise and makes no global nonemptiness assumption.
This quotient of the original module is distinct from the compact-section
quotient in Renard's later printed-p.42 Remark.

Worker 523 implemented the proof. Worker 623 checked the original passage,
the annihilator argument, the universe scope and the unchanged protected
import closure, and contributed this proof description. These coauthor checks
do not replace independent semantic review.
