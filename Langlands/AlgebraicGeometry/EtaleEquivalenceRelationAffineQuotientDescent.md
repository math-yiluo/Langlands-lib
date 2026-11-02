# Affine quotients descend along cofiltered cartesian diagrams

This internal helper proves affine quotient descent for an arbitrary cofiltered
cartesian diagram of étale equivalence relations in universe `u`. Let `D` be
such a diagram, let every level have affine object and relation schemes, and
let `c` be a cone whose object cone is a limit. If `c.pt.HasAffineQuotient`,
then `(D.obj i).HasAffineQuotient` for some index `i`. No Noetherianity or
finite type hypothesis is imposed on the diagram or on its limit.

The application is the affine part of Stacks Lemma 70.5.10 (Tag 07SQ), used
for the finite affine cover in Lemma 70.5.11 (Tag 07SR) and in the proof of
Proposition 70.8.1 (Tag 07SU). The registered sources are
`stacks-noetherian-approximation-2026-11-01` (`07SQ.html`, proof, especially
the eventual cartesian comparison) and `stacks-stratification-2026-11-02`
(`07SR.html`, proof). This is a derived presentation-level argument, rather
than a declaration of either full algebraic-space lemma. The implemented
proof uses the existing Noetherian pushout theorem and finite-presentation
factorization; it does not assume affine quotient descent or a Noetherian
first level. Scheme gluing and the final first-level construction remain
separate steps.

`AffineLimit.isIso_baseChangeMap_of_isPullback` identifies a supplied
base-change map with the composite of the two canonical pullback
isomorphisms. Its hypotheses are two actual pullback squares, one for `X`
and one for `Y`, with the same scheme at their upper left. The pullback
universal property gives the equality with that composite, so the map is
an isomorphism.

`EtaleEquivalenceRelation.locallyOfFinitePresentation_toSpecULiftZ` shows
that the structure map of `Spec B` to the terminal `Spec (ULift ℤ)` is
locally of finite presentation when `B` is of finite type over `ℤ`.
The unique algebra structure over `ULift ℤ` changes the base of the finite
type assertion. The base ring is Noetherian, so Mathlib upgrades locally
finite type to locally finite presentation. Uniqueness of maps to the
terminal scheme identifies this spectrum map with the stated map. This
retains the arbitrary universe `u`.

`EtaleEquivalenceRelation.exists_finitelyPresented_kernel_square` assumes
an affine object and relation and an affine quotient of a relation `E`.
The existing `exists_fg_pushout_of_hasAffineQuotient` supplies finite type
rings `A`, `B`, an étale faithfully flat map `A → B`, and a bijective
tensor-product presentation of `Γ(E.R)`. The ring pushout criterion turns
that presentation into a pushout. Applying `Spec` and transporting by the
canonical affine isomorphisms gives actual affine schemes `U = Spec B`,
`M = Spec A`, an étale surjection `q : U → M`, and `f : E.U → U` with
`IsPullback (E.t ≫ f) E.s q (f ≫ q)`. Both `U` and `M` are locally of finite
presentation over `Spec (ULift ℤ)`, by the preceding lemma. The proof uses
the existing kernel-pair module's pushout-to-pullback route.

The remaining declarations are in `EtaleEquivalenceRelation.CartesianDiagram`.

`exists_kernel_square` starts with an object map `f : (D.obj i).U → U`,
its source-target compatibility after `q`, and the corresponding kernel
square at the limit. Put `B = U ×_M (D.obj i).U` and let
`F : (D.obj i).R → B` be induced by `t ≫ f` and `s`. The source cartesian
square of the cone and the assumed kernel square show that the base
change of `F` to the limit is an isomorphism. Restrict the diagram to
indices mapping to `i`. Both schemes over `(D.obj i).U` are affine and
locally of finite presentation: their structure maps are étale. The
existing `AffineLimit.exists_isIso_baseChangeMap` produces an index over
`i` at which the comparison is an isomorphism. Transport the source
pullback along this isomorphism and paste it with the defining pullback
of `B`. The result is the required kernel square at an actual later
index, with its actual transition to `i`.

`exists_hasAffineQuotient` first derives affineness of the limit's object
and relation schemes from their affine limit diagrams. It obtains the
finitely presented kernel model above and factors `f` through an object
level, using Mathlib's
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` over the
terminal base. The kernel square gives equality of the two composites
from the relation limit into `M`. Because `M` is locally of finite type
over that base, `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`
makes this equality hold after a transition. Cone naturality retains the
original map `f`. Now `exists_kernel_square` supplies a kernel square at
a further index. The existing
`hasAffineQuotient_of_isPullback_kernelPair` theorem gives an affine
quotient there.

`affineQuotientLevel` chooses an index from this proved existence result;
`hasAffineQuotient_affineQuotientLevel` records its property.
`hasAffineQuotient_of_above_affineQuotientLevel` applies the published
cartesian affine quotient theorem to the supplied transition morphism.
It proves the property at every level mapping to the chosen index.

The mathematical inputs are the imported, proved ring presentation and
kernel-pair criteria, Mathlib's affine limit and finite-presentation
results, the earlier eventual-isomorphism helper, and pullback universal
properties. These yield the stated internal construction without assuming
any approximation statement.
