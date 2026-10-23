# Commuting Hecke and enveloping actions on actual adelic functions

This internal construction combines the published operators in
`FiniteDifferential` with the finite-fiber integration and corner action in
`Langlands.Representation.Hecke`. It applies to every number field
`K : Type u`, every natural rank `n` (including zero), and complex coefficients.
The finite adelic matrix group retains its actual topology. Integration assumes
an explicit Borel measurable structure and a supplied left Haar measure `μ`.
There is no new assertion of Haar measure existence.

`finiteSmoothFiniteRightAction_isSmooth` proves that the published finite right
action on `FiniteSmoothRationalFunctions` is smooth: its defining common open
stabilizer fixes the vector in this concrete subspace. Each genuine enveloping
operator is bundled as `finiteSmoothDifferentialFiniteIntertwiner`, using the
already proved commutation between finite translation and differentiation.

`finiteSmoothHeckeAction` integrates that action. Its evaluation formula is

`(H(h)f)(x) = ∫ d, h(d) f(x * ofFinite(d)) dμ(d)`.

Thus the right translation is positive, with no inversion of `d`. Multiplication
in the Hecke algebra is the existing left-Haar convolution. The operator is a
nonunital complex algebra homomorphism to algebraic endomorphisms. The
representation carrier needs no norm or completeness, and evaluation needs no
continuity as a linear functional: the actual locally constant compactly
supported weighted orbit map is integrated by a finite measurable presentation.

`finiteSmoothEnvelopingAction_heckeAction` proves that every such Hecke operator
commutes with every genuine enveloping operator. The proof applies the published
integration naturality theorem to the constructed differential intertwiner.
It does not differentiate a Bochner integral or assume analytic bounds.

`centerFiniteHeckeAction` integrates the already constructed finite action on
`CenterFiniteFiniteSmoothRationalFunctions`. The injective concrete inclusion
intertwines this action with `finiteSmoothHeckeAction`; hence it is precisely
the restriction of the same operator. The enveloping and Hecke actions commute
on this space too. More precisely, `centerFamilyAnnihilator_le_heckeAction`
shows that every central operator annihilating all slices of an input also
annihilates all slices of its Hecke image. This is containment of annihilator
ideals, not equality: a Hecke operator can kill a nonzero vector.

For every subgroup `L` of the finite adelic group, `centerFiniteFixedEnvelopingAction` restricts
the genuine enveloping action to the existing `L`-fixed vectors. Its algebra
laws are inherited through the injective inclusion. For compact open `L`,
`centerFiniteHeckeCornerAction` is the published unital corner action on the
same fixed-vector space. The final commutation theorem is the corner
naturality theorem applied to the genuine differential intertwiner.

The provenance is derived from these published constructions and their
proved naturality laws. Borel–Jacquet, *Automorphic forms and automorphic
representations*, Corvallis Part I, §3.2 and §4.1 (printed p.194, one-based
PDF189), supplies the finite convolution convention and the product separation
of the infinite and finite adelic factors. The present compatibility results
on the larger concrete function spaces are internal derived results, not
quoted statements from that source.

These spaces impose a common finite stabilizer and, for the center-finite
versions, one finite center orbit on the whole family of infinite slices.
They impose neither compact-type finiteness, polynomial growth nor
cuspidality. This module does not prove differential preservation of the full
automorphic form space, construct a full archimedean Hecke algebra, or assert
admissibility or irreducible local components.

The action-type abbreviations `FiniteSmoothHeckeAction`,
`CenterFiniteHeckeAction`, `CenterFiniteFixedEnvelopingAction` and
`CenterFiniteHeckeCornerAction` keep the exported types compact.
`CenterFiniteFixedVectors` is an abbreviation for the existing fixed-vector
submodule, not a new carrier or a new hypothesis. These abbreviations preserve
the definitions and algebraic laws while avoiding repeated expansion of the
nested concrete function-space instances during declaration inspection.
