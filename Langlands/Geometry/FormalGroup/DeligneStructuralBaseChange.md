# Structural pullback of Deligne's homogeneous tangent sheaves

This module constructs structural pullback of the actual tangent-sheaf data
`T` in Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), Section 2 A,
printed p.109 (PDF p.3), final paragraph, continuing on printed p.110
(PDF p.4). There `T` is a cyclically graded structural-module sheaf with
invertible homogeneous components and an operator of degree one satisfying
`Pi^d = pi`. Proposition 2.4, printed p.110, identifies the four data attached
to a base-changed special formal module with inverse image of the original
four data. The construction here is derived infrastructure for that assertion.
It constructs structural pullback of `T` on objects.

All declarations are in `Langlands.DeligneFormalSpace`. Schemes, coefficient
rings and section modules use one universe. For a scheme `S`, a global section
`a : Gamma(S,top)`, positive `d` and a scheme morphism `f : S' -> S`, the final
constructor is

`LinePiSheaf.pullback f : LinePiSheaf d S a -> LinePiSheaf d S' (f.appTop a)`.

It uses the actual `Scheme.Modules.pullback f`. No flatness of `f`, nilpotence
of `a`, valuation, or local-field assumption is required for this construction.
The source's uniformizer is the specialization `a = phi(pi)`.

## Split ranges and homogeneous projections

For structural module sheaves on a site, `splitRange a p h` takes an actual
inclusion candidate `a : N -> M`, a retraction `p : M -> N` and the equation
`a ; p = id_N`. Its sections on each object are exactly the linear range of
`a`. Restriction preserves this range by naturality. To prove the range is a
subsheaf, start with a section `s` locally in that range. On each local range
presentation the retraction equation proves `a(p(s)) = s`; separatedness of
`M` gives this equality globally. Thus `p(s)` is a global range witness.
`splitRangeIso` identifies `N` with this actual range subsheaf, using `a` with
codomain restricted to its range and `p` restricted to the range.
`splitRangeIso_hom_inclusion` records its composite with the subsheaf inclusion.
These helpers apply to the site's sheaf of rings, independently of schemes.

For `M : GradedPiSheaf d R b`, `GradedPiSheaf.sectionProjection` inverts the
existing internal direct-sum inclusion and takes its `i`-th coordinate.
The diagonal and off-diagonal inclusion lemmas give identity and zero,
respectively. `projection` packages these linear maps as genuine module-sheaf
maps. Its restriction naturality is proved by direct-sum induction on sections
of `M`, reducing to a homogeneous section and using the two inclusion lemmas.

`inclusion_projection` and `inclusion_projection_ne` are the corresponding
sheaf-map equations. `section_hom_ext` states that linear maps out of a section
module agree if they agree on every homogeneous submodule; it uses the same
internal-sum induction. `sum_projection_inclusion` proves that the finite sum
of projection followed by inclusion is the identity. The sum is finite because
`d` is positive and the grading is `ZMod d`. The proof evaluates the sum of
sheaf maps through the additive forgetful/evaluation functor and reduces on
each homogeneous section to its single nonzero coordinate.

## Scalars and the distinguished operator

`structuralScalarEnd M a` multiplies each section of the actual structural
module sheaf `M` by the restriction of the global section `a`.
`structuralScalarEnd_apply` records this section formula.
`pullback_structuralScalarEnd` proves that pulling back this endomorphism
is multiplication by `f.appTop a` on the pulled structural module.
The proof transposes both maps under the actual structural pullback/pushforward
adjunction. Naturality and linearity of its unit, followed by the existing
`structuralScalar_pushforward` identity for the scheme's structure-sheaf map,
give equality. The scalar compatibility is proved from `f`, rather than
supplied as a preservation assumption.

`sectionEndHom` evaluates the actual endomorphism monoid of a structural
module sheaf on an open. `PiSheaf.pi_pow_sheaf` turns the existing sectionwise
power relation into an equality of sheaf endomorphisms.
`PiSheaf.pullback` pulls the total sheaf and its operator back by the actual
module pullback functor. Preservation of powers and the proved scalar
identity establish its required relation on every open of `S'`.

## Pulling back the actual homogeneous subsheaves

For a graded structural sheaf, `pullbackInclusion` and `pullbackProjection`
are the pullbacks of its actual inclusions and canonical projections.
Functoriality proves their diagonal identity and off-diagonal zero equations;
additivity proves `pullback_sum_projection_inclusion`.

`pullbackComponent` is the sectionwise range subsheaf of the pulled inclusion,
using `splitRange`. `pullbackComponentIso` identifies the pullback of the
original homogeneous component with this range. Thus the new grading consists
of actual submodules of the pulled total sheaf, and its component comparison
is constructed from the original inclusion and projection.

`pullback_isInternal` evaluates the transported splitting equations on each
open and applies `isInternal_of_finite_splitting`, the finite orthogonal
splitting lemma from `DeligneLatticeBaseChange`. Its conclusion is bijectivity
of the canonical direct-sum inclusion for these actual ranges.
`GradedPiSheaf.pullback` assembles the pulled operator and these homogeneous
subsheaves. The degree-one property follows by pulling back the original
component-operator inclusion square and evaluating it on a range witness.

## Preservation of local rank one

`structuralPullbackUnitIso` identifies pullback of the structure module with
the structure module on `S'`. It is the isomorphism supplied by Mathlib's
`SheafOfModules.pullbackObjUnitToUnit`. The underlying functor `Opens.map
f.base` preserves a terminal object and hence is final, which supplies the
hypothesis for that result.

`structuralPullbackRestrictIso` compares restriction of `f^* M` to the
inverse-image open `f^(-1)(U)` with pullback of `M` restricted to `U`, along
the actual restricted scheme morphism `f|_U`. It composes Mathlib's comparison
between restriction and pullback by an open immersion, pullback composition,
and the equality of the two scheme maps from the restriction square.

`IsLineSheaf.pullback` applies this comparison to an existing local
trivialization around `f(x)` and then applies `structuralPullbackUnitIso`.
This gives a trivialization on the inverse-image open around `x`.
`LinePiSheaf.pullback` combines `GradedPiSheaf.pullback`, this local-triviality
result, and `pullbackComponentIso` to establish the line condition for each
actual homogeneous range. No new trivializations or preservation certificates
are inputs to the constructor.

## Scope

This unit constructs the structural tangent-sheaf pullback on objects and
proves the displayed splitting, scalar and local-triviality laws. It does not
construct morphism functoriality, full four-data base change with its locally
generating `u`, admissibility transport, the functor on Nilp isomorphism
classes, or the normalized `PGL(d,F)` action. The inherited comparison between
stalkwise determinant conditions and an independently constructed exterior-power
subsheaf equality remains open. Proposition 2.4, existence of the special
formal module, and representability are not proved by these constructions.
