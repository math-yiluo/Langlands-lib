# Actual Picard inclusion as a strong transformation

For arbitrary schemes `X S : Scheme.{u}` and a flat morphism `f : X ⟶ S`,
`PicardGroupoid.toFamilyStrongTrans f` is a strong transformation from the
actual relative Picard pseudofunctor
`(relativeSpace f).op.toPseudofunctor.comp PicardGroupoid.pseudofunctor`
to `CoherentSheaves.FamilyGroupoid.pseudofunctor f`. Both pseudofunctors are
defined on the full slice `LocallyDiscrete (Over S)ᵒᵖ`. The universe `u` is
arbitrary.

The component at `T : Over S` is definitionally `relativeToFamily f T`,
as exposed by `toFamilyStrongTrans_app`. It retains the actual module
sheaf on `T.left ×_S X` and every actual module isomorphism between these
line bundles. The imported inclusion supplies the local finite
presentation and relative stalk flatness of this same sheaf, using
flatness of `f` and its base changes.
`toFamilyStrongTransFullyFaithful f T` supplies full-faithfulness data
for this exact component, by `relativeToFamilyFullyFaithful f T`.

The construction uses two private general lifting arguments. First,
`propertyStrongTrans` factors a category-valued strong transformation
through a pullback-stable full-subcategory predicate when all component
objects satisfy that predicate. It lifts the naturality isomorphisms
using `ObjectProperty.isoMk`. The identity and composition laws follow
by full-subcategory morphism extensionality from those of the original
transformation. Applied to `toModuleStrongTrans (relativeSpace f).op`,
this gives a strong transformation into the actual family categories.
Membership of each image object is obtained from the imported
`relativeToFamily` construction.

Second, `coreStrongTrans` lifts a strong transformation from groupoid
fibres to the cores of the target categories. Its component is the
functor to the core, and its naturality isomorphisms lift by `Core.isoMk`.
Core morphism extensionality reduces the identity and composition laws
to the original laws. Its target directly reuses the shared
`CoherentSheaves.corePseudofunctor` from
[CoherentSheaves/Pullback](../CoherentSheaves/Pullback.md), constructed by
Worker 214. Its three coherence proofs translate the original associativity
and unit laws to component equations and apply core morphism extensionality.

These lifts initially give components propositionally equal to
`relativeToFamily`: their object actions and forward module morphisms
agree definitionally, while the chosen inverse data need not.
Functor extensionality, core morphism extensionality, and
full-subcategory morphism extensionality establish the equality.
The general private `replaceStrongTransApp` transports the naturality
isomorphisms along these component equalities. Its laws follow by
substitution from the original strong transformation. This makes the
public component formula definitional without repeating the
geometric pullback coherence calculation.

This is internal categorical infrastructure derived from the actual
Picard-to-module comparison, the actual flat-family inclusion, and the
ordinary family pullback pseudofunctor. It includes naturality for
2-morphisms and compatibility with both identity and composition
comparisons, including the relative-space functor's equality
transports. It assumes only flatness of `f` and imposes no restriction
on test schemes, including empty or non-quasi-compact tests.
It proves no openness, essential surjectivity, descent, algebraicity,
or atlas-existence assertion.
