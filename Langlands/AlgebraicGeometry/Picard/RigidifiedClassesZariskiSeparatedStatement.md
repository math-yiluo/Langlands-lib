# Zariski separatedness of rigidified abelian-scheme classes

`Langlands.AbelianScheme.RigidifiedClassesZariskiSeparatedStatement.{u}`
states that actual rigidified isomorphism classes on an abelian scheme are
determined Zariski-locally on the test scheme. Two classes on `T ×_S A` are
equal if their pullbacks to every member of an open cover of `T` are equal.
This file defines the proposition only. It supplies no proof.

## Exact interface

The statement quantifies over every `S : Scheme.{u}`, every
`A : AbelianScheme S`, every `T : Over S`, every open cover
`𝒰 : T.left.OpenCover.{u}` and every `q r : RigidifiedClasses A T`.

For each index `i`, the member `𝒰.f i : 𝒰.X i ⟶ T.left` is made an `S`-scheme
`Over.mk (𝒰.f i ≫ T.hom)`. `Over.homMk (𝒰.f i)` is the resulting slice
morphism to `T`. The hypothesis is that, for every `i`, the published class
pullback

```lean
RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
  (unitSection_comp A)
  (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)
```

sends `q` and `r` to the same class. The conclusion is `q = r`.

`RigidifiedClasses A T` is the published quotient of the actual category
`RigidifiedFamily A T` by isomorphism. Its objects are line bundles on the
chosen total space `T ×_S A`, rigidified along the section
`(id_T, unitSection A ∘ T.hom)`. Its isomorphisms are module isomorphisms
compatible with the rigidifications. `classesPullback` is `Quotient.map` of
the actual relative rigidified pullback functor. Hence both hypothesis and
conclusion concern actual rigidified isomorphism classes. No ordinary Picard
quotient, sheafification or abstract class functor is used.

The cover has index type in universe `u`, written explicitly as
`OpenCover.{u}`. This includes the chosen affine cover of every
`Scheme.{u}`. Without the explicit level, the Prop-valued definition would
contain an unsolved universe metavariable.

There is no restriction on `S` or `T`. In particular, nonreduced and
non-quasi-separated schemes are included. Neither the cover nor its members
need be affine or quasi-compact. There is no geometric Picard-zero
assumption, so the statement applies in particular to Picard-zero classes.
The statement has no hypothesis asserting a dual scheme, representability,
a universal family, a class sheaf, triviality of rigidified automorphisms or
universal global functions.

## Derived provenance

This is a derived, Zariski-only consequence needed for local-to-global
classification of rigidified classes. A typical use restricts a class to an
affine open cover of an arbitrary test scheme, identifies its restrictions
there, and must then recover the identification of the original global
class. The relative existence route of
`PicardZeroQuasiSeparatedExtensionStatement.md` lists exactly this
Zariski separatedness as one way to identify global classes.

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
Chapter VI §1, paragraph (6.2), printed pp.88–89 (PDF pp.92–93), registered
as `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`, was read
for these pages. Under its hypotheses `(∗)`, the source assumes that
`f : X → S` is quasi-compact and quasi-separated, that
`f_* O_(X ×_S T) = O_T` for all `S`-schemes `T`, and that `f` has a section
`ε`. On printed p.88 it identifies an endomorphism of a rigidified line
bundle with a global function `h` on `X_T` satisfying `ε^*(h) = 1`. It
deduces that rigidified line bundles have no nontrivial automorphisms. It
then defines the functor `P_{X/S,ε}` of rigidified isomorphism classes. On
printed p.89, item (iii) states that this functor is an fppf sheaf, by descent
theory for line bundles. No source-specific errata for this draft were found
in the project literature collection or published notes.

The present statement isolates a weaker consequence of (iii). It replaces
fppf coverings by Zariski open covers, asserts only separatedness, and
specializes to abelian schemes. It asserts no gluing of local classes and no
fppf sheaf property. It states no ordinary Picard functor and no
ordinary/fppf comparison. The source's `X ×_S T` is the Library's
`T ×_S A`, by the convention of the published relative family.

The final statement omits the source's global-functions hypothesis because an
applicable result is already published, rather than because that hypothesis
is assumed silently. `Langlands.AbelianScheme.universalGlobalFunctions`
proves that every actual projection `T ×_S A → T` induces an isomorphism on
global functions. It follows from
`Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`, since
every such projection is a base change of the smooth, proper, geometrically
connected structure morphism of `A`. Using that theorem is an obligation of
the proof, not part of this statement.

## Remaining proof obligations

Equality of the restricted classes supplies, for each `i`, only the
existence of some rigidified isomorphism between the pullbacks of chosen
representatives of `q` and `r`. These local witnesses are unrelated a priori.
Their restrictions to overlaps need not agree, so they do not glue without
further argument. Compatibility of the witnesses on overlaps needs a proof.

One route proves uniqueness of rigidified isomorphisms between actual
rigidified line bundles. It applies universal global functions, so that a
rigidified automorphism, a unit global function equal to `1` along the
section, is the identity. The local witnesses then agree on the pulled-back
overlaps. The proof glues these compatible local module isomorphisms over
the pulled-back open cover of the total space `T ×_S A`. Finally it checks
that the glued isomorphism preserves the rigidification globally.
Identifying the iterated pullbacks to overlaps can use the published
pullback coherence. Any proof must include nonreduced and non-quasi-separated tests
and covers indexed by universe `u`.

These are obligations of a separate exact-target proof task. The
ordinary Picard and fppf, ordinary/rigidified comparison, relative existence,
relative geometry, field existence and openness, and global-functions
workflows retain their separate ownership and existing controls.
