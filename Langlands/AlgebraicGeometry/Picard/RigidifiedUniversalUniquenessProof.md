# Uniqueness of universal rigidified line bundles

`Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.universalBundleUniqueness`
proves exactly the published proposition `UniversalBundleUniquenessStatement`,
imported from `Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalStatements`.
The proof preserves its universe parameter and its arbitrary base schemes,
scheme map, and section. It assumes the proposition
`RigidifiedModule.PullbackCoherenceStatement` explicitly, just as the target does.

Let `L` over the parameter scheme `P` and `M` over `Q` be universal. Surjectivity
of the classifying map for `M` at `P` supplies a morphism `a : P → Q` whose
pullback class is the class of `L`. Surjectivity for `L` at `Q` similarly
supplies `b : Q → P` whose pullback class is the class of `M`.

The proof applies injectivity of the classifying map for `L` at `P` to show
`a ≫ b = 𝟙 P`. The composition law rewrites the class of the pullback along
`a ≫ b` as pullback along `a` of the class classified by `b`. The two chosen
class equalities identify this with the class of `L`; the identity law gives
the same class for `𝟙 P`. Reversing the roles gives `b ≫ a = 𝟙 Q`.
The imported composition and identity laws use precisely the given coherence
hypothesis. These two inverse equations construct an isomorphism in `Over S`.

`classifyingMap_eq_iff` turns the class equality for `a` into existence of an
actual rigidified bundle isomorphism from the relative pullback of `M` to `L`.
For any other compatible parameter-scheme isomorphism `e`, the same equivalence
says that `e.hom` has this class. Injectivity of the classifying map for `M`
forces `e.hom = a`, and `Iso.ext` gives equality of isomorphisms. Thus the
uniqueness asserted is that of the scheme isomorphism; the proof does not assert
uniqueness of the rigidified bundle isomorphism.

This is a derived categorical proof using the published universal-property
interface in `RigidifiedUniversalBundle`. The original mathematical provenance
is recorded in the imported statement's Markdown: Edixhoven–van der
Geer–Moonen, *Abelian Varieties*, Chapter VI §1, (6.2), printed p.88.
The implemented proof uses the two classifying maps directly and does not
require a separate comparison with `comparisonIso`. It introduces no extra
axioms or existence hypothesis for universal bundles.
