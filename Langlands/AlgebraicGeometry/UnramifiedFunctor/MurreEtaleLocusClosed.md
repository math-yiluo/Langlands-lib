# Murre's Lemma 2 for closed subschemes of étale schemes (statements)

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreEtaleLocusClosed`
defines two `Prop`-valued statements in the namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus`. It proves nothing.

The conditions `MurreConditions`, the predicate `UnramifiedRepresentable` and
the base change `baseChange` are those of the published module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps`; the helper
`InfinitesimallyEtaleAt` (infinitesimal étaleness of an element at a point,
SGA 3, XI, Remark 1.8) is that of the published module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalSteps`; the
statement `MurreEtaleLocusOpenStatement` (Murre's Lemma 2 over the spectrum of
a noetherian ring) is that of the published module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreEtaleLocusOpen`, whose
Markdown explains its correspondence with Murre's text.
`algebraOver g A` (from the published module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement`, a
dependency of the modules above) is `Spec A`, viewed as an object of
`Over (Spec R)` through `Spec A → Spec R' → Spec R` when `g` is the structure
morphism `Spec R' → Spec R` and `A` is an `R'`-algebra.

## `ClosedEtaleLocusOpenStatement`

`ClosedEtaleLocusOpenStatement.{u, v}`: let `R : CommRingCat.{u}` be a
noetherian ring and `F : (Over (Spec R))ᵒᵖ ⥤ Type v` a presheaf with
`MurreConditions F`. Suppose that

- for every point `s : Spec R`, the base change
  `baseChange ((Spec R).fromSpecStalk s) F` of `F` to `Spec 𝒪_{Spec R, s}`
  satisfies `UnramifiedRepresentable`;
- for every ideal `I : Ideal R` with `I ≠ ⊥`, the base change of `F` to the
  closed subscheme `Spec (R/I)` (along
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`) satisfies
  `UnramifiedRepresentable`.

These are exactly the hypotheses on `R` and `F` of
`MurreEtaleLocusOpenStatement`. Let `R'` be an étale `R`-algebra
(`[Algebra R R'] [Algebra.Etale R R']`, with `R'` in universe `u`), `𝔍` an
ideal of `R'`, and
`ξ : F.obj (op (algebraOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (R' ⧸ 𝔍)))`,
that is, an element of `F` over the closed subscheme `Spec (R'/𝔍)` of the
étale `Spec R`-scheme `Spec R'`. Then the set
`{y | InfinitesimallyEtaleAt F ξ y}` of points of `Spec (R'/𝔍)` at which
`ξ` is infinitesimally étale is open.

This is the special case of `MurreEtaleLocusOpenStatement` in which the
scheme `U` is `Spec (R'/𝔍)` over `Spec R` through `Spec R'` (such a `U` is of
finite type, affine, hence separated and quasi-compact, and formally
unramified over `Spec R`).

## `ClosedReductionStatement`

`ClosedReductionStatement.{u, v}` is the implication
`ClosedEtaleLocusOpenStatement.{u, v} → MurreEtaleLocusOpenStatement.{u, v}`:
the special case above implies the general Lemma 2. Universe parameters: `u`
for schemes and rings, `v` for the values of `F`. It is proved in module
`MurreEtaleLocusClosedProof` as
`Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus.murreEtaleLocusOpen_of_closed`.

## Correspondence with Murre's proof

Murre's proof of Lemma 2 (printed p.250, PDF p.9) begins: "First we note that
we may assume `τ : Y → S` is a closed immersion. Because if `y ∈ U`, then we
have (after replacing, if necessary, `Y` by a neighbourhood of `y`) a
factorization `Y → S' → S`, with `τ'` closed immersion and `φ` étale." He
then base changes `F` along `φ` and continues with `F' = F ×_S S'` and the
closed immersion `τ' : Y → S'` (printed pp.250–251).

The factorization is EGA IV, Corollary 18.4.7: a morphism locally of finite
type is formally unramified at `x` if and only if, on an open neighbourhood
`U` of `x`, it factors as a closed immersion followed by an étale morphism.
`ClosedReductionStatement` is the first half of Murre's step: openness of the
étale locus is local on `Y`, and locally `Y` is a closed subscheme
`Spec (R'/𝔍)` of an étale `Spec R`-scheme `Spec R'`. In the statement the
functor `F` is not base changed to `Spec R'`: `Spec (R'/𝔍)` is kept as an
object over `Spec R` and the hypotheses on `R` and `F` are those of Lemma 2.
The passage to `F'` over `S'` belongs to the proof of
`ClosedEtaleLocusOpenStatement`, which is not given here.

## Sources and provenance

Provenance is derived: both statements are intermediate statements of this
project, splitting Murre's proof of Lemma 2 at its first reduction step as
described above. Murre does not state them separately.

- J. P. Murre, *Representation of unramified functors. Applications
  (according to unpublished results of A. Grothendieck)*, Séminaire Bourbaki
  exp. 294 (1964–65), registered as
  `murre-1965-bourbaki-294-unramified-functors` (SHA-256
  `e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`).
  Printed page `p` is PDF page `p − 241`. Lemma 2 and the first step of its
  proof: printed pp.250–251 (PDF pp.9–10).
- A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique IV,
  Quatrième partie*, Publ. Math. IHÉS 32 (1967), registered as
  `grothendieck-dieudonne-ega-iv4-1967` (SHA-256
  `b4277fb99c6edf8feec5b01f54368e4b8521bcd52871316c0edf6ff4ae69389e`).
  Corollary 18.4.7: printed pp.121–122 (PDF pp.120–121).
