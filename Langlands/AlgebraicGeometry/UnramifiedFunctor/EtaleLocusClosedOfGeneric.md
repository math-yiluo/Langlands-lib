# Murre's Lemma 2 for closed subschemes of étale charts, from the generic case (statement)

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusClosedOfGeneric`
defines one `Prop`-valued statement in the namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus`. It proves nothing.

It imports the published module
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreEtaleLocusClosed`. That
module defines `ClosedEtaleLocusOpenStatement` (Murre's Lemma 2 for closed
subschemes `Spec (R'/𝔍)` of étale `Spec R`-schemes `Spec R'`); its Markdown
explains the statement and its correspondence with Murre's text. The
conditions `MurreConditions` are those of the published module
`MurreProofSteps`. `InfinitesimallyEtaleAt` (infinitesimal étaleness of an
element at a point, SGA 3, XI, Remark 1.8) is that of `MurreLocalToGlobalSteps`.
`NoLargerLift` and `algebraOver` are those of `MurreCriterionStatement`.

## `ClosedOfGenericStatement`

`ClosedOfGenericStatement.{u, v}` is the implication `H → ClosedEtaleLocusOpenStatement.{u, v}`,
where the hypothesis `H` says the following. Let `R : CommRingCat.{u}` be
noetherian and `F : (Over (Spec R))ᵒᵖ ⥤ Type v` a presheaf with
`MurreConditions F`. Let `R'` be an étale `R`-algebra in universe `u`, `𝔍` an
ideal of `R'`, and
`ξ : F.obj (op (algebraOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (R' ⧸ 𝔍)))`.
Let `y : PrimeSpectrum (R' ⧸ 𝔍)` be a point at which `ξ` is infinitesimally
étale (`InfinitesimallyEtaleAt F ξ y`), and suppose its prime in `R`,
`y.asIdeal.comap (algebraMap R (R' ⧸ 𝔍))`, is contained in `nilradical R`.
Then there is an open set `V` of `PrimeSpectrum (R' ⧸ 𝔍)` containing `y` such
that, for every `w ∈ V`, writing
`O_w = Localization.AtPrime (w.asIdeal.comap (Ideal.Quotient.mk 𝔍))` for the
local ring of `Spec R'` at the prime below `w`:

- the ideal `𝔍.map (algebraMap R' O_w)` is nilpotent, and
- `NoLargerLift O_w ξ`: the restriction of `ξ` to `Spec (O_w/𝔍O_w)` lifts to
  no closed subscheme `Spec (O_w/J)` of `Spec O_w` with `J < 𝔍O_w`.

The hypothesis is written out in full. Its text is the statement
`EtaleLocus.GenericNoLargerLiftStatement` that the two executors of this task
agreed on. Worker 175 is proving that statement separately. Once it is
published, applying the theorem proving `ClosedOfGenericStatement` to it gives
`ClosedEtaleLocusOpenStatement`.

Universe parameters: `u` for schemes and rings, `v` for the values of `F`.
The statement is proved in module `EtaleLocusAssembly` as
`Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus.closedEtaleLocusOpen_of_generic`.

## Correspondence with Murre's proof

Murre proves Lemma 2 (printed p.250, PDF p.9) after reducing to a closed
immersion `τ' : Y → S'` into an étale `S`-scheme `S'` (the reduction is
`ClosedReductionStatement`, published). He then fixes `y` in the étale locus
`E` and lets `s` be its image in `S`. He distinguishes two cases (printed
pp.251–252, PDF pp.10–11):

- (a) `s` is not a generic point of an irreducible component of `S`. With
  `𝔍` the ideal of the reduced closed subscheme `{s̄}`, he considers the
  thickenings `S_n = ({s̄}, 𝒪_S/𝔍^{n+1})`. `F` is representable over them by
  the hypothesis on closed subschemes. He then passes to the formal
  completion of `Y` along these thickenings.
- (b) `s` is a generic point of an irreducible component of `S`, which he may
  assume to be `S` itself. Then `Y = V(𝔍)` with `𝔍` nilpotent. By (F8)
  (`GenericNonLifting`) and (F2), at every point `z` of a neighbourhood the
  restriction of `ξ` lifts to no subscheme of `Spec 𝒪_{S,z}` strictly larger
  than `Spec 𝒪_{Y,z}`. He then concludes with an argument on the local rings
  of the representing scheme of the base change to `Spec 𝒪_{S,z}`.

Murre's openness criterion is EGA III, chap. 0, Corollary 9.2.6: the étale
locus `U` is open if, for every `y ∈ Y`, the set `closure {y} ∩ U` is either
empty or contains a nonempty open subset of `closure {y}`.

The hypothesis `H` is the first half of case (b), up to the "no larger lift"
conclusion. Here `S = Spec R` is affine and noetherian. A point of `S` is
generic exactly when its prime is minimal. The condition used here, "the prime
of `R` below `y` lies in the nilradical", says that this prime is the unique
minimal prime. The remaining points, including those over a minimal prime of
an `R` with several minimal primes, are treated by the case (a) argument (the
prime is then not nilpotent, so all its powers are nonzero). The nilpotency of
`𝔍 O_w` comes from Murre's choice of the neighbourhood, an irreducible open
subscheme of `S'` whose generic point lies over `s`.

## Sources and provenance

Provenance is derived: the statement is an intermediate statement of this
project, splitting Murre's proof of Lemma 2 between the two cases as described
above. Murre does not state it separately.

- J. P. Murre, *Representation of unramified functors. Applications
  (according to unpublished results of A. Grothendieck)*, Séminaire Bourbaki
  exp. 294 (1964–65), registered as
  `murre-1965-bourbaki-294-unramified-functors` (SHA-256
  `e36edaf9f965bbc92b0bdc36d8026fd7c87d890b859841d1dd965193385227dd`).
  Printed page `p` is PDF page `p − 241`. Lemma 2 and its proof: printed
  pp.250–252 (PDF pp.9–11).
