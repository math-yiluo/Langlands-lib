# Coinduced Galois fixed sections and ordinary higher direct images

Module `Langlands.Cohomology.AnalyticEtaleGaloisCoinducedLocalAcyclic`, namespace
`Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic`.

This module states one local analytic input,
`AnalyticEtaleGaloisCoinducedLocalAcyclicStatement`, and the two auxiliary
definitions it needs. The statement is **unproved**: it is a `def` of type `Prop`, and
no result in this module assumes or proves it.

## Setting

`K` is a complete ultrametric normed field, `L` a normed `K`-algebra that is a
field, and `X : LocalizedCategory.{u, v, v}` an analytic space. `G` is a group with a
topology and `ρ : G →* Aut X` is an action. Coefficients are modules over a
commutative ring `R : Type (max u (v + 1) uL)`. An étale `G`-sheaf is an object
`S : EtaleGSheaf ρ (ModuleCat R)`: a sheaf on the twisted étale site whose sections
are locally discrete for the lifts on distinguished étale objects (Library
`Langlands.Sheaf.Equivariant.Analytic.EtaleGSheaf`). Its sections over a twisted
object `V` are `S.obj.obj.obj (op V)`.

The statement `AnalyticEtaleGaloisCoinducedLocalAcyclicStatement` binds three
instance hypotheses explicitly in its own signature, so all three are part of the
elaborated statement:

* `[IsTopologicalGroup G]`: `G` is a topological group;
* `[Small.{max u (v + 1) uL} G]`;
* `[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]`:
  admissible refinements for the lifts on distinguished étale objects.

## Scope relative to `AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement`

The module imports
`Langlands.Cohomology.AnalyticEtaleSmoothPointProductLocalAcyclicCorrected`. Its
statement `AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement` is the target
this input serves. Like the statement here, it binds `[IsTopologicalGroup G]`,
`Small` and `HasAdmissibleRefinements` on the definition itself. The older proposition
`AnalyticEtaleSmoothPointProductLocalAcyclicStatement` declared
`[IsTopologicalGroup G]` only as an unused section variable, so Lean dropped it from
the signature. It is not to be used as a target or premise. The topological-group
hypothesis is needed by the source argument (step 3 of the expected proof below).

## Auxiliary definitions

* `deckEndomorphism V e he`. For an object `V` of the twisted étale category and an
  automorphism `e` of `V.obj.left` with `e.hom ≫ V.hom = V.hom` (an automorphism over
  `X`), this is the twisted endomorphism of `V` with twist `1` and underlying arrow
  `e.hom`. Restriction along it is the action of the deck transformation `e` on
  sections.

* `liftFixedSubmodule S V l Kₒ hK`. For an action lift `l : ActionLift ρ V.hom` with
  open subgroup `l.subgroup`, and a subgroup `Kₒ ≤ l.subgroup`, this is the
  submodule of sections `s` of `S` over `V` with `S.map (liftAction l k).unop.op s = s`
  for every `k ∈ Kₒ`. Here `liftAction l k` is the Library's local action of the lift:
  the twisted endomorphism with twist `k⁻¹` and arrow `(l.action k⁻¹).hom`.

* `HasCoinducedGaloisFixedSections L S`. For every datum consisting of
  1. an object `V` of the twisted étale category whose structure arrow is
     distinguished étale (`IsDistinguishedEtale V.hom`);
  2. a finite group `Γ : Type` and a homomorphism `deck : Γ →* Aut V.obj.left` with
     every `deck γ` over `X` (`(deck γ).hom ≫ V.hom = V.hom`);
  3. freeness on `L`-points: if `deck γ` fixes some point
     `p : (localizedFieldPointFunctor L).obj V.obj.left`, then `γ = 1`;
  4. a lift `l : ActionLift ρ V.hom` whose automorphisms `(l.action k).hom` commute
     with every `(deck γ).hom`;
  5. an open subgroup `Kₒ` of `G` with `Kₒ ≤ l.subgroup`;

  there are a module `A : ModuleCat R` and an `R`-linear map
  `π : S.obj.obj.obj (op V) →ₗ[R] A` such that the map sending a section `s` in
  `liftFixedSubmodule S V l Kₒ hK` to the function `γ ↦ π (γ s)` is a bijection onto
  all functions `Γ → A`. Here `γ s` is restriction of `s` along
  `deckEndomorphism V (deck γ) _`. In other words, the `Kₒ`-fixed sections over `V` form
  a coinduced `Γ`-module, `Map(Γ, A)`.

## The statement

`AnalyticEtaleGaloisCoinducedLocalAcyclicStatement L X R G ρ` (with the three
instance hypotheses above) says the following. Assume the underlying topological
space `localizedSpaceFunctor.obj X` is Hausdorff and `IsContinuousAction ρ` holds.
Let `S` be an étale `G`-sheaf with `HasCoinducedGaloisFixedSections L S`. Then for every `q : ℕ`, the object

`(etaleUnderlyingHigherDirectImage X R (q + 1)).obj F`

is zero, where
`F = (TwistedOver.restriction ρ (etaleTopology X) (ModuleCat R)).obj
  ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _).obj S`
is the ordinary étale sheaf underlying `S`. The functor
`etaleUnderlyingHigherDirectImage X R n` is the Library's actual `n`-th right derived
functor of the direct image from the ordinary étale site of `X` to sheaves on the
underlying topological space. So all positive ordinary higher direct images of `F`
vanish.

## Provenance

This is a derived statement. It isolates the analytic content of step (1′) in the
proof of Proposition 1.5.1 in Berkovich's manuscript *Etale equivariant sheaves on
p-adic analytic spaces* (1995–1996, printed pp. 10–11). Berkovich verifies
`H^q(Gal_{H(x)}, F_x) = 0` for `q ≥ 1` there. To do so he shrinks `X` and `G`
(observation (a)) so that a distinguished étale `φ : X′ → X` with `φ⁻¹(x) = {x′}` and
`H(x′) = K` is a `G`-morphism and a finite Galois covering with group
`Gal(K/H(x))`. He writes `F_x(K)` as an inductive limit of sections over the
`φ⁻¹(U)`, then uses that the relevant sections are products of coinduced
`Gal`-modules. The statement here keeps exactly this structure. The coinducedness of
the fixed sections on equivariant finite Galois data is the hypothesis. The vanishing
of the positive higher direct images is the conclusion.

## Expected proof (not part of this module)

Write `F` for the ordinary étale sheaf underlying `S`, and fix `q ≥ 1`.

1. **Germ criterion.** By the Library theorem
   `isZero_etaleUnderlyingHigherDirectImage_iff_germCohomology`, it suffices that the
   ordinary germ cohomology `etaleUnderlyingGermCohomology X R y q` of `F` vanishes at
   every point `y`. By Berkovich 1993, Proposition 4.2.4 (printed p. 87), this germ
   cohomology is `H^q(G_y, F_ȳ)`, with `G_y = Gal(H(y)^s / H(y))`. Identifying the two
   in Lean is the main analytic work of the proof.
2. **Inflation.** `H^q(G_y, F_ȳ)` is the colimit over finite Galois extensions
   `K/H(y)` of `H^q(Gal(K/H(y)), F_y(K))`, where `F_y(K) = F_ȳ^{G_K}`. It suffices to
   show that each `H^q(Gal(K/H(y)), F_y(K))` vanishes.
3. **Galois neighbourhoods with lifts.** By Berkovich 1993, Proposition 4.2.2 and
   Theorem 3.4.1 (printed pp. 87 and 65), `F_y(K)` is the filtered colimit of `F(V)` over
   distinguished étale `φ : V → X` that are finite Galois coverings of small
   neighbourhoods of `y`, with group `Γ = Gal(K/H(y))` acting by deck transformations
   over `X`, one point `y′` over `y` and `H(y′) = K`. Distinguished étale neighbourhoods
   are cofinal (Equish p. 6). Shrinking to connected neighbourhoods makes `Γ` act freely
   on the `L`-points of `V`: a deck transformation fixing an `L`-point fixes a point and
   its residue field, so it is trivial on the connected covering. Equish step (1′)
   (p. 11) then shrinks `X` and `G` so that `φ` becomes a `G`-morphism. This is the Key
   Lemma (Equish §1.4; Library `QuasiEtaleActionLiftStatement`, which assumes
   `IsTopologicalGroup G`), giving an action lift `l` of an open subgroup on `V`. This
   step uses the topological-group structure: lifts provided by admissible refinements
   sit on objects reached by twisted arrows of some twist `g`, and moving them back to a
   neighbourhood of `y′` replaces an open subgroup `H` by `g H g⁻¹`. That subgroup is
   open because conjugation is a homeomorphism of a topological group.
4. **Restriction of discreteness.** Every section of `S` is locally discrete. On the
   compact closure of a smaller Galois neighbourhood, finitely many admissible pieces
   suffice, so a finite intersection of open subgroups works. With
   `IsDiscreteSection.restrict` and `HasAdmissibleRefinements.isRestrictionEquivariant`,
   the restriction of the section to a smaller Galois neighbourhood `V′` lies in some
   `liftFixedSubmodule S V′ l Kₒ hK` with `Kₒ` open.
5. **Commuting with the deck group.** Apply `isRestrictionEquivariant` to the
   endomorphisms `deckEndomorphism V (deck γ) _`, which have twist `1`. Comparing twists
   forces the two lift elements in the compatibility to coincide, so `l` and `Γ` commute
   on an open subgroup. Intersecting these finitely many open subgroups, one for each
   `γ`, gives a lift commuting with all of `Γ`.
6. **Coinduced colimit.** Steps 3–5 write `F_y(K)` as a filtered colimit of the
   `Γ`-modules `liftFixedSubmodule S V l Kₒ hK`. By hypothesis these are coinduced, of
   the form `Map(Γ, A)`, so their positive `Γ`-cohomology vanishes (Shapiro's lemma).
   Cohomology of the finite group `Γ` commutes with filtered colimits. Hence
   `H^q(Gal(K/H(y)), F_y(K)) = 0` for `q ≥ 1`, and the positive higher direct images
   of `F` vanish.

Only genuine Galois data appear in this argument. As explained in step 3, freeness on
`L`-points holds for them. Requiring coinducedness only for data with free action on
`L`-points therefore does not weaken the hypothesis below what the proof uses. That
restriction is what makes the hypothesis verifiable for the induced point products
built from `L`-points. For those, the fixed sections are products over `Γ`-free sets of
`L`-points, as in Berkovich's formula `∏_i ∏_{(i, x′, ψ)} F_{x_i}`.

## Intended use

For the actual smooth point product `S` (the locally discrete part of the twisted
induction of a point product over `L`-points), the fixed sections over an admissible
object are coordinate families over left cosets of `Kₒ` and the `L`-point fibres of the
translates of `V`. On these, `Γ` acts freely through its action on `L`-points. This
gives `HasCoinducedGaloisFixedSections L S` by an algebraic argument, so this
statement implies `AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement`. That
algebraic reduction is not part of this module.
