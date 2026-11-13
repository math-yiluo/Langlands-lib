# Representability of an fppf sheaf through a flat proper equivalence relation

Author: Worker 22, for task `07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705).
Worker 5705 uses the statement in the Picard construction of that task.

## Statement

`Langlands.AlgebraicGeometry.FppfQuotientRepresentabilityStatement.{u}` is a
proposition. Nothing here asserts a proof of it. It uses the conventions of
`Langlands.AlgebraicGeometry.AlgebraicSpace.Basic`:

- `FppfSheaf S = Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))`, the
  type-valued sheaves for the fppf topology on the slice `Over S`;
- `fppfTopology S = Scheme.fppfTopology.over S`;
- `schemeYoneda S = uliftYoneda.{u + 1}`, the functor of points of an object of
  `Over S` with values lifted to `Type (u + 1)`.

The Library's Picard sheaf `RelativePicard.classSheaf f` has the type
`FppfSheaf S`.

The statement quantifies over

- a noetherian commutative ring `A : Type u`, with `S = Spec (CommRingCat.of A)`;
- an fppf sheaf `G : FppfSheaf S`;
- objects `Z` and `R` of `Over S`;
- a morphism of presheaves `ζ : (schemeYoneda S).obj Z ⟶ G.obj`, that is, a map
  from the functor of points of `Z` to `G`. By the Yoneda lemma it is the same as
  an element of `G` over `Z`;
- two morphisms `s t : R ⟶ Z` in `Over S`.

Its hypotheses are:

1. `IsHQuasiProjective Z.hom`: the structure morphism of `Z` is a quasi-compact
   immersion into some `ProjectiveSpace A n` over `S` (see
   `Langlands.AlgebraicGeometry.HQuasiProjective`).
2. `Presheaf.IsLocallySurjective (fppfTopology S) ζ` (Mathlib): for every object
   `T` of `Over S` and every `g ∈ G(T)`, the morphisms `T' ⟶ T` along which `g`
   lifts to a `T'`-point of `Z` form an fppf-covering sieve. In other words,
   `ζ` is a surjection of fppf sheaves.
3. `IsPullback ((schemeYoneda S).map s) ((schemeYoneda S).map t) ζ ζ`: in the
   category of presheaves `(Over S)ᵒᵖ ⥤ Type (u + 1)`, the square formed by the
   functors of points of `s` and `t` and two copies of `ζ` is a pullback square.
   Thus `R`, with its projections `s` and `t`, represents `Z ×_G Z`: for each
   `T`, the `T`-points of `R` correspond, through `s` and `t`, to the pairs of
   `T`-points `x, y` of `Z` with `ζ x = ζ y`.
4. `Flat s.left` and `IsProper s.left`: the first projection `R ⟶ Z` is a flat
   and proper morphism of schemes.

The conclusion is that there are an object `Q` of `Over S`, a morphism
`π : Z ⟶ Q` in `Over S` and an isomorphism of presheaves
`e : (schemeYoneda S).obj Q ≅ G.obj` such that

- `IsHQuasiProjective Q.hom`;
- `(schemeYoneda S).map π ≫ e.hom = ζ`: under `e`, the map `ζ` is the functor of
  points of `π`;
- `π.left` is flat, surjective, proper and locally of finite presentation.

The isomorphism `e` says that `Q` represents `G` on all of `Over S`. With the
second clause, it also says that `ζ` is represented by the morphism `π`, so
every base change of `ζ` along a point of `G` is a flat, surjective, proper
morphism of schemes that is locally of finite presentation.

## Source

The statement is the fppf and flat form of Lemma 4.9 of S. L. Kleiman, *The
Picard scheme* (`kleiman-2005-picard-scheme-arxiv-math0504020v1`, p.30, proof
pp.30–31). Kleiman states:

> Lemma 4.9. Let `α : Z → P` be a map of étale sheaves, and set `R := Z ×_P Z`.
> Assume `α` is a surjection, `Z` is representable by a quasi-projective
> `S`-scheme, `R` is representable by an `S`-scheme, and the first projection
> `R → Z` is representable by a smooth and proper map. Then `P` is representable
> by a quasi-projective `S`-scheme, and `α` is representable by a smooth map.

The proof uses Exercise 4.10 (p.31): a map of étale sheaves `F → G` is a
surjection if and only if `G` is the coequaliser of `F ×_G F ⇉ F`. Kleiman calls
it "an elementary exercise in general Grothendieck topology".

Kleiman's conventions (p.15) say: "Throughout these notes, we work only with
locally Noetherian schemes". So his sheaves `Z`, `R` and `P` are sheaves on
locally noetherian `S`-schemes. The Lean sheaf `G` lives on all of `Over S`,
including non-noetherian `S`-schemes. The derivation below explains why the
argument does not need the restriction.

## Derivation of the Lean statement

The Lean statement changes Kleiman's lemma in the following ways. Its
provenance is therefore "derived".

- **Topology and smoothness.** Kleiman works with étale sheaves and assumes the
  first projection `R → Z` smooth. The Lean statement works with fppf sheaves,
  matching the Library's Picard sheaf `RelativePicard.classSheaf f`. It assumes
  `R → Z` only flat and proper. It concludes that `π` is flat, surjective,
  proper and locally of finite presentation, instead of smooth.
- **Base.** The base is the affine noetherian scheme `Spec A`. Kleiman's base in
  Theorem 4.8 is a noetherian scheme.
- **Quasi-projectivity.** "Quasi-projective" is `IsHQuasiProjective`, for `Z`
  and for `Q`. Over an affine base the two notions agree: Stacks Lemma 29.44.16
  in the retained snapshot `stacks-projective-space-twists-morphisms-2026-10-26`
  shows that quasi-projective implies H-quasi-projective, and Lemmas 29.44.11
  and 29.44.3 give the converse.
- **Representability of `R`.** "`R := Z ×_P Z` is representable by an
  `S`-scheme" is hypothesis 3, with the two projections named `s` and `t`.
- **Test category.** Kleiman's sheaves live on locally noetherian `S`-schemes
  (p.15). The Lean `G` is an fppf sheaf on all of `Over S`, and hypotheses 2
  and 3 and the isomorphism `e` concern all `S`-schemes. The argument below
  does not use the restriction. The quotient theorem of step 2 concerns only
  the schemes `Z`, `R` and `Q`. These are of finite type over the noetherian
  ring `A`, hence noetherian, and they lie in both categories. Exercise 4.10
  holds in any site. Mathlib shows that the fppf topology on schemes is
  subcanonical (`fppfTopology.Subcanonical`, in
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`), and so is its restriction to the
  slice `Over S`. Steps 3 and 4 therefore work on all of `Over S`.

Kleiman's proof gives the Lean statement after these changes, as follows. This
is an explanation of why the statement holds, not a Lean proof.

1. `R ⟶ Z ×_S Z` is a monomorphism, because by hypothesis 3 a point of `R` is
   determined by its two projections. The `T`-points of `R` form the graph of
   the equivalence relation "same image in `G`" on the `T`-points of `Z`.
   Kleiman next shows that `R ⟶ Z ×_S Z` is a closed embedding. The quotient
   statement used in step 2 does not need this.
2. `R ⟶ Z` is flat and proper and `Z` is H-quasi-projective over `S`. The
   flat proper equivalence relation is then effective: there are an
   H-quasi-projective `Q` and a flat, surjective, proper `π : Z ⟶ Q`, locally
   of finite presentation, with `R = Z ×_Q Z`. This is the statement
   `Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientStatement`
   of Task 5705 (lean.statement candidate
   `67461119-f54c-479d-a843-0b255d8fd982`). Its sources are Altman–Kleiman
   [AK80, Thm. (2.9)], as cited by Kleiman, and N. Nitsure, *Construction of
   Hilbert and Quot schemes* (`nitsure-2005-hilbert-quot-arxiv-math0504590v1`),
   Theorem 6.8, p.33. Kleiman applies this quotient theorem at this point.
3. `π` is flat, surjective and locally of finite presentation, so it is an fppf
   covering of `Q`. Hence the functor of points of `π` is a surjection of fppf
   sheaves. Kleiman needs the smoothness of `π` and EGA IV 17.16.3 (ii) at this
   point to obtain étale-local sections of `π`. In the fppf topology `π` itself
   is a covering, so neither is needed.
4. The fppf topology on `Over S` is subcanonical, so the functor of points of
   `Q` is an fppf sheaf. By Exercise 4.10, in the fppf topology, both `Q` and
   `G` are the coequaliser of `R ⇉ Z` in fppf sheaves: `Q` because of step 3 and
   `R = Z ×_Q Z`, and `G` because of hypotheses 2 and 3. Coequalisers are
   unique up to unique isomorphism. This gives `e` with
   `(schemeYoneda S).map π ≫ e.hom = ζ`.

Kleiman's proof of the smoothness of `α` (smoothness of `π` from the smoothness
of the fibres of `R → Z`) is replaced by the flatness, surjectivity and
properness of `π` from step 2.

## Use

In Kleiman's proof of Theorem 4.8 (pp.29–30), `Z` is an open subscheme of the
scheme of relative effective divisors and `α` is the Abel map onto a piece
`P^{φ₀}_0` of the Picard sheaf. Its fibre products with schemes are linear
systems, and Kleiman shows that the first projection of `Z ×_P Z` is smooth and
projective. Task 5705 applies the present statement to the fppf Picard sheaf
`RelativePicard.classSheaf f`, or to a subsheaf of it, in this step.
