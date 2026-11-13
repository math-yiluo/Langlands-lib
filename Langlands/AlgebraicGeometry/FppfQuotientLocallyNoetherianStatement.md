# Representability of an fppf sheaf on locally noetherian tests through a flat proper equivalence relation

Author: Worker 22, for task `07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705).
Worker 5705 designed the Lean interface for the Picard construction of that
task. The hypotheses match what Worker 5705's assembly can supply.

## Statement

`Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianStatement.{u}` is a
proposition. Nothing here asserts a proof of it. It uses the conventions of
`Langlands.AlgebraicGeometry.AlgebraicSpace.Basic`:

- `FppfSheaf S = Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))`, the
  type-valued sheaves for the fppf topology on the slice `Over S`;
- `fppfTopology S = Scheme.fppfTopology.over S`;
- `schemeYoneda S = uliftYoneda.{u + 1}`, the functor of points of an object of
  `Over S` with values lifted to `Type (u + 1)`. Its value on `T` is
  `ULift (T ⟶ Z)`, and `ULift.up x` is the element given by `x : T ⟶ Z`.

The Library's Picard sheaf `RelativePicard.classSheaf f` has the type
`FppfSheaf S`.

The statement quantifies over

- a noetherian commutative ring `A : Type u`, with `S = Spec (CommRingCat.of A)`;
- an fppf sheaf `G : FppfSheaf S`;
- objects `Z` and `R` of `Over S`;
- a morphism of presheaves `ζ : (schemeYoneda S).obj Z ⟶ G.obj`, that is, a map
  from the functor of points of `Z` to `G`;
- two morphisms `s t : R ⟶ Z` in `Over S`.

Its hypotheses are:

1. `IsHQuasiProjective Z.hom`: the structure morphism of `Z` is a quasi-compact
   immersion into some `ProjectiveSpace A n` over `S` (see
   `Langlands.AlgebraicGeometry.HQuasiProjective`).
2. `Presheaf.IsLocallySurjective (fppfTopology S) ζ` (Mathlib): for every object
   `T` of `Over S` and every `g ∈ G(T)`, the morphisms `T' ⟶ T` along which `g`
   lifts to a `T'`-point of `Z` form an fppf-covering sieve. This concerns all
   objects `T` of `Over S`.
3. `(schemeYoneda S).map s ≫ ζ = (schemeYoneda S).map t ≫ ζ`: for every `T` and
   every `r : T ⟶ R`, the points `r ≫ s` and `r ≫ t` of `Z` have the same image
   in `G`.
4. For every object `T` of `Over S` such that the scheme `T.left` is locally
   noetherian, and for all `x y : T ⟶ Z` with
   `ζ.app (op T) (ULift.up x) = ζ.app (op T) (ULift.up y)`, there is a unique
   `r : T ⟶ R` with `r ≫ s = x` and `r ≫ t = y`. Thus `R`, with `s` and `t`,
   represents `Z ×_G Z` on locally noetherian `S`-schemes. Nothing is assumed
   about other test schemes.
5. `Flat s.left` and `IsProper s.left`: the first projection `R ⟶ Z` is a flat
   and proper morphism of schemes.

The conclusion is that there are an object `Q` of `Over S`, a morphism
`π : Z ⟶ Q` in `Over S` and a morphism of presheaves
`e : (schemeYoneda S).obj Q ⟶ G.obj` such that

- `IsHQuasiProjective Q.hom`;
- `(schemeYoneda S).map π ≫ e = ζ`: `ζ` factors as the functor of points of
  `π` followed by `e`;
- for every object `T` of `Over S` with `T.left` locally noetherian, the map
  `e.app (op T)` from the `T`-points of `Q` to `G(T)` is bijective;
- `π.left` is flat, surjective, proper and locally of finite presentation.

So `Q` represents `G` on locally noetherian `S`-schemes, through `e`. The
statement does not claim that `e` is bijective on other `S`-schemes.

## Source

The statement is an fppf and flat form of Lemma 4.9 of S. L. Kleiman, *The
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
locally noetherian `S`-schemes, and "representable" means representable on
that category. Hypothesis 4 and the bijectivity of `e` follow this convention.

The companion statement
`Langlands.AlgebraicGeometry.FppfQuotientRepresentabilityStatement` (published)
assumes instead that `R` represents `Z ×_G Z` on all of `Over S`. The present
form is the one Worker 5705 needs: in the Picard construction, `R` comes from
linear systems, which, as in Kleiman, are known to represent `Z ×_G Z` only on
locally noetherian tests.

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
- **Test category.** `G` is an fppf sheaf on all of `Over S`, and hypothesis 2
  is about all objects of `Over S`. Hypothesis 4, which says that `R`
  represents `Z ×_G Z`, and the conclusion that `e` is bijective are restricted
  to locally noetherian `S`-schemes, as in Kleiman's convention. Hypothesis 3
  makes explicit the part of `R = Z ×_G Z` that is used on all tests. The map
  `e` itself is defined on all tests.

Kleiman's proof gives the Lean statement after these changes, as follows. This
is an explanation of why the statement holds, not a Lean proof. Below,
"locally noetherian `T`" means an object `T` of `Over S` with `T.left` locally
noetherian, and fibre products are taken in `Over S`, where they are fibre
products of schemes.

1. **The schemes involved are noetherian.** `Z` is H-quasi-projective over the
   noetherian ring `A`, so it is of finite type over `A`, hence noetherian.
   `s` is proper, hence of finite type, so `R` is of finite type over `A` and
   noetherian. The fibre products `R ×_{t,Z,s} R` and
   `R ×_{Z ×_S Z} R` are of finite type over `R`, hence noetherian. (A morphism
   from a noetherian scheme is quasi-compact, so `R → Z ×_S Z` is of finite
   type.) In particular `Z`, `R` and these two fibre products are locally
   noetherian tests.
2. **`R` is a flat proper equivalence relation on `Z`.** Each part tests
   hypothesis 4 on one of the noetherian schemes of step 1. Hypothesis 3 gives
   the required equality of images in `G` each time.
   - *Monomorphism.* On `T = R ×_{Z ×_S Z} R`, with projections `p₁, p₂`, the
     points `x = p₁ ≫ s = p₂ ≫ s` and `y = p₁ ≫ t = p₂ ≫ t` have the same image
     in `G`. Both `p₁` and `p₂` satisfy `r ≫ s = x` and `r ≫ t = y`, so the
     uniqueness in hypothesis 4 gives `p₁ = p₂`. Hence
     `(s, t) : R ⟶ Z ×_S Z` is a monomorphism of schemes. This is the
     hypothesis `Mono (pullback.lift s t h)` of the quotient statement in step 3.
   - *Reflexivity.* On `T = Z` with `x = y = 𝟙 Z`, there is `δ : Z ⟶ R` with
     `δ ≫ s = δ ≫ t = 𝟙 Z`. Every point `x` of `Z` is related to itself
     through `x ≫ δ`.
   - *Symmetry.* On `T = R` with `x = t` and `y = s`, there is `σ : R ⟶ R` with
     `σ ≫ s = t` and `σ ≫ t = s`. If `φ` relates `x` to `y`, then `φ ≫ σ`
     relates `y` to `x`.
   - *Transitivity.* On `T = R ×_{t,Z,s} R`, with projections `q₁, q₂`, the
     points `q₁ ≫ s` and `q₂ ≫ t` have the same image in `G`. So there is
     `μ : T ⟶ R` with `μ ≫ s = q₁ ≫ s` and `μ ≫ t = q₂ ≫ t`. If `φ₁` relates
     `x` to `y` and `φ₂` relates `y` to `w`, then `(φ₁, φ₂)` followed by `μ`
     relates `x` to `w`.

   These arguments hold for points with values in an arbitrary scheme, since
   they only compose with the morphisms `δ`, `σ` and `μ`. So the hypothesis of
   the quotient statement that the relation is an equivalence relation on
   `T`-points for every scheme `T` holds.
3. **The quotient.** Hypothesis 1, step 2 and hypothesis 5 are the hypotheses
   of `Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientStatement`
   (published, Task 5705), applied to `Z.hom`, `s.left` and `t.left`. It gives
   an H-quasi-projective `Q` over `S` and a flat, surjective, proper
   `π : Z ⟶ Q` over `S`, locally of finite presentation, such that `R`, with
   `s` and `t`, is the fibre product `Z ×_Q Z`. Its sources are Altman–Kleiman
   [AK80, Thm. (2.9)], as cited by Kleiman, and N. Nitsure, *Construction of
   Hilbert and Quot schemes* (`nitsure-2005-hilbert-quot-arxiv-math0504590v1`),
   Theorem 6.8, p.33. Kleiman applies this quotient theorem at this point.
4. **The map `e` on all tests.** Let `a : T ⟶ Q`. The base change
   `p : T' = T ×_Q Z ⟶ T` of `π` is flat, surjective and locally of finite
   presentation. So `{p}` is a covering for Mathlib's fppf topology, whose
   covering families are jointly surjective families of flat morphisms locally
   of finite presentation (`Scheme.fppfPrecoverage`). Let `a' : T' ⟶ Z` be the
   second projection. Then `T' ×_T T' = T ×_Q (Z ×_Q Z) = T ×_Q R`, so the two
   pullbacks of `ζ(a')` to `T' ×_T T'` are `ζ(r ≫ s)` and `ζ(r ≫ t)` for a
   morphism `r` to `R`. They agree by hypothesis 3. Since `G` is a sheaf, they
   glue to a unique `e(a) ∈ G(T)` with `p^* e(a) = ζ(a')`. Uniqueness makes `e`
   natural in `T`. If `a = x ≫ π` for some `x : T ⟶ Z`, then `p` has the
   section `(𝟙 T, x)`, which gives `e(x ≫ π) = ζ(x)`. Hence
   `(schemeYoneda S).map π ≫ e = ζ`. This is the coequaliser property of
   Exercise 4.10 for `Q`: in the
   fppf topology, `π` itself is a covering. Kleiman needs the smoothness of `π`
   and EGA IV 17.16.3 (ii) at this point to get étale-local sections of `π`.
   That is not needed here.
5. **Bijectivity on locally noetherian tests.** Let `T` be locally noetherian.
   A scheme locally of finite type over `T` is again locally noetherian, so
   every member of an fppf covering family of `T` is a locally noetherian test.
   The functor of points of `Q` is an fppf sheaf, because Mathlib proves that
   the fppf topology is subcanonical (`fppfTopology.Subcanonical` in
   `Mathlib.AlgebraicGeometry.Sites.Fpqc`), and so is its restriction to the
   slice `Over S`.
   - *Injectivity.* Let `a, b : T ⟶ Q` with `e(a) = e(b)`. Let
     `T'' = (T ×_{a,Q} Z) ×_T (T ×_{b,Q} Z)`, with `p'' : T'' ⟶ T` and the two
     maps `x, x' : T'' ⟶ Z`. Then `p''` is flat, surjective and locally of
     finite presentation, and `T''` is locally noetherian. By step 4 and
     naturality, `ζ(x) = e(p'' ≫ a) = e(p'' ≫ b) = ζ(x')`. Hypothesis 4 gives
     `r : T'' ⟶ R` with `r ≫ s = x` and `r ≫ t = x'`. Since `s ≫ π = t ≫ π`,
     we get `p'' ≫ a = x ≫ π = x' ≫ π = p'' ≫ b`. As `{p''}` is an fppf
     covering and the functor of points of `Q` is a sheaf, `a = b`.
   - *Surjectivity.* Let `g ∈ G(T)`. By hypothesis 2 the sieve of morphisms
     along which `g` lifts to `Z` is an fppf-covering sieve, so it contains an
     fppf covering family `{fᵢ : Tᵢ ⟶ T}`, with `xᵢ : Tᵢ ⟶ Z` and
     `ζ(xᵢ) = fᵢ^* g`. On `Tᵢ ×_T Tⱼ`, which is locally noetherian, the two
     pullbacks of `xᵢ` and `xⱼ` have the same image in `G`. Hypothesis 4 and
     `s ≫ π = t ≫ π` then show that the morphisms `xᵢ ≫ π` agree on
     `Tᵢ ×_T Tⱼ`. They glue to `a : T ⟶ Q`. Then `fᵢ^* e(a) = ζ(xᵢ) = fᵢ^* g`
     for all `i`, and `G` is a sheaf, so `e(a) = g`.
6. **Why the conclusion is restricted.** Both parts of step 5 apply
   hypothesis 4 to schemes that are locally of finite type over `T`, so they
   need `T` locally noetherian. Hypothesis 4 says nothing about other tests,
   and `G` is not assumed to be locally of finite presentation. So the
   statement asserts bijectivity of `e` only on locally noetherian tests.

Kleiman's proof of the smoothness of `α` (smoothness of `π` from the smoothness
of the fibres of `R → Z`) is replaced by the flatness, surjectivity and
properness of `π` from step 3.

## Use

In Kleiman's proof of Theorem 4.8 (pp.29–30), `Z` is an open subscheme of the
scheme of relative effective divisors and `α` is the Abel map onto a piece
`P^{φ₀}_0` of the Picard sheaf. Its fibre products with schemes are linear
systems, and Kleiman shows that the first projection of `Z ×_P Z` is smooth and
projective. In Task 5705, Worker 5705 plans to apply the present statement with `G`
the image subsheaf of the Abel map in `RelativePicard.classSheaf f`, for which
hypothesis 2 holds by construction.
