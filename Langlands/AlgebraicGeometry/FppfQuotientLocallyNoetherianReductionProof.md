# Proof: reduction of the fppf quotient on locally noetherian tests to effective quotients

Authors: Worker 22.

Worker 22 wrote this module for task `07219dde-fd87-48cf-83be-db16cbb3707c`
(Task 5705), by agreement with that task's first executor, Worker 5705. It
proves the published proposition
`Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReductionStatement`
(module of the same name, by Worker 22). The operator's answer to request
`98389b48910e54088e0e2b2ba6aaad9c` allows such prerequisite proofs to stay
under Task 5705. Task 6193 (`3b764af9-5a6e-4596-86a0-8a3e0529d073`) asks for a
proof of `FppfQuotientLocallyNoetherianStatement`. Its context proposes proving
exactly this implication from the quotient theorem as a first step.

The main theorem is

```lean
theorem Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReduction.fppfQuotientLocallyNoetherianReduction :
    FppfQuotientLocallyNoetherianReductionStatement.{u}
```

Its type is the target proposition exactly, for an arbitrary universe `u`. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

The statement is the implication (c) ⟹ (c''):

- (c) `FlatProperEquivalenceRelationQuotientStatement`: for a noetherian ring
  `A`, an H-quasi-projective `p : Z ⟶ Spec A` and `s t : R ⟶ Z` with
  `s ≫ p = t ≫ p`, such that `pullback.lift s t _ : R ⟶ Z ×_A Z` is a
  monomorphism, the relation defined by `R` on `T`-points is an equivalence
  relation for every scheme `T`, and `s` is flat and proper, there are an
  H-quasi-projective `q : Q ⟶ Spec A` and a flat, surjective, proper,
  locally finitely presented `π : Z ⟶ Q` with `π ≫ q = p` and
  `IsPullback s t π π`.
- (c'') `FppfQuotientLocallyNoetherianStatement`: let `G` be an fppf sheaf on
  `Over (Spec A)`, `Z` H-quasi-projective, `ζ : Z → G` fppf-locally surjective,
  and `s t : R ⟶ Z` over `Spec A` with `ζ ∘ s = ζ ∘ t` (hypothesis `hst`).
  Assume that on every test `T` with `T.left` locally noetherian two `T`-points
  `x, y` of `Z` with the same image in `G` are `r ≫ s` and `r ≫ t` for a unique
  `r : T ⟶ R` (hypothesis `huniq`), and that `s.left` is flat and proper. Then
  there are an H-quasi-projective `Q`, a flat, surjective, proper, locally
  finitely presented `π : Z ⟶ Q` and `e : Q → G` with `e ∘ π = ζ` that is
  bijective on every locally noetherian test.

## Source

The argument follows S. L. Kleiman, *The Picard scheme*
(`kleiman-2005-picard-scheme-arxiv-math0504020v1`), Lemma 4.9 (p.30) and its
proof (pp.30–31) with Exercise 4.10 (p.31). There the quotient theorem of
Altman–Kleiman is applied to `R = Z ×_P Z`, and the sheaf `P` is then
identified with the quotient. Kleiman works with the étale topology and a
smooth proper relation. Here the topology is fppf and the relation is flat
and proper; the tests are locally noetherian as in Kleiman's conventions
(p.15). The proof below is the implemented Lean proof; it follows steps 1, 2,
4 and 5 of the section "Derivation of the Lean statement" in the Markdown of
`FppfQuotientLocallyNoetherianStatement`, with step 3 being the hypothesis (c).

## Helper lemmas (section `General`)

All declarations are in the namespace
`Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReduction`. The
section works over an arbitrary scheme `S`, with `G : FppfSheaf S`,
`Z R : Over S`, `ζ : (schemeYoneda S).obj Z ⟶ G.obj` and `s t : R ⟶ Z`.

- `app_comp`: naturality of `ζ` on points, `ζ (f ≫ x) = G(f) (ζ x)`.
- `app_s_eq_app_t`: from `hst`, `ζ (r ≫ s) = ζ (r ≫ t)` for every point
  `r : T ⟶ R`.
- `fac_app`: from `e ∘ π = ζ`, `e (x ≫ π) = ζ x` for every point `x : T ⟶ Z`.
- `QuasiAffineApproximation.exists_fac_of_kernelPair`: if `q : U' ⟶ M` is flat, locally of finite presentation and
  surjective with kernel pair `IsPullback t' s' q q`, and `c : U' → F` takes
  the same value on `t'` and `s'` (`F` an fppf sheaf), then `c` factors
  through `q`. This shared Library lemma is imported from
  `Langlands.AlgebraicGeometry.FppfKernelPairDescent`: the image of `q` in fppf
  sheaves is locally surjective (Library lemma
  `isLocallySurjective_schemeYoneda_map`), hence a regular, so effective,
  epimorphism, and `c` is compatible with it because every pair of points with
  the same image under `q` lifts to `R'`.

The remaining lemmas assume `hst` and `huniq` (stated for `Over S`).

- `eq_of_comp_eq`: on a locally noetherian test, two points `a, b : T ⟶ R`
  with `a ≫ s = b ≫ s` and `a ≫ t = b ≫ t` are equal. This is the uniqueness
  part of `huniq` for `x = a ≫ s`, `y = a ≫ t`.
- `mono_of_fst_snd`: if `R.left` is locally noetherian and `s.left` is locally
  of finite type, every `l : R.left ⟶ Z ×_S Z` with projections `s.left` and
  `t.left` is a monomorphism. Since `l ≫ fst = s.left` is locally of finite
  type, so is `l`, and the kernel pair `K = R ×_{Z ×_S Z} R` is locally of
  finite type over `R`, hence locally noetherian. Its two projections to `R`
  agree after `s` and after `t`, so they are equal by `eq_of_comp_eq` applied
  to `K` as an object of `Over S`. A morphism whose kernel-pair projections
  agree is a monomorphism.
- `equivalence`: if `Z.left` and `R.left` are locally noetherian and
  `s.left` is locally of finite type, then for every scheme `T` the relation
  "`x = φ ≫ s.left` and `y = φ ≫ t.left` for some `φ : T ⟶ R.left`" on
  `T ⟶ Z.left` is an equivalence relation. The existence part of `huniq` is
  used three times:
  - on `Z` with `x = y = 𝟙`, giving a diagonal `δ : Z ⟶ R` (reflexivity);
  - on `R` with `x = t`, `y = s`, giving `σ : R ⟶ R` that swaps the
    projections (symmetry);
  - on `P = R ×_{t, Z, s} R` (locally of finite type over `R`, hence locally
    noetherian) with `x = p₁ ≫ s`, `y = p₂ ≫ t`, giving `μ : P ⟶ R`
    (transitivity).

  A point of `T` is then composed with `δ`, `σ` or `μ`. The test `T` is
  arbitrary, since only these three universal points are needed.
- `eq_of_cover`: let `e ∘ π = ζ` and `s ≫ π = t ≫ π`, and let `x, y : T ⟶ Q`
  have the same image under `e`. If there are a locally noetherian scheme
  `W`, an epimorphism `d : W ⟶ T.left` and `a, b : W ⟶ Z.left` with
  `a ≫ π = d ≫ x` and `b ≫ π = d ≫ y`, then `x = y`. Indeed `a` and `b` have
  the same image in `G`, so `huniq` on `W` gives `r` with `r ≫ s = a`,
  `r ≫ t = b`; then `d ≫ x = r ≫ s ≫ π = r ≫ t ≫ π = d ≫ y`, and `d` is an
  epimorphism.
- `injective_app`: if moreover `π` is flat, surjective and locally of finite
  presentation, `e` is injective at every locally noetherian test `T`. Apply
  `eq_of_cover` with `W = (T ×_{x, Q} Z) ×_{Q} Z`, where the second fibre
  product is along `T ×_{x, Q} Z ⟶ T ⟶ Q` (via `y`) and `π`. The map
  `W ⟶ T` is a composite of base changes of `π`, so it is flat, surjective
  and locally of finite type. It is therefore an epimorphism of schemes
  (Mathlib `Flat.epi_of_flat_of_surjective`, Stacks 02VW), and `W` is locally
  noetherian. The two points of `Z` are the projections of `W` to `Z`
  (one through `T ×_{x, Q} Z`, one directly).
- `surjective_app`: if moreover `ζ` is fppf-locally surjective, `e` is
  surjective at every locally noetherian test `T`. Let `g ∈ G(T)`. Let `Pr` be
  the presieve of arrows `f : V ⟶ T` in the image sieve of `g` under `ζ` with
  `f.left` locally of finite type. It generates a covering sieve: the image
  sieve contains an fppf covering family, whose members are flat and locally
  of finite presentation and so lie in `Pr` (written out with
  `Scheme.mem_grothendieckTopology_iff` and `Sieve.overEquiv_iff`; the
  multiplicativity of `Flat ⊓ LocallyOfFinitePresentation` is built by hand).
  For every `f ∈ Pr` choose a lift `ℓ f : V ⟶ Z` with `ζ (ℓ f) = G(f) g`. The
  family `ℓ f ≫ π` of points of `Q` is compatible: for `f₁, f₂ ∈ Pr`, the
  fibre product `V₁ ×_T V₂` is locally of finite type over `T`, hence
  locally noetherian, and the two pulled-back lifts have the same image in
  `G`, so `huniq` gives `r` with `r ≫ s` and `r ≫ t` equal to them; then
  `hπ : s ≫ π = t ≫ π` makes the two points of `Q` equal. The functor of
  points of `Q` is an fppf sheaf (`schemeSheaf`), so the family glues to
  `x : T ⟶ Q`. On each `f ∈ Pr`, `e (f ≫ x) = e (ℓ f ≫ π) = ζ (ℓ f) = G(f) g`.
  Since `G` is separated for `Pr`, `e x = g`.

## Main theorem (section `Main`)

`fppfQuotientLocallyNoetherianReduction` takes (c) as `hc` and the data and
hypotheses of (c'').

1. `Z.hom` is locally of finite type: it is a composite of an immersion into
   projective space over `A` and the structure map (the H-quasi-projective
   data `hZ`). Hence `Z.left` is locally noetherian (`A` is noetherian), and
   `R.left` is locally noetherian because `s.left` is proper, hence locally
   of finite type.
2. `mono_of_fst_snd` and `equivalence` give the monomorphism and equivalence
   relation hypotheses of (c) for `p = Z.hom`, `s.left`, `t.left`. Applying
   `hc` gives `q : Q₀ ⟶ Spec A`, `π₀ : Z.left ⟶ Q₀` with `π₀ ≫ q = Z.hom`,
   all the properties of `π₀`, and `IsPullback s.left t.left π₀ π₀`.
3. Put `Q = Over.mk q` and `π = Over.homMk π₀`. The pullback square lifts to
   `Over (Spec A)` (`IsPullback.of_map_of_faithful` for the forgetful
   functor), so `R` with `s, t` is the kernel pair of `π` there.
4. `QuasiAffineApproximation.exists_fac_of_kernelPair` applied to `π` and `ζ` (with `hst`) gives `e` with
   `e ∘ π = ζ`.
5. `injective_app` and `surjective_app` give bijectivity of `e` on every
   locally noetherian test. The remaining conclusions are those of step 2.

## Dependencies

The module imports the statement module
`Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReductionStatement`,
`Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability` (for
`isLocallySurjective_schemeYoneda_map`) and
`Langlands.AlgebraicGeometry.ProjectiveSpace.Structure` (for the finite type
instances on projective space). It adds no axioms and no new definitions
other than the lemmas listed above.
