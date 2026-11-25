# Archimedean standard-module components of cuspidal realizations

Lean module: `Langlands.Automorphic.CuspidalArchimedeanComponentStatement`.

This module states six propositions in the namespace `Langlands.Automorphic`.
They connect the standard-module parameters of an actual cuspidal realization
at an infinite place to the local hypotheses of the Archimedean case of
Getz–Hahn, Theorem 11.5.2. All six are `Prop`-valued `def`s. They are statement
targets, not proofs: the module contains no theorem and proves none of them. It
imports `Automorphic.AssociatedFactorStatement` (for
`HasUnitaryCentralCharacter`), `Automorphic.ArchimedeanPlaceParameter`,
`Representation.Archimedean.RealStandardModuleGKModule` and
`Representation.Archimedean.UnitaryGenericPairRegularityStatement`. It changes
no published file and introduces no new predicate, structure or factor.

## Why this module exists

The published `CuspidalPairPoleStatement` (module
`Global.Factors.CuspidalPairPoleStatement`) writes the Archimedean part of the
completed Rankin–Selberg `L`-function of two cuspidal realizations `T`, `T'` as
the product of the inverses of the denominators
`(realPairLFactor (dR v) (dR' v)).denominator s` and
`(complexPairLFactor (dC v) (dC' v)).denominator s`. Here `dR v`, `dR' v` (resp.
`dC v`, `dC' v`) are standard-module parameters of `T` and `T'` at the infinite
place `v`, in the sense of `OperatorRealization.HasRealPlaceParameter`
(resp. `HasComplexPlaceParameter`). The strong multiplicity one argument of
Getz–Hahn (Theorem 11.7.2, `CuspidalStrongMultiplicityOneStatement`) needs these denominators to be
nonzero at `s = 1`.

The published Archimedean case of Getz–Hahn, Theorem 11.5.2
(`Archimedean.RealUnitaryGenericPairRegularityStatement`,
`Archimedean.ComplexUnitaryGenericPairRegularityStatement`) gives this for
`(𝔤, K)`-modules that are irreducible, admissible, generic and unitarizable and
have the given standard parameter. The step between the two is the
global-to-local passage: if `ds` is a parameter of a cuspidal realization at `v`,
then the standard module of `ds` itself has these four properties. This module
states that passage and the resulting pair regularity.

## Sources

- Getz and Hahn, *An introduction to automorphic representations*, 2024
  (registered source `getz-hahn-2024-automorphic-representations`; PDF page =
  printed page + 11 in Chapter 11).
  - Theorem 11.3.6, printed page 298 (PDF page 309): every smooth vector `φ`
    of a cuspidal automorphic representation of `A_{GL_n} \ GL_n(𝔸_F)` has the
    Whittaker expansion `φ(g) = ∑_{γ ∈ N_{n-1}(F) \ GL_{n-1}(F)} W_φ^ψ((γ, 1) g)`.
    The text before it says that all such cuspidal representations are
    `ψ`-generic for every generic character `ψ`.
  - Printed pages 300–302 (PDF pages 311–313), displays (11.14)–(11.17): for a
    globally generic cuspidal representation `(π, V)`,
    `V^sm ≅ V_∞^sm ⊗ (⊗'_{v ∤ ∞} V_v)` by Flath's theorem (GH Theorem 5.7.1)
    and Theorem 6.6.3. In the number field case `V_∞ ≅ ⊗̂_{v | ∞} V_v` "for some
    irreducible unitary representations `(π_v, V_v)`" (by [Fol95, Theorem 7.25]
    and GH Theorem 3.10.2). GH then "fix isomorphisms `V_v^sm → W(π_v, ψ_v)`" for
    all `v`, that is, every local component is generic. Proposition 11.4.2
    (printed page 302) factors the global Whittaker function as a product of
    local ones.
  - Printed page 309 (PDF page 320), before Theorem 11.7.1: "Thus without loss
    of generality we can assume that `π` (resp. `π'`) is trivial on `A_{GL_n}`
    (resp. `A_{GL_m}`). In this case `L(s, π_v × π'_v)` converges absolutely for
    `Re(s) ≥ 1` for all `v` by Theorem 11.5.2." Theorem 11.7.2 (strong
    multiplicity one) is on the same page, and its proof is left as Exercise 11.6.
- Badulescu and Renard, *Unitary dual of GL(n) at archimedean places and global
  Jacquet–Langlands correspondence*, Compositio Math. 146 (2010) (registered
  source `badulescu-renard-2010-unitary-dual`; journal PDF page = printed
  page − 1113).
  - §2 (from the `arXiv` source `0905.4143.tex` in the same folder): in the
    Archimedean case the representations are Harish-Chandra modules with respect
    to `O(n)` for `GL(n, ℝ)` and `U(n)` for `GL(n, ℂ)`. `R` is the Grothendieck
    group of finite-length modules, and `π₁ × π₂` is normalized parabolic
    induction. `R` is the free `ℤ`-module on the irreducible classes. Remark 2.3,
    printed page 1123 (PDF page 10), warns that `π₁ × π₂ = π₂ × π₁` in `R`,
    although the two induced representations are not isomorphic in general.
  - Proposition 2.4, printed page 1124 (PDF page 11): "The ring `(R, ×)` is
    graded commutative."
  - Theorem 3.3(i), printed pages 1124–1125 (PDF pages 11–12): for
    `d = (d₁, …, d_l)` written in a standard order, `λ(d) = d₁ × ⋯ × d_l` "has a
    unique irreducible quotient `Lg(d)` appearing with multiplicity one in a
    Jordan–Hölder sequence of `λ(d)`." Theorem 3.3(iii): `d ↦ Lg(d)` is a
    bijection from multisets of essentially square-integrable representations
    onto `Irr`.
- Knapp and Vogan, *Cohomological induction and unitary representations*, 1995
  (registered source `knapp-vogan-1995-cohomological-induction`), display
  (0.5), printed page 6 (PDF page 28). This is the notion of infinitesimal
  unitarity encoded by the published `IsRealUnitarizableGKModule` and
  `IsComplexUnitarizableGKModule`. See the Markdown of
  `UnitaryGenericPairRegularityStatement`.
- Flath, *Decomposition of representations into tensor products*, 1979
  (registered source `flath-1979-tensor-products`), used through GH Theorem
  5.7.1 as above.

## Notation

`F : Type u` is a number field with `CompactSpace (AdeleQuotient F)`. This is the
standing hypothesis of the Library's cuspidality, as in every published
cuspidal statement. `T : CuspidalOperatorRealization F r` is an actual cuspidal
realization of `GL_{r+1}`: a subspace `T.realization` of the Library's stable
automorphic forms that is irreducible for the operator algebra generated by
`GL_{r+1}(𝔸_f)`, the standard compact subgroup at infinity and the enveloping
algebra, and that is cuspidal. `v` ranges over
`{v : NumberField.InfinitePlace F // v.IsReal}` or
`{v : NumberField.InfinitePlace F // v.IsComplex}`.

For `ds : List RealBlock` the published `(𝔤𝔩_n(ℝ), O(n))`-module of the real
standard module is
`(Archimedean.realStandardRep n ds, Archimedean.realStandardLie n ds)` (module
`RealStandardModuleGKModule`). Its carrier is the `O(n)`-finite part of
`realStandardModule n ds`. It acts by right translation and by right
derivatives, and it is a `(𝔤, K)`-module by the published
`isRealGKModule_realStandardModule`. For `ds : List ComplexCharacterData` the
complex analogue is
`(Archimedean.complexStandardRep n ds, Archimedean.complexStandardLie n ds)` on
the `U(n)`-finite part of `complexStandardModule n ds`, the principal series of
the characters of `ds` (module `PrincipalSeriesGKModule`; published
`isComplexGKModule_complexStandardModule`).

`T.realization.HasRealPlaceParameter v ds` (published, module
`ArchimedeanPlaceParameter`) says that `realRank ds = r + 1` and that there is an
injective `ℂ`-linear map `A` from `realStandardKFinite (r + 1) ds` (the same
carrier) into `T.realization.Space`. `A` carries right translation by
`k ∈ O(r+1)` to `realPlaceCompactRepresentation v k`, and the right derivative
along `X ∈ 𝔤𝔩_{r+1}(ℝ)` to `realPlaceLieAction v (1 ⊗ X)`.
`HasComplexPlaceParameter` is the complex analogue, with `ds.length = r + 1`.

## Declarations

### `ArchimedeanStandardAdmissibleStatement`

```lean
(∀ (n : ℕ) (ds : List RealBlock),
  Archimedean.IsAdmissibleGKModule (Archimedean.realStandardRep n ds)) ∧
∀ (n : ℕ) (ds : List ComplexCharacterData),
  Archimedean.IsAdmissibleGKModule (Archimedean.complexStandardRep n ds)
```

This holds for every real and every complex standard module. `IsAdmissibleGKModule`
(published, `GKModule`; GH Definition 4.4.4 and p. 116) says: for every `d` and
every continuous `τ : K →* Matrix (Fin d) (Fin d) ℂ`, the space of
`K`-intertwiners `ℂ^d → V` is finite-dimensional. The statement is local. It has
no rank hypothesis and involves no global object. It is placed here because the
reduction below needs it. The real half is also stated as
`Archimedean.RealStandardAdmissibleStatement` (module
`Langlands.Representation.Archimedean.RealStandardModuleAdmissible`).

### `CuspidalArchimedeanStandardIrreducibleStatement.{u}`

For every `F`, `r` and `T` as above:

- for every real place `v` and every `ds : List RealBlock`, if
  `T.realization.HasRealPlaceParameter v ds`, then
  `IsIrreducibleGKModule (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds)`;
- for every complex place `v` and every `ds : List ComplexCharacterData`, if
  `T.realization.HasComplexPlaceParameter v ds`, then
  `IsIrreducibleGKModule (complexStandardRep (r + 1) ds) (complexStandardLie (r + 1) ds)`.

`IsIrreducibleGKModule` (published, `GKModule`; GH p. 116) means that the carrier
is nontrivial and has no subspace other than `0` and the whole space that is
stable under both actions.

### `CuspidalArchimedeanStandardGenericStatement.{u}`

The same hypotheses, with conclusions
`IsRealGenericGKModule (r + 1) (realStandardLie (r + 1) ds)` and
`IsComplexGenericGKModule (r + 1) (complexStandardLie (r + 1) ds)`. These
published predicates (`GKModule`) assert a nonzero linear functional `ℓ` on the
carrier and coefficients `a_i ≠ 0` (`i + 1 < r + 1`) such that every strictly
upper triangular `X` acts on `ℓ` by the differential of the nondegenerate
character `u ↦ exp(i ∑ a_i u_{i,i+1})` (over `ℂ`: `exp(i Re ∑ a_i u_{i,i+1})`).

### `CuspidalArchimedeanStandardUnitarizableStatement.{u}`

For every `F`, `r` and `T` with
`Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T`
(published, `AssociatedFactorStatement`: `T` has a central character
`χ : C_F →ₜ* ℂˣ` with `‖χ x‖ = 1` for all `x`), the same parameter hypotheses
give
`IsRealUnitarizableGKModule (r + 1) (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds)`
and the complex analogue `IsComplexUnitarizableGKModule`. These published
predicates (`UnitaryGenericPairRegularityStatement`) assert a positive definite
Hermitian form invariant under `K` such that every real Lie direction `1 ⊗ X`
acts skew-adjointly. This is KV (0.5).

### `CuspidalArchimedeanPairRegularityStatement.{u}` (entry point)

For every `F : Type u`, every `r t : ℕ`, every
`T : CuspidalOperatorRealization F r` and `T' : CuspidalOperatorRealization F t`,
both with `HasUnitaryCentralCharacter`:

```lean
(∀ (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds ds' : List RealBlock),
  T.realization.HasRealPlaceParameter v ds →
  T'.realization.HasRealPlaceParameter v ds' →
    ∀ s : ℂ, 1 ≤ s.re → (realPairLFactor ds ds').denominator s ≠ 0) ∧
∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
  (ds ds' : List ComplexCharacterData),
  T.realization.HasComplexPlaceParameter v ds →
  T'.realization.HasComplexPlaceParameter v ds' →
    ∀ s : ℂ, 1 ≤ s.re → (complexPairLFactor ds ds').denominator s ≠ 0
```

`realPairLFactor` and `complexPairLFactor` (published, `ArchimedeanPairFactor`)
are values of `ReciprocalEntire`: `L(s) = 1 / P(s)` with `P = denominator` entire.
So `P(s) ≠ 0` says that the Archimedean pair factor `L(s, ds × ds')` has no pole
at `s`; it is then nonzero there. This is exactly the shape of the factors in
`CuspidalPairPoleStatement`.

### `CuspidalArchimedeanPairRegularityReductionStatement.{u}`

```lean
ArchimedeanStandardAdmissibleStatement →
  CuspidalArchimedeanStandardIrreducibleStatement.{u} →
    CuspidalArchimedeanStandardGenericStatement.{u} →
      CuspidalArchimedeanStandardUnitarizableStatement.{u} →
        Archimedean.RealUnitaryGenericPairRegularityStatement.{0, 0} →
          Archimedean.ComplexUnitaryGenericPairRegularityStatement.{0, 0} →
            CuspidalArchimedeanPairRegularityStatement.{u}
```

The local statements are used at universe `0`, because the carriers
`kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` are subtypes of
`GL_n(ℝ) → ℂ` and live in `Type`.

## Correspondence with the sources

- **Components.** GH's local component `π_v` of a cuspidal `π` at an infinite
  place is the factor `V_v` of (11.15). The Library has no tensor
  factorization of a realization. Instead, a standard-module parameter
  `HasRealPlaceParameter v ds` is an injective `(𝔤_v, K_v)`-map from the
  standard module of `ds` into the realization. The irreducibility statement
  says that such a standard module is irreducible. Its proof (below) shows that
  it is then isomorphic to the `(𝔤_v, K_v)`-module of `π_v`, so the generic and
  unitarizable statements are GH's assertions that `π_v` is generic (the fixed
  isomorphisms `V_v^sm → W(π_v, ψ_v)` on p. 301) and unitary (p. 301).
- **Unitarity hypothesis.** GH (p. 309) normalize `π`, `π'` to be trivial on
  `A_{GL_n}` and `A_{GL_m}`. Then `π`, `π'` are irreducible subrepresentations of
  `L²_cusp`, so their local components are unitary, which is the hypothesis of
  Theorem 11.5.2. This module assumes instead that the central characters are
  unitary (`HasUnitaryCentralCharacter`). That assumption suffices for the
  unitarity of the components, and it is the hypothesis of the published
  p-adic analogue `CuspidalUnitaryLocalUnitarityStatement`.
  `CuspidalPairPoleStatement` uses `IsTrivialOnSplitCentre`. The step from
  `IsTrivialOnSplitCentre` to `HasUnitaryCentralCharacter` is proved in the
  Library as `cuspidalSplitCentreUnitaryCentralCharacter` (module
  `Langlands.Global.Factors.CuspidalSplitCentreUnitaryProof`): an
  irreducible cuspidal realization has a central character, triviality on
  `A_{GL_n}` makes it trivial on the positive real ideles `A_{G_m}`, and such
  a character is unitary (`HeckeCharacter.isUnitary_of_positiveRealIdeles`).
- **Pair factor.** GH define `L(s, π_v × π'_v)` through the Archimedean local
  Langlands correspondence (GH p. 305). The Library's factor of the standard
  parameters `ds`, `ds'` is the `L`-function of the tensor product of their
  Weil-group representations. For irreducible standard modules this is GH's
  factor by the published `StandardModule` Markdown ("Scope of the parameter
  predicates", Knapp 1994). The identification is a Library convention and is
  not restated in Lean.
- **Order of the blocks.** `ds` is a list, and the standard module depends on its
  order. In general, modules induced from the same blocks in different orders
  are not isomorphic (BR Remark 2.3, printed p. 1123). They do have the same
  class in BR's Grothendieck group (Proposition 2.4, printed p. 1124), which is
  free on the irreducible classes. So they have the same composition factors
  with multiplicities. If one ordering is irreducible, every ordering is
  irreducible and isomorphic to it, as the published `StandardModule`
  Markdown also states (Derived choice 4). The hypotheses quantify over every
  order for which a parameter exists. A standard module is not irreducible for
  every parameter list. The statements claim irreducibility only for
  parameters that embed into a cuspidal realization, and the embedding `A` is
  what the intended argument (step 2 below) uses to prove it.
- GH's "converges absolutely for `Re(s) ≥ 1`" is read as "has no pole on
  `Re(s) ≥ 1`". Nothing is asserted for `Re(s) < 1`.

## Relation to Library modules

- `CuspidalArchimedeanPlaceComponent` (statements, proved by
  `cuspidalArchimedeanIrreducibleAdmissibleComponent` in `PlaceComponentExistence`
  and `cuspidalArchimedeanWhittakerFunctional` in `CuspidalWhittaker.PlaceWhittaker`).
  These give some irreducible admissible subspace at every infinite place, and a
  Whittaker functional on every nonzero stable subspace. They concern subspaces
  of the realization. They do not say that the standard module of a given
  parameter is irreducible or unitarizable, so they do not duplicate this
  module.
- `CuspidalArchimedeanGenericComponentReduction` and
  `ArchimedeanParameterReduction` derive the existence of a parameter
  (`CuspidalArchimedeanParameterExistenceStatement`) from local Langlands-quotient
  statements. This module takes the parameter as a hypothesis and does not assume
  its existence. If `T` has no parameter at `v`, the clauses at `v` hold vacuously.
- `CuspidalUnitaryLocalUnitarityStatement` and
  `CuspidalUnitaryLocalGenericityStatement` are the p-adic analogues of the
  unitarizable and generic statements.
- `OperatorRealization.IsUnitarizable` and
  `isUnitarizable_of_hasUnitaryCentralCharacter` (module `CuspidalUnitaryForm`,
  proved) give one positive definite form on the whole realization that is
  invariant under the standard compact subgroup at infinity and skew under real
  Lie directions.

## Why the statements are true

This is the intended argument; none of it is proved in this module.

1. **Admissibility.** Every function `f` of `realStandardModule n ds` lies in
   `principalSeries ℝ n χ`. So it satisfies
   `f(diag(a) u g) = χ'(a) f(g)` with `u` upper unipotent, and by the Iwasawa
   decomposition `GL_n(ℝ) = B · O(n)` it is determined by `f|_{O(n)}`. If `T` is
   an `O(n)`-intertwiner from `τ` into the carrier, then
   `(T x)(k) = (T (τ k x))(1)`. Hence `T ↦ (x ↦ (T x)(1))` is an injective linear
   map into the dual of `ℂ^d`, and the intertwiner space has dimension at most
   `d`. The complex case is the same with `U(n)`.
2. **Irreducibility.** The realization is an irreducible admissible
   `(𝔤_∞, K_∞) × GL(𝔸_f)`-module. By Flath's theorem (GH (11.14)–(11.15)), as a
   `(𝔤_v, K_v)`-module it is `π_v ⊗ U` for an irreducible `π_v` and a vector
   space `U`, so it is a direct sum of copies of `π_v`. The image of `A` is a
   `(𝔤_v, K_v)`-submodule, so the standard module `I(ds)` is isomorphic to
   `π_v^{⊕k}` for some `k ≥ 1`, and `k` is finite by admissibility. The
   Library's standard module of `ds` is BR's product of the blocks in the order
   of `ds` (`StandardModule` Markdown, Derived choices 4 and 7). In BR's
   Grothendieck group, `[I(ds)] = [λ(d)]` for `d` the blocks of `ds` in a
   standard order, by Proposition 2.4 (the same fact is Derived choice 4 of the
   `StandardModule` Markdown). By Theorem 3.3(i), `Lg(d)` occurs in `[λ(d)]` with
   multiplicity one. Since `[I(ds)] = k [π_v]`, this forces `π_v ≅ Lg(d)` and
   `k = 1`, so `I(ds)` is irreducible.
3. **Genericity.** The image `W` of `A` is a nonzero subspace stable under the
   place actions at `v`. The published theorem
   `cuspidalArchimedeanWhittakerFunctional` gives a functional `ℓ` on the
   realization, nonzero on `W`, that is a Whittaker functional on `W` for a
   nondegenerate character. Then `ℓ ∘ A` is a nonzero Whittaker functional on
   `I(ds)`, because `A` carries right derivatives to `realPlaceLieAction v (1 ⊗ X)`.
   This is the infinitesimal form of GH Theorem 11.3.6 and Proposition 11.4.2.
4. **Unitarizability.** Take the form `b` of
   `isUnitarizable_of_hasUnitaryCentralCharacter` (the Petersson form on a band in
   `|det|`). The place actions at `v` are restrictions of the actions of the
   standard compact subgroup at infinity and of the real Lie directions. So
   `(f, g) ↦ b(A f, A g)` is a Hermitian form on `I(ds)`, invariant under `K_v`
   and skew under `𝔤𝔩_{r+1}(F_v)`. It is positive definite because `A` is
   injective.
5. **Reduction.** Apply `RealUnitaryGenericPairRegularityStatement.{0, 0}` with
   `V = realStandardKFinite (r + 1) ds` and the module structures above. The
   carrier is a `(𝔤, K)`-module by `isRealGKModule_realStandardModule`, and the
   four other properties come from the four component statements.
   `HasRealStandardParameter (r + 1) _ _ ds` holds with `A = id` by
   `isRealStandardIntertwiner_id`, using `realRank ds = r + 1` from the place
   parameter. Do the same for `ds'` and `t + 1`. The complex case uses
   `isComplexGKModule_complexStandardModule` and
   `isComplexStandardIntertwining_id`.
6. **Entry point.** It follows from the reduction once the four component
   statements and the two published local statements are proved.

## Proofs of the statements

1. `ArchimedeanStandardAdmissibleStatement`: elementary (step 1). It needs the
   Iwasawa decomposition for `GL_n(ℝ)` and `GL_n(ℂ)`. Proved as
   `archimedeanStandardAdmissible` (module
   `Langlands.Automorphic.ArchimedeanStandardAdmissibleProof`).
2. `CuspidalArchimedeanStandardGenericStatement`: short, from the published
   `cuspidalArchimedeanWhittakerFunctional` (step 3). Proved as
   `cuspidalArchimedeanStandardGeneric` (module
   `Langlands.Automorphic.CuspidalArchimedeanStandardGenericProof`).
3. `CuspidalArchimedeanStandardUnitarizableStatement`: short to moderate, from
   `isUnitarizable_of_hasUnitaryCentralCharacter` and the relation between place
   actions and the global compact and Lie actions (step 4). Proved as
   `cuspidalArchimedeanStandardUnitarizable` (module
   `Langlands.Automorphic.CuspidalArchimedeanComponentUnitaryProof`).
4. `CuspidalArchimedeanStandardIrreducibleStatement`: deep (step 2). It needs the
   tensor factorization at `v` and BR's Langlands classification for
   Harish-Chandra modules. Proved as `cuspidalArchimedeanStandardIrreducible`
   (module `Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof`).
5. `CuspidalArchimedeanPairRegularityReductionStatement`: immediate (step 5).
   Proved as `cuspidalArchimedeanPairRegularityReduction` (module
   `Langlands.Automorphic.CuspidalArchimedeanPairRegularityReductionProof`).

## What is not asserted

- No statement about the existence of parameters, or about isomorphism classes
  of components beyond the four properties.
- No statement at finite places. Those are covered by the published
  `CuspidalUnitaryLocal…` statements and the spectral presentations.
- No statement about `Re(s) < 1`, and no identification of the pair factor with
  GH's factor in Lean.

## Provenance

The propositions are derived. They are the global-to-local step of GH §11.4
(pp. 300–302) and the Archimedean regularity used on GH p. 309, phrased for the
Library's place parameters and published `(𝔤, K)`-module predicates. The
admissibility statement is a standard property of induced representations. It
is stated here for the Library's carriers; it is not quoted from a source. The
choice of unitary central character instead of triviality on `A_{GL_n}` is an
internal design decision that matches the published p-adic analogue.

## Lean checks

The module compiles with `lean_check` with no errors or
warnings. Inspection of the entry point
`CuspidalArchimedeanPairRegularityStatement` reports a definition returning
`Prop` with universe parameter `u`, using only `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorry` and no new axiom.
