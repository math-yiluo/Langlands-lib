# Proof: the canonical class quotient on the supplied split Steinberg product

Author: Worker 5055.

The theorem `Langlands.GroupScheme.splitSteinbergQuotient` has exactly the
published proposition `Langlands.GroupScheme.SplitSteinbergQuotientStatement.{u}`
as its type. That proposition is defined in
`Langlands.GroupScheme.Rational.SplitSteinbergQuotientStatement`. The theorem
keeps the single universe parameter `u` and adds no hypothesis. Lean inspection
reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

Let `k : Type u` be an arbitrary field: finite or infinite, of any
characteristic, perfect or imperfect. Let `G` be an actual group scheme over
`Spec k` with affine structure morphism, `p : SplitPinning G` a supplied split
pinning, and assume `IsSimplyConnected G`, the Library's central-isogeny
definition. Take any `r : ℕ`, any ordering `e : Fin r ≃ p.base.support`, any
supplied normalized simple-root family
`x : p.NormalizedSimpleRootParametrizations` and any supplied simple-reflection
family `n : p.SimpleReflectionRepresentatives`. The theorem proves

```lean
IsIso (SplitPinning.steinbergProduct e x n ≫ ClassFunctions.rho G)
```

in `Over (Spec (CommRingCat.of k))`. The quotient is the canonical equalizer
quotient `ClassFunctions.quotient G`, and the map is the actual
`ClassFunctions.rho G`. No choice of ordering, root maps or representatives is
restricted, and no comparison with fundamental characters is assumed.

## Implemented proof

The Lean proof is a single term. It applies two published conditional
assemblies and supplies every one of their inputs with a published
unconditional theorem.

### Step 1: reduction to an algebraic closure

`splitSteinbergQuotient_of_algClosed`, from
`Langlands.GroupScheme.Rational.SteinbergGeometricReduction`, has type

```lean
IsSimplyConnectedAlgebraicClosureAscentStatement.{u} →
  SplitSteinbergQuotientAlgClosedStatement.{u} →
    SplitSteinbergQuotientStatement.{u}
```

`SplitSteinbergQuotientAlgClosedStatement.{u}` is the target restricted to
algebraically closed fields, with the same data and conclusion. The published
proof sets `K = AlgebraicClosure k`, takes the actual pullback group `GK`, and
transports the pinning (`p.baseChange`), the ordering
(`fieldBaseChangeOrder e`), the root maps (`fieldBaseChangeRootMaps x`) and the
representatives (`fieldBaseChangeRepresentatives n`). The algebraically closed
statement applies to these transported data. Then
`SplitPinning.isIso_steinbergQuotient_baseChange_iff`, from
`Langlands.GroupScheme.Rational.SteinbergFieldBaseChange`, turns the
conclusion back into the conclusion for the original product and the original
canonical quotient over `k`. That theorem rests on the published comparison of
the class-function quotient with its base change and on fpqc descent of
isomorphisms along `Spec K → Spec k`, which needs no perfectness of `k`.

The ascent input is supplied by

```lean
fun k _ G hG => isSimplyConnectedFieldExtension k (AlgebraicClosure k) G hG
```

Here `isSimplyConnectedFieldExtension`, from
`Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof`,
proves `IsSimplyConnectedFieldExtensionStatement.{u}`: simple connectedness is
preserved by base change along `Spec.map (CommRingCat.ofHom (algebraMap k K))`
for every field extension `K/k`. The ascent statement uses
`toAlgebraicClosure k`, which is an `abbrev` for exactly
`Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))`, so the
specialization `K = AlgebraicClosure k` has the required type by definitional
unfolding.

### Step 2: the algebraically closed case

The second input is

```lean
fun k _ _ G _ p hG r e x n =>
  splitSteinbergQuotient_algClosed_of_character_inputs hExists
    splitFundamentalCharacterGeneration splitSteinbergCharacterTriangular
    k G p hG r e x n
```

`splitSteinbergQuotient_algClosed_of_character_inputs`, from
`Langlands.GroupScheme.Rational.SteinbergCharacterTriangularity`, takes three
propositions as explicit inputs and proves the quotient isomorphism over an
algebraically closed field. Its published proof chooses one actual fundamental
representation `F a` for each simple root, using the existence input. It then
applies `steinbergProduct_rho_isIso_of_fundamental_triangular`. That lemma
shows that the restriction of the invariant algebra to the polynomial
coordinates of the product (`SplitPinning.steinbergRestriction`), composed with
the fundamental-character polynomial map, equals the triangular substitution
`X j ↦ c j • X j + f j`. Here each `c j` is a unit and each `f j` involves only
lower variables for a well-founded relation. The proved
`TriangularPolynomial.substitution_bijective` makes this composite bijective.
Since the fundamental-character map is bijective,
`steinbergProduct_rho_isIso_of_polynomial_generators` (module
`Langlands.GroupScheme.Rational.SteinbergRestriction`) shows that the
restriction is bijective. The published criterion
`steinbergProduct_rho_isIso_iff` then gives the isomorphism: by the spectrum
identity `steinbergRestriction_spec` and full faithfulness of the relative
spectrum, the composite is an isomorphism exactly when the restriction is
bijective.

The three inputs are supplied as follows.

1. **Fundamental representations exist**
   (`SplitFundamentalRepresentationsExistStatement.{u}`, module
   `Langlands.GroupScheme.Rational.FundamentalRepresentations`). The proof
   supplies the term

   ```lean
   splitFundamentalRepresentationsExist_of_corootSpan_of_highestWeight
     splitSimplyConnectedCorootSpan splitDominantHighestWeightRepresentationsExist
   ```

   - `splitFundamentalRepresentationsExist_of_corootSpan_of_highestWeight`,
     from `Langlands.GroupScheme.Rational.FundamentalRepresentationsAssembly`,
     is the published assembly. It uses integral coroot generation to form the
     integral dual basis of fundamental weights. These weights are dominant.
     It packages a highest-weight representation at each of them as a
     `p.FundamentalRepresentation a`.
   - `splitSimplyConnectedCorootSpan`, from
     `Langlands.GroupScheme.SimplyConnected.SplitNecessity`, proves
     `SplitSimplyConnectedCorootSpanStatement.{u}`. For an algebraically simply
     connected group with a split maximal torus and a finite reduced root datum
     of it, the coroots span the full cocharacter lattice over `ℤ` (Milne,
     Proposition 23.59, split case).
   - `splitDominantHighestWeightRepresentationsExist`, from
     `Langlands.GroupScheme.Rational.DominantHighestWeightProof`, proves
     `SplitDominantHighestWeightRepresentationsExistStatement.{u}`. Over an
     algebraically closed field, every dominant character of a split pinning is
     the highest weight of an actual irreducible finite matrix representation
     with the full `IsHighestWeight` package.

   The closing module states no separate theorem for this proposition. It only
   uses the term above as an argument.
2. **Free generation of the invariant algebra**
   (`SplitFundamentalCharacterGenerationStatement.{u}`, module
   `Langlands.GroupScheme.Rational.FundamentalCharacters`) is the published
   theorem `splitFundamentalCharacterGeneration`, from
   `Langlands.GroupScheme.Rational.FundamentalCharacterGenerationProof`.
   Over an algebraically closed field, for a simply connected split group,
   every ordering and every family of fundamental representations, the
   polynomial map sending variable `j` to the trace character of `F (e j)` is
   a bijection onto `ClassFunctions.algebra G`.
3. **Triangular character restriction**
   (`SplitSteinbergCharacterTriangularStatement.{u}`, module
   `Langlands.GroupScheme.Rational.SteinbergCharacterTriangularity`) is the
   published theorem `splitSteinbergCharacterTriangular`, from
   `Langlands.GroupScheme.Rational.SteinbergTriangularCoordinates`. It holds
   for every supplied ordering, fundamental-representation family, root family
   and representative family, with a unit diagonal coefficient and lower
   remainders for a well-founded relation.

The whole closing argument consists of these applications. Nothing is
reproved locally.

## Relation to the original source

The theorem is the derived arbitrary-field form of R. Steinberg, *Regular
elements of semi-simple algebraic groups*, Publications Mathématiques de
l'IHÉS 25 (1965), 49–80, Theorem 7.9 (printed p.68, PDF p.21). The source is
registered as `steinberg-1965-regular-elements-semisimple-groups`, SHA-256
`bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`. PDF pages
15–17 and 21–22 of that file were read for this proof. The statement's own
Markdown records the translation from Steinberg's varieties to the actual
group scheme, the canonical equalizer quotient and the supplied data.

Steinberg's proof (printed pp.68–69, PDF pp.21–22) uses 7.5 to put each
reflection representative in its rank-one subgroup. With 7.1 the root
coordinates are then affine coordinates on `N`, and the triangular formula
7.14 gives the theorem. Steinberg's map `ρ` of 6.10 (printed p.64, PDF p.17)
has the fundamental characters as coordinates; by 6.1(b) (printed p.62, PDF
p.15) they freely generate the algebra of regular class functions. The
implemented route keeps the same two ingredients: free generation by
fundamental characters, and triangularity of their restrictions to the ordered
product. It differs in the following ways.

- It never shows that `N` is a closed subvariety isomorphic to affine space
  (7.1). Instead it proves bijectivity of the coordinate-ring map from the
  invariant algebra to the polynomial algebra of the source affine space.
- Arbitrary reflection representatives and root maps are handled inside the
  published triangularity theorem, which allows any unit diagonal coefficient.
  The representatives are not first normalized by 7.5, and the root maps are
  not rescaled to the normalization of 7.14.
- Arbitrary fields are reached by base change to an algebraic closure and fpqc
  descent of the isomorphism, rather than by Steinberg's rationality remarks
  in §9.

## Scope

- The field is arbitrary, including finite fields and imperfect fields of
  positive characteristic. The universe `u` is arbitrary.
- The data `p`, `e`, `x` and `n` are arbitrary supplied data of the existing
  types. Their existence is neither asserted nor used.
- The conclusion concerns the actual `ClassFunctions.rho G`. No other quotient
  map, no fundamental-character coordinate map and no invariant-algebra
  comparison appears as a premise.
- The statement pair `SplitSteinbergQuotientStatement` and every pair it imports
  are unchanged. So is the parent `QuasiSplitSteinbergQuotientStatement` pair.
  This proof makes no claim about quasi-split descent, about outer forms with a
  factor of type `A_n` with `n` even, or about a global rational section for
  such forms.
