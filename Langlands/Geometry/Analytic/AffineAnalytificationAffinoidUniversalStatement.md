# Statement: strong maps from affinoid spectra to an affine analytification

`Langlands.Analytic.AffineAnalytification.AffineAnalytificationAffinoidUniversalStatement`
is a proposition. It is stated here and not proved. It says that strong maps from
the spectrum of a presented affinoid algebra `R` to the polynomial-locus
analytification of `Spec A` correspond to `K`-algebra maps `A → R`, naturally in
`R` and in `A`. This is the universal property of the analytification, tested on
affinoid spaces, at the level of strong atlas maps.

## Source

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), §3.4, assumes that the valuation of `k` is nontrivial. Theorem 3.4.1,
printed p.63/PDF p.77, states that for a scheme `X` locally of finite type over
`k`, the functor sending a `k`-analytic space `𝒳` to the set `Hom_k(𝒳, X)` of
morphisms of `k`-ringed spaces is represented by `X^an` with a morphism
`π : X^an → X`. Step (1) of the proof, printed p.64/PDF p.78, identifies
`Hom_k(𝒳, 𝔸^n) ≅ Γ(𝒳, 𝒪_𝒳)^n ≅ Hom_k(𝒳, Spec k[T_1, …, T_n])`. Steps (2)–(3)
extend this to subschemes, and hence to all affine schemes of finite type. For an affinoid space `𝒳 = M(R)`, the global
functions are `R`, so the represented set `Hom_k(M(R), Spec A)` is the set of
`k`-algebra maps `A → R`. Representability then gives a bijection between
analytic morphisms `M(R) → Spec(A)^an` and `k`-algebra maps `A → R`, natural in
`R` and in `A`. Remark 3.4.2, printed p.64/PDF p.78, describes the points of
`Spec(A)^an` as the multiplicative seminorms on `A` that extend the norm of `k`.
The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, in the final paragraph of the proof of Proposition 5.11(3), uses the
functorial analytification of Conrad–Temkin and its functorial property
`X(k) = X^an(k)` as sets. For `R = K`, assertions 2 and 3 are the affine case of
this property at the level of strong maps. The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The formulation is derived for the Library's model. The analytic morphisms are
the Library's strong atlas maps from the singleton atlas
`PresentedAffinoidSpace.atlasPresentation (Opposite.op R)` to the constructed
atlas `presentation K P`. The two directions of the bijection are the published
constructions `affinoidStrongHom` and `strongHomAlgHom` of
`AffineAnalytificationAffinoidMap`.

## Statement

For every complete, ultrametric, nontrivially normed field `K : Type u`, every
commutative `K`-algebra `A : Type v` and every finite polynomial presentation
`P : FinitePolynomialPresentation K A`, the following six assertions hold. Here
`R` and `R'` range over all presented affinoid algebras over `K`, and `M(R)`
denotes the singleton atlas presentation
`PresentedAffinoidSpace.atlasPresentation (Opposite.op R)`.

1. **Chart independence.** Let `F : StrongHom M(R) (presentation K P)`. Let `j` be
   any chart of `presentation K P` whose image contains the image under
   `F.baseMap` of the single chart of `M(R)`, with containment proof `h`. Then
   for every `a : A`, `F.pullback PUnit.unit j h` sends the coordinate-algebra
   image `PolynomialLocus.algebraMap P (polyradius K P.arity j.val) a` to
   `strongHomAlgHom F a`.
2. **Left inverse.** For every `φ : A →ₐ[K] R`,
   `strongHomAlgHom (affinoidStrongHom K P R φ) = φ`.
3. **Right inverse.** For every `F : StrongHom M(R) (presentation K P)`,
   `affinoidStrongHom K P R (strongHomAlgHom F) = F`.
4. **Points.** For every `φ : A →ₐ[K] R`, every point `x : BanachSpectrum R` and
   every `a : A`, the published seminorm `pointSeminorm K P` of
   `(affinoidStrongHom K P R φ).baseMap x` takes the value `x (φ a)` at `a`.
5. **Naturality in the affinoid.** For every bounded algebra map
   `g : R ⟶ R'` and every `φ : A →ₐ[K] R`, composing the strong singleton-atlas
   map `PresentedAffinoidSpace.strongAtlasMap g.op : StrongHom M(R') M(R)` with
   `affinoidStrongHom K P R φ` by `StrongHom.compOfDirected` gives
   `affinoidStrongHom K P R' (g.toAlgHom.comp φ)`. The directedness proofs are
   `PresentedAffinoidSpace.atlasPresentation_hasDirectedCharts (Opposite.op R)`
   and `atlas_hasDirectedCharts K P`.
6. **Naturality in the algebra.** For every commutative `K`-algebra
   `B : Type w`, presentation `Q : FinitePolynomialPresentation K B`, `K`-algebra
   map `f : A →ₐ[K] B` and `ψ : B →ₐ[K] R`, composing
   `affinoidStrongHom K Q R ψ` with the published `strongHom K P Q f` by
   `StrongHom.compOfDirected` gives `affinoidStrongHom K P R (ψ.comp f)`. The
   directedness proofs are `atlas_hasDirectedCharts K Q` and
   `atlas_hasDirectedCharts K P`.

Assertions 2 and 3 say that `affinoidStrongHom K P R` is a bijection from
`A →ₐ[K] R` to the strong maps `M(R) → presentation K P`, with inverse
`strongHomAlgHom`. Assertions 5 and 6 are the naturality of this bijection.
Assertion 4 identifies the underlying point map with Berkovich's description of
`Spec(A)^an` by seminorms. Assertion 1 shows that `strongHomAlgHom` does not
depend on the chosen target chart.

## Hypotheses and scope

The field must be nontrivially normed, as in Berkovich §3.4 and as the Library's
polynomial-locus construction requires. `A` and `B` are arbitrary commutative
`K`-algebras with finite polynomial presentations, in independent universes. `R`
and `R'` are arbitrary presented affinoid algebras, possibly nonreduced, zero or
with empty spectrum. No reducedness, positive arity or nonemptiness is assumed.

The unit supplies no proof and edits no published input. It imports
`AffineAnalytificationAffinoidMap`, `AffineAnalytificationSeminorm` and
`DirectedAtlasComposition`. It does not state the bijection for morphisms in the
localized category `SaturatedAtlasPresentation.LocalizedCategory`. That needs a
comparison of localized morphisms out of an affinoid with strong maps from its
refinements, and the gluing of maps out of finite affinoid covers. It also does
not state the universal property for general analytic test spaces, for schemes
that are not affine or for algebraic spaces. These remain obligations of the
parent task.
