# Cartier characters and their intrinsic evaluation

For an arbitrary scheme `S` and an arbitrary commutative group scheme `G` over
`S`, this module constructs the Cartier character functor and its intrinsic
evaluation pairing. The namespace is `Langlands.GroupScheme.Cartier`.

The imports supply actual group schemes, actual pullback group schemes, the
relative-Hom restriction functor, and the constructed multiplicative group
scheme `Gm S`. In particular, a character is a morphism of group schemes.
It is not an arbitrarily supplied homomorphism of abstract point groups.
The character group uses the Library's additive notation for morphisms between
commutative group schemes; its addition is pointwise multiplication in `Gm`.

## The character functor and its actual relative-Hom presentation

`characters G : (Over S)ᵒᵖ ⥤ AddCommGrpCat` is
`relativeHomFunctor G (Gm S)`. Its value at `T` is the group of actual
homomorphisms `G_T → (Gm S)_T`.

`CharacterHom G T` is the actual Hom group `G_T → Gm T.left`.
`characterHomEquiv G T` is the additive equivalence from the preceding
presentation to this one. It postcomposes with
`(Gm.commBaseChangeIso T.hom).hom`; its inverse postcomposes with the inverse
isomorphism. The inverse equations and additivity follow from categorical
composition and the preadditive structure.

Write `c_G(a) : G_T' ≅ (G_T)_T'` for `baseChangeCompIso G a` and
`b_f : (Gm S)_T ≅ Gm T.left` for the multiplicative-group base-change
isomorphism. `gmBaseChange_comp` proves the coherence equation

```
c_Gm(a).hom ≫ pullback(a.left)(b_T.hom) ≫ b_a.hom = b_T'.hom.
```

The proof tests the two actual homomorphisms on every test-scheme point and
uses the natural units interpretation of `Gm`. Both resulting units are
pullbacks of the Laurent coordinate along the same scheme morphism. The equality
of those morphisms is precisely the first-projection formula for the canonical
iterated-pullback comparison. Thus coherence is proved from the constructed
isomorphisms, not imposed as extra data.

For `a : T' ⟶ T`, `characterHomRestrict G a χ` is the actual homomorphism

```
c_G(a).hom ≫ pullback(a.left)(χ) ≫ b_a.hom.
```

`characterHomEquiv_restrict` proves that the additive equivalence intertwines
the existing relative-Hom restriction with this formula.
`characterHomRestrict_id` and `characterHomRestrict_comp` prove its identity and
contravariant composition laws by that equivalence and the existing laws.
`characterHomFunctor` packages the actual groups `Hom_T(G_T,Gm_T)` into a
functor. Its additive maps are transported through the equivalence;
`characterHomFunctor_map_apply` proves they are exactly the displayed
base-change maps. `characterHomNatIso` supplies a natural isomorphism
`characters G ≅ characterHomFunctor G`. This is an equivalence of the
actual relative-Hom functors, including restriction maps.

## Contravariance in the group scheme

For `φ : G' ⟶ G`, `charactersMap φ : characters G ⟶ characters G'`
specializes the existing natural transformation defined by precomposition with
`φ_T`. `charactersMap_id` and `charactersMap_comp` give identity and reversed
composition. `characterHomEquiv_precompose` proves that in the actual
`Hom_T(G_T,Gm_T)` presentation its value is `φ_T ≫ χ`.

These constructions have no finiteness, flatness, affineness or annihilation
hypotheses on `G`.

## Intrinsic evaluation

For a character `χ` over `T`,
`characterEvaluation χ : (T ⟶ G.X) →* (T ⟶ (Gm S).X)` specializes the imported
section evaluation. Given `x : T ⟶ G.X`, the pullback point equivalence
identifies `x` with a section of `G_T`; composing that section with `χ` and
applying the inverse identification produces the evaluated `Gm S` point.

`characterEvaluation_section` checks this interpretation in the actual
`Gm_T` presentation: applying `characterHomEquiv G T χ` to the section of `x`
and interpreting the result as a global unit gives exactly the unit attached to
`characterEvaluation χ x`. The proof uses the units formula for the canonical
base-change isomorphism and the first projection of the section correspondence.

The six laws `characterEvaluation_one`, `_mul`, `_inv`, `_zero`, `_add`, and
`_neg` express the two group laws:

```
e(χ, 1) = 1,       e(χ, xy) = e(χ,x)e(χ,y),      e(χ, x⁻¹) = e(χ,x)⁻¹,
e(0, x) = 1,       e(χ+ψ,x) = e(χ,x)e(ψ,x),      e(-χ,x) = e(χ,x)⁻¹.
```

`characterEvaluation_restrict` proves
`e(a*χ, a*x) = a*e(χ,x)` for every map of test schemes.
`characterEvaluation_precompose` proves
`e(φ*χ,x) = e(χ,φ(x))`. These are specializations of the intrinsic laws of
the imported relative-Hom evaluation, so there is no free bilinear form among
the construction's inputs.

## Factorization through the actual roots-of-unity scheme

Let `n : ℕ` and assume
`h : multiplication G.toGrp (n : ℤ) = 1`.
Here `1` is the constant identity-valued group-scheme homomorphism, hence the
zero morphism in the additive notation on `CommGroupScheme`. This is the
actual scheme-level annihilation condition `[n]_G = 0`.

`muEvaluation n h χ x : T ⟶ (mu S n).X` is the imported canonical torsion
lift specialized to `Gm`. The target is the actual torsion kernel of the
power morphism, not merely a subgroup supplied separately.
`muEvaluation_incl` proves that composing this point with `mu.incl S n`
recovers `characterEvaluation χ x`. `muEvaluation_unique` proves uniqueness
among points with this inclusion property, using the torsion kernel's universal
property.

`muEvaluation_restrict` proves naturality in the test scheme.
`muEvaluation_precompose` proves compatibility with `φ : G' ⟶ G` when both
`G` and `G'` have the displayed annihilation condition.
The six laws `muEvaluation_one`, `_mul`, `_inv`, `_add`, `_neg`, and `_zero`
specialize the imported bilinearity and identity/inverse laws of the torsion
lift.

The construction works for every natural `n`, including zero, consistently
with the imported `mu` and `rootsOfUnity` definitions. In particular it includes
every positive integer required by the source. Annihilation is required only
for the torsion-valued evaluations and their root interpretations.

## Global sections and affine tests

`rootsEvaluation n h χ x` applies `mu.pointsEquiv S n T` to the intrinsic
`muEvaluation` and therefore lies in `rootsOfUnity n Γ(T.left, ⊤)`.
`rootsEvaluation_val` identifies its underlying unit with
`Gm.pointsEquiv S T (characterEvaluation χ x)`.
`rootsEvaluation_restrict` proves that restriction along `a : T' ⟶ T`
is `restrictRootsOfUnity a.left.appTop.hom n`.

For a commutative ring `R` and `f : Spec R ⟶ S`,
`affineRootsEvaluation n h f χ x` applies the imported affine point equivalence
and lies in `rootsOfUnity n R`.
`affineRootsEvaluation_val` identifies its underlying unit with
`Gm.affinePointsEquiv f (characterEvaluation χ x)`.
For every ring homomorphism `φ : R ⟶ R'`,
`affineRootsEvaluation_naturality` identifies evaluation after restriction
along `Spec φ` with `restrictRootsOfUnity φ.hom n` of the original value.
The proofs combine naturality of the actual torsion lift with the imported
natural point equivalences. No primitive root is chosen.

## Original source and scope

Source: Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
draft, registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

- Chapter III, Examples 2 and 3, printed p.32 / PDF p.36, give the
  multiplicative group, its units interpretation, and the roots-of-unity
  subgroup. This module imports those constructions and uses their point
  equivalences for evaluation.
- (3.21), printed p.41 / PDF p.45, defines characters for any commutative group
  scheme as the contravariant group functor `T ↦ Hom_T(G_T,Gm_T)`.
  `characterHomFunctor` realizes that formula; `characterHomNatIso` proves
  the equivalent pullback-target presentation used by `characters`.
- (3.23), printed p.43 / PDF p.47, gives the induced dual morphism with
  reversed variance for finite locally free group schemes. `charactersMap`
  is the intrinsic precomposition on the functors, without a representability
  assertion or finiteness hypothesis.
- (11.11)(i) and the following bilinearity paragraph, printed p.162 /
  PDF p.166, evaluate a character on a point and factor into `μ_n` under
  annihilation. This module constructs that intrinsic evaluation and its
  factorization for arbitrary commutative `G`.

The explicit coherence, naturality, section formula, unique torsion lift, and
affine comparison are derived implementations of these constructions using the
imported pullback, units and kernel interfaces. Their proofs are described above.
The source's separate representability and biduality theorem (3.22), printed
p.42 / PDF p.46, is not asserted here. Neither are finiteness or local freeness
of a dual, isogeny kernel duality, perfectness of an isogeny pairing, or
etaleness of `μ_n`. In particular, no isomorphism from a dual-isogeny kernel
to this character functor is assumed as input.
