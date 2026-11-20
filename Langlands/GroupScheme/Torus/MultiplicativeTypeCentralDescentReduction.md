# Descent of central homomorphisms from rigidity (SGA 3, IX, 5.4 from 5.3)

Worker 754.

This module proves

```lean
theorem descent_of_rigidity (hrig : MultiplicativeTypeCentralRigidityStatement.{u}) :
    MultiplicativeTypeCentralDescentStatement.{u}
```

in the namespace `Langlands.GroupScheme.MultiplicativeTypeCentralDescent`. It derives the
Library statement
[`MultiplicativeTypeCentralDescentStatement`](MultiplicativeTypeCentralDescentStatement.md)
(SGA 3, IX, Corollaire 5.4) from the Library statement
[`MultiplicativeTypeCentralRigidityStatement`](MultiplicativeTypeCentralRigidityStatement.md)
(SGA 3, IX, 5.1–5.3), which it takes as a hypothesis. Only part 3 (Corollaire 5.3) of the
rigidity statement is used. The module adds no axioms. Its only new definitions are the
auxiliary homomorphism `diffHom`, the predicate `FibreConstant` and the descended morphism
`underlying`/`overHom`/`hom` described below.

The route is SGA 3's proof of 5.4 (p.50, margins 60–61, of the Gille–Polo edition registered
as `sga3-expose-ix-gille-polo-2009`), with two changes. The descent step is done by hand for an
effective epimorphism rather than through SGA 3, IV 2.3. The connectedness step works with one
geometric point at a time, so it needs neither the connectedness of products of connected
spaces nor the fibres of `S'' = S' ×_S S'` over `S`.

Notation: `π : S' ⟶ S`, `H' = H ×_S S'`, `G' = G ×_S S'`, `S'' = S' ×_S S'` (`Descent.Overlap
π`, with projections `Descent.fst π` and `Descent.snd π`), and `A`, `B` the pullbacks of `H'`,
`G'` along `Descent.fst π`.

## Section `Difference`

For group schemes `A`, `B` over a scheme `Y` and two central homomorphisms `f g : A ⟶ B`:

- `isCentral_comp_iso`: composing a central homomorphism with an isomorphism `B ≅ B'` keeps
  it central.
- `isMonHom_mul_inv`: the pointwise quotient `f · g⁻¹` (using the group structure on
  `A.X ⟶ B.X` in the category of schemes over the base) is a monoid homomorphism. Unit: from
  `f` and `g` preserving the unit. Multiplication: on `A × A` with the projections, the claim
  is `a c (b d)⁻¹ = (a b⁻¹)(c d⁻¹)` with `a = pr₁ f`, `b = pr₁ g`, `c = pr₂ f`, `d = pr₂ g`.
  Since `c` and `d` are central points, `c d⁻¹` commutes with `b⁻¹`, and the identity follows
  by group rewriting.
- `diffHom f g hf hg : A ⟶ B` is this homomorphism `f · g⁻¹`.
- `baseChange_diffHom_eq_one_iff`: for `q : T ⟶ Y`, the base change of `f · g⁻¹` along `q` is
  trivial if and only if `pullback.fst A.X.hom q ≫ f = pullback.fst A.X.hom q ≫ g`. The proof
  uses the Library's point equivalence `baseChangePointsEquiv` (a group isomorphism between
  the points of `A_T` over a `T`-scheme `T'` and the points of `A` over `T'` viewed as a
  `Y`-scheme), applied to the identity point of `A_T`, and its naturality
  `baseChangePointsEquiv_comp`.

## Section `Agreement`

- `fst_comp_eq_iff`: `pullback.fst p q ≫ φ = pullback.fst p q ≫ ψ` holds exactly when
  `α ≫ φ = α ≫ ψ` for every `α : Z ⟶ X`, `β : Z ⟶ T` with `α ≫ p = β ≫ q` (the universal
  property of the pullback).
- `agree_of_flat_comp`: if `r : T' ⟶ T` is flat and surjective and the agreement holds for
  all points over `r ≫ q`, it holds for all points over `q`. Proof: for `α`, `β` over `q`, the
  projection `pullback β r ⟶ Z` is flat and surjective, hence an epimorphism (Mathlib's
  `Flat.epi_of_flat_of_surjective`), and the agreement holds after composing with it.

## Section `Overlap`

For a homomorphism `u' : H' ⟶ G'`:

- `u₁ π u'` is the base change of `u'` along `Descent.fst π`, and `u₂ π u'` is its base change
  along `Descent.snd π` transported to `A ⟶ B` by the Library's canonical identifications
  `Descent.canonicalOverlap π H` and `Descent.canonicalOverlap π G` (these are SGA 3's
  `u''₁` and `u''₂`). `isCentral_u₁` and `isCentral_u₂`: both are central when `u'` is, by
  the Library's `IsCentral.baseChange` and `IsCentral.comp` and by `isCentral_comp_iso`.
- `baseChange_map_fst`, `canonical_fst_fst`, `canonical_inv_fst_fst`, `canonical_fst_snd`,
  `fst_snd`, `u₁_fst_fst`, `u₂_fst_fst` compute the composites of these maps with the
  projections to `H`, `G` and `S'`. `hom_ext_B` says that maps into `B` are determined by
  their composites with `B ⟶ G` and `B ⟶ S''`.
- `agree_diagonal`: on points of `A` lying over the diagonal `S' ⟶ S''`, the underlying maps
  of `u₁` and `u₂` agree. Over the diagonal both identifications pick out the same point of
  `H'`, so both maps send it to the image under `u'` of that point.
- `constant_of_eq`: if the underlying maps of `u₁` and `u₂` are equal, then for any two points
  `x y : Z ⟶ H'` with the same image in `H`, `x ≫ u' ≫ (G' ⟶ G) = y ≫ u' ≫ (G' ⟶ G)`. Proof:
  the pair `(x, y)` defines a point `α` of `A`. Its image under the first identification is
  `x`, and under the second it is `y`.

## Section `Connected`

`mem_of_isClopen_of_diagonal`: assume that `S' ×_S Spec K` is connected for every
algebraically closed `K` and every `x : Spec K ⟶ S`. Then a clopen subset `U` of `S''`
containing the image of the diagonal contains every point `t`. Proof: let `K` be an algebraic
closure of `κ(t)` and `τ : Spec K ⟶ S''` the induced point, with coordinates `a, b : Spec K ⟶
S'` over `x = a ≫ π`. The map `m : S' ×_S Spec K ⟶ S''`, `(s', k) ↦ (s', b(k))`, is
continuous, so `m⁻¹ U` is clopen. It contains the image of the section `σ_b = (b, 𝟙)`,
because `σ_b ≫ m = b ≫ diagonal`, so by connectedness it is everything. Hence it contains
`σ_a = (a, 𝟙)`, and `m (σ_a pt) = τ pt = t`.

## Section `Descent`

`FibreConstant π u'` (a `Prop`) says that `u'` composed with `G' ⟶ G` takes equal values on
any two points of `H'` with equal images in `H`. Assume `FibreConstant π u'`, that the
projection `H' ⟶ H` is an effective epimorphism, and that pullback `Over S ⥤ Over S'` along
`π` is faithful. Then:

- `underlying : H ⟶ G` on underlying schemes is `EffectiveEpi.desc` of `u' ≫ (G' ⟶ G)`, and
  `underlying_fac` is its factorisation property. `underlying_over`: it lies over `S`
  (cancel the epimorphism `H' ⟶ H`).
- `overHom` is this map in `Over S`, and `pullback_overHom` shows that its pullback along `π`
  is the underlying map of `u'`.
- `overHom_isMonHom`: it is a monoid homomorphism, because its pullback is one and the
  faithful monoidal functor `Over.pullback π` reflects this (the Library's
  `GaloisCocharacterDescent.isMonHom_of_faithfulMap`).
- `hom` is the descended homomorphism. `baseChange_hom` says that its base change is `u'`, and
  `existsUnique_hom` says that it is the unique such homomorphism (faithfulness of
  `Over.pullback π`).

This section repeats the pattern of the Library's `Descent.FpqcHomDescent`, but for an
arbitrary effective epimorphism and with fibre constancy in place of a compatibility with
descent data.

## Section `Main`

- `baseChange_hom_props`: separatedness, local finite presentation and quasi-compactness of
  `C.X.hom` pass to the base change of the group scheme `C`.
- `fibreConstant_of_rigidity`: given the rigidity statement, `IsMultiplicativeType H`, `G`
  separated, locally of finite presentation and quasi-compact, connected geometric fibres of
  `π` and a central `u'`, the homomorphism `u'` is fibre-constant. Proof: let
  `w = diffHom (u₁ π u') (u₂ π u')`, a homomorphism `A ⟶ B` over `S''`. Here `A` is of
  multiplicative type (`IsMultiplicativeType.baseChange` twice), and `B` is separated, locally
  of finite presentation and quasi-compact (`baseChange_hom_props` twice), so part 3 of the
  rigidity statement gives an open `U ⊆ S''` with closed underlying set. Its points are those
  `s` where the fibre of `w` is trivial, and `w` is trivial over `U`. Each diagonal point
  `Δ(y)` lies in `U`. By `baseChange_diffHom_eq_one_iff` and `fst_comp_eq_iff` this means that
  `u₁` and `u₂` agree on points over `Spec κ(Δ y) ⟶ S''`. By `agree_of_flat_comp` with the
  flat surjective `Spec κ(y) ⟶ Spec κ(Δ y)` (a field extension is faithfully flat), it is
  enough to check points over `Spec κ(y) ⟶ S' ⟶ S''`, which lie over the diagonal
  (`agree_diagonal`). By `mem_of_isClopen_of_diagonal`, `U` contains every point. Lifting the
  structure map of `A` through the open immersion `U.ι` (`IsOpenImmersion.lift`), triviality
  over `U` gives `u₁ = u₂`, and `constant_of_eq` concludes.
- `descent_of_rigidity`: the main theorem. Fibre constancy comes from
  `fibreConstant_of_rigidity`. If `π` is flat, quasi-compact and surjective, so is `H' ⟶ H`,
  which is therefore an effective epimorphism (Mathlib's fpqc instance in
  `AlgebraicGeometry.Sites.Fpqc`). `Over.pullback π` is then faithful by Mathlib's instance in
  `AlgebraicGeometry.Morphisms.FlatDescent`. If `π` has a section `g`, every pullback
  `pullback.fst f π` has the section `pullback.lift (𝟙 _) (f ≫ g)`. So `H' ⟶ H` is a split,
  hence effective, epimorphism (`IsSplitEpi.EffectiveEpi`), and `Over.pullback π` is faithful
  by `Over.faithful_pullback`. In both cases `existsUnique_hom` gives the result.

## Status

The module compiles with no errors or warnings, using only the axioms `propext`,
`Classical.choice` and `Quot.sound`. The companion module
[`MultiplicativeTypeCentralDescentProof`](MultiplicativeTypeCentralDescentProof.md) applies
`descent_of_rigidity` to the Library's proof `multiplicativeTypeCentralRigidity` of the rigidity
statement, which proves `MultiplicativeTypeCentralDescentStatement` outright.
