# Assembly of the separating line bundle

Supporting module for the proof of
`Langlands.GroupScheme.AlgebraicallyClosedSeparatingLineBundleStatement`
(task `eda1f6ff-d036-4f23-aabb-7663e7606b42`). It imports `TensorFamily`, the published
`RationalPoints`, `GeometricPicardZero`, `TensorPowerDistributivity`, `FiniteSectionSeed`,
`FieldTheoremOfTheSquareStatement`, the published seed existence proof
`AlgebraicallyClosedSectionSeedExistenceProof`, and the target statement.

The vanishing lemmas used below come from published Library proofs, through `TensorFamily`.
`vanishesAlong_pullback_iff` and `vanishesAlong_mapIso_iff` are in
`Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof`. The field-point,
cancellation and tangent lemmas (`vanishesAlong_tensor_field_iff`,
`vanishesAlong_tensor_left_iff`, `vanishesAlong_tensor_right_iff`,
`mem_trivializationOpen_of_isTangentVectorAt`, `mem_preimage_trivializationOpen_iff`) are
in `Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof`.

This module proves the implication from
`Langlands.GroupScheme.FieldTheoremOfTheSquareStatement` to the separating-bundle
target. It supplies the seed by the published proof
`Langlands.GroupScheme.algebraicallyClosedSectionSeedExistence`.
The separate entry module
`Langlands.AbelianScheme.AlgebraicallyClosedSeparatingLineBundleProof` supplies the
published proof `Langlands.GroupScheme.fieldTheoremOfTheSquare` to obtain the
unconditional target.

Notation: `S = Spec K`, and `P` is the type `Over.mk (𝟙 S) ⟶ G.X` of points of `G` over
the base. `P` is a group under `open scoped CategoryTheory.MonObj`. For `c : P`, `τ_c`
is the Library `translation G c`, and `Q_c` is the pullback of `L` along `τ_c.left`.
`W(s)` is the trivialization open of a section `s`.

## Provenance

The construction is Milne's proof of Theorem 7.1 (*Abelian Varieties*, 1986 article,
author revision 2022, pp.10–11; registered as
`milne-abelian-varieties-1986-author-2022`). Milne takes prime divisors `Z_i` through `0`
with `⋂ Z_i = {0}` and no common tangent vector at `0`. He uses the theorem of the
square in the form `D_a + D_b + D_{-a-b} ~ 3D` (Remark 6.9, p.10) to see that the
translates `Σ_i (Z_{i,a_i} + Z_{i,b_i} + Z_{i,-a_i-b_i})` lie in `|3D|`. He then
chooses the parameters `a_i, b_i` generically.

This module works with line-bundle sections instead of divisors. The seed sections
`s i` of `L i` play the role of the local equations of the `Z_i`. The seed conditions
are the published predicate
`Langlands.AlgebraicGeometry.Picard.IsFinitePointTangentSectionSeed`. The line bundle
`(L i ⊗ L i) ⊗ L i` plays the role of `3 Z_i`. The group is written multiplicatively.
The pullback of `s` along `τ_c` vanishes at `d` exactly when `s` vanishes at `c d`, so
its zero locus is `c⁻¹ Z`. This reverses Milne's sign convention for translates. The genericity arguments use
irreducibility of `G` and density of rational points (from `RationalPoints`) instead of
Milne's "proper closed subsets".

Milne only says that tangent separation "is similar". The tangent case here is derived
from the point case. It also needs the tensor cancellation lemmas and the finite-product
lemma `vanishesAlong_famSection_iff_of_mem` of `TensorFamily`. Milne does
not list base-point freeness among his conditions. Here it comes from the same generic
choice.

## Seed predicate and auxiliary predicate

The seed predicate is the published `IsFinitePointTangentSectionSeed p z n L s`. Every
`s i` vanishes along `z`. Each `s i` is nonzero at some rational point. For every
rational point `x ≠ z`, some `s i` is nonzero at `x`. For every nonzero tangent vector
`t` at `z`, some `s i` does not vanish along `t`.

- `SquareFor G L`: for all `a b : P` there is an isomorphism
  `Q_{ab} ⊗ L ≅ Q_a ⊗ Q_b`. This is the conclusion of the theorem of the square for
  one line bundle. It is an auxiliary definition, not a stand-in: it is the body of
  `FieldTheoremOfTheSquareStatement` for fixed `G` and `L`.

The published `AlgebraicallyClosedSectionSeedExistenceStatement` says that over an
algebraically closed field every commutative smooth proper geometrically connected group
scheme `G` has finitely many sections satisfying `IsFinitePointTangentSectionSeed` at the
unit `(1 : P).left`.

## Translations

- `comp_translation c d : d ≫ τ_c = c * d`, from the Library `points_translation`.
  The unique map to the terminal object `Over.mk (𝟙 S)` is the identity.
- `left_comp_translation`: the same identity on underlying morphisms.
- `translation_comp_translation a b : τ_a ≫ τ_b = τ_{b a}`. The proof unfolds
  `translation` and uses `MonObj.comp_mul` and associativity.
- `left_translation_comp`: the same identity on underlying morphisms.
- `isRationalPoint_left d`: `d.left` is a rational point. This is the commuting triangle
  of `d`.
- `isNonzeroTangentVectorAt_translate d ht`: if `t` is a nonzero tangent vector at
  `d.left`, then `t ≫ τ_{d⁻¹}.left` is a nonzero tangent vector at the unit. `τ` lies
  over `S`, so the structure condition holds. `d⁻¹ d = 1`, so the base point is the
  unit. Translating back by `τ_d` recovers `t`, because `τ_{d⁻¹} ≫ τ_d = τ_1 = 𝟙`
  (`translation_one`). Hence the constant tangent vector at the unit can only come from
  the constant tangent vector at `d.left`.

## The theorem of the square

The square theorem for each `L i` comes from the published proposition
`Langlands.GroupScheme.FieldTheoremOfTheSquareStatement` (Milne, Theorem 6.7, p.10). For
fixed `G` and `L` its body is `SquareFor G L`. So a hypothesis
`hsquare : FieldTheoremOfTheSquareStatement` gives
`hsquare K G hsm hpr hgc L : SquareFor G L` by definitional unfolding. The proof of the
square from the theorem of the cube is the published
`Langlands.GroupScheme.fieldTheoremOfTheSquare`, in
`Langlands.AbelianScheme.FieldTheoremOfTheSquareProof`.
The entry module supplies it to the conditional assembly.

## Common nonvanishing points

Assume that `K` is algebraically closed, that `G.X.hom` is locally of finite type, and
that `G.X.left` is irreducible.

- `exists_forall_not_vanishesAlong φ N u h`: take finitely many endomorphisms `φ k` of
  `G.X` and sections `u k` of `N k`. Suppose each `u k` is nonzero at `b ≫ φ k` for some
  `b : P`. Then a single `b : P` works for every `k`. The sets
  `(φ k).left ⁻¹ W(u k)` are open and nonempty. The published
  `exists_rationalPoint_mem_of_isOpen` gives a rational point in all of them, and
  `mem_preimage_trivializationOpen_iff` turns membership into nonvanishing.
- `exists_good_second L s hs d a` (for commutative `G`): suppose `s` is nonzero at some
  rational point `y`. Then for all `d, a` some `b` keeps `s` nonzero at `b d` and at
  `(a b)⁻¹ d`. The previous item is applied to `φ 0 = τ_d` and
  `φ 1 = (𝟙 G.X)⁻¹ ≫ τ_{a⁻¹ d}` (inversion followed by translation), with witnesses
  `d⁻¹ y` and `y⁻¹ a⁻¹ d`. Commutativity rewrites `b⁻¹ ≫ τ_{a⁻¹d}`, that is `a⁻¹ d b⁻¹`,
  as `(a b)⁻¹ d`.
- `exists_good_pair L s hs d`: some `a, b` keep `s` nonzero at `a d`, `b d` and
  `(a b)⁻¹ d`. Take `a = y d⁻¹` and `b` from the previous item.

## Triple translates

- `transLB G L c`, `transSection G L s c`: the pullbacks of `L` and of `s` along `τ_c`.
- `cubeLB G L`: the line bundle `(L ⊗ L) ⊗ L`.
- `transOneIso G L c hc`: if `c = 1`, then `Q_c ≅ L`. It combines `translation_one`
  with `Scheme.Modules.pullbackId`.
- `tripleIso hsq a b`: with `c = (a b)⁻¹`, it identifies `Q_c ⊗ (Q_a ⊗ Q_b)` with
  `(L ⊗ L) ⊗ L`. The steps are `SquareFor` for `a, b`, the associator, `SquareFor` for
  `c, a b`, and `transOneIso` for `c (a b) = 1`.
- `tripleSection s hsq a b`: the image of
  `τ_c^* s ⊗ (τ_a^* s ⊗ τ_b^* s)` under `tripleIso`, a section of `(L ⊗ L) ⊗ L`.
- `vanishesAlong_transSection_iff`: `τ_c^* s` vanishes along `f` exactly when `s`
  vanishes along `f ≫ τ_c.left` (`vanishesAlong_pullback_iff`).
- `vanishesAlong_tripleSection_point_iff`: at a rational point `d.left`, the triple
  section vanishes exactly when `s` vanishes at `(a b)⁻¹ d`, at `a d` or at `b d`. The
  isomorphism does not change vanishing (`vanishesAlong_mapIso_iff`). The field-point
  tensor rule `vanishesAlong_tensor_field_iff` then splits the condition, and
  `left_comp_translation` computes the translated points.
- `vanishesAlong_tripleSection_tangent_iff`: let `t` be a tangent vector at `d.left`
  with `s` nonzero at `b d` and at `(a b)⁻¹ d`. Then the triple section vanishes along
  `t` exactly when `s` vanishes along `t ≫ τ_a.left`. By
  `mem_trivializationOpen_of_isTangentVectorAt`, `t` lands in the trivialization opens
  of the `c`- and `b`-factors. These factors are then cancelled with
  `vanishesAlong_tensor_left_iff` and `vanishesAlong_tensor_right_iff`.

## Assembly

`separatesPointsAndTangents_of_isSeed L s hsq hseed`: suppose `G` is commutative, locally
of finite type and irreducible over an algebraically closed field. Suppose also that
the sections `s` form a seed at the unit and the square theorem holds for every `L i`.
Then `famBundle n (fun i ↦ cubeLB G (L i))` separates points and tangent vectors.

For parameter families `A, B : Fin n → P`, the candidate section is the product
`famSection` of the `tripleSection (s i) (hsq i) (A i) (B i)`. Every rational point is
`d.left` for some `d : P`. If `A i0 = d⁻¹`, the product vanishes at `d.left`, because
the `a`-translate of factor `i0` vanishes at `d⁻¹ d = 1` (seed clause 1).

- Base-point freeness at `d`: choose `A i, B i` by `exists_good_pair` at `d`. The
  needed nonvanishing points come from seed clause 2. By
  `vanishesAlong_famSection_field_iff` and the point rule, no factor vanishes at `d`.
- Points `dx.left ≠ dy.left`: then `dx⁻¹ dy ≠ 1`, so seed clause 3 gives `i0` with
  `s i0` nonzero at `dx⁻¹ dy`. Set `A i0 = dx⁻¹`, and let `B i0` come from
  `exists_good_second` at `dy` with `a = dx⁻¹`. The other parameters come from
  `exists_good_pair` at `dy`. The product vanishes at `dx`. None of the three points of
  any factor at `dy` lies in the zero locus of `s`, so the product does not vanish at
  `dy`.
- Tangent vectors: let `t` be a nonzero tangent vector at `dx.left`. Seed clause 4,
  applied to the translate `t ≫ τ_{dx⁻¹}.left`, gives `i0` with `s i0` not vanishing
  along it. Set `A i0 = dx⁻¹`, and let `B i0` come from `exists_good_second` at `dx` with
  `a = dx⁻¹`. The other parameters come from `exists_good_pair` at `dx`. The product
  vanishes at `dx`. Every factor `i ≠ i0` is nonzero at `dx`, so `t` lands in its
  trivialization open. `vanishesAlong_famSection_iff_of_mem` reduces vanishing along `t`
  to factor `i0`. The tangent rule then reduces it to `s i0` along
  `t ≫ τ_{dx⁻¹}.left`, which does not vanish.

`algebraicallyClosedSeparatingLineBundle_of_seedExistence hseed hsquare`: the target
proposition follows from `AlgebraicallyClosedSectionSeedExistenceStatement` and
`FieldTheoremOfTheSquareStatement`. `G` is
irreducible by the published `irreducibleSpace_of_smooth_of_isProper`, and smoothness
gives local finite type. The witness is the line bundle of the previous theorem for the
seed supplied by `hseed`, with the square theorem for each `L i` supplied by
`hsquare`.

`algebraicallyClosedSeparatingLineBundle_of_square hsquare`: the target proposition
follows from `FieldTheoremOfTheSquareStatement` alone. It applies the previous theorem
to the published proof `algebraicallyClosedSectionSeedExistence`.


## Empty seed and scope

No positive dimension or nonempty index set is assumed. If `n = 0`, `famBundle` is the
trivial line bundle and `famSection` is its unit section. The base-point argument uses
the empty-family nonvanishing equivalence. The seed's point and tangent clauses imply
that there are no distinct rational points and no nonzero tangent vector at the unit;
the same assembly proof handles this case without a separate dimension argument.
The result keeps arbitrary universe `u` and arbitrary characteristic. It uses neither
projectivity nor ample existence.

## Recovery and authorship

The Lean implementation and original proof explanation were carried from the shared
draft by Worker 899 of the previous instance (old revision 8, transferred as revision 1).
Worker 2441 recovered the pair, checked it against the current published dependencies,
and updated this documentation. Mathematical dependencies are the
published declarations imported by Lean name.
The square derivation is owned separately by task
`e236fdea-a458-40b7-935e-5def16b126aa` (current Worker 2784).

The theorem
`Langlands.GroupScheme.SeparatingLineBundle.algebraicallyClosedSeparatingLineBundle_of_square`
has exactly the type
`FieldTheoremOfTheSquareStatement.{u} → AlgebraicallyClosedSeparatingLineBundleStatement.{u}`,
with only universe parameter `u`. The final entry theorem supplies the published
proof of the premise.
