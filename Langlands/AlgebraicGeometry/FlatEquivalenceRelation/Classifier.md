# The classifying morphism of a flat proper equivalence relation

Helper module of the proof of
`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionStatement` (entry
module `Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionProof`),
written for the proof of scheme representability, with affine neighbourhoods, of the Picard
sheaf of pointed projective flat families with geometrically integral fibres over noetherian
rings. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.FlatEquivalenceRelation`. This is the first part of the
proof of Nitsure, *Construction of Hilbert and Quot schemes*
(`nitsure-2005-hilbert-quot-arxiv-math0504590v1`), Theorem 6.8 (proof pp.33–35), up to and
including property (***) on p.34.

**Ideal sheaves.**

- `ker_le_ker_iff_exists`: a morphism `g` factors through a closed immersion `e` exactly when
  `e.ker ≤ g.ker`.
- `comap_le_ker_iff`, `comap_eq_bot_iff`: `I.comap m ≤ g.ker ↔ I ≤ (g ≫ m).ker`.
- `le_of_forall_le_ker`: `I ≤ J` if every morphism whose kernel contains `J` has kernel
  containing `I`. Test with the closed subscheme of `J`.

**Base change.** `bc f sT sT' u hu : X ×_S T' ⟶ X ×_S T` is the map induced by `u : T' ⟶ T`
over `S` (written with Mathlib's `pullback.map`), with `bc_comp`, `bc_id`, `bc_congr`.

**Hilbert schemes.** `Classifier f`, for `f : X ⟶ S`, packages the first two clauses of
`HilbertSchemeUniversalFamilyStatement`. These are a scheme `H` with `πH : H ⟶ S` and an ideal
sheaf `W` on `X ×_S H` such that pulling back `W` along `bc` is a bijection. It maps the
morphisms `T ⟶ H` over `S` onto the ideal sheaves on `X ×_S T` whose closed subscheme is flat
and locally of finite presentation over `T` (fields `family` and `unique`). Then `D`, `ιD` and
`pD : D ⟶ H` denote the universal closed subscheme and its projection, which is flat and
locally of finite presentation (`flat_pD`, `locallyOfFinitePresentation_pD`), and proper when
`f` is (`isProper_pD`). `eq_of_comap_eq` is the uniqueness half.

**The family of an equivalence relation.** Let `i : Z ⟶ X` with `i ≫ f = p`, and
`s t : R ⟶ Z` with `s ≫ p = t ≫ p`. `Rel s t x y` is the relation
`∃ ρ, ρ ≫ s = x ∧ ρ ≫ t = y` of the statement.

- `family s t i hi h : R ⟶ X ×_S Z` is `r ↦ (i (t r), s r)`.
- `mono_family`: it is a monomorphism when `i` and `pullback.lift s t h` are.
  `isClosedImmersion_family`: it is then a closed immersion if moreover `f` is separated and
  `s` is proper. It is a proper monomorphism; use Mathlib's
  `IsClosedImmersion.iff_isProper_and_mono`.
- `subschemeι_ker_family`, `flat_ker_family`, `locallyOfFinitePresentation_ker_family`: its
  closed subscheme is `R` over `Z` through `s`. So it is flat, respectively locally of finite
  presentation, over `Z` when `s` is.

**The classifying morphism detects the relation.** Assume
`hW : C.W.comap (bc f C.πH p φ hφ) = (family s t i hi h).ker`, so that `φ : Z ⟶ H` classifies
the family. Assume also that `Rel s t` is an equivalence relation on `T`-points for every `T`
(`hEq`), and that `i` is a monomorphism.

- `famAt`, `comap_bc_comp`, `famAt_le_ker_iff`: the pullback of the family along `z : T ⟶ Z`
  is the pullback of `W` along `z ≫ φ`. A morphism `g` into `X ×_S T` has kernel containing it
  exactly when `g` comes from a point of `R`.
- `famAt_le_of_rel`: related points have comparable pulled-back families. Here the equivalence
  axioms are used.
- `rel_iff`: **`Rel s t x y ↔ x ≫ φ = y ≫ φ`** for all `T` and all `x y : T ⟶ Z`. This is
  Nitsure's property (***). For `→`, the pullbacks of the family along `x` and `y` agree, and
  `eq_of_comap_eq` applies. For `←`, the two pulled-back families agree. By reflexivity the
  point `(x ≫ i, 𝟙 T)` of `X ×_S T` lies in the family along `x`, so it lies in the family
  along `y`. This gives `Rel s t y x`, and symmetry gives the claim.
- `t_comp_eq_s_comp`: `t ≫ φ = s ≫ φ`.
- `graph₀`, `le_ker_graph₀`, `graph`, `graph_ιD`, `graph_pD`: the graph `(i, φ) : Z ⟶ X ×_S H`
  factors through the universal closed subscheme. This gives `graph : Z ⟶ D` over `H`.
- `exists_factor`: if `a : T ⟶ Z` and `b : T ⟶ D` lie over the same point of `H`, then
  `b = c ≫ t ≫ graph` for some `c : T ⟶ R` with `c ≫ s = a`. So every point of `Z ×_H D`
  comes from `R`.
