# Statement: extensions of groups of multiplicative type over a field

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeFieldExtensionStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.MultiplicativeType`](MultiplicativeType.md), for the field-level predicate
  `IsMultiplicativeType` and, through it, the diagonalizable groups
  `Diagonalizable.groupScheme`;
- [`Torus.Split`](Split.md), for `IsSplitTorus`;
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for the fppf quotient predicate `RelativeRoot.IsFppfQuotient`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `i : H ⟶ G` in it is a homomorphism of
group schemes over `S`. Its underlying morphism of `S`-schemes is `i.hom.hom : H.X ⟶ G.X`,
and `G.X.left` is the underlying scheme of `G`.

## Lean statement

```lean
def MultiplicativeTypeFieldExtensionStatement : Prop :=
  ∀ (k : Type u) [Field k] (H G K : GroupScheme (Spec (CommRingCat.of k)))
    (i : H ⟶ G) (p : G ⟶ K),
    Mono i.hom.hom → RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p →
      (IsMultiplicativeType H → IsMultiplicativeType K →
          (IsCommMonObj G.X ∨ ConnectedSpace K.X.left) → IsMultiplicativeType G) ∧
        ((∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
            Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)) →
          IsSplitTorus K →
          ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
            Nonempty (G ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp))
```

## Predicates used

- `IsMultiplicativeType H` (field level, module `Langlands.GroupScheme.Torus.MultiplicativeType`):
  there are a field `K₀ : Type u`, an algebra `k → K₀`, a finitely generated abelian group
  `Λ₀ : Type u` and an isomorphism of group schemes over `Spec K₀` from the base change of
  `H` onto `Diagonalizable.groupScheme (CommRingCat.of K₀) Λ₀`, the diagonalizable group
  `D_{K₀}(Λ₀) = Spec K₀[Λ₀]`. Such an `H` is affine and of finite type over `k`, because
  these properties descend along `Spec K₀ ⟶ Spec k`.
- `Diagonalizable.groupScheme (CommRingCat.of k) Λ`: the diagonalizable group `D_k(Λ)` over
  `k`, an object of `CommGroupScheme`; `.toGrp` is its underlying group scheme.
- `IsSplitTorus K`: `K` is isomorphic, as a group scheme over `Spec k`, to the split torus
  `splitTorus (Spec k) I = G_m^I` for a finite index type `I`.
- `SubgroupFunctor.range i`: the subgroup functor of `G` whose `T`-points are the
  `T`-points of `G` that factor through `i`.
- `RelativeRoot.IsFppfQuotient N p` for `p : G ⟶ K`: the morphism `p.hom.hom.left` is flat,
  surjective and locally of finite presentation, and the subgroup functor of points of the
  scheme-theoretic kernel `kernel p` is exactly `N`.
- `IsCommMonObj G.X`: the multiplication of `G` is commutative, that is, `G` is a
  commutative group scheme.
- `ConnectedSpace K.X.left`: the underlying topological space of `K` is connected.

## Statement and quantifiers

The proposition quantifies over a field `k : Type u`, group schemes `H`, `G`, `K` over
`Spec k`, and homomorphisms `i : H ⟶ G` and `p : G ⟶ K` such that `i.hom.hom` is a
monomorphism and `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p` holds. Its
conclusion is the conjunction of two parts.

1. If `H` and `K` are of multiplicative type, and `G` is commutative or `K` is connected,
   then `G` is of multiplicative type.
2. If `H` is isomorphic to `D_k(Λ)` for a finitely generated abelian group `Λ : Type u` and
   `K` is a split torus, then `G` is isomorphic to `D_k(Λ')` for a finitely generated
   abelian group `Λ' : Type u`.

No hypothesis is placed on `G` beyond the two exactness conditions; in particular `G` is
not assumed to be affine or of finite type.

## Source

A. Grothendieck, *Exposé IX. Groupes de type multiplicatif : homomorphismes dans un schéma
en groupes*, SGA 3, Tome II, Lecture Notes in Mathematics 152, recomposed annotated edition
by P. Gille and P. Polo (provisional version of 8 November 2009). It is registered as
`sga3-expose-ix-gille-polo-2009`, file
`Grothendieck - SGA 3 Expose IX, Groupes de type multiplicatif, homomorphismes dans un schema en groupes (Gille-Polo recomposed edition, vers.pdf`
(SHA-256 `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). Page numbers
are the recomposed page numbers, with the original LNM 152 margin numbers in parentheses.

- Proposition 8.2, p.61 (margin 75): "Soient k un corps, H, K des k-schémas en groupes de
  type multiplicatif et de type fini, et G un k-schéma en groupes tel que l'on ait une
  suite exacte 1 → H → G → K → 1 (ce qui entraîne que G est de type fini sur k).
  (i) Si on suppose G commutatif ou K connexe, alors G est de type multiplicatif.
  (ii) Si K et H sont diagonalisables, K étant un tore, alors G est diagonalisable."
- The proof (pp.61–62, margin 75–76) refers to XVII 7.1.1 for (i). For (ii) it first gets
  that `G` is of multiplicative type from (i), since a torus is connected. It then
  classifies the extensions of `K ≃ D_k(M)` by `H ≃ D_k(N)` that become diagonalizable
  over a separable closure `k_s` by `H¹(Γ, L) = Hom_cont(Γ, L)`, where
  `Γ = Gal(k_s / k)` and `L = Hom(N, M)`. When `K` is a torus, `M` and hence `L` are
  torsion-free, so this group is zero and the extension is diagonalizable. This is
  explanation only.
- Remarque 8.3, p.62 (margin 76), notes that (i) holds over any base (XVII 7.1.1) and that
  (ii) extends to integral normal bases. Neither generalization is stated here.

James S. Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers.

- Corollary 12.22, p.239: "An extension of algebraic groups of multiplicative type is of
  multiplicative type if and only if it is commutative."
- Corollary 12.42, p.244: "An extension of algebraic groups of multiplicative type is of
  multiplicative type if it is connected."
- Example 12.10, p.234, gives the group of monomial `2 × 2` matrices, an extension
  `e → D₂ → G → S₂ → e` of diagonalizable groups that is not commutative and hence not
  diagonalizable. Here `K = S₂` is not connected, so this example does not contradict
  part 1; it shows that part 1 needs its alternative hypothesis.

Milne's two corollaries are the commutative case of part 1 and a special case of its
connected case (a connected `G` has connected quotient `K`). They support part 1 but are
not its source.

## Derivation from the source

- **Short exact sequence.** Exactness of `1 → H → G → K → 1` of `k`-group schemes means
  that `H → G` is a monomorphism identifying `H` with the kernel of `G → K`, and that
  `G → K` is an fppf surjection. The statement encodes this as `Mono i.hom.hom` together
  with `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p`, as in the published
  [`Torus.CentralExtensionStatement`](CentralExtensionStatement.md) and other Library
  statements. The source's remark that `G` is then of finite type over `k` is not a
  hypothesis.
- **Multiplicative type and finite type.** The source assumes `H` and `K` of
  multiplicative type and of finite type. The Library's `IsMultiplicativeType` (a
  finitely generated diagonalizable model over some field extension) is the field case of
  this notion: over a field a group of multiplicative type and of finite type is
  diagonalizable over a finite separable extension with finitely generated character
  group (SGA 3 X 1.4; Milne, Corollary 12.19, p.238), and conversely such a model forces
  finite type.
- **Commutative, connected.** "G commutatif" is `IsCommMonObj G.X`; "K connexe" is
  `ConnectedSpace K.X.left`.
- **Diagonalizable, torus.** Over the field `k`, "diagonalisable" means isomorphic to
  `D_k(M)` for an abelian group `M`, which is finitely generated for a group of finite
  type; the statement takes the isomorphism to `Diagonalizable.groupScheme` with `Λ`
  finitely generated, both in the hypothesis on `H` and in the conclusion on `G`. "K
  diagonalisable, K étant un tore" means `K ≃ D_k(M)` with `M` free of finite rank, that
  is `K ≃ G_m^n`, which is `IsSplitTorus K`.
- **Universes.** The character groups `Λ` are in the universe `u` of `k`, as in
  `IsMultiplicativeType`.

## Related Library results

- `IsMultiplicativeType.of_isClosedSubgroup`
  ([`Torus.MultiplicativeTypeSubgroups`](MultiplicativeTypeSubgroups.md)) and
  `IsMultiplicativeType.of_fppfHom`
  ([`Torus.MultiplicativeTypeQuotients`](MultiplicativeTypeQuotients.md)) prove the other
  direction over a field (SGA 3 IX 8.1): closed subgroups and fppf quotients of a group of
  multiplicative type are of multiplicative type.
- `CentralTorusExtensionStatement`
  ([`Torus.CentralExtensionStatement`](CentralExtensionStatement.md)) states that a central
  extension of a torus by a torus is a torus. It has a different conclusion (a torus) and
  different hypotheses (tori, central kernel).
