# Statement: deforming groups of multiplicative type over complete local rings

`Langlands.GroupScheme.MultiplicativeTypeCompleteLocalDeformationStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicates `RelativeMultiplicativeType.IsDiagonalizable` and
  `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1) and,
  transitively, the base-change functor `GroupScheme.baseChange`;
- Mathlib's `AlgebraicGeometry.Morphisms.Etale` and `AlgebraicGeometry.Morphisms.Finite`,
  for `Etale` and `IsFinite`;
- Mathlib's `RingTheory.AdicCompletion.Basic`, for `IsAdicComplete`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `f : H ⟶ G` in it is a homomorphism of
group schemes over `S`, with underlying morphism of schemes `f.hom.hom.left`. Inside the
definition the namespace `RelativeMultiplicativeType` is open, so `IsDiagonalizable` and
`IsMultiplicativeType` are the relative predicates, not the field-level ones.

## Objects and predicates used

- `A : Type u` is a commutative ring with `IsLocalRing A`, `IsNoetherianRing A` and
  `IsAdicComplete (IsLocalRing.maximalIdeal A) A`. Together these say that `A` is a
  complete local noetherian ring: `IsAdicComplete I A` (Mathlib) means that `A` is
  `I`-adically Hausdorff and every `I`-adic Cauchy sequence converges. Write `S = Spec A`.
- `sp := Spec.algebraMap A (IsLocalRing.ResidueField A)` is the morphism `Spec k ⟶ Spec A`
  of the closed point, where `k = IsLocalRing.ResidueField A`.
  `(GroupScheme.baseChange sp).obj G` is the special fibre `G_k`, and
  `(GroupScheme.baseChange sp).map f : H_k ⟶ G_k` is the special fibre `f_k` of `f`.
- `IsDiagonalizable H'`, for a group scheme `H'` over a scheme `S'`: `H'` is isomorphic, as
  a group scheme over `S'`, to the diagonalizable group `D_{S'}(Λ)` of a finitely generated
  abelian group `Λ`.
- `IsMultiplicativeType H'`: there is an fppf cover of the base (a jointly surjective family
  of flat morphisms locally of finite presentation) over each member of which `H'` becomes
  diagonalizable.
- `IsFinite p`, `Etale p` and `Surjective p`: the morphism of schemes `p` is finite, étale
  and surjective.

## Statement and quantifiers

The proposition quantifies over every complete local noetherian ring `A : Type u` as above
and all group schemes `G H` over `S = Spec A`, where `G → S` is affine
(`IsAffineHom G.X.hom`), locally of finite type and flat. It has two hypotheses:

1. **`H` splits over a finite étale cover.** There are a scheme `S'` and a finite, étale,
   surjective morphism `p : S' ⟶ S` such that the base change `H_{S'}` is diagonalizable.
2. **The special fibre of `G` is of multiplicative type.** `IsMultiplicativeType G_k`, for
   the relative predicate over `Spec k`.

The conclusion has two parts.

1. **Lifting and uniqueness.** For every homomorphism `f₀ : H_k ⟶ G_k` there is exactly
   one homomorphism `f : H ⟶ G` with `f_k = f₀`.
2. **Isomorphisms on the special fibre.** For every homomorphism `f : H ⟶ G` such that
   `f_k` is an isomorphism, the morphism of schemes underlying `f` is both an open immersion
   and a closed immersion.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Theorem B.3.2, p.288: "Let (A, m) be a complete local noetherian ring with residue field
  k, S = Spec A, G an affine S-group of finite type, and H an S-group of multiplicative
  type that splits over a finite étale cover of S. Let S_n = Spec A/m^{n+1}. … 2. If G is
  S-flat and the special fiber G₀ is of multiplicative type then the map
  Hom_{S-gp}(H, G) → Hom_{k-gp}(H₀, G₀) is bijective and any isomorphism j₀ : H₀ ≃ G₀
  uniquely lifts to an open and closed immersion j : H → G." The source adds that the
  splitting hypothesis is temporary, since it always holds by Proposition B.3.4, and that
  the flatness hypothesis in (2) cannot be dropped.
- Definition B.1.1, p.280, defines `S`-groups of multiplicative type and, in the following
  paragraph, split (diagonalizable) ones.

Conrad's proof (pp.288–290) uses Galois descent along the finite étale splitting cover to
reduce to `H = D_S(M)`, refers to the proof of SGA 3, IX, 7.1 for part (1) (this is the
reference in the Lean docstring), reduces bijectivity to Artin local rings by part (1), proves there
that `G` is itself diagonalizable using Corollary B.2.6 and the vanishing of Hochschild
cohomology, and for the open and closed immersion assertion uses the fibral flatness
criterion, Lemma B.1.3 and Nakayama's lemma on the torsion subgroups of the kernel. This is
explanation only.

## Derivation from the source

- **Complete local noetherian ring.** `(A, m)` is encoded by `IsLocalRing A`,
  `IsNoetherianRing A` and `IsAdicComplete (maximalIdeal A) A`. Completeness in the source
  includes the Hausdorff property, which `IsAdicComplete` contains.
- **`G`.** "An affine S-group of finite type" that is "S-flat" is `IsAffineHom G.X.hom`,
  `LocallyOfFiniteType G.X.hom` and `Flat G.X.hom`. An affine morphism is quasi-compact, so
  the first two together say that `G → S` is affine of finite type.
- **`H`.** "An S-group of multiplicative type that splits over a finite étale cover of S"
  is hypothesis 1. A finite étale cover is a finite, étale, surjective morphism
  `p : S' ⟶ S`, and `H` splits over it when `H_{S'}` is diagonalizable. This hypothesis
  already implies that `H` is of multiplicative type, because `p` alone is an fppf cover
  (finite étale morphisms are flat and of finite presentation), so the statement does not
  repeat `IsMultiplicativeType H`.
- **Special fibre.** "The special fiber G₀ is of multiplicative type" is hypothesis 2, with
  `G₀ = G_k` over `Spec k`. Over a field this uses the same relative Definition B.1.1.
- **Bijectivity.** "The map Hom_{S-gp}(H, G) → Hom_{k-gp}(H₀, G₀) is bijective" is part 1:
  the map is `f ↦ f_k`, and part 1 says every `f₀` has exactly one preimage.
- **Open and closed immersion.** "Any isomorphism j₀ : H₀ ≃ G₀ uniquely lifts to an open and
  closed immersion j : H → G": by part 1 the isomorphism `j₀` has exactly one lift `j`,
  and part 2 says that `j` is an open and closed immersion. Conversely, part 2 is the
  assertion of the source for the lift `j` of `j₀ = j_k`.

## Scope and omissions

`A` and all schemes are in universe `u`. The statement omits part (1) of Theorem B.3.2,
the bijectivity of `Hom_{S-gp}(H, G) → lim Hom_{S_n-gp}(H_{S_n}, G_{S_n})` for affine `G`
of finite type, which is used in the source to prove part (2). It also omits the
counterexample showing that flatness cannot be dropped.
