# Statement: lifting homomorphisms from groups of multiplicative type over complete local rings

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeCompleteLocalLiftStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1)
  and, transitively, the base-change functor `GroupScheme.baseChange`;
- [`Reductive.Basic`](../Reductive/Basic.md), for `IsClosedSubgroup`;
- [`InnerAutomorphism`](../InnerAutomorphism.md), for `GroupScheme.constantPoint` and
  `GroupScheme.innerIso`;
- Mathlib's `Mathlib.RingTheory.AdicCompletion.Basic`, for `IsAdicComplete`.

`GroupScheme S` is `Grp (Over S)`. The scoped notation of `CategoryTheory.MonObj` is open,
so for `T : Over S` the set of points `T ⟶ G.X` carries the group structure induced by the
group law of `G`, and `1` is its unit.

## Objects and predicates used

- `A : Type u` is a commutative ring with `IsLocalRing A`, `IsNoetherianRing A` and
  `IsAdicComplete (IsLocalRing.maximalIdeal A) A`. Together these say that `A` is a
  complete local noetherian ring: `IsAdicComplete I A` (Mathlib) means that `A` is
  `I`-adically Hausdorff and every `I`-adic Cauchy sequence converges. Write `S = Spec A`.
- `sp := Spec.algebraMap A (IsLocalRing.ResidueField A)` is the morphism
  `Spec k ⟶ Spec A` of the closed point, where `k = IsLocalRing.ResidueField A`.
- `(GroupScheme.baseChange sp).obj G` is the special fibre `G_k`, with the induced group
  law, and `(GroupScheme.baseChange sp).map f : H_k ⟶ G_k` is the special fibre `f_k` of a
  homomorphism `f : H ⟶ G`.
- `IsMultiplicativeType H`: there is an fppf cover of `S` (a jointly surjective family of
  flat morphisms locally of finite presentation) over each member of which `H` becomes
  isomorphic to `D(Λ)` for a finitely generated abelian group `Λ`.
- A point `g : Over.mk (𝟙 S) ⟶ G.X` is an element of `G(S)`.
  `G.constantPoint g (Over.mk sp)` is its pullback `Spec k ⟶ S ⟶ G` along `sp`, that is,
  the image of `g` in `G(k)`. The equation `G.constantPoint g (Over.mk sp) = 1` therefore
  says that `g` lies in `ker(G(S) → G(k))`.
- `G.innerIso g : G ≅ G` is the inner automorphism `int(g)`; on `T`-points it is
  `x ↦ g_T x g_T⁻¹` (`comp_innerIso_hom`). Hence `f ≫ (G.innerIso g).hom` is the
  homomorphism `int(g) ∘ f`.
- `IsClosedSubgroup f` means that the morphism of schemes underlying `f` is a closed
  immersion.

## Statement and quantifiers

For every complete local noetherian ring `A : Type u` as above, every smooth affine group
scheme `G` over `S = Spec A` (`Smooth G.X.hom`, `IsAffineHom G.X.hom`) and every group
scheme `H` over `S` with `IsMultiplicativeType H`, the following three assertions hold.

1. **Existence of lifts.** For every group-scheme homomorphism `f₀ : H_k ⟶ G_k` there is a
   group-scheme homomorphism `f : H ⟶ G` with `f_k = f₀`.
2. **Conjugacy of lifts.** For all homomorphisms `f, f' : H ⟶ G` with `f_k = f'_k`, there
   is `g ∈ G(S)` whose image in `G(k)` is `1` such that `f' = int(g) ∘ f`.
3. **Closed immersions.** For every homomorphism `f : H ⟶ G`, if `f_k` is a closed
   immersion then `f` is a closed immersion.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Corollary B.3.5, p.292: "Let S = Spec A for a complete local noetherian ring (A, m) with
  residue field k. Let G be a smooth affine S-group and H an S-group of multiplicative type.
  Any homomorphism f₀ : H₀ → G₀ between special fibers lifts to an S-homomorphism
  f : H → G, and if f′ : H → G is another such lift then f and f′ are conjugate under
  ker(G(S) → G(k)). Moreover, if f₀ is a closed immersion then so is any such f." Conrad
  notes that this is a special case of SGA3 IX 7.3.
- Definition B.1.1, p.280, defines S-groups of multiplicative type.

Conrad's proof (pp.292–293) uses `G(S) = lim G(S_n)` for the infinitesimal neighbourhoods
`S_n = Spec A/m^{n+1}`, the bijectivity of (B.3.1) for groups of multiplicative type
(Proposition B.3.4), and the vanishing of Hochschild cohomology of groups of multiplicative
type (Remark B.2.4, Corollary B.2.6) to lift step by step and to control the conjugacy of
lifts. For the closed immersion assertion it reduces to `ker f = 1` (Lemma B.1.3), then by
Nakayama to triviality of the kernel on fibres, and handles non-closed points by a complete
discrete valuation ring and Corollary B.3.3. This is explanation only.

## Derivation from the source

- **Complete local noetherian ring.** `(A, m)` is encoded by `IsLocalRing A`,
  `IsNoetherianRing A` and `IsAdicComplete (maximalIdeal A) A`. Completeness in the source
  includes the Hausdorff property, which `IsAdicComplete` contains.
- **Special fibres.** "Special fibers" `H₀, G₀` are the base changes along the closed point
  `Spec k ⟶ Spec A`, here `sp`; `f₀ = f_k` is expressed by
  `(GroupScheme.baseChange sp).map f = f₀`.
- **Existence.** "Any homomorphism f₀ … lifts to an S-homomorphism f" is part 1.
- **Conjugacy.** "If f′ is another such lift then f and f′ are conjugate under
  ker(G(S) → G(k))": two lifts of the same `f₀` are exactly two homomorphisms with equal
  special fibres, which is the hypothesis of part 2. Conjugate under the subgroup
  `ker(G(S) → G(k))` means `f' = int(g) ∘ f` for some `g` in that kernel. Membership in the
  kernel is `G.constantPoint g (Over.mk sp) = 1`. Since the kernel is a subgroup, the choice
  of direction (`f' = int(g) ∘ f` rather than `f = int(g) ∘ f'`) does not matter.
- **Closed immersions.** "If f₀ is a closed immersion then so is any such f" is part 3. A
  homomorphism `f` with `f_k` a closed immersion is a lift of `f₀ = f_k`, so quantifying
  over all `f` covers "any such f".

## Scope and omissions

`A` and all schemes are in universe `u`. Nothing beyond the source's hypotheses is assumed:
`G` is smooth and affine over `S` and `H` is of multiplicative type; no connectedness,
reductivity or splitting hypothesis is imposed. The statement does not assert uniqueness
of `g` in part 2, and the source does not claim it.

## Related Library statements

- `RelativeSplitTorusLiftingStatement` ([`Torus.RelativeLiftingStatement`](RelativeLiftingStatement.md))
  lifts a split torus in a residue fibre to an étale neighbourhood (Conrad, Proposition
  3.1.6). The present statement lifts homomorphisms from an arbitrary group of
  multiplicative type over a complete local base, without passing to an étale
  neighbourhood.
