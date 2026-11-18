# Proof: linear reductivity is invariant under extension of the base field

`Langlands.GroupScheme.LinearReductivity.linearlyReductiveFieldExtension` proves
`Langlands.GroupScheme.LinearlyReductiveFieldExtensionStatement.{u}` (in
[`LinearlyReductiveFieldExtensionStatement`](LinearlyReductiveFieldExtensionStatement.md)). Its
type is exactly that statement, for every universe `u`, with no additional hypotheses.

Let `k` and `K` be fields with `[Algebra k K]`, and let `G` be a group scheme over `Spec k` with
affine structure morphism. Then `G` is linearly reductive iff its base change
`G_K = (GroupScheme.baseChange (Spec.map (algebraMap k K))).obj G` is linearly reductive. Here
"linearly reductive" is the `IsLinearlyReductive` condition of the statement. The proof uses
neither `[LocallyOfFiniteType G.X.hom]` nor any condition on `K / k`.

## Route

The proof does not follow Milne. Milne proves the descent direction (Remark 12.53(c), via
Proposition 4.19(a)) and the separable case of the other direction; the general case is
referred to the classification (footnote to Remark 12.53). Here, instead, both directions go
through the local integral criterion of the helper module
[`LinearlyReductiveIntegral`](LinearlyReductiveIntegral.md):

`linearlyReductive_iff_hasLocalRightIntegrals ψ`: for any affine presentation
`ψ : Spec B ≅ H.X` of a group `H` over a field, `H` is linearly reductive iff
`HasLocalRightIntegrals ψ`. That is, for every finite `T ⊆ B` there is a functional `r` with
`r 1 = 1` and `leftAct r y = r(y) • 1` for all `y ∈ T`.

Local right integrals transfer along `K / k` in both directions, for any field extension.

## The base-changed presentation

Fix a presentation `ψ : Spec B ≅ G.X` over `k`. Write `e` for its corepresentation
`corepresentableBy G ψ`, and `B_K = K ⊗[k] B`.

- `baseChangePresentation k K G ψ : Spec (K ⊗[k] B) ≅ G_K.X` over `Spec K`. It is the published
  `Descent.TensorCoordinates.baseChangeIso`, made an isomorphism over `Spec K` by
  `baseChangeIso_hom_snd`. Write `e_K` for its corepresentation.
- `affineBaseChangeEquiv_pt`: the published pullback comparison
  `Lie.affineBaseChangeEquiv k K G A` sends the point of `G_K` classified by a `K`-algebra map
  `f : K ⊗ B → A` to the point of `G` classified by `b ↦ f(1 ⊗ b)`. Here `A` is a `K`-algebra with
  compatible `k`-algebra structure. Both points are compared on underlying morphisms, using
  `affineBaseChangeEquiv_left` and `baseChangeIso_hom_fst`.
- `comul_baseChange_comp_includeRight`: for `b ∈ B`, `comul e_K (1 ⊗ b)` is the image of
  `comul e b` under the `k`-algebra map `B ⊗ B → B_K ⊗[K] B_K`, `x ⊗ y ↦ (1 ⊗ x) ⊗ (1 ⊗ y)`.
  Both sides are `k`-algebra maps `B → C := B_K ⊗[K] B_K`, so it suffices that they classify the
  same point of `G` over `C` (published `pt_injective`). The left side classifies the image under
  `affineBaseChangeEquiv` of the point classified by `comul e_K`. That point is the product of the two universal
  points over `C` (published `pt_comul`). `affineBaseChangeEquiv` is multiplicative, and by
  `affineBaseChangeEquiv_pt` it sends the two universal points to the points classified by
  `x ↦ (1 ⊗ x) ⊗ 1` and `x ↦ 1 ⊗ (1 ⊗ x)`. Their product is classified by the right side
  (published `pt_productMap_comp_comul`). The `k`-algebra structure on `C` is the one Mathlib
  provides for tensor products.
- `contract_comul_baseChange`: for a `K`-linear functional `g` on `B_K` and `b ∈ B`,
  `contract g (comul e_K (1 ⊗ b)) = (g₀ ⊗ id)(comul e b)` in `K ⊗[k] B`, where
  `g₀(x) = g(1 ⊗ x)`. This is the previous item followed by
  `(1 ⊗ x) ⊗ (1 ⊗ y) ↦ g(1 ⊗ x) • (1 ⊗ y) = g(1 ⊗ x) ⊗ y`, checked on pure tensors. Recall
  `leftAct g = contract g ∘ comul e_K`.

## From `k` to `K`

`hasLocalRightIntegrals_baseChange : HasLocalRightIntegrals ψ →
HasLocalRightIntegrals (baseChangePresentation k K G ψ)`.

Let `T ⊆ K ⊗ B` be finite. Each `y ∈ K ⊗ B` lies in the `K`-span of finitely many `1 ⊗ b`,
for `b` in a finite set `S(y)` (`exists_finset_mem_span`, by induction on tensors and
`c ⊗ b = c • (1 ⊗ b)`). Take `r` from `HasLocalRightIntegrals ψ` for the finite set
`⋃_{y ∈ T} S(y)`, and let `r_K = LinearMap.liftBaseChange K (algebraMap ∘ r)`, the
`K`-linear extension `c ⊗ b ↦ c · r(b)`.

- `r_K(1) = r_K(1 ⊗ 1) = r(1) = 1`.
- For `b` in the union, `contract_comul_baseChange` gives
  `leftAct r_K (1 ⊗ b) = (algebraMap ∘ r ⊗ id)(comul e b) = 1 ⊗ contract r (comul e b)`.
  This equals `1 ⊗ leftAct r b = 1 ⊗ (r(b) • 1) = r_K(1 ⊗ b) • 1`.
- Both sides of `leftAct r_K y = r_K(y) • 1` are `K`-linear in `y`. So the identity extends
  from the generators `1 ⊗ b`, `b ∈ S(y)`, to `y` (`Submodule.span_induction`).

## From `K` to `k`

`hasLocalRightIntegrals_of_baseChange :
HasLocalRightIntegrals (baseChangePresentation k K G ψ) → HasLocalRightIntegrals ψ`.

Choose a `k`-linear `φ : K → k` with `φ(1) = 1` (`Module.Projective.exists_dual_eq_one`, as `K`
is a free `k`-module and `1 ≠ 0`). Let `T ⊆ B` be finite. Take `g` from the hypothesis for the
finite set `{1 ⊗ b : b ∈ T}`, and put `r = φ ∘ g₀`, that is `r(x) = φ(g(1 ⊗ x))`.

- `r(1) = φ(g(1 ⊗ 1)) = φ(1) = 1`.
- Let `π : K ⊗[k] B → B` be the `k`-linear map `c ⊗ x ↦ φ(c) • x`. On pure tensors,
  `π ∘ (g₀ ⊗ id) = contract r`.
- For `b ∈ T`, `contract_comul_baseChange` and the integral property of `g` give
  `(g₀ ⊗ id)(comul e b) = leftAct g (1 ⊗ b) = g(1 ⊗ b) • 1 = g(1 ⊗ b) ⊗ 1`.
  Applying `π`: `leftAct r b = contract r (comul e b) = φ(g(1 ⊗ b)) • 1 = r(b) • 1`.

## The theorem

`linearlyReductiveFieldExtension`. After introducing `k`, `K`, `G` and the instances, the local
predicate `IsLinearlyReductive` of the statement is, by definition, `∀ N ρ, sSup (simpleStable ρ) = ⊤`
for `G` and for `G_K` (`change`). The criterion with the presentation `Lie.coordinateIso G` of
`G` (which uses `[IsAffineHom G.X.hom]`) and with
`baseChangePresentation k K G (Lie.coordinateIso G)` of `G_K` turns both sides into
`HasLocalRightIntegrals`. The two transfer results above prove the equivalence.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Lean notes

Several lemmas are elaborated with `set_option backward.isDefEq.respectTransparency false in`.
This is needed to identify the point types `Lie.AffinePoints G_K A` and the values of the
affine point functor, and the carriers of `CommAlgCat.of K (K ⊗[k] B)` with `K ⊗[k] B`. The
published `Lie.BaseChange` and `Descent.TensorCoordinates` modules set the same option.
