# The analytic relation of affine test points of a presheaf

Let `K` be a complete ultrametric nontrivially normed field and `F` a presheaf on
`K`-schemes. For affine test points `u : Spec A → F`, `v : Spec B → F`, a model
`M : ExistenceReduction.TestModel u v` is a finitely presented `K`-algebra `C` with a finite
polynomial presentation `M.R` and maps `M.f : A → C`, `M.g : B → C` such that
`Spec C` represents `Spec A ×_F Spec B` in the presheaf category on all `K`-schemes.

The definition `ExistenceReduction.TestModel.ARel M P Q α β` (namespace
`Langlands.Analytic.SpaceAnalytification`) says that two analytic maps
`α : T ⟶ Spec(A)ᵃⁿ` and `β : T ⟶ Spec(B)ᵃⁿ` (for presentations `P`, `Q`, in the Library's
localized category) factor jointly through `Spec(C)ᵃⁿ`: there is `t : T ⟶ Spec(C)ᵃⁿ` with
`t ≫ (M.f)ᵃⁿ = α` and `t ≫ (M.g)ᵃⁿ = β`.

The module proves:

- `ChartQuotient.lhom_comp` and `lhom_id` give functoriality of `localizedHom` from
  `affineAnalytificationLocalizedFunctoriality`. The lemma `lhom_isPullback` sends a
  presheaf pullback of affine representables over an affine representable base to an
  analytic pullback. The coordinate algebras form a tensor-product pushout. The proof
  uses `isPullback_localizedHom_of_isPullback_ty`.
- `ARel.comp`: the relation is stable under precomposition.
- `ARel.symm`: `M.ARel P Q α β` gives `M.flip.ARel Q P β α`.
- `aRel_localizedHom`: analytifications of algebra maps `φ : A → E`, `ψ : B → E` with
  `ty φ ≫ u = ty ψ ≫ v` are related.
- `aRel_refl`: for a model of `Spec A ×_F Spec A`, every `α` is related to itself (through the
  analytified diagonal).
- `jointly_mono`: the two analytified projections of a model are jointly monic.
- `ARel.trans`: relations through models of `u, v` and of `v, w` compose to a relation through
  any model of `u, w`.
- `ARel.of_model`: the relation does not depend on the model.

## Proof

- `aRel_localizedHom`: the universal property of `M` (`TestModel.exists_lift`) gives
  `k : C → E` with `k ∘ M.f = φ` and `k ∘ M.g = ψ`; take `t = kᵃⁿ`.
- `aRel_refl`: apply `exists_lift` to `id, id` to get the diagonal `μ : C → A`; then
  `t = α ≫ μᵃⁿ` works by `lhom_comp` and `lhom_id`.
- `jointly_mono`: let `N` be the chosen model of `Spec A ×_{Spec K} Spec B`
  (`testModel` along `Algebra.ofId`), and `k : N.C → C` the map induced by `M.f, M.g`. The
  morphism `ty k` is a monomorphism of presheaves, since `M` is a pullback, so its kernel pair
  is the identity square; analytification keeps it a pullback square (`lhom_isPullback`).
  Two maps `l, m` with equal composites to `Spec(A)ᵃⁿ` and `Spec(B)ᵃⁿ` have equal composites
  with `kᵃⁿ` (they agree after both projections of the analytified product square of `N`),
  so they factor through the kernel pair, which is the identity, and `l = m`.
- `ARel.trans`: from `t₁ : T ⟶ Spec(C₁)ᵃⁿ` and `t₂ : T ⟶ Spec(C₂)ᵃⁿ` agreeing on
  `Spec(B)ᵃⁿ`, the analytified pullback square of the chosen model `N` of
  `Spec C₁ ×_{Spec B} Spec C₂` gives `t : T ⟶ Spec(N.C)ᵃⁿ`; the universal property of `M₃`
  gives `k : C₃ → N.C` compatible with the outer projections, and `t ≫ kᵃⁿ` relates `α` and
  `γ`.
- `ARel.of_model`: the universal property of `M'` gives `k : C' → C` over `A` and `B`;
  compose `t` with `kᵃⁿ`.

## Provenance

Derived. For an étale chart `U → X` of an algebraic space, the relation `R = U ×_X U` and the
analytic equivalence relation `Rᵃⁿ ⇉ Uᵃⁿ` are those of Conrad–Temkin, *Non-archimedean
analytification of algebraic spaces* (2009), §4.2, the paragraph after Theorem 4.2.1, p.20
(`conrad-temkin-2009-nonarchimedean-analytification`); the module states the reflexivity,
symmetry and transitivity of this relation on morphisms from test spaces, with the fibre
products of affine test points represented by the Library's finite polynomial models
(`ExistenceReduction.TestModel`).
