# The smooth contragredient is self-adjoint on the right

Module `Langlands.Representation.Category.ContragredientAdjunction`.

## Lemma I.4.2.1

Renard 2026, Lemma I.4.2.1 (printed p.24, PDF p.30), states that for nondegenerate modules
`V` and `W`, `Hom(V, W~) → Hom(W, V~)`, `φ ↦ ψ` with `ψ(w)(v) = φ(v)(w)`, is a natural
isomorphism. Renard states it for modules over an algebra with idempotents. The Lean
version works directly with smooth representations `SmoothRep.{uR, uG, max uR uV} R G` and
the Library's smooth contragredient functor `contragredientFunctor : Cᵒᵖ ⥤ C`. The carrier
universe `max uR uV` contains the coefficient universe, so the smooth dual stays in the
same category.

Namespace `Langlands.SmoothRep`:

- `bidualHom A : A ⟶ A~~`: the Library's evaluation map `smoothBidual`, packaged as a
  morphism.
- `smoothDualPairing_bidualHom`: `⟨bidualHom A a, ℓ⟩ = ⟨ℓ, a⟩`. This holds by `rfl`.
- `bidualHom_naturality`: `f ≫ bidualHom B = bidualHom A ≫ f~~`. This is the Library's
  `smoothBidual_natural`.
- `bidualHom_contragredient_comp`: `bidualHom A~ ≫ (bidualHom A)~ = 𝟙 A~`. This holds by
  extensionality and `rfl`.
- `bidualTransformation : 𝟭 ⟶ D.rightOp ⋙ D` and
  `bidualCotransformation : D ⋙ D.rightOp ⟶ 𝟭`: bidual evaluation and its opposite.
- `contragredientAdjunction : D.rightOp ⊣ D`. The unit is `bidualTransformation` and the
  counit is `bidualCotransformation`. Both triangle identities are
  `bidualHom_contragredient_comp`. The structure fields are given directly.
- `contragredientAdjunction_homEquiv_apply`: the hom equivalence is Renard's
  transposition, `⟨(homEquiv f) b, a⟩ = ⟨f a, b⟩` (by `rfl`). So this adjunction is
  Lemma I.4.2.1 in categorical form.

## The bidual copresentation

The rest of the module concerns smooth complex representations `SmoothRep.{0, uG, uV} ℂ G`
of a group in which compact open subgroups are cofinal (`hG : CompactOpenCofinal G`). In
VI.9.6 (printed p.202, PDF p.208) Renard writes the exact sequence
`0 → π → π~~ → π₁~~`, where `π₁` is the cokernel of `π → π~~`. These declarations build
that sequence.

- `bidualHom_injective`, `mono_bidualHom`: with `hG`, bidual evaluation is injective. This
  is the Library's `smoothBidual_injective_of_compact_cofinal`.
- `bidualCopresentationMap A : A~~ ⟶ (cokernel (bidualHom A))~~`: the projection onto the
  Library's concrete quotient `SmoothRep.cokernel`, followed by bidual evaluation of the
  quotient.
- `bidualHom_comp_bidualCopresentationMap`: the composite of the two maps is zero.
- `bidualCopresentationIsLimit hG A`: `A` is a kernel of `bidualCopresentationMap A`. This
  is `isLimitCokernelπComp` applied to the two injective bidual evaluations.
