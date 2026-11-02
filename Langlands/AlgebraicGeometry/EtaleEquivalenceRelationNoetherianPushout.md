# A Noetherian ring presentation of an affine quotient

Authors: Worker 1110.

This helper module proves one theorem,
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.exists_fg_pushout_of_hasAffineQuotient`.
It uses the published definitions of `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`
unchanged (`EtaleEquivalenceRelation`, `HasAffineQuotient`), the two helper modules
`Langlands.AlgebraicGeometry.EtaleFaithfullyFlatNoetherianDescent` (theorem
`exists_subalgebra_fg_etale_faithfullyFlat`) and
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationKernelPair` (theorem
`CommRingCat.isPushout_of_bijective`), and Mathlib (pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`). Its proof depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Statement

```lean
theorem exists_fg_pushout_of_hasAffineQuotient (E : EtaleEquivalenceRelation.{u})
    [IsAffine E.U] [IsAffine E.R] (hq : E.HasAffineQuotient) :
    ∃ (A₁ B₁ : Type u) (_ : CommRing A₁) (_ : CommRing B₁) (_ : Algebra A₁ B₁),
      Algebra.FiniteType ℤ A₁ ∧ Algebra.FiniteType ℤ B₁ ∧ Algebra.Etale A₁ B₁ ∧
        Module.FaithfullyFlat A₁ B₁ ∧
      ∃ (φ : B₁ →+* Γ(E.U, ⊤)),
        letI : Algebra A₁ Γ(E.U, ⊤) := (φ.comp (algebraMap A₁ B₁)).toAlgebra
        ∃ F : B₁ ⊗[A₁] Γ(E.U, ⊤) →+* Γ(E.R, ⊤),
          (∀ b d, F (b ⊗ₜ d) = E.t.appTop (φ b) * E.s.appTop d) ∧ Function.Bijective F
```

In words: let `E` be an étale equivalence relation `t, s : R ⇉ U` with `U` and `R` affine that
has an affine quotient. Then there are a ring `A₁` of finite type over `ℤ` (so Noetherian), an
étale and faithfully flat `A₁`-algebra `B₁`, also of finite type over `ℤ`, and a ring map
`φ : B₁ → Γ(U)` with the following property. Make `Γ(U)` an `A₁`-algebra through
`A₁ → B₁ → Γ(U)`. Then the ring map `B₁ ⊗[A₁] Γ(U) → Γ(R)`, `b ⊗ d ↦ t*(φ b) · s*(d)`, is
bijective. So `R` is the fibre product `Spec B₁ ×_{Spec A₁} U`, with `t` and `s` as the two
projections.

## Provenance

The statement is a derived helper for the proof of
`EtaleEquivalenceRelationNoetherianCoverLevelStatement`. Its role is to put a relation with an
affine quotient into the ring-level shape that the cartesian criterion
`hasAffineQuotient_of_bijective` of `EtaleEquivalenceRelationKernelPair` accepts. The
underlying facts are standard. An étale relation with affine quotient `M` is the kernel pair
of `U → M` (part of the definition of `HasAffineQuotient`). The quotient map is étale by fpqc
descent of étaleness, which is used here only through Mathlib's descent results for étale
morphisms (`Mathlib/AlgebraicGeometry/Morphisms/LocalFlatDescent.lean`). The étale, faithfully
flat algebra `Γ(M) → Γ(U)` is defined over a finitely generated subring of `Γ(M)` by
`exists_subalgebra_fg_etale_faithfullyFlat` (see that module's Markdown for its provenance).

## The implemented proof

Let `q : U ⟶ M` be the affine quotient, with `IsPullback E.t E.s q q`, `q` flat, locally of
finite presentation and surjective, and `M` affine.

1. `q` is étale. Étaleness descends along surjective, flat, quasi-compact morphisms (Mathlib
   instance `DescendsAlong @Etale (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` in
   `LocalFlatDescent.lean`, used through `MorphismProperty.of_isPullback_of_descendsAlong`). It
   is applied to the pullback square
   `IsPullback E.t E.s q q`: the base change `E.t` of `q` along `q` is étale, and `q` is
   surjective, flat and quasi-compact (quasi-compact because `U` is affine and `M` is affine,
   hence separated).
2. Ring level. Since `U` and `M` are affine, `q.appTop : Γ(M) → Γ(U)` is étale
   (`HasRingHomProperty.iff_of_isAffine`) and faithfully flat
   (`Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`). These give the instances
   `Algebra.Etale Γ(M) Γ(U)` and `Module.FaithfullyFlat Γ(M) Γ(U)` for the algebra structure
   `q.appTop.hom.toAlgebra`.
3. Noetherian descent. `exists_subalgebra_fg_etale_faithfullyFlat ℤ` gives a finitely
   generated subring `A₁ ⊆ Γ(M)`, an étale, faithfully flat `A₁`-algebra `B₁` and
   `e : Γ(U) ≃ₐ[Γ(M)] Γ(M) ⊗[A₁] B₁`. `A₁` is of finite type over `ℤ` by
   `Subalgebra.fg_iff_finiteType`, and `B₁` by `Algebra.FiniteType.trans` (étale algebras are
   of finite type).
4. The map `φ`. Put `φ = e.symm ∘ includeRight : B₁ → Γ(M) ⊗[A₁] B₁ → Γ(U)`.
5. First pushout square. The square `A₁ → B₁`, `A₁ → Γ(M)`, `φ : B₁ → Γ(U)`,
   `q.appTop : Γ(M) → Γ(U)` is a pushout of commutative rings. It is the flip of
   `CommRingCat.isPushout_of_bijective` applied to `q.appTop`, `φ` and the bijective map
   `e.symm`. The required identity `e.symm (a ⊗ b) = q.appTop a · φ b` follows from
   `a ⊗ b = a • (1 ⊗ b)` and the `Γ(M)`-linearity of `e.symm`.
6. Second pushout square. Mathlib's `isPushout_appTop_of_isPullback` turns the pullback square
   `IsPullback E.t E.s q q` of affine schemes into a pushout square of global sections
   `q.appTop, q.appTop, E.t.appTop, E.s.appTop`. Pasting the first square onto it vertically
   (`IsPushout.paste_vert`) shows that the square `A₁ → B₁`, `A₁ → Γ(U)`,
   `φ ≫ E.t.appTop`, `E.s.appTop` is a pushout.
7. Comparison with the tensor product. With `Γ(U)` an `A₁`-algebra through `φ ∘ algebraMap`,
   Mathlib's `CommRingCat.isPushout_tensorProduct A₁ B₁ Γ(U)` is another pushout of the same
   span: its map `A₁ → Γ(U)` equals `A₁ → Γ(M) → Γ(U)` by the commutativity of the first
   square. The comparison isomorphism `IsPushout.isoIsPushout` gives
   `F : B₁ ⊗[A₁] Γ(U) → Γ(R)`, bijective because it underlies an isomorphism of rings
   (`commRingCatIsoToRingEquiv`). The formula `F (b ⊗ d) = t*(φ b) · s*(d)` follows from
   `b ⊗ d = (b ⊗ 1) · (1 ⊗ d)` and the two identities `inl_isoIsPushout_hom` and
   `inr_isoIsPushout_hom`.
