# Affine fibre squares in presheaf-model form

This conditional derivation takes `AffineAnalytificationFibreProductStatement`
(Task 7168) and `AffineAnalytificationLocalizedFunctorialityStatement` (Task 7119)
as hypotheses. `AffineAnalytificationLocalizedFunctorialityProof` supplies the
second hypothesis in the Library.

`isPullback_localizedHom_of_isPullback_ty`: let `Spec D` with `a : A → D` and `b : B → D` be
a presheaf fibre product of `ty f : Spec A → Spec C` and `ty g : Spec B → Spec C`, for
`K`-algebra maps `f : C → A` and `g : C → B`. Then, for any finite polynomial presentations,
the analytified square
`localizedHom a, localizedHom b, localizedHom f, localizedHom g` is a pullback. This is the
presheaf-model form of affine fibre products used by the existence reduction
(`AnalyticInputs.affPullback`). It is also the form of Worker 790's
`AffineTestPullbackPreservation`.

Proof:
1. Make `A`, `B` and `D` into `C`-algebras through `f`, `g` and `a ∘ f`, with the evident
   scalar towers over `K`. Then `a ∘ f = b ∘ g`, because `ty` is faithful.
2. Build `φ : A ⊗[C] B → D` with `Algebra.TensorProduct.lift`.
3. Build `ψ : D → A ⊗[C] B` from the presheaf pullback property of `D`
   (`exists_algHom_of_isPullback`), using `f c ⊗ 1 = 1 ⊗ g c`.
4. The composite `φ ∘ ψ` is the identity by the uniqueness part of the pullback property.
   The composite `ψ ∘ φ` is the identity by induction on tensors.
5. Transport the presentation of `D` along `ψ` to a presentation of `A ⊗[C] B`. Apply the
   fibre product statement, where `IsScalarTower.toAlgHom` gives back `f` and `g`.
6. Transfer the pullback square along the isomorphism `Spec(D)ᵃⁿ ≅ Spec(A ⊗[C] B)ᵃⁿ`, whose
   components are `localizedHom ψ` and `localizedHom φ`; it is invertible by functoriality.
