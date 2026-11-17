import Langlands.GroupScheme.Reductive.WeilFactorCanonical

/-! # Natural multiplicative bijections of idempotents and the algebra isomorphisms they induce -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.WeilFactor

open Langlands.Algebra.GraphIdempotent

/-- A transfer of idempotents from `B ⊗_A X` to `B'' ⊗_A X`, for all `A`-algebras `X`: mutually
inverse maps on idempotents that are natural in `X`, multiplicative, and send `0` to `0`. -/
structure IdemTransfer (A B B'' : Type u) [CommRing A] [CommRing B] [CommRing B'']
    [Algebra A B] [Algebra A B''] where
  /-- The forward map. -/
  map : ∀ X : CommAlgCat.{u} (CommRingCat.of A), B ⊗[A] X → B'' ⊗[A] X
  /-- The backward map. -/
  inv : ∀ X : CommAlgCat.{u} (CommRingCat.of A), B'' ⊗[A] X → B ⊗[A] X
  map_idem : ∀ (X : CommAlgCat.{u} (CommRingCat.of A)) (e : B ⊗[A] X),
    IsIdempotentElem e → IsIdempotentElem (map X e)
  inv_idem : ∀ (X : CommAlgCat.{u} (CommRingCat.of A)) (e : B'' ⊗[A] X),
    IsIdempotentElem e → IsIdempotentElem (inv X e)
  map_lT : ∀ {X Y : CommAlgCat.{u} (CommRingCat.of A)} (χ : X ⟶ Y) (e : B ⊗[A] X),
    IsIdempotentElem e → map Y (lT χ e) = lT χ (map X e)
  inv_lT : ∀ {X Y : CommAlgCat.{u} (CommRingCat.of A)} (χ : X ⟶ Y) (e : B'' ⊗[A] X),
    IsIdempotentElem e → inv Y (lT χ e) = lT χ (inv X e)
  map_mul : ∀ (X : CommAlgCat.{u} (CommRingCat.of A)) (e f : B ⊗[A] X),
    IsIdempotentElem e → IsIdempotentElem f →
    map X (f * e) = map X f * map X e
  inv_mul : ∀ (X : CommAlgCat.{u} (CommRingCat.of A)) (e f : B'' ⊗[A] X),
    IsIdempotentElem e → IsIdempotentElem f →
    inv X (f * e) = inv X f * inv X e
  map_zero : ∀ X : CommAlgCat.{u} (CommRingCat.of A), map X 0 = 0
  inv_zero : ∀ X : CommAlgCat.{u} (CommRingCat.of A), inv X 0 = 0
  inv_map : ∀ (X : CommAlgCat.{u} (CommRingCat.of A)) (e : B ⊗[A] X),
    IsIdempotentElem e → inv X (map X e) = e
  map_inv : ∀ (X : CommAlgCat.{u} (CommRingCat.of A)) (e : B'' ⊗[A] X),
    IsIdempotentElem e → map X (inv X e) = e

namespace IdemTransfer

variable {A B B'' B''' : Type u} [CommRing A] [CommRing B] [CommRing B''] [CommRing B''']
  [Algebra A B] [Algebra A B''] [Algebra A B''']

/-- The inverse transfer. -/
def symm (τ : IdemTransfer A B B'') : IdemTransfer A B'' B where
  map := τ.inv
  inv := τ.map
  map_idem := τ.inv_idem
  inv_idem := τ.map_idem
  map_lT := τ.inv_lT
  inv_lT := τ.map_lT
  map_mul := τ.inv_mul
  inv_mul := τ.map_mul
  map_zero := τ.inv_zero
  inv_zero := τ.map_zero
  inv_map := τ.map_inv
  map_inv := τ.inv_map

/-- The identity transfer. -/
def refl (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : IdemTransfer A B B where
  map _ e := e
  inv _ e := e
  map_idem _ _ h := h
  inv_idem _ _ h := h
  map_lT _ _ _ := rfl
  inv_lT _ _ _ := rfl
  map_mul _ _ _ _ _ := rfl
  inv_mul _ _ _ _ _ := rfl
  map_zero _ := rfl
  inv_zero _ := rfl
  inv_map _ _ _ := rfl
  map_inv _ _ _ := rfl

/-- The composite transfer. -/
def trans (τ₁ : IdemTransfer A B B'') (τ₂ : IdemTransfer A B'' B''') : IdemTransfer A B B''' where
  map X e := τ₂.map X (τ₁.map X e)
  inv X e := τ₁.inv X (τ₂.inv X e)
  map_idem X e h := τ₂.map_idem X _ (τ₁.map_idem X e h)
  inv_idem X e h := τ₁.inv_idem X _ (τ₂.inv_idem X e h)
  map_lT χ e h := by rw [τ₁.map_lT χ e h, τ₂.map_lT χ _ (τ₁.map_idem _ e h)]
  inv_lT χ e h := by rw [τ₂.inv_lT χ e h, τ₁.inv_lT χ _ (τ₂.inv_idem _ e h)]
  map_mul X e f he hf := by
    rw [τ₁.map_mul X e f he hf, τ₂.map_mul X _ _ (τ₁.map_idem X e he) (τ₁.map_idem X f hf)]
  inv_mul X e f he hf := by
    rw [τ₂.inv_mul X e f he hf, τ₁.inv_mul X _ _ (τ₂.inv_idem X e he) (τ₂.inv_idem X f hf)]
  map_zero X := by rw [τ₁.map_zero, τ₂.map_zero]
  inv_zero X := by rw [τ₂.inv_zero, τ₁.inv_zero]
  inv_map X e h := by rw [τ₂.inv_map X _ (τ₁.map_idem X e h), τ₁.inv_map X e h]
  map_inv X e h := by rw [τ₁.map_inv X _ (τ₂.inv_idem X e h), τ₂.map_inv X e h]

theorem map_ne_zero (τ : IdemTransfer A B B'') {X : CommAlgCat.{u} (CommRingCat.of A)}
    {e : B ⊗[A] X} (he : IsIdempotentElem e) (h : e ≠ 0) : τ.map X e ≠ 0 := by
  intro h0
  apply h
  rw [← τ.inv_map X e he, h0, τ.inv_zero]

theorem isMinimalIdem_map (τ : IdemTransfer A B B'') {X : CommAlgCat.{u} (CommRingCat.of A)}
    {e : B ⊗[A] X} (he : IsMinimalIdem e) : IsMinimalIdem (τ.map X e) where
  idem := τ.map_idem X e he.idem
  ne_zero T₁ χ hT₁ := by
    rw [← τ.map_lT χ e he.idem]
    exact τ.map_ne_zero (he.idem.map _) (he.ne_zero T₁ χ hT₁)
  minimal T₁ χ f hf hle hne := by
    have htr := τ.map_idem X e he.idem
    have hg := τ.inv_idem T₁ f hf
    have hle' : τ.inv T₁ f * lT χ e = τ.inv T₁ f := by
      have h1 := congrArg (τ.inv T₁) hle
      rw [τ.inv_mul T₁ _ _ (htr.map _) hf, ← τ.map_lT χ e he.idem,
        τ.inv_map T₁ _ (he.idem.map _)] at h1
      exact h1
    have hne' : ∀ (T₂ : CommAlgCat.{u} (CommRingCat.of A)) (χ' : T₁ ⟶ T₂), Nontrivial T₂ →
        lT χ' (τ.inv T₁ f) ≠ 0 := by
      intro T₂ χ' hT₂
      rw [← τ.inv_lT χ' f hf]
      exact τ.symm.map_ne_zero (hf.map _) (hne T₂ χ' hT₂)
    have hmin := he.minimal T₁ χ _ hg hle' hne'
    calc f = τ.map T₁ (τ.inv T₁ f) := (τ.map_inv T₁ f hf).symm
      _ = τ.map T₁ (lT χ e) := by rw [hmin]
      _ = lT χ (τ.map X e) := τ.map_lT χ e he.idem

/-- The property of `α : B'' ≃ B` attached to `τ`: the transfer of the graph idempotent of any
`φ : B → X` is the graph idempotent of `φ ∘ α`. -/
def IsAlgEquiv (τ : IdemTransfer A B B'') (α : B'' ≃ₐ[A] B) : Prop :=
  ∀ (X : CommAlgCat.{u} (CommRingCat.of A)) (φ : B →ₐ[A] X) (e : B ⊗[A] X),
    IsGraphIdempotent φ e → IsGraphIdempotent (φ.comp (α : B'' →ₐ[A] B)) (τ.map X e)

variable [Module.Finite A B] [Module.Projective A B] [Algebra.Etale A B]
  [Module.Finite A B''] [Module.Projective A B''] [Algebra.Etale A B'']

omit [Module.Finite A B] [Module.Projective A B] in
set_option backward.isDefEq.respectTransparency false in
theorem exists_algHom (τ : IdemTransfer A B B'') :
    ∃ α : B'' →ₐ[A] B, ∀ (X : CommAlgCat.{u} (CommRingCat.of A)) (φ : B →ₐ[A] X)
      (e : B ⊗[A] X), IsGraphIdempotent φ e → IsGraphIdempotent (φ.comp α) (τ.map X e) := by
  let TB : CommAlgCat.{u} (CommRingCat.of A) := CommAlgCat.of (CommRingCat.of A) B
  obtain ⟨δ, hδ⟩ := exists_isGraphIdempotent (A := A) (B := B) (T := TB) (AlgHom.id A B)
  obtain ⟨α, hα⟩ := (τ.isMinimalIdem_map
    (isMinimalIdem_of_isGraphIdempotent (T := TB) (φ := AlgHom.id A B) hδ)).exists_isGraphIdempotent
  refine ⟨α, fun X φ e he => ?_⟩
  have hφ := hδ.map φ
  rw [AlgHom.comp_id] at hφ
  have heq : e = lT (CommAlgCat.ofHom φ : TB ⟶ X) δ := by
    rw [lT_apply]; exact he.unique hφ
  rw [heq, τ.map_lT _ δ hδ.isIdempotentElem, lT_apply]
  exact hα.map φ

set_option backward.isDefEq.respectTransparency false in
theorem exists_algEquiv (τ : IdemTransfer A B B'') : ∃ α : B'' ≃ₐ[A] B, τ.IsAlgEquiv α := by
  obtain ⟨α, hα⟩ := τ.exists_algHom
  obtain ⟨α', hα'⟩ := τ.symm.exists_algHom
  let TB : CommAlgCat.{u} (CommRingCat.of A) := CommAlgCat.of (CommRingCat.of A) B
  let TB'' : CommAlgCat.{u} (CommRingCat.of A) := CommAlgCat.of (CommRingCat.of A) B''
  obtain ⟨δ, hδ⟩ := exists_isGraphIdempotent (A := A) (B := B) (T := TB) (AlgHom.id A B)
  obtain ⟨δ'', hδ''⟩ := exists_isGraphIdempotent (A := A) (B := B'') (T := TB'') (AlgHom.id A B'')
  have h1 : α.comp α' = AlgHom.id A B := by
    have h := hα' TB ((AlgHom.id A B).comp α) _ (hα TB (AlgHom.id A B) δ hδ)
    change IsGraphIdempotent _ (τ.inv TB (τ.map TB δ)) at h
    rw [τ.inv_map TB δ hδ.isIdempotentElem] at h
    have h' := hδ.algHom_eq h
    ext b
    exact (congrArg (fun f : B →ₐ[A] B => f b) h').symm
  have h2 : α'.comp α = AlgHom.id A B'' := by
    have h := hα TB'' ((AlgHom.id A B'').comp α') _ (hα' TB'' (AlgHom.id A B'') δ'' hδ'')
    change IsGraphIdempotent _ (τ.map TB'' (τ.inv TB'' δ'')) at h
    rw [τ.map_inv TB'' δ'' hδ''.isIdempotentElem] at h
    have h' := hδ''.algHom_eq h
    ext b
    exact (congrArg (fun f : B'' →ₐ[A] B'' => f b) h').symm
  exact ⟨AlgEquiv.ofAlgHom α α' h1 h2, fun X φ e he => hα X φ e he⟩

/-- The `A`-algebra isomorphism `B'' ≃ B` induced by a transfer of idempotents. -/
def algEquiv (τ : IdemTransfer A B B'') : B'' ≃ₐ[A] B :=
  Classical.choose τ.exists_algEquiv

theorem algEquiv_spec (τ : IdemTransfer A B B'') : τ.IsAlgEquiv τ.algEquiv :=
  Classical.choose_spec τ.exists_algEquiv

omit [Module.Finite A B] [Module.Projective A B] [Module.Finite A B'']
  [Module.Projective A B''] [Algebra.Etale A B''] in
set_option backward.isDefEq.respectTransparency false in
theorem IsAlgEquiv.eq {τ : IdemTransfer A B B''} {α α' : B'' ≃ₐ[A] B} (h : τ.IsAlgEquiv α)
    (h' : τ.IsAlgEquiv α') : α = α' := by
  let TB : CommAlgCat.{u} (CommRingCat.of A) := CommAlgCat.of (CommRingCat.of A) B
  obtain ⟨δ, hδ⟩ := exists_isGraphIdempotent (A := A) (B := B) (T := TB) (AlgHom.id A B)
  have h1 := (h TB (AlgHom.id A B) δ hδ).algHom_eq (h' TB (AlgHom.id A B) δ hδ)
  ext b
  exact congrArg (fun f : B'' →ₐ[A] B => f b) h1

/-- Uniqueness: an isomorphism with the defining property is `τ.algEquiv`. -/
theorem algEquiv_unique (τ : IdemTransfer A B B'') {α : B'' ≃ₐ[A] B} (h : τ.IsAlgEquiv α) :
    α = τ.algEquiv :=
  h.eq τ.algEquiv_spec

theorem algEquiv_refl : (refl A B).algEquiv = AlgEquiv.refl := by
  symm
  apply algEquiv_unique
  intro X φ e he
  have h : φ.comp ((AlgEquiv.refl : B ≃ₐ[A] B) : B →ₐ[A] B) = φ := by
    ext
    rfl
  rw [h]
  exact he

theorem algEquiv_trans [Module.Finite A B'''] [Module.Projective A B'''] [Algebra.Etale A B''']
    (τ₁ : IdemTransfer A B B'') (τ₂ : IdemTransfer A B'' B''') :
    (τ₁.trans τ₂).algEquiv = τ₂.algEquiv.trans τ₁.algEquiv := by
  symm
  apply algEquiv_unique
  intro X φ e he
  exact τ₂.algEquiv_spec X _ _ (τ₁.algEquiv_spec X φ e he)

end IdemTransfer

section WeilInstance

variable {A B B'' : Type u} [CommRing A] [CommRing B] [CommRing B''] [Algebra A B]
  [Algebra A B''] [Module.Finite A B] [Module.Projective A B] [Module.Finite A B'']
  [Module.Projective A B''] [Algebra.Etale A B] [Algebra.Etale A B'']
  {G : GroupScheme (Spec (CommRingCat.of B))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {G'' : GroupScheme (Spec (CommRingCat.of B''))} [IsAffine G''.X.left]
  [LocallyOfFiniteType G''.X.hom]
  (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive G) (hsimple : ∀ s, IsAlmostSimple (geometricFiber G s))
  (hred'' : IsReductive G'') (hsimple'' : ∀ s, IsAlmostSimple (geometricFiber G'' s))

/-- The transfer of idempotents along an isomorphism of Weil restrictions, as an
`IdemTransfer`. -/
def idemTransfer (Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'') :
    IdemTransfer A B B'' where
  map _ e := transfer Φ hR hred'' hsimple'' e
  inv _ e := transfer Φ.symm hR hred hsimple e
  map_idem _ _ h := transfer_isIdempotentElem Φ hR hred'' hsimple'' h
  inv_idem _ _ h := transfer_isIdempotentElem Φ.symm hR hred hsimple h
  map_lT χ _ h := transfer_lTensor Φ hR hred'' hsimple'' χ h
  inv_lT χ _ h := transfer_lTensor Φ.symm hR hred hsimple χ h
  map_mul _ _ _ he hf := transfer_mul Φ hR hred'' hsimple'' he hf
  inv_mul _ _ _ he hf := transfer_mul Φ.symm hR hred hsimple he hf
  map_zero _ := transfer_zero Φ hR hred'' hsimple''
  inv_zero _ := transfer_zero Φ.symm hR hred hsimple
  inv_map _ _ h := transfer_symm_transfer Φ hR hred'' hsimple'' hred hsimple h
  map_inv _ _ h := transfer_transfer_symm Φ hR hred hsimple hred'' hsimple'' h

/-- The algebra isomorphism of `idemTransfer Φ` is `weilAlgEquiv Φ`. -/
theorem idemTransfer_algEquiv
    (Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'') :
    (idemTransfer hR hred hsimple hred'' hsimple'' Φ).algEquiv =
      weilAlgEquiv hR hred hsimple hred'' hsimple'' Φ :=
  weilAlgEquiv_unique hR hred hsimple hred'' hsimple'' Φ
    (idemTransfer hR hred hsimple hred'' hsimple'' Φ).algEquiv_spec

end WeilInstance

end Langlands.GroupScheme.WeilFactor
