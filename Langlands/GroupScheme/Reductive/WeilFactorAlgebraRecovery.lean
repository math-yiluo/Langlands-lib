import Langlands.GroupScheme.Reductive.WeilFactorTransfer
import Langlands.Algebra.EtaleGraphIdempotent

/-! # Recovering the étale algebra of a Weil restriction from its factor projections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilFactor

open Langlands.Algebra.GraphIdempotent Algebra.TensorProduct

section Minimal

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Base change of `B ⊗ T` along `χ : T ⟶ T₁`. -/
abbrev lT {T T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) :
    B ⊗[A] T →ₐ[B] B ⊗[A] T₁ :=
  Algebra.TensorProduct.lTensor (S := B) B χ.hom

theorem lT_apply {T T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) (x : B ⊗[A] T) :
    lT χ x = Algebra.TensorProduct.map (AlgHom.id A B) χ.hom x := by
  induction x with
  | tmul b t => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- An idempotent of `B ⊗ T` that is nonzero over every nonzero `T`-algebra and minimal among
idempotents with this property, over every `T`-algebra. -/
structure IsMinimalIdem {T : CommAlgCat.{u} (CommRingCat.of A)} (e : B ⊗[A] T) : Prop where
  idem : IsIdempotentElem e
  ne_zero : ∀ (T₁ : CommAlgCat.{u} (CommRingCat.of A)) (χ : T ⟶ T₁), Nontrivial T₁ →
    lT χ e ≠ 0
  minimal : ∀ (T₁ : CommAlgCat.{u} (CommRingCat.of A)) (χ : T ⟶ T₁) (f : B ⊗[A] T₁),
    IsIdempotentElem f → f * lT χ e = f →
    (∀ (T₂ : CommAlgCat.{u} (CommRingCat.of A)) (χ' : T₁ ⟶ T₂), Nontrivial T₂ → lT χ' f ≠ 0) →
    f = lT χ e

theorem isMinimalIdem_of_isGraphIdempotent {T : CommAlgCat.{u} (CommRingCat.of A)}
    {φ : B →ₐ[A] T} {e : B ⊗[A] T} (he : IsGraphIdempotent φ e) : IsMinimalIdem e where
  idem := he.isIdempotentElem
  ne_zero T₁ χ _ := by
    rw [lT_apply]
    exact (he.map χ.hom).ne_zero
  minimal T₁ χ f hf hle hne := by
    rw [lT_apply] at hle ⊢
    refine (he.map χ.hom).eq_of_le hf hle ?_
    intro T₂ _ _ χ' hT₂
    have h := hne (CommAlgCat.of (CommRingCat.of A) T₂) (CommAlgCat.ofHom χ') hT₂
    rwa [lT_apply] at h

theorem IsMinimalIdem.exists_isGraphIdempotent [Module.Finite A B] [Module.Projective A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    {T : CommAlgCat.{u} (CommRingCat.of A)} {e : B ⊗[A] T} (he : IsMinimalIdem e) :
    ∃ φ : B →ₐ[A] T, IsGraphIdempotent φ e := by
  apply exists_isGraphIdempotent_of_minimal he.idem
  · intro f hf hle hne
    have h := he.minimal (CommAlgCat.of (CommRingCat.of A) (B ⊗[A] T ⧸ Ideal.span {1 - e}))
      (CommAlgCat.ofHom ((Ideal.Quotient.mkₐ A (Ideal.span {1 - e})).comp includeRight)) f hf
      (by rw [lT_apply]; exact hle)
      (fun T₂ χ' hT₂ => by rw [lT_apply]; exact hne T₂ χ'.hom hT₂)
    rw [lT_apply] at h
    exact h
  · intro m hm
    have h := he.ne_zero (CommAlgCat.of (CommRingCat.of A) (T ⧸ m))
      (CommAlgCat.ofHom (Ideal.Quotient.mkₐ A m)) (Ideal.Quotient.nontrivial_iff.mpr hm.ne_top)
    rw [lT_apply] at h
    exact h

end Minimal

section Recovery

variable {A B B'' : Type u} [CommRing A] [CommRing B] [CommRing B''] [Algebra A B]
  [Algebra A B''] [Module.Finite A B] [Module.Projective A B] [Module.Finite A B'']
  [Module.Projective A B''] [Algebra.Etale A B] [Algebra.Etale A B'']
  {G : GroupScheme (Spec (CommRingCat.of B))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {G'' : GroupScheme (Spec (CommRingCat.of B''))} [IsAffine G''.X.left]
  [LocallyOfFiniteType G''.X.hom]
  (Φ : AffineWeil.groupScheme A B G ≅ AffineWeil.groupScheme A B'' G'')
  (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive G) (hsimple : ∀ s, IsAlmostSimple (geometricFiber G s))
  (hred'' : IsReductive G'') (hsimple'' : ∀ s, IsAlmostSimple (geometricFiber G'' s))

theorem transfer_transfer_symm {T : CommAlgCat.{u} (CommRingCat.of A)} {e : B'' ⊗[A] T}
    (he : IsIdempotentElem e) :
    transfer Φ hR hred'' hsimple'' (transfer Φ.symm hR hred hsimple e) = e :=
  transfer_symm_transfer Φ.symm hR hred hsimple hred'' hsimple'' he

include hred hsimple in
theorem transfer_ne_zero {T : CommAlgCat.{u} (CommRingCat.of A)} {e : B ⊗[A] T}
    (he : IsIdempotentElem e) (h : e ≠ 0) : transfer Φ hR hred'' hsimple'' e ≠ 0 := by
  intro h0
  apply h
  rw [← transfer_symm_transfer Φ hR hred'' hsimple'' hred hsimple he, h0, transfer_zero]

include hred hsimple in
theorem isMinimalIdem_transfer {T : CommAlgCat.{u} (CommRingCat.of A)} {e : B ⊗[A] T}
    (he : IsMinimalIdem e) : IsMinimalIdem (transfer Φ hR hred'' hsimple'' e) where
  idem := transfer_isIdempotentElem Φ hR hred'' hsimple'' he.idem
  ne_zero T₁ χ hT₁ := by
    rw [lT, ← transfer_lTensor Φ hR hred'' hsimple'' χ he.idem]
    exact transfer_ne_zero Φ hR hred hsimple hred'' hsimple'' (he.idem.map _)
      (he.ne_zero T₁ χ hT₁)
  minimal T₁ χ f hf hle hne := by
    have htr : IsIdempotentElem (transfer Φ hR hred'' hsimple'' e) :=
      transfer_isIdempotentElem Φ hR hred'' hsimple'' he.idem
    have hg : IsIdempotentElem (transfer Φ.symm hR hred hsimple f) :=
      transfer_isIdempotentElem Φ.symm hR hred hsimple hf
    have hle' : transfer Φ.symm hR hred hsimple f * lT χ e =
        transfer Φ.symm hR hred hsimple f := by
      have h1 := congrArg (transfer Φ.symm hR hred hsimple) hle
      rw [transfer_mul Φ.symm hR hred hsimple (htr.map _) hf, lT,
        ← transfer_lTensor Φ hR hred'' hsimple'' χ he.idem,
        transfer_symm_transfer Φ hR hred'' hsimple'' hred hsimple (he.idem.map _)] at h1
      exact h1
    have hne' : ∀ (T₂ : CommAlgCat.{u} (CommRingCat.of A)) (χ' : T₁ ⟶ T₂), Nontrivial T₂ →
        lT χ' (transfer Φ.symm hR hred hsimple f) ≠ 0 := by
      intro T₂ χ' hT₂
      rw [lT, ← transfer_lTensor Φ.symm hR hred hsimple χ' hf]
      exact transfer_ne_zero Φ.symm hR hred'' hsimple'' hred hsimple (hf.map _) (hne T₂ χ' hT₂)
    have hmin := he.minimal T₁ χ _ hg hle' hne'
    calc f = transfer Φ hR hred'' hsimple'' (transfer Φ.symm hR hred hsimple f) :=
          (transfer_transfer_symm Φ hR hred hsimple hred'' hsimple'' hf).symm
      _ = transfer Φ hR hred'' hsimple'' (lT χ e) := by rw [hmin]
      _ = lT χ (transfer Φ hR hred'' hsimple'' e) :=
          transfer_lTensor Φ hR hred'' hsimple'' χ he.idem

set_option backward.isDefEq.respectTransparency false in
include hred hsimple in
/-- The `A`-algebra map `B'' → B` read off from the transfer of the diagonal idempotent. -/
theorem exists_algHom_transfer :
    ∃ α : B'' →ₐ[A] B, ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (φ : B →ₐ[A] T)
      (e : B ⊗[A] T), IsGraphIdempotent φ e →
        IsGraphIdempotent (φ.comp α) (transfer Φ hR hred'' hsimple'' e) := by
  let TB : CommAlgCat.{u} (CommRingCat.of A) := CommAlgCat.of (CommRingCat.of A) B
  obtain ⟨δ, hδ⟩ := exists_isGraphIdempotent (A := A) (B := B) (T := TB) (AlgHom.id A B)
  obtain ⟨α, hα⟩ := (isMinimalIdem_transfer Φ hR hred hsimple hred'' hsimple''
    (isMinimalIdem_of_isGraphIdempotent (T := TB) (φ := AlgHom.id A B) hδ)).exists_isGraphIdempotent
  refine ⟨α, fun T φ e he => ?_⟩
  have hφ := hδ.map φ
  rw [AlgHom.comp_id] at hφ
  have heq : e = lT (CommAlgCat.ofHom φ : TB ⟶ T) δ := by
    rw [lT_apply]; exact he.unique hφ
  rw [heq, lT, transfer_lTensor Φ hR hred'' hsimple'' _ hδ.isIdempotentElem, ← lT, lT_apply]
  exact hα.map φ

set_option backward.isDefEq.respectTransparency false in
include hred hsimple in
/-- An isomorphism of Weil restrictions determines an `A`-algebra isomorphism `B'' ≃ B`
compatible with graph idempotents. -/
theorem exists_algEquiv_transfer :
    ∃ α : B'' ≃ₐ[A] B, ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (φ : B →ₐ[A] T)
      (e : B ⊗[A] T), IsGraphIdempotent φ e →
        IsGraphIdempotent (φ.comp (α : B'' →ₐ[A] B)) (transfer Φ hR hred'' hsimple'' e) := by
  obtain ⟨α, hα⟩ := exists_algHom_transfer Φ hR hred hsimple hred'' hsimple''
  obtain ⟨α', hα'⟩ := exists_algHom_transfer Φ.symm hR hred'' hsimple'' hred hsimple
  let TB : CommAlgCat.{u} (CommRingCat.of A) := CommAlgCat.of (CommRingCat.of A) B
  let TB'' : CommAlgCat.{u} (CommRingCat.of A) := CommAlgCat.of (CommRingCat.of A) B''
  obtain ⟨δ, hδ⟩ := exists_isGraphIdempotent (A := A) (B := B) (T := TB) (AlgHom.id A B)
  obtain ⟨δ'', hδ''⟩ := exists_isGraphIdempotent (A := A) (B := B'') (T := TB'') (AlgHom.id A B'')
  have h1 : α.comp α' = AlgHom.id A B := by
    have h := hα' TB ((AlgHom.id A B).comp α) _ (hα TB (AlgHom.id A B) δ hδ)
    rw [transfer_symm_transfer Φ hR hred'' hsimple'' hred hsimple hδ.isIdempotentElem] at h
    have h' := hδ.algHom_eq h
    ext b
    have := congrArg (fun f : B →ₐ[A] B => f b) h'
    exact this.symm
  have h2 : α'.comp α = AlgHom.id A B'' := by
    have h := hα TB'' ((AlgHom.id A B'').comp α') _ (hα' TB'' (AlgHom.id A B'') δ'' hδ'')
    rw [transfer_transfer_symm Φ hR hred hsimple hred'' hsimple'' hδ''.isIdempotentElem] at h
    have h' := hδ''.algHom_eq h
    ext b
    have := congrArg (fun f : B'' →ₐ[A] B'' => f b) h'
    exact this.symm
  exact ⟨AlgEquiv.ofAlgHom α α' h1 h2, fun T φ e he => hα T φ e he⟩

end Recovery

end Langlands.GroupScheme.WeilFactor
