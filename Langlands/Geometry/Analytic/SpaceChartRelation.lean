import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceAffinePullbacks
import Langlands.Geometry.Analytic.AffineAnalytificationFibreProductProof
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof

/-! # The analytic relation of affine test points of a presheaf

For two affine test points `u : Spec A → F` and `v : Spec B → F` of a presheaf with a finite
polynomial model `Spec C = Spec A ×_F Spec B`, two analytic maps into `Spec(A)ᵃⁿ` and
`Spec(B)ᵃⁿ` are related when they factor jointly through `Spec(C)ᵃⁿ`. This relation is
reflexive, symmetric and transitive across models, and independent of the model. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ChartQuotient

open SaturatedAtlasPresentation AffineAnalytification ExistenceReduction
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Functoriality

variable {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C]

theorem lhom_comp (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (R : FinitePolynomialPresentation K C) (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    localizedHom K P R (g.comp f) = localizedHom K Q R g ≫ localizedHom K P Q f :=
  (affineAnalytificationLocalizedFunctoriality K A B C P P Q R f g).2.2.2.1

theorem lhom_id (P : FinitePolynomialPresentation K A) :
    localizedHom K P P (AlgHom.id K A) = 𝟙 _ :=
  (affineAnalytificationLocalizedFunctoriality K A A A P P P P (AlgHom.id K A)
    (AlgHom.id K A)).2.2.1

theorem lhom_isPullback {D : Type u} [CommRing D] [Algebra K D]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (R : FinitePolynomialPresentation K C) (U : FinitePolynomialPresentation K D)
    (f : C →ₐ[K] A) (g : C →ₐ[K] B) (a : A →ₐ[K] D) (b : B →ₐ[K] D)
    (hsq : IsPullback (ty a) (ty b) (ty f) (ty g)) :
    IsPullback (localizedHom K P U a) (localizedHom K Q U b)
      (localizedHom K R P f) (localizedHom K R Q g) :=
  isPullback_localizedHom_of_isPullback_ty affineAnalytificationFibreProduct
    affineAnalytificationLocalizedFunctoriality P Q R U f g a b hsq

end Functoriality

end Langlands.Analytic.SpaceAnalytification.ChartQuotient

namespace Langlands.Analytic.SpaceAnalytification.ExistenceReduction.TestModel

open SaturatedAtlasPresentation AffineAnalytification
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Analytic.SpaceAnalytification.ChartQuotient

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable {F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of K))}
  {A B D : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing D] [Algebra K D]
  {u : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K A) ⟶ F}
  {v : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶ F}
  {w : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K D) ⟶ F}
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (S : FinitePolynomialPresentation K D)

/-- Analytic maps into `Spec(A)ᵃⁿ` and `Spec(B)ᵃⁿ` related through the model `M`. -/
def ARel (M : TestModel u v) {T : LocalizedCategory.{u, u, u} (K := K)}
    (α : T ⟶ localized K P) (β : T ⟶ localized K Q) : Prop :=
  ∃ t : T ⟶ localized K M.R, t ≫ localizedHom K P M.R M.f = α ∧
    t ≫ localizedHom K Q M.R M.g = β

variable {P Q S}
variable {T T' : LocalizedCategory.{u, u, u} (K := K)}

theorem ARel.comp {M : TestModel u v} {α : T ⟶ localized K P} {β : T ⟶ localized K Q}
    (h : M.ARel P Q α β) (e : T' ⟶ T) : M.ARel P Q (e ≫ α) (e ≫ β) := by
  obtain ⟨t, rfl, rfl⟩ := h
  exact ⟨e ≫ t, Category.assoc _ _ _, Category.assoc _ _ _⟩

theorem ARel.symm {M : TestModel u v} {α : T ⟶ localized K P} {β : T ⟶ localized K Q}
    (h : M.ARel P Q α β) : M.flip.ARel Q P β α := by
  obtain ⟨t, ht₁, ht₂⟩ := h
  exact ⟨t, ht₂, ht₁⟩

/-- Algebra maps whose test points agree give related analytic maps. -/
theorem aRel_localizedHom (M : TestModel u v) {E : Type u} [CommRing E] [Algebra K E]
    (U : FinitePolynomialPresentation K E) (φ : A →ₐ[K] E) (ψ : B →ₐ[K] E)
    (h : ty φ ≫ u = ty ψ ≫ v) :
    M.ARel P Q (localizedHom K P U φ) (localizedHom K Q U ψ) := by
  obtain ⟨k, hk₁, hk₂⟩ := M.exists_lift φ ψ h
  refine ⟨localizedHom K M.R U k, ?_, ?_⟩
  · rw [← lhom_comp, hk₁]
  · rw [← lhom_comp, hk₂]

/-- Reflexivity through any model of the self-intersection of a test point. -/
theorem aRel_refl (M : TestModel u u) (α : T ⟶ localized K P) : M.ARel P P α α := by
  obtain ⟨μ, hμ₁, hμ₂⟩ := M.exists_lift (AlgHom.id K A) (AlgHom.id K A) rfl
  refine ⟨α ≫ localizedHom K M.R P μ, ?_, ?_⟩
  · rw [Category.assoc, ← lhom_comp, hμ₁, lhom_id, Category.comp_id]
  · rw [Category.assoc, ← lhom_comp, hμ₂, lhom_id, Category.comp_id]

/-- The two projections of a model are jointly monic. -/
theorem jointly_mono (M : TestModel u v) (l m : T ⟶ localized K M.R)
    (h₁ : l ≫ localizedHom K P M.R M.f = m ≫ localizedHom K P M.R M.f)
    (h₂ : l ≫ localizedHom K Q M.R M.g = m ≫ localizedHom K Q M.R M.g) : l = m := by
  let P₀ : FinitePolynomialPresentation K K := FinitePolynomialPresentation.ofFiniteType K K
  let N := testModel P Q (Algebra.ofId K A) (Algebra.ofId K B)
  obtain ⟨k, hk₁, hk₂⟩ := N.exists_lift M.f M.g (by
    rw [← ty_comp, ← ty_comp]
    congr 1
    exact AlgHom.ext fun r => by simp only [AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes])
  have hmono : Mono (ty k) := by
    constructor
    intro T a b hab
    apply M.isPullback.hom_ext
    · rw [← hk₁, ty_comp, ← Category.assoc, hab, Category.assoc]
    · rw [← hk₂, ty_comp, ← Category.assoc, hab, Category.assoc]
  have hker : IsPullback (ty (AlgHom.id K M.C)) (ty (AlgHom.id K M.C)) (ty k) (ty k) := by
    rw [ty_id]
    exact IsKernelPair.id_of_mono (ty k)
  have hkerAn := lhom_isPullback M.R M.R N.R M.R k k (AlgHom.id K M.C) (AlgHom.id K M.C) hker
  rw [lhom_id] at hkerAn
  have hN := lhom_isPullback P Q P₀ N.R (Algebra.ofId K A) (Algebra.ofId K B) N.f N.g
    N.isPullback
  have hlm : l ≫ localizedHom K N.R M.R k = m ≫ localizedHom K N.R M.R k := by
    apply hN.hom_ext
    · rw [Category.assoc, Category.assoc, ← lhom_comp, hk₁, h₁]
    · rw [Category.assoc, Category.assoc, ← lhom_comp, hk₂, h₂]
  obtain ⟨t, ht₁, ht₂⟩ := hkerAn.exists_lift l m hlm
  rw [Category.comp_id] at ht₁ ht₂
  rw [← ht₁, ← ht₂]

/-- Transitivity of the analytic relation across three models. -/
theorem ARel.trans {M₁ : TestModel u v} {M₂ : TestModel v w} (M₃ : TestModel u w)
    {α : T ⟶ localized K P} {β : T ⟶ localized K Q} {γ : T ⟶ localized K S}
    (h₁ : M₁.ARel P Q α β) (h₂ : M₂.ARel Q S β γ) : M₃.ARel P S α γ := by
  obtain ⟨t₁, ht₁, rfl⟩ := h₁
  obtain ⟨t₂, ht₂, rfl⟩ := h₂
  let N := testModel M₁.R M₂.R M₁.g M₂.f
  have hN := lhom_isPullback M₁.R M₂.R Q N.R M₁.g M₂.f N.f N.g N.isPullback
  obtain ⟨t, htf, htg⟩ := hN.exists_lift t₁ t₂ (by rw [ht₂])
  obtain ⟨k, hk₁, hk₂⟩ := M₃.exists_lift (N.f.comp M₁.f) (N.g.comp M₂.g) (by
    rw [ty_comp, ty_comp, Category.assoc, Category.assoc, M₁.w, ← Category.assoc, N.w,
      Category.assoc, M₂.w])
  refine ⟨t ≫ localizedHom K M₃.R N.R k, ?_, ?_⟩
  · rw [Category.assoc, ← lhom_comp, hk₁, lhom_comp, ← Category.assoc, htf, ht₁]
  · rw [Category.assoc, ← lhom_comp, hk₂, lhom_comp, ← Category.assoc, htg]

/-- The analytic relation does not depend on the model. -/
theorem ARel.of_model {M : TestModel u v} (M' : TestModel u v) {α : T ⟶ localized K P}
    {β : T ⟶ localized K Q} (h : M.ARel P Q α β) : M'.ARel P Q α β := by
  obtain ⟨t, rfl, rfl⟩ := h
  obtain ⟨k, hk₁, hk₂⟩ := M'.exists_lift M.f M.g M.w
  refine ⟨t ≫ localizedHom K M'.R M.R k, ?_, ?_⟩
  · rw [Category.assoc, ← lhom_comp, hk₁]
  · rw [Category.assoc, ← lhom_comp, hk₂]

end Langlands.Analytic.SpaceAnalytification.ExistenceReduction.TestModel
