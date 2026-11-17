import Langlands.AlgebraicGeometry.FiniteProductCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Limits

/-! # Coefficient tensor coordinates for a finite affine cover -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Langlands.AlgebraicGeometry.AffineCoverCoefficientTensors

variable {S X Y : Scheme.{u}} [IsAffine S] [IsAffine X] [IsAffine Y]

/-- The canonical affine overlap ring is the tensor product of the two chart
rings over the base's global-section ring. -/
def overlapTensorEquiv (f : X ⟶ S) (g : Y ⟶ S) :
    letI := f.appTop.hom.toAlgebra
    letI := g.appTop.hom.toAlgebra
    Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(Y, ⊤) ≃+* Γ(pullback f g, ⊤) := by
  letI := f.appTop.hom.toAlgebra
  letI := g.appTop.hom.toAlgebra
  exact ((CommRingCat.isPushout_tensorProduct Γ(S, ⊤) Γ(X, ⊤) Γ(Y, ⊤)).isoIsPushout
    Γ(X, ⊤) Γ(Y, ⊤)
    (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f g))).commRingCatIsoToRingEquiv

@[simp] theorem overlapTensorEquiv_tmul_one (f : X ⟶ S) (g : Y ⟶ S) (x : Γ(X, ⊤)) :
    letI := f.appTop.hom.toAlgebra
    letI := g.appTop.hom.toAlgebra
    overlapTensorEquiv f g (x ⊗ₜ[Γ(S, ⊤)] 1) = (pullback.fst f g).appTop.hom x := by
  letI := f.appTop.hom.toAlgebra
  letI := g.appTop.hom.toAlgebra
  have h := congrArg (fun k : Γ(X, ⊤) ⟶ Γ(pullback f g, ⊤) => k.hom x)
    (IsPushout.inl_isoIsPushout_hom Γ(X, ⊤) Γ(Y, ⊤)
      (CommRingCat.isPushout_tensorProduct Γ(S, ⊤) Γ(X, ⊤) Γ(Y, ⊤))
      (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f g)))
  exact h

@[simp] theorem overlapTensorEquiv_one_tmul (f : X ⟶ S) (g : Y ⟶ S) (y : Γ(Y, ⊤)) :
    letI := f.appTop.hom.toAlgebra
    letI := g.appTop.hom.toAlgebra
    overlapTensorEquiv f g (1 ⊗ₜ[Γ(S, ⊤)] y) = (pullback.snd f g).appTop.hom y := by
  letI := f.appTop.hom.toAlgebra
  letI := g.appTop.hom.toAlgebra
  have h := congrArg (fun k : Γ(Y, ⊤) ⟶ Γ(pullback f g, ⊤) => k.hom y)
    (IsPushout.inr_isoIsPushout_hom Γ(X, ⊤) Γ(Y, ⊤)
      (CommRingCat.isPushout_tensorProduct Γ(S, ⊤) Γ(X, ⊤) Γ(Y, ⊤))
      (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f g)))
  exact h

@[simp] theorem overlapTensorEquiv_tmul (f : X ⟶ S) (g : Y ⟶ S)
    (x : Γ(X, ⊤)) (y : Γ(Y, ⊤)) :
    letI := f.appTop.hom.toAlgebra
    letI := g.appTop.hom.toAlgebra
    overlapTensorEquiv f g (x ⊗ₜ[Γ(S, ⊤)] y) =
      (pullback.fst f g).appTop.hom x * (pullback.snd f g).appTop.hom y := by
  letI := f.appTop.hom.toAlgebra
  letI := g.appTop.hom.toAlgebra
  calc
    _ = overlapTensorEquiv f g
        ((x ⊗ₜ[Γ(S, ⊤)] 1) * (1 ⊗ₜ[Γ(S, ⊤)] y)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = _ := by rw [map_mul, overlapTensorEquiv_tmul_one, overlapTensorEquiv_one_tmul]

section Family

variable {α : Type u} [Finite α] (U : α → Scheme.{u}) [∀ a, IsAffine (U a)]
  (f : ∀ a, U a ⟶ S)

/-- The canonical base map to the finite product of affine chart rings. -/
def coverRingMap : Γ(S, ⊤) →+* (∀ a, Γ(U a, ⊤)) :=
  RingHom.pi (fun a => (f a).appTop.hom)

/-- A finite flat jointly surjective affine family gives a faithfully flat map
to the product of its chart rings. -/
theorem coverRingMap_faithfullyFlat [∀ a, Flat (f a)]
    [Surjective (Sigma.desc f)] : (coverRingMap U f).FaithfullyFlat := by
  let e : (∐ U) ≅ Spec (CommRingCat.of (∀ a, Γ(U a, ⊤))) :=
    (Sigma.mapIso (fun a => (U a).isoSpec)) ≪≫
      asIso (sigmaSpec (fun a => Γ(U a, ⊤)))
  have h : e.hom ≫ Spec.map (CommRingCat.ofHom (coverRingMap U f)) =
      Sigma.desc f ≫ S.isoSpec.hom := by
    apply Sigma.hom_ext
    intro a
    simp only [e, Iso.trans_hom, Category.assoc, Sigma.ι_mapIso_hom_assoc,
      asIso_hom, ι_sigmaSpec_assoc, Sigma.ι_comp_desc_assoc]
    rw [← Spec.map_comp]
    change (U a).isoSpec.hom ≫ Spec.map (f a).appTop = f a ≫ S.isoSpec.hom
    exact Scheme.isoSpec_hom_naturality (f a)
  have hm : Spec.map (CommRingCat.ofHom (coverRingMap U f)) =
      e.inv ≫ Sigma.desc f ≫ S.isoSpec.hom := by
    rw [← h, Iso.inv_hom_id_assoc]
  haveI : Flat (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Flat) (fun a => inferInstance)
  apply (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (coverRingMap U f))).mp
  rw [hm]
  exact ⟨inferInstance, inferInstance⟩

/-- Tensor extension of the product coefficient algebra expressed as global
sections on the actual pairwise overlaps. -/
def coefficientTensorEquiv (I : α → Type u) [∀ a, Finite (I a)] :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    ((∀ a, Γ(U a, ⊤)) ⊗[Γ(S, ⊤)] (∀ a, I a → Γ(U a, ⊤))) ≃+*
      (∀ a b, I b → Γ(pullback (f a) (f b), ⊤)) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  exact (FiniteProductCoefficients.tensorCoefficients Γ(S, ⊤) (fun a => Γ(U a, ⊤)) I).toRingEquiv.trans
    (RingEquiv.piCongrRight fun a => RingEquiv.piCongrRight fun b =>
      RingEquiv.piCongrRight fun _ : I b => overlapTensorEquiv (f a) (f b))

@[simp] theorem coefficientTensorEquiv_tmul (I : α → Type u) [∀ a, Finite (I a)]
    (x : ∀ a, Γ(U a, ⊤)) (z : ∀ a, I a → Γ(U a, ⊤)) (a b : α) (i : I b) :
    letI (a : α) := (f a).appTop.hom.toAlgebra
    coefficientTensorEquiv U f I (x ⊗ₜ[Γ(S, ⊤)] z) a b i =
      (pullback.fst (f a) (f b)).appTop.hom (x a) *
        (pullback.snd (f a) (f b)).appTop.hom (z b i) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  exact overlapTensorEquiv_tmul (f a) (f b) (x a) (z b i)

end Family
end Langlands.AlgebraicGeometry.AffineCoverCoefficientTensors
