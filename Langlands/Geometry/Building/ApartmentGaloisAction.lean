import Langlands.Geometry.Building.RootFunctionGaloisAction

/-! # Actual coefficient actions on stable root-valuation apartments -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left] {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i) ω)

/-- Stability of this supplied full valuation class under the actual family action. -/
def GaloisStable : Prop :=
  ∀ (σ : K ≃ₐ[k] K) (φ : RootFunctionFamily T_K G_K), φ ∈ D.carrier →
    RootFunctionFamily.galoisAction k K T G σ φ ∈ D.carrier

/-- Stability of the full class is equivalent to equipollence of one of its
members with each of its actual coefficient conjugates. -/
theorem galoisStable_iff_equipollent (x : D.Apartment) :
    GaloisStable k K i D ↔ ∀ σ : K ≃ₐ[k] K,
      Equipollent x.val (RootFunctionFamily.galoisAction k K T G σ x.val) := by
  constructor
  · intro h σ
    exact D.equipollent_of_mem x.mem (h σ x.val x.mem)
  · intro h σ φ hφ
    apply (D.mem_iff_equipollent x.mem).2
    exact (h σ).trans (RootFunctionFamily.galoisAction_equipollent k K T G σ
      (D.equipollent_of_mem x.mem hφ))

variable (hD : GaloisStable k K i D)

/-- Restriction of actual coefficient transport to this same apartment. -/
def galoisAction : (K ≃ₐ[k] K) →* Equiv.Perm D.Apartment where
  toFun σ :=
    { toFun x := ⟨RootFunctionFamily.galoisAction k K T G σ x.val, hD σ x.val x.mem⟩
      invFun x := ⟨RootFunctionFamily.galoisAction k K T G σ⁻¹ x.val, hD σ⁻¹ x.val x.mem⟩
      left_inv x := by
        apply Apartment.ext
        change (RootFunctionFamily.galoisAction k K T G σ⁻¹ *
          RootFunctionFamily.galoisAction k K T G σ) x.val = x.val
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv x := by
        apply Apartment.ext
        change (RootFunctionFamily.galoisAction k K T G σ *
          RootFunctionFamily.galoisAction k K T G σ⁻¹) x.val = x.val
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by
    apply Equiv.ext
    intro x
    apply Apartment.ext
    change RootFunctionFamily.galoisAction k K T G 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply Equiv.ext
    intro x
    apply Apartment.ext
    change RootFunctionFamily.galoisAction k K T G (σ * τ) x.val =
      (RootFunctionFamily.galoisAction k K T G σ *
        RootFunctionFamily.galoisAction k K T G τ) x.val
    rw [map_mul]

@[simp] theorem galoisAction_val (σ : K ≃ₐ[k] K) (x : D.Apartment) :
    (galoisAction k K i D hD σ x).val =
      RootFunctionFamily.galoisAction k K T G σ x.val := rfl

/-- The restricted action is affine for the existing reduced translation space. -/
theorem galoisAction_vadd (σ : K ≃ₐ[k] K) (v : TranslationSpace (S := T_K) i_K)
    (x : D.Apartment) :
    galoisAction k K i D hD σ (v +ᵥ x) =
      galoisTranslationAction k K i σ v +ᵥ galoisAction k K i D hD σ x := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  apply Apartment.ext
  exact RootFunctionFamily.galoisAction_vadd k K T G σ w x.val

/-- Actual affine equivalences of this apartment, with the previously constructed
coefficient action as their linear part. -/
def galoisAffineAction : (K ≃ₐ[k] K) →* (D.Apartment ≃ᵃ[ℝ] D.Apartment) where
  toFun σ :=
    { toEquiv := galoisAction k K i D hD σ
      linear := galoisTranslationAction k K i σ
      map_vadd' := fun x v => galoisAction_vadd k K i D hD σ v x }
  map_one' := by
    apply AffineEquiv.ext
    intro x
    change galoisAction k K i D hD 1 x = x
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply AffineEquiv.ext
    intro x
    change galoisAction k K i D hD (σ * τ) x =
      (galoisAction k K i D hD σ * galoisAction k K i D hD τ) x
    rw [map_mul]

@[simp] theorem galoisAffineAction_apply (σ : K ≃ₐ[k] K) (x : D.Apartment) :
    galoisAffineAction k K i D hD σ x = galoisAction k K i D hD σ x := rfl

@[simp] theorem galoisAffineAction_linear (σ : K ≃ₐ[k] K) :
    (galoisAffineAction k K i D hD σ).linear = galoisTranslationAction k K i σ := rfl

/-- Existing apartment filtrations are exactly covariant at every real depth. -/
theorem rationalConjugate_mem_filtration_iff (σ : K ≃ₐ[k] K) (x : D.Apartment)
    (a : characterLattice T_K) (r : ℝ) (g : rationalPoints G_K) :
    rationalConjugate k K G σ g ∈
      D.filtration (galoisAction k K i D hD σ x)
        (characterLattice.galoisRepresentation k K T σ a) r ↔
      g ∈ D.filtration x a r :=
  rationalConjugate_mem_rootFiltration_iff k K i σ x.val a r g

end Langlands.Geometry.Building.KPApartmentData
