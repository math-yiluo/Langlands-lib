import Langlands.Geometry.Building.KPApartmentGaloisTransport

/-! # Coefficient images of supplied KP apartment classes -/

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

/-- The actual coefficient image of the whole supplied compatible valuation class.
No stability of that class under coefficient automorphisms is assumed. -/
def galoisImage (σ : K ≃ₐ[k] K)
    (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t) :
    KPApartmentData (S := T_K) i_K ω where
  carrier := RootFunctionFamily.galoisAction k K T G σ '' D.carrier
  exists_eq_orbit := by
    obtain ⟨φ, hφ, hcompat, hc⟩ := D.exists_eq_orbit
    refine ⟨RootFunctionFamily.galoisAction k K T G σ φ,
      hφ.galoisTransport k K i σ,
      IsSplitTorusCompatible.galoisTransport k K i σ hω hcompat, ?_⟩
    rw [hc]
    apply Set.ext
    intro ψ
    constructor
    · rintro ⟨χ, ⟨v, rfl⟩, rfl⟩
      exact ⟨galoisCocharacterAction k K T σ v,
        (RootFunctionFamily.galoisAction_vadd k K T G σ v φ).symm⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨v, rfl⟩ := (galoisCocharacterAction k K T σ).surjective w
      exact ⟨v +ᵥ φ, ⟨v, rfl⟩,
        RootFunctionFamily.galoisAction_vadd k K T G σ v φ⟩
  smul_mem := by
    intro n ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := hψ
    obtain ⟨m, rfl⟩ := (normalizerGaloisAction k K i σ).surjective n
    exact ⟨m • φ, D.smul_mem m φ hφ,
      RootFunctionFamily.galoisAction_smul k K i σ m φ⟩

@[simp] theorem galoisImage_carrier (σ : K ≃ₐ[k] K)
    (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t) :
    (galoisImage k K i D σ hω).carrier =
      RootFunctionFamily.galoisAction k K T G σ '' D.carrier := rfl

/-- The image class contains precisely the coefficient images of original members. -/
theorem galoisImage_mem_iff (σ : K ≃ₐ[k] K)
    (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t)
    (φ : RootFunctionFamily T_K G_K) :
    RootFunctionFamily.galoisAction k K T G σ φ ∈
        (galoisImage k K i D σ hω).carrier ↔ φ ∈ D.carrier := by
  constructor
  · rintro ⟨ψ, hψ, h⟩
    exact (RootFunctionFamily.galoisAction k K T G σ).injective h ▸ hψ
  · intro hφ
    exact ⟨φ, hφ, rfl⟩

/-- Actual coefficient transport is an equivalence to the image apartment. -/
def galoisImageEquiv (σ : K ≃ₐ[k] K)
    (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t) :
    D.Apartment ≃ (galoisImage k K i D σ hω).Apartment where
  toFun x := ⟨RootFunctionFamily.galoisAction k K T G σ x.val,
    ⟨x.val, x.mem, rfl⟩⟩
  invFun y := ⟨(RootFunctionFamily.galoisAction k K T G σ).symm y.val, by
    apply (galoisImage_mem_iff k K i D σ hω _).1
    rw [Equiv.apply_symm_apply]
    exact y.mem⟩
  left_inv x := Apartment.ext
    ((RootFunctionFamily.galoisAction k K T G σ).symm_apply_apply x.val)
  right_inv y := Apartment.ext
    ((RootFunctionFamily.galoisAction k K T G σ).apply_symm_apply y.val)

@[simp] theorem galoisImageEquiv_val (σ : K ≃ₐ[k] K)
    (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t) (x : D.Apartment) :
    (galoisImageEquiv k K i D σ hω x).val =
      RootFunctionFamily.galoisAction k K T G σ x.val := rfl

/-- The apartment equivalence intertwines reduced translations by the actual
coefficient linear action. -/
theorem galoisImageEquiv_vadd (σ : K ≃ₐ[k] K)
    (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t)
    (v : TranslationSpace (S := T_K) i_K) (x : D.Apartment) :
    galoisImageEquiv k K i D σ hω (v +ᵥ x) =
      galoisTranslationAction k K i σ v +ᵥ galoisImageEquiv k K i D σ hω x := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  apply Apartment.ext
  exact RootFunctionFamily.galoisAction_vadd k K T G σ w x.val

/-- The actual affine equivalence from a supplied apartment to its coefficient image. -/
def galoisImageAffineEquiv (σ : K ≃ₐ[k] K)
    (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t) :
    D.Apartment ≃ᵃ[ℝ] (galoisImage k K i D σ hω).Apartment where
  toEquiv := galoisImageEquiv k K i D σ hω
  linear := galoisTranslationAction k K i σ
  map_vadd' := fun x v => galoisImageEquiv_vadd k K i D σ hω v x

@[simp] theorem galoisImageAffineEquiv_linear (σ : K ≃ₐ[k] K)
    (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t) :
    (galoisImageAffineEquiv k K i D σ hω).linear =
      galoisTranslationAction k K i σ := rfl

/-- The image equivalence intertwines the actual normalizer actions. -/
theorem galoisImageEquiv_normalizer_smul (σ : K ≃ₐ[k] K)
    (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t)
    (n : normalizerPoints (T := T_K) i_K) (x : D.Apartment) :
    galoisImageEquiv k K i D σ hω (n • x) =
      normalizerGaloisAction k K i σ n • galoisImageEquiv k K i D σ hω x := by
  apply Apartment.ext
  exact RootFunctionFamily.galoisAction_smul k K i σ n x.val

/-- Every root filtration is transported at the original real depth. -/
theorem rationalConjugate_mem_galoisImage_filtration_iff (σ : K ≃ₐ[k] K)
    (hω : ∀ t, ω (Units.map σ.toMonoidHom t) = ω t) (x : D.Apartment)
    (a : characterLattice T_K) (r : ℝ) (g : rationalPoints G_K) :
    rationalConjugate k K G σ g ∈
        (galoisImage k K i D σ hω).filtration (galoisImageEquiv k K i D σ hω x)
          (characterLattice.galoisRepresentation k K T σ a) r ↔
      g ∈ D.filtration x a r :=
  rationalConjugate_mem_rootFiltration_iff k K i σ x.val a r g

end Langlands.Geometry.Building.KPApartmentData
