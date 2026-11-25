/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit

/-!
# The composition pairing at the point over a field

Let `Λ` be a finite field. In the derived category `D(Λ)`, with unit `U = Λ[0]`, the composition
pairing
`Hom(U, E) × Hom(E, U) ⟶ End(U) = Λ`
is nondegenerate on both sides as soon as `H^0(E)` is finite-dimensional: over a field `E` is
split, `E ≅ ⊕ H^n(E)[-n]`, and both sides are computed by the degree-zero summand. Through the
equivalence `RΓ(Spec k, -) : D(Spec k_ét, Λ) ≌ D(Λ)` for `k` separably closed, the same holds
in the point category, with `U` the unit `Λ_s`.

This is the input from linear algebra for the degreewise perfectness of the Poincaré pairings
over a field (`WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Perfectness`).

## Main statements

- `LinearMap.isPerfPair_of_comp`: a bilinear pairing which is a composition pairing
  `⟨x, y⟩ = ℓ(x ≫ g(y))` with `g` bijective and both sides nondegenerate is perfect.
- `DerivedCategory.nondegenerate_comp_singleFunctor_of_isField`: the composition pairing with
  `Λ[0]` in `D(Λ)` is nondegenerate.
- `AlgebraicGeometry.Etale.nondegenerate_comp_unit_of_isSepClosed`: the composition pairing with
  the unit `Λ_s` of the point category is nondegenerate.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

/-- A bilinear pairing `p` on `Hom(U, E) × W` which is a composition pairing
`p(x, y) = ℓ(x ≫ g(y))`, for a bijection `g : W ≃ Hom(E, U)` and a map `ℓ` on `End(U)` vanishing
only at `0`, is perfect over a field as soon as `Hom(U, E)` is finite and the composition
pairing `Hom(U, E) × Hom(E, U) ⟶ End(U)` is nondegenerate on both sides. -/
lemma LinearMap.isPerfPair_of_comp {K : Type*} [CommRing K] (hK : IsField K) {C : Type*}
    [Category C] [Preadditive C] {U E : C} [Module K (U ⟶ E)] [Finite (U ⟶ E)] {W : Type*}
    [AddCommGroup W] [Module K W] (p : (U ⟶ E) →ₗ[K] W →ₗ[K] K) (g : W → (E ⟶ U))
    (hg : Function.Bijective g) (hg₀ : g 0 = 0) (ℓ : (U ⟶ U) → K) (hℓ : ∀ z, ℓ z = 0 → z = 0)
    (hp : ∀ x y, p x y = ℓ (x ≫ g y)) (h₁ : ∀ x : U ⟶ E, x ≠ 0 → ∃ f : E ⟶ U, x ≫ f ≠ 0)
    (h₂ : ∀ f : E ⟶ U, f ≠ 0 → ∃ x : U ⟶ E, x ≫ f ≠ 0) : p.IsPerfPair := by
  let _ := hK.toField
  have : Module.Finite K (U ⟶ E) := Module.Finite.of_finite
  refine LinearMap.IsPerfPair.of_injective ((injective_iff_map_eq_zero p).2 fun x hx ↦ ?_)
    ((injective_iff_map_eq_zero p.flip).2 fun y hy ↦ ?_)
  · by_contra hx0
    obtain ⟨f, hf⟩ := h₁ x hx0
    obtain ⟨y, rfl⟩ := hg.2 f
    exact hf (hℓ _ ((hp x y).symm.trans (LinearMap.congr_fun hx y)))
  · refine hg.1 (hg₀.symm ▸ ?_)
    by_contra hy0
    obtain ⟨x, hx⟩ := h₂ (g y) hy0
    exact hx (hℓ _ ((hp x y).symm.trans (LinearMap.congr_fun hy x)))

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D)
  [F.Full] [F.Faithful] [F.PreservesZeroMorphisms] {U E : C} {U' E' : D}

/-- Nondegeneracy of the composition pairing `Hom(U, E) × Hom(E, U) ⟶ End(U)` on the left is
reflected by a fully faithful functor `F`, with `F(U) ≅ U'` and `F(E) ≅ E'`. -/
lemma exists_comp_ne_zero_of_fullyFaithful (eU : F.obj U ≅ U') (eE : F.obj E ≅ E')
    (h : ∀ x : U' ⟶ E', x ≠ 0 → ∃ f : E' ⟶ U', x ≫ f ≠ 0) (x : U ⟶ E) (hx : x ≠ 0) :
    ∃ f : E ⟶ U, x ≫ f ≠ 0 := by
  obtain ⟨f', hf'⟩ := h (eU.inv ≫ F.map x ≫ eE.hom) fun h0 ↦ hx <| by
    rw [← F.map_eq_zero_iff]
    simpa using congrArg (fun z ↦ eU.hom ≫ z ≫ eE.inv) h0
  refine ⟨F.preimage (eE.hom ≫ f' ≫ eU.inv), fun h0 ↦ hf' ?_⟩
  have := congrArg (fun z ↦ eU.inv ≫ F.map z ≫ eU.hom) h0
  simpa using this

/-- Nondegeneracy of the composition pairing `Hom(U, E) × Hom(E, U) ⟶ End(U)` on the right is
reflected by a fully faithful functor `F`, with `F(U) ≅ U'` and `F(E) ≅ E'`. -/
lemma exists_comp_ne_zero_of_fullyFaithful' (eU : F.obj U ≅ U') (eE : F.obj E ≅ E')
    (h : ∀ f : E' ⟶ U', f ≠ 0 → ∃ x : U' ⟶ E', x ≫ f ≠ 0) (f : E ⟶ U) (hf : f ≠ 0) :
    ∃ x : U ⟶ E, x ≫ f ≠ 0 := by
  obtain ⟨x', hx'⟩ := h (eE.inv ≫ F.map f ≫ eU.hom) fun h0 ↦ hf <| by
    rw [← F.map_eq_zero_iff]
    simpa using congrArg (fun z ↦ eE.hom ≫ z ≫ eU.inv) h0
  refine ⟨F.preimage (eU.hom ≫ x' ≫ eE.inv), fun h0 ↦ hx' ?_⟩
  have := congrArg (fun z ↦ eU.inv ≫ F.map z ≫ eU.hom) h0
  simpa using this

omit [Preadditive C] [Preadditive D] [F.PreservesZeroMorphisms] in
/-- Finiteness of `Hom(U, E)` is reflected by a fully faithful functor. -/
lemma finite_hom_of_fullyFaithful (eU : F.obj U ≅ U') (eE : F.obj E ≅ E')
    [Finite (U' ⟶ E')] : Finite (U ⟶ E) :=
  Finite.of_equiv _ ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
    (eU.homCongr eE)).symm

end CategoryTheory.Functor

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

instance : Projective (ModuleCat.of R R) :=
  ModuleCat.projective_of_free (Module.Basis.singleton Unit R)

/-- For a module `M` over `R`, morphisms `R[0] ⟶ E` in `D(R)` are the elements of `H^0(E)`. -/
noncomputable def homSingleRingEquiv (E : DerivedCategory (ModuleCat.{u} R)) :
    ((singleFunctor _ 0).obj (ModuleCat.of R R) ⟶ E) ≃
      (homologyFunctor (ModuleCat.{u} R) 0).obj E :=
  (homSingleEquivOfProjective (ModuleCat.of R R) 0 E).trans
    (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ _).toEquiv)

/-- **The composition pairing with `R[0]` is nondegenerate over a finite field.** Let `R` be a
finite field and `E ∈ D(R)` with `H^0(E)` finite-dimensional. Then `Hom(R[0], E)` is finite and
the composition pairing `Hom(R[0], E) × Hom(E, R[0]) ⟶ End(R[0])` is nondegenerate on both
sides.

As in the blueprint (`corollary-degreewise-duality-over-fields--1`), `E` is split: it is the complex
`H` of its cohomology spaces with zero differential. The inclusion and the projection of the
degree-zero summand `H^0(E)[0]` give, for `v ∈ H^0(E)` and `φ ∈ H^0(E)^∨`, morphisms
`x_v : R[0] ⟶ E` and `f_φ : E ⟶ R[0]` with `x_v ≫ f_φ = φ(v)`. Counting, `v ↦ x_v` and
`φ ↦ f_φ` are bijective: `Hom(R[0], E) = H^0(E)`, and `Hom(E, R[0]) = H^0(E^∨) ≅ H^0(E)^∨`
(`DerivedCategory.nonempty_iso_homology_ihom`). -/
theorem nondegenerate_comp_singleFunctor_of_isField (hR : IsField R) [Finite R]
    (E : DerivedCategory (ModuleCat.{u} R))
    (hE : Module.Finite R ((homologyFunctor (ModuleCat.{u} R) 0).obj E)) :
    Finite ((singleFunctor _ 0).obj (ModuleCat.of R R) ⟶ E) ∧
      (∀ x : (singleFunctor _ 0).obj (ModuleCat.of R R) ⟶ E, x ≠ 0 →
        ∃ f : E ⟶ (singleFunctor _ 0).obj (ModuleCat.of R R), x ≫ f ≠ 0) ∧
      (∀ f : E ⟶ (singleFunctor _ 0).obj (ModuleCat.of R R), f ≠ 0 →
        ∃ x : (singleFunctor _ 0).obj (ModuleCat.of R R) ⟶ E, x ≫ f ≠ 0) := by
  let _ := hR.toField
  have : IsSemisimpleRing R := inferInstance
  obtain ⟨H, φ, hφ, hd, eH⟩ := exists_quasiIso_of_zero_differential (Q.objPreimage E)
  have : IsIso (Q.map φ) := (isIso_Q_map_iff_quasiIso (C := ModuleCat.{u} R) φ).2 hφ
  let e : Q.obj H ≅ E := asIso (Q.map φ) ≪≫ Q.objObjPreimageIso E
  let S := HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0
  let ι : S.obj (H.X 0) ⟶ H :=
    HomologicalComplex.mkHomFromSingle (𝟙 _) (fun k _ ↦ by simp [hd])
  let π : H ⟶ S.obj (H.X 0) :=
    HomologicalComplex.mkHomToSingle (𝟙 _) (fun k _ ↦ by simp [hd])
  have hιπ : ι ≫ π = 𝟙 _ := by
    apply HomologicalComplex.from_single_hom_ext
    simp [ι, π]
    rfl
  -- The identification `H^0(E) ≅ H.X 0`.
  let eE : (homologyFunctor (ModuleCat.{u} R) 0).obj E ≅ H.X 0 :=
    (homologyFunctor _ 0).mapIso (Q.objObjPreimageIso E).symm ≪≫
      (homologyFunctorFactors _ 0).app _ ≪≫ (eH 0).some.symm
  have : Module.Finite R (H.X 0) := Module.Finite.equiv eE.toLinearEquiv
  have : Finite (H.X 0) := Module.finite_of_finite R
  have : Finite (Module.Dual R (H.X 0)) := Module.finite_of_finite R
  let U := (singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  -- The scalars `r • 𝟙` of `R[0]`.
  let T : R → (U ⟶ U) := fun r ↦ r • 𝟙 U
  have hT₁ : ∀ r, T r = (singleFunctor (ModuleCat.{u} R) 0).map (r • 𝟙 (ModuleCat.of R R)) :=
    fun r ↦ by simp [T, Functor.map_smul]; rfl
  have hT : ∀ r, T r = 0 ↔ r = 0 := fun r ↦ by
    rw [hT₁, Functor.map_eq_zero_iff]
    constructor
    · intro h
      simpa using congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R ↦ f.hom 1) h
    · rintro rfl
      simp
  have hTinj : Function.Injective T := fun r r' h ↦ by
    rw [← sub_eq_zero, ← hT]
    simp only [T, sub_smul, h, sub_self]
  let Φ : H.X 0 → (U ⟶ E) := fun v ↦
    Q.map (S.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ v)) ≫ ι) ≫ e.hom
  let Ψ : Module.Dual R (H.X 0) → (E ⟶ U) := fun χ ↦
    e.inv ≫ Q.map (π ≫ S.map (ModuleCat.ofHom χ))
  have key : ∀ v χ, Φ v ≫ Ψ χ = T (χ v) := fun v χ ↦ by
    have : Φ v ≫ Ψ χ = Q.map (S.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ v) ≫
        ModuleCat.ofHom χ)) := by
      simp only [Φ, Ψ, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp]
      rw [reassoc_of% hιπ]
      simp only [Functor.map_comp]
    rw [this, hT₁]
    change Q.map (S.map _) = Q.map (S.map _)
    congr 2
    ext
    simp
  have hΦ₀ : Φ 0 = 0 := by simp [Φ]
  have hΨ₀ : Ψ 0 = 0 := by simp [Ψ]
  have hΦ : Function.Injective Φ := fun v v' h ↦ by
    rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff R _).1 fun χ ↦ ?_
    rw [map_sub, sub_eq_zero]
    exact hTinj (by rw [← key, ← key, h])
  have hΨ : Function.Injective Ψ := fun χ χ' h ↦ by
    ext v
    exact hTinj (by rw [← key, ← key, h])
  -- Counting.
  let eV : (U ⟶ E) ≃ H.X 0 := (homSingleRingEquiv E).trans eE.toLinearEquiv.toEquiv
  have : Finite (U ⟶ E) := Finite.of_equiv _ eV.symm
  obtain ⟨eD⟩ := nonempty_iso_homology_ihom hR E 0
  rw [neg_zero] at eD
  let eW : (E ⟶ U) ≃ Module.Dual R (H.X 0) :=
    ((Iso.refl E).homCongr (singleFunctorObjUnitIso (ModuleCat.{u} R))).trans <|
      ((ρ_ E).homCongr (Iso.refl _)).symm.trans <|
        ((ihom.adjunction E).homEquiv _ _).trans <|
          ((singleFunctorObjUnitIso (ModuleCat.{u} R)).homCongr (Iso.refl _)).symm.trans <|
            (homSingleRingEquiv _).trans <| eD.toLinearEquiv.toEquiv.trans
              eE.symm.toLinearEquiv.dualMap.toEquiv
  have : Finite (E ⟶ U) := Finite.of_equiv _ eW.symm
  have hΦb : Function.Bijective Φ :=
    hΦ.bijective_of_nat_card_le (Nat.card_congr eV).le
  have hΨb : Function.Bijective Ψ :=
    hΨ.bijective_of_nat_card_le (Nat.card_congr eW).le
  refine ⟨inferInstance, fun x hx ↦ ?_, fun f hf ↦ ?_⟩
  · obtain ⟨v, rfl⟩ := hΦb.2 x
    have hv : v ≠ 0 := by rintro rfl; exact hx hΦ₀
    obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual R (H.X 0), χ v ≠ 0 := by
      by_contra! h
      exact hv ((Module.forall_dual_apply_eq_zero_iff R v).1 h)
    exact ⟨Ψ χ, by rw [key, Ne, hT]; exact hχ⟩
  · obtain ⟨χ, rfl⟩ := hΨb.2 f
    have hχ : χ ≠ 0 := by rintro rfl; exact hf hΨ₀
    obtain ⟨v, hv⟩ : ∃ v, χ v ≠ 0 := by
      by_contra! h
      exact hχ (LinearMap.ext h)
    exact ⟨Φ v, by rw [key, Ne, hT]; exact hv⟩

end DerivedCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

variable (Λ k) in
/-- Over a separably closed field `k`, the derived global sections of the unit `Λ_s` of the point
category are `Λ[0]`. -/
noncomputable def rightDerivedGlobalSectionsUnitIso :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of Λ Λ) :=
  (rightDerivedGlobalSections _ _).mapIso (unitIsoSingleFunctorConstantSheaf Λ _) ≪≫
    (rightDerivedGlobalSectionsIsoMapDerivedCategoryInv _ _).app _ ≪≫
      ((constantSheaf (Spec (.of k)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).inv.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          ((constantSheaf (Spec (.of k)).smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).asEquivalence.unitIso.app _).symm

/-- **The composition pairing with the unit is nondegenerate at the point.** Let `k` be a
separably closed field, `Λ` a finite field and `E` an object of the point category
`D(Spec k_ét, Λ)` with `H^0(RΓ(Spec k, E))` finite-dimensional. Then `Hom(Λ_s, E)` is finite and
the composition pairing `Hom(Λ_s, E) × Hom(E, Λ_s) ⟶ End(Λ_s)` is nondegenerate on both sides.
This follows from the case of `D(Λ)`
(`DerivedCategory.nondegenerate_comp_singleFunctor_of_isField`) through the equivalence
`RΓ(Spec k, -)` (blueprint `theorem-global-verdier-duality`). -/
theorem nondegenerate_comp_unit_of_isSepClosed (hΛ : IsField Λ) [Finite Λ]
    (E : DerivedCategoryModule Λ (Spec (.of k)))
    (hE : Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj E))) :
    Finite (𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ E) ∧
      (∀ x : 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))) ⟶ E, x ≠ 0 →
        ∃ f : E ⟶ 𝟙_ _, x ≫ f ≠ 0) ∧
      (∀ f : E ⟶ 𝟙_ (DerivedCategoryModule Λ (Spec (.of k))), f ≠ 0 →
        ∃ x : 𝟙_ _ ⟶ E, x ≫ f ≠ 0) := by
  let F := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  obtain ⟨h₀, h₁, h₂⟩ := DerivedCategory.nondegenerate_comp_singleFunctor_of_isField hΛ _ hE
  exact ⟨F.finite_hom_of_fullyFaithful (rightDerivedGlobalSectionsUnitIso Λ k) (Iso.refl _),
    F.exists_comp_ne_zero_of_fullyFaithful (rightDerivedGlobalSectionsUnitIso Λ k)
      (Iso.refl _) h₁,
    F.exists_comp_ne_zero_of_fullyFaithful' (rightDerivedGlobalSectionsUnitIso Λ k)
      (Iso.refl _) h₂⟩

end AlgebraicGeometry.Etale
