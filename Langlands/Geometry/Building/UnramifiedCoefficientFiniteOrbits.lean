import Langlands.Geometry.Building.FieldIsoCoefficientChart
import Langlands.Geometry.Building.CoefficientChartFixing
import Langlands.GroupScheme.Rational.CocharacterFiniteFixing
import Langlands.GroupScheme.Torus.SplitCocharacterGeneration
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointReduction

/-! # Finite orbits of the Galois coefficient action on the unramified building -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-- An action of `Aut(K/k)` has finite orbit at a point fixed by the fixing subgroup of a
finite intermediate field. -/
theorem finite_range_of_fixingSubgroup {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Type*} (ρ : (K ≃ₐ[k] K) →* Equiv.Perm X) (z : X) (E : IntermediateField k K)
    [FiniteDimensional k E] (hfix : ∀ σ ∈ E.fixingSubgroup, ρ σ z = z) :
    (Set.range fun σ => ρ σ z).Finite := by
  let q : (K ≃ₐ[k] K) → (E →ₐ[k] K) := fun σ => σ.toAlgHom.comp E.val
  have hq : ∀ σ τ, q σ = q τ → ρ σ z = ρ τ z := by
    intro σ τ h
    have h1 : τ⁻¹ * σ ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h2 := DFunLike.congr_fun h ⟨y, hy⟩
      change σ y = τ y at h2
      rw [AlgEquiv.mul_apply, h2, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    calc ρ σ z = ρ (τ * (τ⁻¹ * σ)) z := by rw [mul_inv_cancel_left]
      _ = ρ τ (ρ (τ⁻¹ * σ) z) := by rw [map_mul]; rfl
      _ = ρ τ z := by rw [hfix _ h1]
  let g : Set.range q → X := fun y => ρ y.2.choose z
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨σ, rfl⟩
  exact ⟨⟨q σ, σ, rfl⟩, hq _ _ (⟨q σ, σ, rfl⟩ : Set.range q).2.choose_spec⟩

namespace MaximalUnramified

open Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

private instance finiteOrbitsAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

omit [IsAffineHom G.X.hom] in
/-- `σ⁻¹` on units undoes `σ`. -/
theorem unitsCoeff_map (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (z : (inertiaFixedField F)ˣ) : unitsCoeff F σ (Units.map σ.toMonoidHom z) = z := by
  apply Units.ext
  simp [unitsCoeff]

variable (C : BuildingData F (baseChanged F (inertiaFixedField F) G))

/-- Torus compatibility of `σ` from compatibility on finitely many generating cocharacters. -/
theorem torus_compat_of_cocharacters {J : Type u} [Fintype J]
    (ν : J → cocharacterLattice C.S)
    (hgen : ∀ t : rationalPoints C.S.toGrp, ∃ x : J → (inertiaFixedField F)ˣ,
      t = ∏ j, CocharacterUniformizer.cocharacterPoints (inertiaFixedField F) C.S (ν j) (x j))
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (hσ : ∀ j t, rationalConjugate F (inertiaFixedField F) G σ
        (rationalPoints.map C.i
          (CocharacterUniformizer.cocharacterPoints (inertiaFixedField F) C.S (ν j) t)) =
      rationalPoints.map C.i (CocharacterUniformizer.cocharacterPoints (inertiaFixedField F) C.S
        (ν j) (Units.map σ.toMonoidHom t))) (t : rationalPoints C.S.toGrp) :
    ∃ t', rationalConjugateAction F (inertiaFixedField F) G σ (rationalPoints.map C.i t) =
        rationalPoints.map C.i t' ∧
      ∀ χ, unitsCoeff F σ (torusCharacterValue χ t') = torusCharacterValue χ t := by
  obtain ⟨x, hx⟩ := hgen t
  subst hx
  refine ⟨∏ j, CocharacterUniformizer.cocharacterPoints (inertiaFixedField F) C.S (ν j)
    (Units.map σ.toMonoidHom (x j)), ?_, ?_⟩
  · rw [rationalConjugateAction_apply]
    classical
    induction (Finset.univ : Finset J) using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, map_one]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, map_mul, map_mul, ih, hσ a (x a)]
  · intro χ
    simp only [torusCharacterValue, map_prod,
      CocharacterUniformizer.rationalCharacterEval_cocharacterPoints]
    rw [← unitsCoeff_map σ (∏ j, x j ^ latticePairing C.S χ (ν j))]
    congr 1
    rw [map_prod]
    exact Finset.prod_congr rfl fun j _ => (map_zpow _ _ _).symm

theorem coefficientActionData_action_mk (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (x : C.Apartment) :
    (coefficientActionData C).action σ
        (ApartmentQuotient.mk C.apartment.sharpFixerFamily (g, x)) =
      ApartmentQuotient.mk C.apartment.sharpFixerFamily
        (rationalConjugateAction F (inertiaFixedField F) G σ g * (coefficientChart C σ).c,
          (coefficientChart C σ).a x) :=
  (coefficientActionData C).action_mk σ g x

/-- A point `[(g, x)]` is fixed by `σ` when `σ` fixes `g` and the corrected chart fixes `x`. -/
theorem coefficientActionData_action_mk_eq (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (x : C.Apartment)
    (hg : rationalConjugateAction F (inertiaFixedField F) G σ g = g)
    (hx : (coefficientChart C σ).c • ApartmentQuotient.apartment C.apartment.sharpFixerFamily
        ((coefficientChart C σ).a x) =
      ApartmentQuotient.apartment C.apartment.sharpFixerFamily x) :
    (coefficientActionData C).action σ
        (ApartmentQuotient.mk C.apartment.sharpFixerFamily (g, x)) =
      ApartmentQuotient.mk C.apartment.sharpFixerFamily (g, x) := by
  rw [coefficientActionData_action_mk, hg, ApartmentQuotient.mk_eq_smul_apartment,
    ApartmentQuotient.mk_eq_smul_apartment, mul_smul, hx]

/-- **Finite orbits.** Every orbit of the Galois coefficient action on the reduced building of
an arbitrary supplied datum is finite. -/
theorem coefficientAction_finite_orbit [LocallyOfFiniteType G.X.hom] (z : C.ReducedBuilding) :
    (Set.range fun σ => (coefficientActionData C).action σ z).Finite := by
  classical
  have : Infinite F := LocalField.infinite_of_isNonarchimedeanLocalField F
  have : Infinite (inertiaFixedField F) :=
    Infinite.of_injective (algebraMap F (inertiaFixedField F))
      (algebraMap F (inertiaFixedField F)).injective
  have : LocallyOfFiniteType (baseChanged F (inertiaFixedField F) G).X.hom := by
    change LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
    infer_instance
  have hS : IsSplitTorus C.S.toGrp := C.isMaximalSplitTorus.1.1
  have : Fintype (relativeRoots C.i) := (hS.finite_relativeRoots C.i).fintype
  obtain ⟨J, hJ, ν, hgen⟩ := IsSplitTorus.exists_cocharacterPoints_prod hS
  induction z using ApartmentQuotient.ind with
  | h g x =>
  have hu : ∀ α : relativeRoots C.i, ∃ u ∈ rootGroupPoints C.i α.val, x.val α u ≠ ⊤ :=
    fun α => x.isValuation.exists_ne_top α.2
  choose u _ hne using hu
  obtain ⟨E₁, hE₁, hfix₁⟩ := GaloisCocharacterDescent.exists_finite_fixing_cocharacterValues
    F (inertiaFixedField F) G (fun j => CommGroupScheme.groupHom (ν j) ≫ C.i)
  obtain ⟨E₂, hE₂, hfix₂⟩ := TwistedGeneratorReduction.exists_finite_fixing_rationalPoints
    F (inertiaFixedField F) (G := G) (fun o : Option (relativeRoots C.i) => o.elim g u)
  have := hE₁
  have := hE₂
  have hcoch : ∀ τ ∈ E₁.fixingSubgroup, ∀ j t,
      rationalConjugate F (inertiaFixedField F) G τ
        (rationalPoints.map C.i
          (CocharacterUniformizer.cocharacterPoints (inertiaFixedField F) C.S (ν j) t)) =
      rationalPoints.map C.i (CocharacterUniformizer.cocharacterPoints (inertiaFixedField F)
        C.S (ν j) (Units.map τ.toMonoidHom t)) :=
    fun τ hτ j t => hfix₁ τ hτ j t
  apply finite_range_of_fixingSubgroup _ _ (E₁ ⊔ E₂)
  intro σ hσ
  have hσ₁ : σ ∈ E₁.fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ y (le_sup_left (a := E₁) hy)
  have hσ₂ : σ ∈ E₂.fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ y (le_sup_right (a := E₁) hy)
  have hθ := fun t => torus_compat_of_cocharacters C ν hgen σ (hcoch σ hσ₁) t
  have hθ' : ∀ t, ∃ t', rationalPoints.map C.i t =
      rationalConjugateAction F (inertiaFixedField F) G σ (rationalPoints.map C.i t') := by
    intro t
    obtain ⟨t'', ht'', -⟩ := torus_compat_of_cocharacters C ν hgen σ⁻¹
      (hcoch σ⁻¹ (inv_mem hσ₁)) t
    refine ⟨t'', ?_⟩
    rw [← ht'', rationalConjugateAction_apply, rationalConjugateAction_apply,
      ← rationalConjugate_mul, mul_inv_cancel, rationalConjugate_one]
  have hroot : ∀ α : relativeRoots C.i, ∃ u', x.val α u' ≠ ⊤ ∧
      rationalConjugateAction F (inertiaFixedField F) G σ u' = u' :=
    fun α => ⟨u α, hne α, hfix₂ σ hσ₂ (some α)⟩
  have hg : rationalConjugateAction F (inertiaFixedField F) G σ g = g := hfix₂ σ hσ₂ none
  have key := (coefficientChart C σ).c_smul_apartment_a_eq C.isConnectedReductive
    C.isMaximalSplitTorus.1 hθ hθ' x hroot
  exact coefficientActionData_action_mk_eq C σ g x hg key

/-- The Galois coefficient action on the reduced building of `C`, with its finite orbits and its
semilinearity for the rational-point action. -/
def coefficientAction :
    (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →* Equiv.Perm C.ReducedBuilding :=
  (coefficientActionData C).action

theorem coefficientAction_smul (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (z : C.ReducedBuilding) :
    coefficientAction C σ (g • z) =
      rationalConjugate F (inertiaFixedField F) G σ g • coefficientAction C σ z :=
  (coefficientActionData C).action_smul σ g z

theorem coefficientAction_finite_range [LocallyOfFiniteType G.X.hom] (z : C.ReducedBuilding) :
    (Set.range fun σ => coefficientAction C σ z).Finite :=
  coefficientAction_finite_orbit C z

end MaximalUnramified

end Langlands.Geometry.Building
