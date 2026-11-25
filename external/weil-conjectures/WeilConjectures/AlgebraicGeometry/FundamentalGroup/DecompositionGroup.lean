/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Specialization
public import WeilConjectures.Mathlib.RingTheory.Invariant.Profinite

/-!
# Decomposition and inertia groups at a point

Let `a : Spec R ⟶ Y` be a morphism from the spectrum of a domain `R` with fraction field `K`, and
`Ω / K` a separably closed Galois extension. The integral closure `B` of `R` in `Ω` gives a
geometric point `Spec Ω ⟶ Spec B ⟶ Y`, on whose fibre functor `Gal(Ω / K)` acts
(`AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut`). A maximal ideal `Q` of `B` gives a second
geometric point `Spec (B ⧸ Q) ⟶ Y`, and the specialization
`AlgebraicGeometry.Scheme.FiniteEtale.specialization` relates the two.

The decomposition group of `Q` is its stabilizer in `Gal(Ω / K)`, and the inertia group the
subgroup acting trivially on `B ⧸ Q`. The inertia group acts trivially on the generic geometric
fibres of all finite étale `Y`-schemes
(`AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut_hom_app_eq_of_mem_inertia`): through the
specialization, it acts as it does on `B ⧸ Q`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}} {R K Ω : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω] [IsSepClosed Ω] (a : Spec (.of R) ⟶ Y)

variable (Ω) in
/-- The point `Spec B ⟶ Spec R ⟶ Y` of the integral closure `B` of `R` in `Ω`. -/
noncomputable abbrev integralClosurePoint : Spec (.of (integralClosure R Ω)) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R Ω))) ≫ a

omit [IsDomain R] [IsFractionRing R K] [IsGalois K Ω] [IsSepClosed Ω] in
lemma pointOfAlgebra_integralClosurePoint :
    pointOfAlgebra Ω (integralClosurePoint Ω a) =
      pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a) := by
  simp only [pointOfAlgebra, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext x
  change algebraMap R Ω x = algebraMap K Ω (algebraMap R K x)
  rw [← IsScalarTower.algebraMap_apply]

/-- The restriction of a `K`-automorphism of `Ω` to the integral closure of `R` in `Ω`. -/
noncomputable abbrev galoisIntegralClosure (σ : Ω ≃ₐ[K] Ω) :
    integralClosure R Ω ≃+* integralClosure R Ω :=
  MulSemiringAction.toRingEquiv _ _ σ

omit [IsDomain R] [IsFractionRing R K] [IsGalois K Ω] [IsSepClosed Ω] in
lemma specMap_galoisIntegralClosure_comp (σ : Ω ≃ₐ[K] Ω) :
    Spec.map (CommRingCat.ofHom (galoisIntegralClosure (R := R) σ : integralClosure R Ω →+*
      integralClosure R Ω)) ≫ integralClosurePoint Ω a = integralClosurePoint Ω a := by
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext x
  change σ (algebraMap R Ω x) = algebraMap R Ω x
  rw [IsScalarTower.algebraMap_apply R K Ω, AlgEquiv.commutes]

/-- **Inertia acts trivially on the covers.** An element of the inertia group of a maximal ideal
`Q` of the integral closure of `R` in `Ω` acts trivially on the geometric fibre at
`Spec Ω ⟶ Spec K ⟶ Y` of every finite étale `Y`-scheme. -/
theorem galoisToAut_hom_app_eq_of_mem_inertia [ConnectedSpace Y]
    (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal] {σ : Ω ≃ₐ[K] Ω}
    (hσ : σ ∈ Q.inertia (Ω ≃ₐ[K] Ω)) (P : Y.FiniteEtale)
    (t : (fiber (pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a))).obj P) :
    (galoisToAut _ σ).asIso.hom.app P t = t := by
  let _ := Ideal.Quotient.field Q
  have : IsSepClosed (integralClosure R Ω ⧸ Q) := Ideal.isSepClosed_quotient_integralClosure K Q
  set ap := integralClosurePoint Ω a
  have h := pointOfAlgebra_integralClosurePoint (K := K) (Ω := Ω) a
  let t' : (fiber (pointOfAlgebra Ω ap)).obj P := Over.homMk t.left (by
    change t.left ≫ P.obj.hom = _
    rw [fiber_left_comp, h]
    rfl)
  have heΩ : (specMapIso σ.toRingEquiv).hom ≫ pointOfAlgebra Ω ap = pointOfAlgebra Ω ap := by
    rw [h]
    exact specMapIso_hom_comp_pointOfAlgebra _ σ
  have heκ : (specMapIso (RingEquiv.refl (integralClosure R Ω ⧸ Q))).hom ≫
      pointOfAlgebra (integralClosure R Ω ⧸ Q) ap =
        pointOfAlgebra (integralClosure R Ω ⧸ Q) ap := by
    change Spec.map (𝟙 _) ≫ _ = _
    rw [Spec.map_id, Category.id_comp]
  have key := specialization_app_fiberPrecompIso ap (galoisIntegralClosure σ) σ.toRingEquiv
    (RingEquiv.refl _) (specMap_galoisIntegralClosure_comp a σ) (by ext; rfl) (by
      ext b
      change Ideal.Quotient.mk Q (σ • b) = Ideal.Quotient.mk Q b
      rw [Ideal.Quotient.eq]
      exact hσ b) heΩ heκ P t'
  have hrefl :
      (fiberPrecompIso _ (specMapIso (RingEquiv.refl (integralClosure R Ω ⧸ Q))) heκ).hom.app
      P ((specialization Ω (integralClosure R Ω ⧸ Q) ap).app P t') =
      (specialization Ω (integralClosure R Ω ⧸ Q) ap).app P t' := by
    apply fiber_ext
    rw [fiberPrecompIso_hom_app_left]
    change Spec.map (𝟙 _) ≫ _ = _
    rw [Spec.map_id, Category.id_comp]
  rw [hrefl] at key
  have hinj : Function.Injective ((specialization Ω (integralClosure R Ω ⧸ Q) ap).app P) :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  have := congrArg Over.Hom.left (hinj key)
  apply fiber_ext
  rw [galoisToAut_hom_app_left]
  rw [fiberPrecompIso_hom_app_left] at this
  exact this

end AlgebraicGeometry.Scheme.FiniteEtale
