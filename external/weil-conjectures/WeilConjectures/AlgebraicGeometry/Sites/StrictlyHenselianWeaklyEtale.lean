/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianLift

/-!
# Sections of weakly étale schemes over a strictly henselian local scheme

Let `A` be a strictly henselian local ring. A weakly étale morphism `f : Y ⟶ Spec A` has a
section through every point `y` of `Y` over the closed point
(`AlgebraicGeometry.Scheme.exists_section_apply_eq_of_weaklyEtale_of_isStrictlyHenselianLocalRing`):
if `Spec B ⊆ Y` is an affine open containing `y` and `n ⊆ B` the corresponding prime, the local
homomorphism `A ⟶ B_n` is weakly étale, hence bijective by Olivier's theorem
(`Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing`). This is the weakly étale
version of `AlgebraicGeometry.Scheme.exists_section_apply_eq_of_isStrictlyHenselianLocalRing`.

The section can be chosen through any given geometric point of `Y` over a geometric point of
the closed point (`AlgebraicGeometry.Scheme.exists_section_comp_eq_of_weaklyEtale`), since a
morphism with a section through `y` induces an isomorphism of residue fields at `y`
(`AlgebraicGeometry.Scheme.Hom.surjective_residueFieldMap_of_comp_eq_id`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- If `σ` is a section of `f : Y ⟶ X`, then the residue field map of `f` at `σ x` is
surjective: it is inverse to the residue field map of `σ` at `x`. -/
lemma Hom.surjective_residueFieldMap_of_comp_eq_id {X Y : Scheme.{u}} (σ : X ⟶ Y) (f : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 X) (x : X) : Function.Surjective (f.residueFieldMap (σ x)) := by
  intro b
  let e := X.residueFieldCongr (x := (σ ≫ f) x) (y := (𝟙 X) x) (by rw [hσ])
  refine ⟨e.inv (σ.residueFieldMap x b), (σ.residueFieldMap x).hom.injective ?_⟩
  have h₁ := ConcreteCategory.congr_hom (residueFieldMap_comp σ f x)
    (e.inv (σ.residueFieldMap x b))
  have h₂ := ConcreteCategory.congr_hom (Hom.residueFieldMap_congr hσ x)
    (e.inv (σ.residueFieldMap x b))
  rw [residueFieldMap_id] at h₂
  exact (h₁.symm.trans h₂).trans (ConcreteCategory.congr_hom e.inv_hom_id _)

variable {A : Type u} [CommRing A] [IsStrictlyHenselianLocalRing A]

set_option backward.isDefEq.respectTransparency.types false in
/-- Over a strictly henselian local ring `A`, a weakly étale morphism `f : Y ⟶ Spec A` has a
section through every point `y` of `Y` over the closed point. -/
theorem exists_section_apply_eq_of_weaklyEtale_of_isStrictlyHenselianLocalRing {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of A)) [WeaklyEtale f] (y : Y) (hy : f y = IsLocalRing.closedPoint A) :
    ∃ σ : Spec (.of A) ⟶ Y, σ ≫ f = 𝟙 _ ∧ σ (IsLocalRing.closedPoint A) = y := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hV : IsAffineOpen V := hV
  let B := Γ(Y, V)
  let φ : CommRingCat.of A ⟶ B := Spec.preimage (hV.fromSpec ≫ f)
  have hφ : Spec.map φ = hV.fromSpec ≫ f := Spec.map_preimage _
  have hφe : φ.hom.WeaklyEtale := by
    rw [← HasRingHomProperty.Spec_iff (P := @WeaklyEtale), hφ]
    infer_instance
  algebraize [φ.hom]
  let n := hV.primeIdealOf ⟨y, hyV⟩
  have hn : n.asIdeal.comap φ.hom = IsLocalRing.maximalIdeal A := by
    have h : (Spec.map φ) n = IsLocalRing.closedPoint A := by
      change (Spec.map φ) (hV.primeIdealOf ⟨y, hyV⟩) = _
      rw [hφ, Scheme.Hom.comp_apply, hV.fromSpec_primeIdealOf, hy]
    exact congrArg PrimeSpectrum.asIdeal h
  let Bn := Localization.AtPrime n.asIdeal
  have : Algebra.WeaklyEtale A B := (RingHom.weaklyEtale_algebraMap_iff).1 hφe
  have : Algebra.WeaklyEtale A Bn := Algebra.WeaklyEtale.trans A B Bn
  have : IsLocalHom (algebraMap A Bn) := by
    refine ⟨fun x hx ↦ ?_⟩
    rw [IsScalarTower.algebraMap_apply A B Bn,
      IsLocalization.AtPrime.isUnit_to_map_iff Bn n.asIdeal] at hx
    by_contra hx'
    exact hx (by
      have : x ∈ IsLocalRing.maximalIdeal A := hx'
      rw [← hn] at this
      exact this)
  have hbij := Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing (R := A) (S := Bn)
  let e : A ≃+* Bn := RingEquiv.ofBijective (algebraMap A Bn) hbij
  let ψ : B ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (e.symm.toRingHom.comp (algebraMap B Bn))
  have hψ : φ ≫ ψ = 𝟙 _ := by
    ext x
    change e.symm (algebraMap B Bn (algebraMap A B x)) = x
    rw [← IsScalarTower.algebraMap_apply A B Bn]
    exact e.symm_apply_apply x
  refine ⟨Spec.map ψ ≫ hV.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, hψ, Spec.map_id]
  · rw [Scheme.Hom.comp_apply]
    have hpt : (Spec.map ψ) (IsLocalRing.closedPoint A) = n := by
      apply PrimeSpectrum.ext
      change Ideal.comap (e.symm.toRingHom.comp (algebraMap B Bn))
        (IsLocalRing.maximalIdeal A) = n.asIdeal
      rw [← Ideal.comap_comap]
      have he : Ideal.comap e.symm.toRingHom (IsLocalRing.maximalIdeal A) =
          IsLocalRing.maximalIdeal Bn := by
        ext b
        simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact (isUnit_map_iff e.symm b).not
      rw [he]
      exact Localization.AtPrime.under_maximalIdeal
    rw [hpt]
    exact hV.fromSpec_primeIdealOf ⟨y, hyV⟩

/-- Over a strictly henselian local ring `A`, let `c : Spec K ⟶ Spec A` be a morphism from the
spectrum of a field onto the closed point. Then a weakly étale morphism `f : Y ⟶ Spec A` has a
section through every lift `y : Spec K ⟶ Y` of `c`. -/
theorem exists_section_comp_eq_of_weaklyEtale {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of A)) [WeaklyEtale f] (c : Spec (.of K) ⟶ Spec (.of A))
    (hc : c (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint A) (y : Spec (.of K) ⟶ Y)
    (hy : y ≫ f = c) : ∃ σ : Spec (.of A) ⟶ Y, σ ≫ f = 𝟙 _ ∧ c ≫ σ = y := by
  have hy₀ : f (y (IsLocalRing.closedPoint K)) = IsLocalRing.closedPoint A := by
    rw [← Scheme.Hom.comp_apply, hy, hc]
  obtain ⟨σ, hσ, hσy⟩ :=
    exists_section_apply_eq_of_weaklyEtale_of_isStrictlyHenselianLocalRing f _ hy₀
  have hpt : (c ≫ σ) (IsLocalRing.closedPoint K) = y (IsLocalRing.closedPoint K) := by
    rw [Scheme.Hom.comp_apply, hc, hσy]
  refine ⟨σ, hσ, eq_of_comp_eq_of_surjective_residueFieldMap f _ y ?_ hpt ?_⟩
  · rw [Category.assoc, hσ, Category.comp_id, hy]
  · rw [Scheme.Hom.comp_apply, hc]
    exact Hom.surjective_residueFieldMap_of_comp_eq_id σ f hσ _

end AlgebraicGeometry.Scheme
