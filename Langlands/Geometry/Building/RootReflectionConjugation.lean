import Langlands.Geometry.Building.ApartmentRootReflections

/-! # Actual normalizer conjugation of affine root groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The affine functional transported by the actual normalizer action:
`(n ψ)(x) = ψ(n⁻¹ x)`. -/
def conjugateAffineFunctional (n : normalizerPoints i) (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    D.Apartment →ᵃ[ℝ] ℝ :=
  ψ.comp (D.normalizerAffineEquiv n⁻¹).toAffineMap

@[simp]
theorem conjugateAffineFunctional_apply (n : normalizerPoints i)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (x : D.Apartment) :
    D.conjugateAffineFunctional n ψ x = ψ (n⁻¹ • x) :=
  rfl

@[simp]
theorem conjugateAffineFunctional_inv (n : normalizerPoints i)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    D.conjugateAffineFunctional n⁻¹ (D.conjugateAffineFunctional n ψ) = ψ := by
  ext x
  simp only [conjugateAffineFunctional_apply, inv_inv, inv_smul_smul]

theorem conjugateAffineFunctional_add_const (n : normalizerPoints i)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (c : ℝ) :
    D.conjugateAffineFunctional n (ψ + AffineMap.const ℝ D.Apartment c) =
      D.conjugateAffineFunctional n ψ + AffineMap.const ℝ D.Apartment c := by
  ext x
  rfl

theorem conjugateAffineFunctional_neg (n : normalizerPoints i)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    D.conjugateAffineFunctional n (-ψ) = -D.conjugateAffineFunctional n ψ := by
  ext x
  rfl

/-- Conjugation transports the actual weak affine root filtration. -/
theorem conj_mem_affineRootGroup (n : normalizerPoints i)
    {a : characterLattice S} {ψ : D.Apartment →ᵃ[ℝ] ℝ}
    {u : rationalPoints G} (hu : u ∈ D.affineRootGroup a ψ) :
    (n : rationalPoints G) * u * (n : rationalPoints G)⁻¹ ∈
      D.affineRootGroup (weylAction i n a) (D.conjugateAffineFunctional n ψ) := by
  rw [affineRootGroup, Subgroup.mem_iInf] at hu ⊢
  intro x
  have h := D.conj_mem_filtration n (hu (n⁻¹ • x))
  simpa only [smul_inv_smul, conjugateAffineFunctional_apply] using h

/-- Equality of actual affine root groups under normalizer conjugation. -/
theorem conj_affineRootGroup (n : normalizerPoints i) (a : characterLattice S)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    (D.affineRootGroup a ψ).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
      D.affineRootGroup (weylAction i n a) (D.conjugateAffineFunctional n ψ) := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact D.conj_mem_affineRootGroup n hu
  · intro u hu
    refine ⟨(n : rationalPoints G)⁻¹ * u * (n : rationalPoints G), ?_, ?_⟩
    · change (n : rationalPoints G)⁻¹ * u * (n : rationalPoints G) ∈
        D.affineRootGroup a ψ
      have h := D.conj_mem_affineRootGroup n⁻¹ hu
      simpa only [weylAction_inv_apply_apply, conjugateAffineFunctional_inv,
        Subgroup.coe_inv, inv_inv] using h
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

/-- Conjugation transports the actual strict affine root filtration. -/
theorem conj_mem_affineRootGroupPlus (n : normalizerPoints i)
    {a : characterLattice S} {ψ : D.Apartment →ᵃ[ℝ] ℝ}
    {u : rationalPoints G} (hu : u ∈ D.affineRootGroupPlus a ψ) :
    (n : rationalPoints G) * u * (n : rationalPoints G)⁻¹ ∈
      D.affineRootGroupPlus (weylAction i n a) (D.conjugateAffineFunctional n ψ) := by
  obtain ⟨c, hc, hu⟩ := mem_affineRootGroupPlus.1 hu
  refine mem_affineRootGroupPlus.2 ⟨c, hc, ?_⟩
  have h := D.conj_mem_affineRootGroup n hu
  rwa [conjugateAffineFunctional_add_const] at h

/-- Equality of actual strict affine root groups under normalizer conjugation. -/
theorem conj_affineRootGroupPlus (n : normalizerPoints i) (a : characterLattice S)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    (D.affineRootGroupPlus a ψ).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
      D.affineRootGroupPlus (weylAction i n a) (D.conjugateAffineFunctional n ψ) := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact D.conj_mem_affineRootGroupPlus n hu
  · intro u hu
    refine ⟨(n : rationalPoints G)⁻¹ * u * (n : rationalPoints G), ?_, ?_⟩
    · change (n : rationalPoints G)⁻¹ * u * (n : rationalPoints G) ∈
        D.affineRootGroupPlus a ψ
      have h := D.conj_mem_affineRootGroupPlus n⁻¹ hu
      simpa only [weylAction_inv_apply_apply, conjugateAffineFunctional_inv,
        Subgroup.coe_inv, inv_inv] using h
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

/-- A normalizer point acting as the reflection of `ψ` transports `ψ` to `-ψ`. -/
theorem conjugateAffineFunctional_eq_neg_of_reflection
    (n : normalizerPoints i) (ψ : D.Apartment →ᵃ[ℝ] ℝ)
    {v : TranslationSpace i} (hv : ψ.linear v = 2)
    (hn : D.normalizerAffineEquiv n = AffineRootSystem.affineReflection ψ hv) :
    D.conjugateAffineFunctional n ψ = -ψ := by
  ext x
  change ψ (n⁻¹ • x) = -ψ x
  have h := congrArg (fun e : D.Apartment ≃ᵃ[ℝ] D.Apartment => ψ (e (n⁻¹ • x))) hn
  simp only [normalizerAffineEquiv_apply, smul_inv_smul,
    AffineRootSystem.apply_affineReflection] at h
  linarith

end KPApartmentData

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    {α : relativeRoots B.i} {u : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- A supplied nonidentity root-point representative negates its actual root. -/
theorem weylAction_reflectionElement
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p) :
    weylAction B.i (B.reflectionElement hp) α = -(α : characterLattice B.S) :=
  hp.weylAction_eq_neg B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hu hu1

/-- The functional of an actual supplied root reflection is sent to its negative. -/
theorem conjugateAffineFunctional_reflectionElement
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p) :
    B.apartment.conjugateAffineFunctional (B.reflectionElement hp)
      (B.reflectionFunctional α u) = -B.reflectionFunctional α u :=
  B.apartment.conjugateAffineFunctional_eq_neg_of_reflection _ _
    (B.rootForm_reflectionCoroot hu hu1 hp)
    (B.normalizerAffineEquiv_reflectionElement hu hu1 hp)

/-- A supplied actual reflection interchanges the two weak affine root groups. -/
theorem conj_affineRootGroup_reflectionElement
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p) :
    (B.affineRootGroup α (B.reflectionFunctional α u)).map
        (MulAut.conj (B.reflectionElement hp : rationalPoints G)).toMonoidHom =
      B.affineRootGroup (-(α : characterLattice B.S)) (-B.reflectionFunctional α u) := by
  rw [B.apartment.conj_affineRootGroup,
    B.weylAction_reflectionElement hu hu1 hp,
    B.conjugateAffineFunctional_reflectionElement hu hu1 hp]

/-- The opposite weak affine root group is sent back by the same representative. -/
theorem conj_neg_affineRootGroup_reflectionElement
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p) :
    (B.affineRootGroup (-(α : characterLattice B.S)) (-B.reflectionFunctional α u)).map
        (MulAut.conj (B.reflectionElement hp : rationalPoints G)).toMonoidHom =
      B.affineRootGroup α (B.reflectionFunctional α u) := by
  rw [B.apartment.conj_affineRootGroup, map_neg,
    B.weylAction_reflectionElement hu hu1 hp,
    B.apartment.conjugateAffineFunctional_neg,
    B.conjugateAffineFunctional_reflectionElement hu hu1 hp, neg_neg, neg_neg]

/-- A supplied actual reflection interchanges the two strict affine root groups. -/
theorem conj_affineRootGroupPlus_reflectionElement
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p) :
    (B.apartment.affineRootGroupPlus α (B.reflectionFunctional α u)).map
        (MulAut.conj (B.reflectionElement hp : rationalPoints G)).toMonoidHom =
      B.apartment.affineRootGroupPlus (-(α : characterLattice B.S))
        (-B.reflectionFunctional α u) := by
  rw [B.apartment.conj_affineRootGroupPlus,
    B.weylAction_reflectionElement hu hu1 hp,
    B.conjugateAffineFunctional_reflectionElement hu hu1 hp]

/-- The opposite strict affine root group is sent back by the same representative. -/
theorem conj_neg_affineRootGroupPlus_reflectionElement
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p) :
    (B.apartment.affineRootGroupPlus (-(α : characterLattice B.S))
        (-B.reflectionFunctional α u)).map
        (MulAut.conj (B.reflectionElement hp : rationalPoints G)).toMonoidHom =
      B.apartment.affineRootGroupPlus α (B.reflectionFunctional α u) := by
  rw [B.apartment.conj_affineRootGroupPlus, map_neg,
    B.weylAction_reflectionElement hu hu1 hp,
    B.apartment.conjugateAffineFunctional_neg,
    B.conjugateAffineFunctional_reflectionElement hu hu1 hp, neg_neg, neg_neg]

end ValuationBuildingData

end Langlands.Geometry.Building
