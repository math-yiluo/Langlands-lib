import Langlands.MathlibBase

/-!
# The first map of the first fundamental exact sequence of Kähler differentials

For a tower `R → A → B`, properties of `KaehlerDifferential.mapBaseChange R A B :
B ⊗[A] Ω[A⁄R] → Ω[B⁄R]`: its cokernel is `Ω[B⁄A]`, it is injective when `Ω[A⁄R]` is flat and
`B` embeds into a formally étale `A`-algebra, and its cokernel is cyclic when both sides have rank
one.
-/

noncomputable section

open KaehlerDifferential TensorProduct

namespace Langlands.CommutativeAlgebra.KaehlerMapBaseChange

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
  [Algebra R B] [IsScalarTower R A B]

/-- The cokernel of `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is `Ω[B⁄A]`
(`KaehlerDifferential.exact_mapBaseChange_map`). -/
def quotRangeMapBaseChangeEquiv :
    (Ω[B⁄R] ⧸ LinearMap.range (mapBaseChange R A B)) ≃ₗ[B] Ω[B⁄A] :=
  (Submodule.quotEquivOfEq _ _ (range_mapBaseChange R A B)).trans
    (LinearMap.quotKerEquivOfSurjective _ (map_surjective R A B))

theorem length_quot_range_mapBaseChange :
    Module.length B (Ω[B⁄R] ⧸ LinearMap.range (mapBaseChange R A B)) =
      Module.length B Ω[B⁄A] :=
  (quotRangeMapBaseChangeEquiv R A B).length_eq

/-- If `A → B` is formally unramified, the cokernel of `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is zero. -/
theorem length_quot_range_mapBaseChange_eq_zero [Algebra.FormallyUnramified A B] :
    Module.length B (Ω[B⁄R] ⧸ LinearMap.range (mapBaseChange R A B)) = 0 := by
  rw [length_quot_range_mapBaseChange]
  exact Module.length_eq_zero

theorem map_map_apply (L : Type*) [CommRing L] [Algebra R L] [Algebra A L] [Algebra B L]
    [IsScalarTower R A L] [IsScalarTower A B L] [IsScalarTower R B L] (ω : Ω[A⁄R]) :
    map R R B L (map R R A B ω) = map R R A L ω := by
  have h : ((map R R B L).restrictScalars A ∘ₗ map R R A B) = map R R A L := by
    apply LinearMap.ext_on_range (span_range_derivation R A)
    intro a
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, map_D,
      ← IsScalarTower.algebraMap_apply]
  exact LinearMap.congr_fun h ω

/-- **Injectivity of `B ⊗[A] Ω[A⁄R] → Ω[B⁄R]`.** If `Ω[A⁄R]` is flat over `A` and `B` embeds into
an `A`-algebra `L` that is formally étale over `A`, then `mapBaseChange R A B` is injective: its
composite with `Ω[B⁄R] → Ω[L⁄R]` agrees with the map `B ⊗[A] Ω[A⁄R] → L ⊗[A] Ω[A⁄R]`, injective
by flatness, followed by the isomorphism `L ⊗[A] Ω[A⁄R] ≅ Ω[L⁄R]`. -/
theorem mapBaseChange_injective (L : Type*) [CommRing L] [Algebra R L] [Algebra A L]
    [Algebra B L] [IsScalarTower R A L] [IsScalarTower A B L] [IsScalarTower R B L]
    [Module.Flat A Ω[A⁄R]] [Algebra.FormallyEtale A L]
    (hBL : Function.Injective (algebraMap B L)) :
    Function.Injective (mapBaseChange R A B) := by
  set T : B ⊗[A] Ω[A⁄R] →ₗ[A] L ⊗[A] Ω[A⁄R] :=
    LinearMap.rTensor Ω[A⁄R] (IsScalarTower.toAlgHom A B L).toLinearMap
  have hT : Function.Injective T :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hBL
  have key : ∀ z, mapBaseChange R A L (T z) = map R R B L (mapBaseChange R A B z) := by
    intro z
    induction z with
    | tmul b ω =>
      simp only [T, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        IsScalarTower.coe_toAlgHom', mapBaseChange_tmul, map_smul, map_map_apply]
      rw [algebra_compatible_smul L b]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  intro z₁ z₂ h
  apply hT
  apply (tensorKaehlerEquivOfFormallyEtale R A L).injective
  rw [tensorKaehlerEquivOfFormallyEtale_apply, tensorKaehlerEquivOfFormallyEtale_apply, key, key,
    h]

/-- **A rank-one cokernel.** Let `ω` generate `Ω[A⁄R]` and let `e : B ≃ Ω[B⁄R]` be a
trivialization. If the image of `ω` in `Ω[B⁄R]` is `c • e 1`, the cokernel of
`B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is `B ⧸ (c)`. -/
def quotRangeMapBaseChangeEquivOfSpan {ω : Ω[A⁄R]} (hω : Submodule.span A {ω} = ⊤)
    (e : B ≃ₗ[B] Ω[B⁄R]) {c : B} (hc : map R R A B ω = c • e 1) :
    (Ω[B⁄R] ⧸ LinearMap.range (mapBaseChange R A B)) ≃ₗ[B] B ⧸ Ideal.span {c} := by
  refine (Submodule.Quotient.equiv (Ideal.span {c}) _ e ?_).symm
  have hrange : LinearMap.range (mapBaseChange R A B) = Submodule.span B {c • e 1} := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      induction z with
      | tmul b η =>
        have hη : η ∈ Submodule.span A {ω} := hω ▸ Submodule.mem_top
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hη
        rw [mapBaseChange_tmul, map_smul, hc, algebra_compatible_smul B a, smul_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      | add z₁ z₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    · rw [Submodule.span_le, Set.singleton_subset_iff, ← hc]
      exact ⟨1 ⊗ₜ ω, by rw [mapBaseChange_tmul, one_smul]⟩
  rw [hrange, Submodule.map_span, Set.image_singleton, ← map_smul, smul_eq_mul, mul_one]
  rfl

theorem length_quot_range_mapBaseChange_eq_ord {ω : Ω[A⁄R]} (hω : Submodule.span A {ω} = ⊤)
    (e : B ≃ₗ[B] Ω[B⁄R]) {c : B} (hc : map R R A B ω = c • e 1) :
    Module.length B (Ω[B⁄R] ⧸ LinearMap.range (mapBaseChange R A B)) = Ring.ord B c :=
  (quotRangeMapBaseChangeEquivOfSpan R A B hω e hc).length_eq

end Langlands.CommutativeAlgebra.KaehlerMapBaseChange
