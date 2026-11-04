import Langlands.Geometry.Building.IwahoriWeylQuotientLemmas
import Langlands.Group.TitsSystemComponents

/-!
# Component representatives for actual Iwahori double cosets

Normalizer covariance of the full parahoric follows from normality of the
centralizer-zero subgroup and the covariance of the sharp fixer. Chamber
component surjectivity then supplies the normalizing representatives used in
the corrected component Bruhat construction.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G) [P.normalizerZero.Normal]

/-- Conjugation by an actual normalizer element takes the full parahoric
into the parahoric of the translated subset. -/
theorem parahoric_le_comap (n : normalizerPoints P.i) (Ω : Set P.Apartment) :
    P.parahoric Ω ≤
      (P.parahoric (n • Ω)).comap (MulAut.conj (n : rationalPoints G)).toMonoidHom := by
  refine sup_le ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩
    have hzN : P.centralizer.toNormalizer z ∈ P.normalizerZero := ⟨z, hz, rfl⟩
    have hc := (inferInstance : P.normalizerZero.Normal).conj_mem _ hzN n
    exact P.map_centralizerZero_le_parahoric _ (P.mem_normalizerZero_iff.1 hc)
  · exact (P.apartment.sharpFixer_le_comap n Ω).trans
      (Subgroup.comap_mono (P.sharpFixer_le_parahoric _))

/-- The full parahoric, including its centralizer-zero part, is covariant
under the actual normalizer action. -/
theorem map_parahoric_conj (n : normalizerPoints P.i) (Ω : Set P.Apartment) :
    (P.parahoric Ω).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
      P.parahoric (n • Ω) := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.2 (P.parahoric_le_comap n Ω)
  · intro g hg
    refine ⟨(n : rationalPoints G)⁻¹ * g * (n : rationalPoints G), ?_, ?_⟩
    · change (n : rationalPoints G)⁻¹ * g * (n : rationalPoints G) ∈ P.parahoric Ω
      have h := P.parahoric_le_comap n⁻¹ (n • Ω) hg
      simpa only [inv_smul_smul, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, Subgroup.coe_inv, inv_inv] using h
    · simp [MulAut.conj_apply, mul_assoc]

/-- Every normalizer element stabilizing a subset normalizes its full
parahoric subgroup. -/
theorem normalizerStabilizer_mem_parahoric_normalizer
    (Ω : Set P.Apartment) (n : normalizerPoints P.i)
    (hn : n ∈ P.normalizerStabilizer Ω) :
    (n : rationalPoints G) ∈ Subgroup.normalizer (P.parahoric Ω : Set (rationalPoints G)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (P.parahoric Ω).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
    P.parahoric Ω
  rw [P.map_parahoric_conj, P.mem_normalizerStabilizer.1 hn]

variable [P.zeroSubgroup.Normal]

/-- Surjectivity of the chamber stabilizer on components gives an actual
normalizer representative of every component that normalizes the full Iwahori. -/
theorem exists_normalizing_component_rep (C : Set P.Apartment)
    (hsurj : Function.Surjective
      (P.toComponents.comp (P.chamberStabilizer C).subtype))
    (γ : rationalPoints G ⧸ P.zeroSubgroup) :
    ∃ n : normalizerPoints P.i,
      QuotientGroup.mk (n : rationalPoints G) = γ ∧
        (n : rationalPoints G) ∈
          Subgroup.normalizer (P.parahoric C : Set (rationalPoints G)) := by
  obtain ⟨w, hw⟩ := hsurj γ
  obtain ⟨n, hn, hnw⟩ := w.property
  refine ⟨n, ?_, P.normalizerStabilizer_mem_parahoric_normalizer C n hn⟩
  change P.toComponents (w : P.IwahoriWeylGroup) = γ at hw
  rw [← hnw] at hw
  exact hw

/-- The same representatives remove the component of every rational point;
this is the representative input for the parabolic component construction. -/
theorem exists_normalizing_zeroSubgroup_rep (C : Set P.Apartment)
    (hsurj : Function.Surjective
      (P.toComponents.comp (P.chamberStabilizer C).subtype))
    (g : rationalPoints G) :
    ∃ n : normalizerPoints P.i,
      g * (n : rationalPoints G)⁻¹ ∈ P.zeroSubgroup ∧
        (n : rationalPoints G) ∈
          Subgroup.normalizer (P.parahoric C : Set (rationalPoints G)) := by
  obtain ⟨n, hn, hnB⟩ := P.exists_normalizing_component_rep C hsurj (QuotientGroup.mk g)
  refine ⟨n, ?_, hnB⟩
  apply (QuotientGroup.eq_one_iff _).1
  change (QuotientGroup.mk' P.zeroSubgroup) (g * (n : rationalPoints G)⁻¹) = 1
  rw [map_mul, map_inv]
  change QuotientGroup.mk g * (QuotientGroup.mk (n : rationalPoints G))⁻¹ = 1
  rw [hn, mul_inv_cancel]

open Langlands.Group Langlands.Group.TitsSystem

variable (C : Set P.Apartment)
  (hI : P.parahoric C ≤ (QuotientGroup.mk' P.zeroSubgroup).ker)
  {S : Set P.toComponents.ker}
  (hTits : IsTitsSystem
    ((P.parahoric C).subgroupOf (QuotientGroup.mk' P.zeroSubgroup).ker)
    ((normalizerPoints P.i).subgroupOf (QuotientGroup.mk' P.zeroSubgroup).ker)
    (kernelProjection (π := QuotientGroup.mk' P.normalizerZero)
      (q := QuotientGroup.mk' P.zeroSubgroup) (c := P.toComponents)
      (hcompat := fun n => P.toComponents_mk n)) S)
  (hsurj : Function.Surjective
    (P.toComponents.comp (P.chamberStabilizer C).subtype))

/-- Conditional actual-data Bruhat equivalence. The actual kernel Tits system,
Iwahori containment and chamber component surjectivity remain explicit inputs. -/
def iwahoriDoubleCosetEquivOfKernelTits :
    P.IwahoriWeylGroup ≃
      DoubleCoset.Quotient (P.parahoric C : Set (rationalPoints G)) (P.parahoric C) :=
  componentDoubleCosetEquiv hI hTits (P.exists_normalizing_component_rep C hsurj)
    (QuotientGroup.mk'_surjective P.normalizerZero)

/-- The conditional equivalence has the required value on every actual
normalizer representative. -/
theorem iwahoriDoubleCosetEquivOfKernelTits_apply (n : normalizerPoints P.i) :
    P.iwahoriDoubleCosetEquivOfKernelTits C hI hTits hsurj (QuotientGroup.mk n) =
      DoubleCoset.mk (P.parahoric C) (P.parahoric C) (n : rationalPoints G) :=
  componentDoubleCosetEquiv_apply hI hTits (P.exists_normalizing_component_rep C hsurj)
    (QuotientGroup.mk'_surjective P.normalizerZero) n

include hI hTits hsurj in
/-- Package the conditional equivalence in the existing fixed-data conclusion. -/
theorem iwahoriDoubleCosetBijection_of_kernelTits : P.IwahoriDoubleCosetBijection C :=
  ⟨P.iwahoriDoubleCosetEquivOfKernelTits C hI hTits hsurj,
    P.iwahoriDoubleCosetEquivOfKernelTits_apply C hI hTits hsurj⟩

end Langlands.Geometry.Building.ParahoricBuildingData
