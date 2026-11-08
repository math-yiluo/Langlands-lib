import Langlands.GroupScheme.Examples.HermitianRootWeilAmbientGeneration

/-! # Parabolic radical generation for actual Weil-restricted weighted Hermitian models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HermitianRoot.WeilSchemeModel

open SU3Root

variable (F k L : Type u) [Field F] [Field k] [Field L]
  [Algebra F k] [FiniteDimensional F k] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)
  {A G : GroupScheme (Spec (CommRingCat.of F))}

/-- A source isomorphism transports full rational-image containment into any
normal subgroup containing the composed upper dynamics. -/
theorem rationalPoints_range_le_of_iso_upper_dynamic (hH : H.IsAnisotropic)
    (e : A ≅ groupScheme F k L H w hw) (a : A ⟶ G)
    (N : Subgroup (rationalPoints G)) [N.Normal]
    (hu : (Dynamic.unipotent (cocharacter F k L H w hw ≫ e.inv ≫ a)).carrier
      (Over.mk (𝟙 _)) ≤ N) :
    (rationalPoints.map a).range ≤ N := by
  have h := rationalPoints_range_le_of_upper_dynamic F k L H w hw hH (e.inv ≫ a) N hu
  rintro _ ⟨x, rfl⟩
  have hx := h ⟨rationalPoints.map e.hom x, rfl⟩
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc,
    ← Grp.comp_hom_hom, e.hom_inv_id_assoc] using hx

/-- Every rational image of an actual Weil-restricted anisotropic-middle Hermitian model lies
in the target's actual parabolic elementary subgroup. -/
theorem rationalPoints_range_le_parabolicElementarySubgroup_of_iso
    (hH : H.IsAnisotropic) (hG : IsConnectedReductive G)
    (e : A ≅ groupScheme F k L H w hw) (a : A ⟶ G) :
    (rationalPoints.map a).range ≤ parabolicElementarySubgroup G :=
  rationalPoints_range_le_of_iso_upper_dynamic F k L H w hw hH e a
    (parabolicElementarySubgroup G)
    (dynamicUnipotent_le_parabolicElementarySubgroup hG
      (cocharacter F k L H w hw ≫ e.inv ≫ a))

/-- The original rational map with its codomain restricted to the target's
actual parabolic elementary subgroup. -/
def rationalPointsToParabolicElementarySubgroup
    (hH : H.IsAnisotropic) (hG : IsConnectedReductive G)
    (e : A ≅ groupScheme F k L H w hw) (a : A ⟶ G) :
    rationalPoints A →* parabolicElementarySubgroup G :=
  (rationalPoints.map a).codRestrict (parabolicElementarySubgroup G) fun x =>
    rationalPoints_range_le_parabolicElementarySubgroup_of_iso F k L H w hw hH hG e a
      ⟨x, rfl⟩

@[simp] theorem rationalPointsToParabolicElementarySubgroup_apply_coe
    (hH : H.IsAnisotropic) (hG : IsConnectedReductive G)
    (e : A ≅ groupScheme F k L H w hw) (a : A ⟶ G) (x : rationalPoints A) :
    (rationalPointsToParabolicElementarySubgroup F k L H w hw hH hG e a x :
      rationalPoints G) = rationalPoints.map a x := rfl

/-- A connected reductive actual Weil-restricted anisotropic-middle Hermitian model is generated
by its actual rational parabolic radicals. -/
theorem parabolicElementarySubgroup_eq_top_of_iso
    (hH : H.IsAnisotropic) (hA : IsConnectedReductive A)
    (e : A ≅ groupScheme F k L H w hw) :
    parabolicElementarySubgroup A = ⊤ := by
  apply top_unique
  intro x _
  have hx := rationalPoints_range_le_parabolicElementarySubgroup_of_iso F k L H w hw
    hH hA e (𝟙 A) ⟨x, rfl⟩
  simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using hx

/-- Containing every actual rational parabolic radical of such a connected
reductive model forces an arbitrary subgroup to be the whole rational group. -/
theorem eq_top_of_parabolic_radicals_of_iso
    (hH : H.IsAnisotropic) (hA : IsConnectedReductive A)
    (e : A ≅ groupScheme F k L H w hw) (N : Subgroup (rationalPoints A))
    (hrad : ∀ (P U : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ A) (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        (rationalPoints.map (r ≫ p)).range ≤ N) : N = ⊤ := by
  apply top_unique
  rw [← parabolicElementarySubgroup_eq_top_of_iso F k L H w hw hH hA e]
  exact (parabolicElementarySubgroup_le_iff N).mpr hrad

end Langlands.GroupScheme.HermitianRoot.WeilSchemeModel
