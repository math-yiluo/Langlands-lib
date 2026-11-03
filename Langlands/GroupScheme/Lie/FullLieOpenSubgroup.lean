import Langlands.GroupScheme.Lie.SubgroupEqualityProof
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Smooth closed subgroups with the full Lie algebra are open -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Lie Lie.SubgroupEquality

variable {k : Type u} [Field k]
    {H K : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom] [Smooth K.X.hom]
    (j : K ⟶ H) (hj : IsClosedSubgroup j)
    (hlie : ∀ X : lieKernel H k, ∃ Y : lieKernel K k,
      Y.val ≫ j.hom.hom = X.val)

include hj hlie

/-- A smooth closed subgroup with the full actual Lie algebra is an open subgroup;
the ambient finite-type affine group need not be smooth or connected. -/
theorem isOpenImmersion_of_fullLie : IsOpenImmersion j.hom.hom.left := by
  let : Field (CommRingCat.of k) := inferInstanceAs (Field k)
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom K.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : IsIso (coordinateIso H).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (coordinateIso H).hom))
  have : IsIso (coordinateIso K).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (coordinateIso K).hom))
  -- The restriction map is surjective.
  have hφ : Function.Surjective (restrictionMap j) := by
    have e : ((algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (restrictionMap j)).op).left ≫ (coordinateIso H).hom.left =
        (coordinateIso K).hom.left ≫ j.hom.hom.left := by
      rw [← Over.comp_left, ← Over.comp_left, restrictionMap_spec]
    have hc : IsClosedImmersion ((algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom (restrictionMap j)).op).left := by
      have h : ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (restrictionMap j)).op).left =
          ((coordinateIso K).hom.left ≫ j.hom.hom.left) ≫ inv (coordinateIso H).hom.left := by
        rw [← e, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [h]
      infer_instance
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom (restrictionMap j).toRingHom)) at hc
    obtain ⟨-, hs⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine
      (Spec.map (CommRingCat.ofHom (restrictionMap j).toRingHom))
    intro y
    obtain ⟨x, hx⟩ := hs ((Scheme.ΓSpecIso (CommRingCat.of (coordinateAlgebra K))).inv y)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (coordinateAlgebra H))).hom x, ?_⟩
    have h := congrArg (fun g => g.hom x)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (restrictionMap j).toRingHom))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, hx, Iso.inv_hom_id_apply] at h
    exact h.symm
  -- The subgroup is smooth and the ambient coordinate algebra is noetherian.
  have hsm : Smooth ((algSpec (CommRingCat.of k)).obj (op (coordinateAlgebra K))).hom := by
    have h : Smooth ((coordinateIso K).hom.left ≫ K.X.hom) := inferInstance
    simpa only [Over.w] using h
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap (CommRingCat.of k) (coordinateAlgebra K)))) at hsm
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at hsm
  have : Algebra.Smooth (CommRingCat.of k) (coordinateAlgebra K) :=
    RingHom.smooth_algebraMap.mp hsm
  have : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  have : Algebra.FiniteType (CommRingCat.of k) (coordinateAlgebra H) :=
    coordinateAlgebraFiniteType H
  have : IsNoetherianRing (coordinateAlgebra H) :=
    Algebra.FiniteType.isNoetherianRing (CommRingCat.of k) (coordinateAlgebra H)
  -- The local step and the translation give `e` with `φ e = 1` annihilating the kernel.
  obtain ⟨f, hf1, hf⟩ := exists_annihilator_of_derivations (restrictionMap j) hφ
    (coordinateOrigin H)
    (fun x hx => by
      rw [RingHom.mem_ker, ← coordinateOrigin_comp_restrictionMap j, AlgHom.comp_apply,
        RingHom.mem_ker.mp hx, map_zero])
    (derivation_eq_zero_of_mem_ker j hlie)
  obtain ⟨g, hg, hg1⟩ := exists_tensor_of_annihilator j hφ f hf
  rw [hf1, map_one] at hg1
  have hmem := productMap_mem_map_annihilator (RingHom.ker (restrictionMap j)) g
    (fun x hx => hg x hx) (restrictionMap j) (AlgHom.id _ _)
  rw [hg1, Ideal.mem_map_iff_of_surjective _ hφ] at hmem
  obtain ⟨e, he, he1⟩ := hmem
  have heker : 1 - e ∈ RingHom.ker (restrictionMap j) := by
    rw [RingHom.mem_ker, map_sub, map_one, he1, sub_self]
  have hidem : IsIdempotentElem (1 - e) := by
    have h : e * (1 - e) = 0 := Submodule.mem_annihilator.mp he _ heker
    unfold IsIdempotentElem
    linear_combination (-1 : coordinateAlgebra H) * h
  have hspan : RingHom.ker (restrictionMap j) = Ideal.span {1 - e} := by
    apply le_antisymm
    · intro x hx
      have hex : e * x = 0 := Submodule.mem_annihilator.mp he x hx
      have hx' : x = x * (1 - e) := by
        calc
          x = x - e * x := by rw [hex, sub_zero]
          _ = x * (1 - e) := by ring
      rw [hx']
      exact Ideal.mul_mem_left _ x (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr heker)
  have hopen : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (restrictionMap j).toRingHom)) :=
    (isOpenImmersion_SpecMap_iff_of_surjective _ hφ).mpr ⟨1 - e, hidem, hspan⟩
  have hjOver : j.hom.hom = (coordinateIso K).inv ≫
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (restrictionMap j)).op ≫
        (coordinateIso H).hom := by
    rw [restrictionMap_spec, Iso.inv_hom_id_assoc]
  have hj' := congrArg (fun a => a.left) hjOver
  change j.hom.hom.left = (coordinateIso K).inv.left ≫
      Spec.map (CommRingCat.ofHom (restrictionMap j).toRingHom) ≫
        (coordinateIso H).hom.left at hj'
  have : IsIso (coordinateIso K).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (coordinateIso K).inv))
  have hleft : IsOpenImmersion (coordinateIso K).inv.left :=
    IsOpenImmersion.of_isIso _
  have hright : IsOpenImmersion (coordinateIso H).hom.left :=
    IsOpenImmersion.of_isIso _
  rw [hj']
  exact @IsOpenImmersion.comp _ _ _ _ _ hleft
    (@IsOpenImmersion.comp _ _ _ _ _ hopen hright)

/-- The actual open range of a smooth closed subgroup with the full Lie algebra. -/
def fullLieOpenRange (hj : IsClosedSubgroup j)
    (hlie : ∀ X : lieKernel H k, ∃ Y : lieKernel K k,
      Y.val ≫ j.hom.hom = X.val) : H.X.left.Opens :=
  letI := isOpenImmersion_of_fullLie j hj hlie
  ⟨Set.range j.hom.hom.left, IsOpenImmersion.isOpen_range _⟩

@[simp]
theorem mem_fullLieOpenRange (x : H.X.left) :
    x ∈ fullLieOpenRange j hj hlie ↔ x ∈ Set.range j.hom.hom.left := Iff.rfl

end Langlands.GroupScheme
