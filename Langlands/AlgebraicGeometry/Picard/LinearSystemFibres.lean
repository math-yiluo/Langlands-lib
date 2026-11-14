import Langlands.AlgebraicGeometry.Picard.LinearSystemCechNaturality
import Langlands.AlgebraicGeometry.Picard.BaseChangeMaps
import Langlands.AlgebraicGeometry.Picard.FibreRegularSection

/-! # Zero loci of linear-system sections with unit ideal of values

For `u : Q → B` whose values generate the unit ideal, the section `σ_u` of `M_B` does not vanish
on any geometric fibre of `Y_B → Spec B`. Hence `σ_u` is regular and its zero locus is a relative
effective Cartier divisor. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open Scheme.TwoAffineOpenCover SectionZeroIdeal

section Zero

variable {X : Scheme.{u}} (L : LineBundle X)

/-- **A section with zero ideal `⊥` is zero.** -/
theorem eq_zero_of_zeroIdeal_eq_bot {σ : Γ(L.obj, ⊤)} (h : zeroIdeal L σ = ⊥) : σ = 0 := by
  have hx := fun x => exists_affine_frame L x
  choose U hxU t ht using hx
  refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨L.obj.presheaf, L.obj.isSheaf⟩)
    (fun x => (U x).1) ⊤ (fun _ => homOfLE le_top)
    (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) _ _ fun x => ?_
  change res L σ (U x).1 = L.obj.presheaf.map _ 0
  rw [map_zero, eq_frameEquiv_smul (ht x) (res L σ (U x).1)]
  have hi := zeroIdeal_ideal_of_equiv L σ (U x) (frameEquiv (ht x))
  rw [h, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, eq_comm,
    Ideal.span_singleton_eq_bot] at hi
  rw [hi, zero_smul]

end Zero

section Sections

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} {M : X.Modules}
  {𝒰 : X.OrderedAffineCover} (C : CechRep π M 𝒰) (A : Type u) [CommRing A] [Algebra R A]

/-- The section attached to the zero map is zero. -/
lemma homEquivSections_zero : C.homEquivSections A 0 = 0 := by
  have h0 : Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv C.δ A 0 = ⟨0, by simp⟩ := by
    apply Subtype.ext
    change (Langlands.CommutativeAlgebra.CokernelDualHom.tensorEquivHom A C.K₀).symm
      ((0 : C.Q →ₗ[R] A).comp _) = 0
    rw [LinearMap.zero_comp, map_zero]
  have h1 : C.kerEquivH0 A ⟨0, by simp⟩ = 0 := by
    apply Subtype.ext
    change C.Θ A 0 = 0
    exact map_zero _
  change (CechRep.sectionsEquivH0 (π := π) (M := M) (𝒰 := 𝒰) A).symm
    (C.kerEquivH0 A (Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv C.δ A 0)) = 0
  rw [h0, h1, map_zero]

lemma homEquivSections_eq_zero_iff (v : C.Q →ₗ[R] A) : C.homEquivSections A v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply (C.homEquivSections A).injective
    rw [h, homEquivSections_zero]
  · rintro rfl
    exact homEquivSections_zero C A

end Sections

section Fibres

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} {L : LineBundle X}
  {𝒰 : X.OrderedAffineCover} (e : ∀ i, Γ(L.obj, 𝒰.U i))
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (𝒰.U i)) (C : CechRep π L.obj 𝒰)
  {B : Type u} [CommRing B] [Algebra R B]

include he in
/-- **Sections with unit ideal of values do not vanish on geometric fibres.** -/
theorem pullbackSection_homEquivSections_ne_zero (v : C.Q →ₗ[R] B)
    (hv : Ideal.span (Set.range v) = ⊤) (K : Type u) [Field K]
    (k : Spec (.of K) ⟶ Spec (.of B)) :
    pullbackSection (pullback.fst (pullback.snd π (specMap R B)) k)
      (pbLB (pullback.fst π (specMap R B)) L) (C.homEquivSections B v) ≠ 0 := by
  intro h0
  let ψ' := Spec.preimage k
  let _ : Algebra R K := (ψ'.hom.comp (algebraMap R B)).toAlgebra
  let φ : B →ₐ[R] K := { ψ'.hom with commutes' := fun _ => rfl }
  have hk : Spec.map (CommRingCat.ofHom φ.toRingHom) = k := by
    rw [← Spec.map_preimage k]
    rfl
  let g := bcMap (π := π) K φ
  have hg₁ := bcMap_fst (π := π) K φ
  have hg₂ := bcMap_snd (π := π) K φ
  let h : pullback π (specMap R K) ⟶ pullback (pullback.snd π (specMap R B)) k :=
    pullback.lift g (pullback.snd _ _) (by rw [hg₂, hk])
  have hh : h ≫ pullback.fst _ _ = g := pullback.lift_fst _ _ _
  have hnat := zeroIdeal_comap_homEquivSections e he C g φ hg₁ hg₂ v
  have hbot : (zeroIdeal (pbLB (pullback.fst π (specMap R B)) L)
      (C.homEquivSections B v)).comap (pullback.fst (pullback.snd π (specMap R B)) k) = ⊥ := by
    rw [zeroIdeal_comap, h0, zeroIdeal_zero]
  rw [← hh, Scheme.IdealSheafData.comap_comp, hbot, Scheme.IdealSheafData.comap_bot] at hnat
  have hσ := eq_zero_of_zeroIdeal_eq_bot _ hnat.symm
  rw [homEquivSections_eq_zero_iff] at hσ
  have hle : Ideal.span (Set.range v) ≤ RingHom.ker ψ'.hom := by
    rw [Ideal.span_le]
    rintro _ ⟨q, rfl⟩
    exact congrArg (fun w : C.Q →ₗ[R] K => w q) hσ
  rw [hv, top_le_iff] at hle
  have h1 : (1 : B) ∈ RingHom.ker ψ'.hom := hle ▸ Submodule.mem_top
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1

include he in
/-- **The zero locus of `σ_v` is a relative effective Cartier divisor** when the values of `v`
generate the unit ideal. -/
theorem homEquivSections_regular_and_relativeEffective [IsNoetherianRing B] [IsProper π] [Flat π]
    [GeometricallyIntegral π] (v : C.Q →ₗ[R] B) (hv : Ideal.span (Set.range v) = ⊤) :
    IsRegularSection (pbLB (pullback.fst π (specMap R B)) L) (C.homEquivSections B v) ∧
      IsRelativeEffectiveCartierIdeal (pullback.snd π (specMap R B))
        (zeroIdeal (pbLB (pullback.fst π (specMap R B)) L) (C.homEquivSections B v)) := by
  have : IsLocallyNoetherian (pullback π (specMap R B)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd π (specMap R B))
  exact isRegularSection_and_isRelativeEffectiveCartierIdeal (pullback.snd π (specMap R B))
    (L := pbLB (pullback.fst π (specMap R B)) L) (C.homEquivSections B v) fun K _ k => pullbackSection_homEquivSections_ne_zero e he C v hv K k

end Fibres

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
