import Langlands.GroupScheme.HomScheme.SplitTorusHopfPoint

/-! # Ranges of homomorphisms from two different split tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme

section Transport

variable {S : Scheme.{u}} {H H₁ H' H₁' G G' : GroupScheme S}

/-- Transport along isomorphisms of two sources and a common target preserves and reflects
inclusions of ranges. -/
theorem range_transport_le_iff₂ (eH : H₁ ≅ H) (eH' : H₁' ≅ H') (eG : G ≅ G') {T : Over S}
    (i : RelativeHom H G T) (i' : RelativeHom H' G T) :
    SubgroupFunctor.range (transport eH' eG i') ≤ SubgroupFunctor.range (transport eH eG i) ↔
      SubgroupFunctor.range i' ≤ SubgroupFunctor.range i := by
  rw [range_le_range_iff, range_le_range_iff]
  let a := ((baseChange T.hom).map eH.hom).hom.hom.left
  let a' := ((baseChange T.hom).map eH'.hom).hom.hom.left
  let b := ((baseChange T.hom).map eG.hom).hom.hom.left
  have ha : IsIso a := (Grp.forget _ ⋙ Over.forget _).map_isIso ((baseChange T.hom).map eH.hom)
  have ha' : IsIso a' :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso ((baseChange T.hom).map eH'.hom)
  have hb : IsIso b := (Grp.forget _ ⋙ Over.forget _).map_isIso ((baseChange T.hom).map eG.hom)
  change (∃ z, z ≫ a ≫ i.hom.hom.left ≫ b = a' ≫ i'.hom.hom.left ≫ b) ↔
    ∃ z, z ≫ i.hom.hom.left = i'.hom.hom.left
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨inv a' ≫ z ≫ a, ?_⟩
    rw [← cancel_mono b, ← cancel_epi a']
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hz
  · rintro ⟨z, hz⟩
    exact ⟨a' ≫ z ≫ inv a, by simp only [Category.assoc, IsIso.inv_hom_id_assoc, reassoc_of% hz]⟩

end Transport

namespace FiniteSource

open Langlands.FiniteBialgebraHom

variable {R : Type u} [CommRing R] {A P P' : Type u} [CommRing A] [CommRing P] [CommRing P']
  [HopfAlgebra R A] [HopfAlgebra R P] [HopfAlgebra R P']

/-- Inclusion of ranges of homomorphisms from two Hopf spectra. -/
theorem range_pointEquiv_symm_le_iff₂ {C : Type u} [CommRing C] [Algebra R C]
    (f : {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f})
    (f' : {f : A →ₐ[R] C ⊗[R] P' // IsHopfPoint R f}) :
    SubgroupFunctor.range ((pointEquiv A P' C).symm f') ≤
        SubgroupFunctor.range ((pointEquiv A P C).symm f) ↔
      ∃ ψ : C ⊗[R] P →+* C ⊗[R] P',
        ψ.comp (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1).toRingHom =
          (AlgHom.liftEquiv R C A (C ⊗[R] P') f'.1).toRingHom := by
  let φ : CommRingCat.of (C ⊗[R] A) ⟶ CommRingCat.of (C ⊗[R] P) :=
    CommRingCat.ofHom (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1).toRingHom
  let φ' : CommRingCat.of (C ⊗[R] A) ⟶ CommRingCat.of (C ⊗[R] P') :=
    CommRingCat.ofHom (AlgHom.liftEquiv R C A (C ⊗[R] P') f'.1).toRingHom
  have h : ((pointEquiv A P C).symm f).hom.hom.left =
      (tensorIso P C).hom ≫ Spec.map φ ≫ (tensorIso A C).inv :=
    rfl
  have h' : ((pointEquiv A P' C).symm f').hom.hom.left =
      (tensorIso P' C).hom ≫ Spec.map φ' ≫ (tensorIso A C).inv :=
    rfl
  rw [range_le_range_iff, h, h']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(Spec.preimage ((tensorIso P' C).inv ≫ z ≫ (tensorIso P C).hom)).hom, ?_⟩
    have hmap : Spec.map (φ ≫ Spec.preimage ((tensorIso P' C).inv ≫ z ≫ (tensorIso P C).hom)) =
        Spec.map φ' := by
      rw [Spec.map_comp, Spec.map_preimage, ← cancel_epi (tensorIso P' C).hom,
        ← cancel_mono (tensorIso A C).inv]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hz
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hmap)
  · rintro ⟨ψ, hψ⟩
    refine ⟨(tensorIso P' C).hom ≫ Spec.map (CommRingCat.ofHom ψ) ≫ (tensorIso P C).inv, ?_⟩
    have hcomp : φ ≫ CommRingCat.ofHom ψ = φ' := CommRingCat.hom_ext hψ
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc, hcomp]

/-- Kernel form of `range_pointEquiv_symm_le_iff₂`. -/
theorem range_pointEquiv_symm_le_iff_ker₂ {C : Type u} [CommRing C] [Algebra R C]
    (f : {f : A →ₐ[R] C ⊗[R] P // IsHopfPoint R f})
    (f' : {f : A →ₐ[R] C ⊗[R] P' // IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1)) :
    SubgroupFunctor.range ((pointEquiv A P' C).symm f') ≤
        SubgroupFunctor.range ((pointEquiv A P C).symm f) ↔
      RingHom.ker (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1) ≤
        RingHom.ker (AlgHom.liftEquiv R C A (C ⊗[R] P') f'.1) := by
  rw [range_pointEquiv_symm_le_iff₂]
  constructor
  · rintro ⟨ψ, hψ⟩ x hx
    rw [RingHom.mem_ker] at hx ⊢
    have hx' := congrArg (· x) hψ
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] at hx'
    rw [← hx', hx, map_zero]
  · intro hker
    let φ := (AlgHom.liftEquiv R C A (C ⊗[R] P) f.1).toRingHom
    let φ' := (AlgHom.liftEquiv R C A (C ⊗[R] P') f'.1).toRingHom
    have hφ : Function.Surjective φ := hf
    refine ⟨(Ideal.Quotient.lift (RingHom.ker φ) φ' (fun x hx => hker hx)).comp
      (RingHom.quotientKerEquivOfSurjective hφ).symm.toRingHom, ?_⟩
    apply RingHom.ext
    intro x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]

end FiniteSource

namespace SplitTorusPoint

open Langlands.FiniteBialgebraHom FiniteSource

variable {R : Type u} [CommRing R] {I I' : Type u} [Fintype I] [DecidableEq I] [Fintype I']
  [DecidableEq I'] {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]

/-- Kernel criterion for inclusion of ranges of homomorphisms from two split tori. -/
theorem range_splitPointEquiv_symm_le_iff_ker₂ {C : Type u} [CommRing C] [Algebra R C]
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      IsHopfPoint R f})
    (f' : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I' → ℤ) //
      IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R C _ _ f.1)) :
    SubgroupFunctor.range ((splitPointEquiv G C).symm f') ≤
        SubgroupFunctor.range ((splitPointEquiv G C).symm f) ↔
      RingHom.ker (AlgHom.liftEquiv R C _ _ f.1) ≤
        RingHom.ker (AlgHom.liftEquiv R C _ _ f'.1) := by
  rw [splitPointEquiv_symm_apply, splitPointEquiv_symm_apply, range_transport_le_iff₂,
    range_pointEquiv_symm_le_iff_ker₂ f f' hf]

/-- Two closed homomorphisms from split tori have the same range exactly when the kernels of
the linear extensions of their Hopf points agree. -/
theorem range_splitPointEquiv_symm_eq_iff_ker₂ {C : Type u} [CommRing C] [Algebra R C]
    (f : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I → ℤ) //
      IsHopfPoint R f})
    (f' : {f : AffineCoordinates.hopfAlgebra G →ₐ[R] C ⊗[R] AddMonoidAlgebra R (I' → ℤ) //
      IsHopfPoint R f})
    (hf : Function.Surjective (AlgHom.liftEquiv R C _ _ f.1))
    (hf' : Function.Surjective (AlgHom.liftEquiv R C _ _ f'.1)) :
    SubgroupFunctor.range ((splitPointEquiv G C).symm f) =
        SubgroupFunctor.range ((splitPointEquiv G C).symm f') ↔
      RingHom.ker (AlgHom.liftEquiv R C _ _ f.1) =
        RingHom.ker (AlgHom.liftEquiv R C _ _ f'.1) := by
  rw [le_antisymm_iff, le_antisymm_iff, range_splitPointEquiv_symm_le_iff_ker₂ f' f hf',
    range_splitPointEquiv_symm_le_iff_ker₂ f f' hf]
  exact and_comm

end SplitTorusPoint

end Langlands.GroupScheme.HomScheme
