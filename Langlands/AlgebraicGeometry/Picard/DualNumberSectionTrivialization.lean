import Langlands.AlgebraicGeometry.Picard.DualNumberAffineFrames
import Langlands.AlgebraicGeometry.Modules.SectionCoefficients

/-! # Global sections not killed by epsilon trivialize first-order deformations -/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.DualNumberThickening

open Langlands.SchemeModule Langlands.Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The global epsilon function of the actual thickening, the image of `ε` under the
structure morphism to `Spec k[ε]`. -/
def globalEpsilon : Γ(thickening f, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv ≫ (structureMap f).appTop)
    (DualNumber.eps : DualNumber k)

/-- The global epsilon function restricts to the epsilon section over every inverse image. -/
lemma globalEpsilon_restrict (U : X.Opens) :
    (thickening f).presheaf.map (homOfLE (le_top : projection f ⁻¹ᵁ U ≤ ⊤)).op
      (globalEpsilon f) = epsilonSection f U := by
  rfl

/-- Epsilon kills a dual-number section with vanishing first coordinate. -/
lemma epsilonSection_mul_sectionMap_of_fst_eq_zero (U : X.Opens) (z : DualNumber Γ(X, U))
    (hz : z.fst = 0) : epsilonSection f U * sectionMap f U z = 0 := by
  have h : (DualNumber.eps : DualNumber Γ(X, U)) * z = 0 := by
    ext
    · simp
    · simp [hz]
  rw [← sectionMap_eps, ← map_mul, h, map_zero]

variable {f}

/-- Over the inverse image of an affine open, a global section is a multiple of the
normalized frame, and the reduction of the coefficient is the restricted reduced
coefficient of the global section. -/
lemma exists_coefficient_affineNormalizedFrame (U : X.Opens) (hU : IsAffineOpen U)
    (L : LineBundle (thickening f))
    (e : (Scheme.Modules.pullback (closedPoint f)).obj L.obj ≅ structureModule X)
    (s : Γ(L.obj, ⊤)) :
    ∃ z : DualNumber Γ(X, U),
      sectionRes L.obj s (projection f ⁻¹ᵁ U) =
          sectionMap f U z • affineNormalizedFrame f U hU L e ∧
        z.fst = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (reducedCoefficient f ⊤ L.obj e s) := by
  have hu := affineNormalizedFrame_isFrame f U hU L e
  obtain ⟨a, ha⟩ := (hu.bijective (le_refl _) (le_refl _)).2
    (sectionRes L.obj s (projection f ⁻¹ᵁ U))
  have hmap : L.obj.presheaf.map (homOfLE (le_refl (projection f ⁻¹ᵁ U))).op
      (affineNormalizedFrame f U hU L e) = affineNormalizedFrame f U hU L e := by
    rw [show (homOfLE (le_refl (projection f ⁻¹ᵁ U))).op = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id]
    rfl
  simp only [hmap] at ha
  refine ⟨(sectionEquiv f U).symm a, ?_, ?_⟩
  · rw [← sectionEquiv_apply, RingEquiv.apply_symm_apply, ha]
  · have h1 := reducedCoefficient_naturality f (le_top : U ≤ ⊤) L.obj e s
    have h2 : reducedCoefficient f U L.obj e (sectionRes L.obj s (projection f ⁻¹ᵁ U)) =
        reductionMap f U a := by
      rw [← ha, reducedCoefficient_smul, reducedCoefficient_affineNormalizedFrame, mul_one]
    rw [← reductionMap_sectionEquiv f U, RingEquiv.apply_symm_apply, ← h2]
    exact h1

/-- If a global section of an actual first-order deformation `L` is not killed by
epsilon, and every global function of the original scheme is zero or a unit, then the
section trivializes `L`: its morphism from the structure module is an isomorphism. -/
theorem isIso_sectionHom_of_globalEpsilon_smul_ne_zero
    (hX : ∀ c : Γ(X, ⊤), c = 0 ∨ IsUnit c)
    (L : LineBundle (thickening f))
    (e : (Scheme.Modules.pullback (closedPoint f)).obj L.obj ≅ structureModule X)
    (s : Γ(L.obj, ⊤)) (hs : globalEpsilon f • s ≠ 0) :
    IsIso (sectionHom L.obj s) := by
  have hcover : ∀ x : thickening f, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ projection f ⁻¹ᵁ U := by
    intro x
    obtain ⟨U, hx⟩ := Opens.mem_iSup.mp
      (show projection f x ∈ ⨆ i : X.affineOpens, (i : X.Opens) by
        rw [iSup_affineOpens_eq_top]; trivial)
    exact ⟨U, U.2, hx⟩
  rcases hX (reducedCoefficient f ⊤ L.obj e s) with hc | hc
  · -- The reduced coefficient vanishes: then epsilon kills the section locally.
    exfalso
    apply hs
    let Msh : TopCat.Sheaf Ab (thickening f) := ⟨L.obj.presheaf, L.obj.isSheaf⟩
    let ι := X.affineOpens
    let V : ι → (thickening f).Opens := fun U ↦ projection f ⁻¹ᵁ (U : X.Opens)
    have hV : (⊤ : (thickening f).Opens) ≤ iSup V := by
      intro x _
      obtain ⟨U, hU, hx⟩ := hcover x
      exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
    refine Msh.eq_of_locally_eq' V ⊤ (fun U ↦ homOfLE le_top) hV _ _ fun U ↦ ?_
    obtain ⟨z, hz, hz0⟩ :=
      exists_coefficient_affineNormalizedFrame (U : X.Opens) U.2 L e s
    rw [hc, map_zero] at hz0
    change L.obj.presheaf.map (homOfLE le_top).op (globalEpsilon f • s) =
      L.obj.presheaf.map (homOfLE le_top).op 0
    rw [Scheme.Modules.map_smul, map_zero, globalEpsilon_restrict]
    change epsilonSection f U • sectionRes L.obj s (projection f ⁻¹ᵁ (U : X.Opens)) = 0
    rw [hz, smul_smul, epsilonSection_mul_sectionMap_of_fst_eq_zero f _ z hz0, zero_smul]
  · -- The reduced coefficient is a unit: then the section is a frame near every point.
    have hloc : ∀ U : X.Opens, IsAffineOpen U →
        projection f ⁻¹ᵁ U ≤ trivializationOpen L.obj s := by
      intro U hU
      obtain ⟨z, hz, hz0⟩ := exists_coefficient_affineNormalizedFrame U hU L e s
      have hzu : IsUnit z := by
        rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hz0]
        exact hc.map _
      have hau : IsUnit (sectionMap f U z) := hzu.map _
      have hframe := isFrameOn_smul_unit _ (affineNormalizedFrame_isFrame f U hU L e) hau.unit
      rw [IsUnit.unit_spec, ← hz] at hframe
      apply le_trivializationOpen_of_bijective
      intro W hW
      have hb := hframe.bijective hW hW
      rw [sectionRes_res] at hb
      have heq : (fun g : Γ(thickening f, W) ↦ (sectionHom L.obj s).app W g) =
          fun g ↦ g • sectionRes L.obj s W :=
        funext (LineBundleDescent.sectionHom_app L.obj s W)
      change Function.Bijective (fun g : Γ(thickening f, W) ↦ (sectionHom L.obj s).app W g)
      rw [heq]
      exact hb
    have htop : (⊤ : (thickening f).Opens) ≤ trivializationOpen L.obj s := by
      intro x _
      obtain ⟨U, hU, hx⟩ := hcover x
      exact hloc U hU hx
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro W
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_sectionHom_app_of_le L.obj s (le_top.trans htop)

end Langlands.AlgebraicGeometry.Picard.DualNumberThickening
