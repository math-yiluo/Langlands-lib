import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Obstruction
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame
import Langlands.AlgebraicGeometry.Picard.AffineNilpotentLineBundle
import Langlands.AlgebraicGeometry.Picard.InfinitesimalAffineOpenNilpotence
import Langlands.AlgebraicGeometry.Picard.NilpotentUnitReduction
import Langlands.AlgebraicGeometry.Picard.DualNumberAffineFrames
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit

/-! # Lifting frames along nilpotent thickenings of relative spaces -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open RelativeAffineSections InfinitesimalAffineOpenNilpotence NilpotentUnitReduction
open Langlands.SchemeModule Langlands.Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (q : A →ₐ[R] B) (hq : Function.Surjective q) (hn : IsNilpotent (RingHom.ker q.toRingHom))

include hq hn

lemma surjective_morphismRestrict_relMap (U : (relSpace f A).Opens) :
    Surjective (relMap f q ∣_ U) := by
  have hs := surjective_relMap f q hq fun x hx => by
    obtain ⟨n, hn⟩ := hn
    refine ⟨n, ?_⟩
    have : x ^ n ∈ RingHom.ker q.toRingHom ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at this
    exact (Ideal.mem_bot.mp this)
  constructor
  intro y
  obtain ⟨x, hx⟩ := hs y.1
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change (relMap f q).base x ∈ U
    rw [hx]
    exact y.2
  · apply Subtype.ext
    rw [morphismRestrict_base_coe]
    exact hx

/-- A frame of the pullback of a line bundle along the relative-space map of a nilpotent
surjection lifts to a frame on any affine open. -/
lemma exists_frame_lift (N : LineBundle (relSpace f A)) (U : (relSpace f A).Opens)
    (hU : IsAffineOpen U)
    (t : Γ((Scheme.Modules.pullback (relMap f q)).obj N.obj, relMap f q ⁻¹ᵁ U))
    (ht : Scheme.Modules.IsFrameOn t (relMap f q ⁻¹ᵁ U)) :
    ∃ s : Γ(N.obj, U), Scheme.Modules.IsFrameOn s U ∧
      Scheme.Modules.pullbackLocalSection (relMap f q) s = t := by
  obtain ⟨e₁⟩ := ht.nonempty_pullback_iso_unit (relMap f q ⁻¹ᵁ U) le_rfl le_rfl
  obtain ⟨hsurj, -⟩ := relativeRestriction_appTop_nilpotentSurjective f q hq hn U hU
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine (relMap f q ⁻¹ᵁ U).toScheme := hU.preimage (relMap f q)
  haveI := surjective_morphismRestrict_relMap f q hq hn U
  let e₂ : (Scheme.Modules.pullback (relMap f q ∣_ U)).obj
      ((LineBundle.pullback U.ι).obj N).obj ≅ structureModule (relMap f q ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.pullbackComp (relMap f q ∣_ U) U.ι).app N.obj ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι (relMap f q) U)).app N.obj ≪≫
        ((Scheme.Modules.pullbackComp (relMap f q ⁻¹ᵁ U).ι (relMap f q)).app N.obj).symm ≪≫ e₁
  obtain ⟨e₃⟩ := lineBundle_trivial_of_affinePullback (relMap f q ∣_ U) hsurj
    ((LineBundle.pullback U.ι).obj N) e₂
  obtain ⟨s₀, hs₀⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit U e₃
  have hp := hs₀.pullbackLocalSection (relMap f q)
  -- the coefficient of `t` with respect to the pulled-back frame is a unit
  set c := CocycleGluing.frameCoeff hp le_rfl t with hc
  have hct : c • Scheme.Modules.pullbackLocalSection (relMap f q) s₀ = t := by
    have := CocycleGluing.frameCoeff_smul_frame hp le_rfl t
    rwa [CocycleGluing.mres_self] at this
  have hcu : IsUnit c := by
    have h1 := CocycleGluing.frameCoeff_mul_frameCoeff hp ht le_rfl le_rfl
    rw [CocycleGluing.mres_self, CocycleGluing.mres_self] at h1
    exact isUnit_iff_exists_inv.mpr ⟨_, h1⟩
  -- lift the unit along the surjection with nilpotent kernel on sections
  obtain ⟨happ, hnilapp⟩ := nilpotentSurjective_of_isPushout _ _ _ _
    (isPushout_sections f q U hU) hq hn
  obtain ⟨a, ha⟩ := unitsMap_surjective _ happ hnilapp hcu.unit
  refine ⟨(a : Γ(relSpace f A, U)) • s₀, DualNumberThickening.isFrameOn_smul_unit s₀ hs₀ a, ?_⟩
  rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Hom.app_eq_appLE]
  have hac : ((relMap f q).appLE U (relMap f q ⁻¹ᵁ U) le_rfl).hom (a : Γ(relSpace f A, U)) = c :=
    congrArg Units.val ha
  erw [hac]
  exact hct

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality
