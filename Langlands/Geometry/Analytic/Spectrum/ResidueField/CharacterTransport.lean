import Langlands.Geometry.Analytic.Spectrum.ResidueField.AlgebraicLift
import Langlands.Geometry.Analytic.Spectrum.ResidueField.Finite
import Langlands.Geometry.Analytic.Spectrum.ResidueField.Functorial
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Transporting prescribed characters through completed residue fields -/

noncomputable section

universe uK uA uB uL

namespace Langlands.Analytic.BanachSpectrum

variable (K : Type uK) [NormedField K] [IsUltrametricDist K]
  {A : Type uA} {B : Type uB} [NormedCommRing A] [NormedCommRing B]
  [NormedAlgebra K A] [NormedAlgebra K B]

/-- A surjective canonical residue comap is an actual bounded algebra
equivalence, with the prescribed comap as its forward map. -/
def completedResidueEquivOfSurjective (f : BoundedAlgHom K A B)
    (y : BanachSpectrum B) (hs : Function.Surjective (completedResidueComap K f y)) :
    BoundedAlgEquiv K (CompletedResidueField K (comap f.toBoundedRingHom y))
      (CompletedResidueField K y) := by
  let ρ := completedResidueComap K f y
  let e := AlgEquiv.ofBijective ρ.toAlgHom
    ⟨(isometry_completedResidueComap K f y).injective, hs⟩
  refine ⟨e, ρ.bounded, 1, zero_lt_one, ?_⟩
  intro z
  rw [one_mul]
  have hz := (isometry_completedResidueComap K f y).norm_map_of_map_zero
    (map_zero _) (e.symm z)
  change ‖e.symm z‖ ≤ ‖z‖
  exact (hz.symm.trans (congrArg norm (e.apply_symm_apply z))).le

@[simp]
theorem completedResidueEquivOfSurjective_apply (f : BoundedAlgHom K A B)
    (y : BanachSpectrum B) (hs : Function.Surjective (completedResidueComap K f y))
    (z : CompletedResidueField K (comap f.toBoundedRingHom y)) :
    completedResidueEquivOfSurjective K f y hs z = completedResidueComap K f y z := rfl

variable {L : Type uL} [NormedField L] [CompleteSpace L] [Algebra K L]

/-- Surjectivity of the actual residue comap gives uniqueness of characters
with a fixed point norm and a fixed restriction to the source algebra. -/
theorem character_eq_of_surjective_completedResidueComap
    (f : BoundedAlgHom K A B) (y : BanachSpectrum B)
    (hs : Function.Surjective (completedResidueComap K f y))
    (g h : B →ₐ[K] L) (hg : ∀ b, ‖g b‖ = y b) (hh : ∀ b, ‖h b‖ = y b)
    (heq : ∀ a, g (f a) = h (f a)) : g = h := by
  let g' := completedResidueLift K y g hg
  let h' := completedResidueLift K y h hh
  have hc : g'.comp (completedResidueComap K f y) =
      h'.comp (completedResidueComap K f y) := by
    apply completedResidueBoundedAlgHom_ext K (comap f.toBoundedRingHom y)
    intro a
    change g' (completedResidueComap K f y
        (completedResidueMap K (comap f.toBoundedRingHom y) a)) =
      h' (completedResidueComap K f y
        (completedResidueMap K (comap f.toBoundedRingHom y) a))
    simpa only [completedResidueComap_map, g', h', completedResidueLift_map] using heq a
  have hext : g' = h' := by
    apply BoundedAlgHom.ext
    intro z
    obtain ⟨w, rfl⟩ := hs z
    exact congrArg (fun φ : BoundedAlgHom K
      (CompletedResidueField K (comap f.toBoundedRingHom y)) L => φ w) hc
  ext b
  exact (completedResidueLift_map K y g hg b).symm.trans
    ((congrArg (fun φ : BoundedAlgHom K (CompletedResidueField K y) L =>
      φ (completedResidueMap K y b)) hext).trans (completedResidueLift_map K y h hh b))

/-- A prescribed source character extends uniquely when the canonical residue
comap is surjective. Algebraic closedness of the target is unnecessary here. -/
theorem existsUnique_character_lift_of_surjective_completedResidueComap
    (f : BoundedAlgHom K A B) (y : BanachSpectrum B)
    (hs : Function.Surjective (completedResidueComap K f y))
    (g : A →ₐ[K] L) (hg : ∀ a, ‖g a‖ = (comap f.toBoundedRingHom y) a) :
    ∃! h : BoundedAlgHom K B L,
      (∀ b, ‖h b‖ = y b) ∧ ∀ a, h (f a) = g a := by
  let e := completedResidueEquivOfSurjective K f y hs
  let i := completedResidueLift K (comap f.toBoundedRingHom y) g hg
  let h := i.comp (e.symm.toBoundedAlgHom.comp (completedResidueMap K y))
  have he (z : CompletedResidueField K y) : ‖e.symm z‖ = ‖z‖ := by
    have hz := (isometry_completedResidueComap K f y).norm_map_of_map_zero
      (map_zero _) (e.symm z)
    exact hz.symm.trans (congrArg norm (e.apply_symm_apply z))
  have hn (b : B) : ‖h b‖ = y b := by
    change ‖i (e.symm (completedResidueMap K y b))‖ = y b
    rw [(isometry_completedResidueLift K _ g hg).norm_map_of_map_zero (map_zero _),
      he, norm_completedResidueMap]
  have hr (a : A) : h (f a) = g a := by
    change i (e.symm (completedResidueMap K y (f a))) = g a
    rw [← completedResidueComap_map K f y a]
    change i (e.symm (e (completedResidueMap K (comap f.toBoundedRingHom y) a))) = _
    rw [e.symm_apply_apply]
    exact completedResidueLift_map K _ g hg a
  refine ⟨h, ⟨hn, hr⟩, ?_⟩
  intro h' hh'
  apply BoundedAlgHom.ext
  exact AlgHom.congr_fun
    (character_eq_of_surjective_completedResidueComap K f y hs h'.toAlgHom h.toAlgHom
      hh'.1 hn (fun a => (hh'.2 a).trans (hr a).symm))

/-- Finiteness of the bounded algebra map suffices to extend any prescribed
point-realizing character into a complete algebraically closed target. -/
theorem exists_character_lift_of_finite
    [IsUltrametricDist L] [IsAlgClosed L]
    (f : BoundedAlgHom K A B) (hf : f.toAlgHom.toRingHom.Finite) (y : BanachSpectrum B)
    (g : A →ₐ[K] L) (hg : ∀ a, ‖g a‖ = (comap f.toBoundedRingHom y) a) :
    ∃ h : BoundedAlgHom K B L,
      (∀ b, ‖h b‖ = y b) ∧ ∀ a, h (f a) = g a :=
  exists_character_lift_of_isAlgebraic_completedResidueComap K f y
    (algebraic_completedResidueComap K f hf y) g hg

end Langlands.Analytic.BanachSpectrum
