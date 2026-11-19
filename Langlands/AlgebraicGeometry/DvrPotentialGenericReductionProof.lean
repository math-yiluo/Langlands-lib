import Langlands.AlgebraicGeometry.DvrPotentialGenericReductionStatement
import Langlands.AlgebraicGeometry.PotentialGeometricReduction
import Langlands.AlgebraicGeometry.DvrDominatingFiniteExtension
import Langlands.AlgebraicGeometry.QuasiCompactAffineEtaleCover

/-! # Proof of potential geometric reducedness of the reduced generic fibre over a DVR

We prove `Langlands.AlgebraicGeometry.DvrPotentialGenericReductionStatement`. Over a field the
reduction of a quasi-compact locally finite-type scheme becomes geometrically reduced after a
finite extension (`exists_good_field`, reducing to the affine case through an affine étale cover).
A DVR `R'` dominating `R` inside that finite extension of the fraction field then gives the
required flat surjective base change.
-/

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

namespace PotentialGeometricReduction

/-- The field case: a quasi-compact locally finite-type scheme over a field becomes good after
a finite extension. -/
theorem exists_good_field (K : Type u) [Field K] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of K)) [QuasiCompact f] [LocallyOfFiniteType f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      Good (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨R, p, hps, hpf, hpg, hpl, -, -⟩ := QuasiCompactAffineEtaleCover.exists_spec_cover Y
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (p ≫ f)
  let : Algebra K R := φ.hom.toAlgebra
  have hlft : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
  have : Algebra.FiniteType K R :=
    RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hlft)
  obtain ⟨L, _, _, _, hL⟩ := exists_good_affine K R
  refine ⟨L, inferInstance, inferInstance, inferInstance, ?_⟩
  set σ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have h1 : Good (pullback.snd (p ≫ f) σ) := by
    have : CommRingCat.ofHom (algebraMap K R) = φ := rfl
    rw [this, hφ] at hL
    exact hL
  have h2 := h1.iso_comp (pullbackRightPullbackFstIso f σ p).hom
  rw [pullbackRightPullbackFstIso_hom_snd] at h2
  have : IsLocallyNoetherian (pullback f σ) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f σ)
  have : GeometricallyReduced (pullback.snd p (pullback.fst f σ)) := inferInstance
  exact Good.of_comp (pullback.snd p (pullback.fst f σ)) _ h2

end PotentialGeometricReduction

open PotentialGeometricReduction in
/-- After a faithfully flat DVR extension, the reduction of the generic fibre of a flat
finite-type scheme is geometrically reduced. -/
theorem dvrPotentialGenericReduction : DvrPotentialGenericReductionStatement.{u} := by
  intro R _ _ _ X hflat hlft hqc
  let K := FractionRing R
  let a : Spec (.of K) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))
  obtain ⟨L, _, _, _, hL⟩ := exists_good_field K (pullback.snd X.hom a)
  obtain ⟨R', _, _, _, _, σ, -, hbflat, hbsurj, hσ⟩ :=
    DvrDominatingFiniteExtension.exists_dvr_of_finite_extension R L
  refine ⟨R', inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap R R')), hbflat, hbsurj, ?_⟩
  have key : Good (pullback.snd
      (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
      (Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))))) := by
    rw [← good_pullback_snd_comp_iff, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hσ,
      CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
      ← Category.assoc, good_pullback_snd_comp_iff, good_pullback_snd_comp_iff]
    exact hL.pullback_snd _
  exact (good_iff _).mp key

end Langlands.AlgebraicGeometry
