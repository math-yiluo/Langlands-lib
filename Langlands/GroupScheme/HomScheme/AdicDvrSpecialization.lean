import Langlands.AlgebraicGeometry.NoetherianDvrSpecialization
import Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Langlands.GroupScheme.HomScheme.AdicSystemBaseChange
import Langlands.GroupScheme.HomScheme.AffineFiberValuation
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # Algebraization on completed DVR specializations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry (DvrSpecialization nonempty_dvrSpecialization_spec)

namespace Langlands.GroupScheme.HomScheme.Adic

private theorem faithfullyFlat_adicCompletion {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    (algebraMap R (AdicCompletion I R)).FaithfullyFlat := by
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  refine ⟨fun m hm => ?_⟩
  rw [Ideal.smul_top_eq_map, IsLocalRing.eq_maximalIdeal hm]
  exact (Submodule.restrictScalars_eq_top_iff _ _ _).ne.mpr
    (AdicCompletion.isMaximal_map_of_le I (maximalIdeal R) hI I.fg_of_isNoetherianRing).ne_top

/-- Every nonclosed point over a Noetherian local base is reached by an
adic test on which the system from a diagonalizable source algebraizes. -/
def CompletedDvrSpecializationEffectivityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (H G : GroupScheme (Spec (CommRingCat.of A)))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
    RelativeMultiplicativeType.IsDiagonalizable H → HasAffineResidueFibers G →
    ∀ (s : System (maximalIdeal A) H G) (η : Spec (CommRingCat.of A)),
      η ≠ closedPoint A →
      ∃ (B : CommRingCat.{u}) (φ : A →+* B),
        IsAdicComplete ((maximalIdeal A).map φ) B ∧
        ∃ x : Spec B, Spec.map (CommRingCat.ofHom φ) x = η ∧
          ∃ f : (baseChange (Spec.map (CommRingCat.ofHom φ))).obj H ⟶
              (baseChange (Spec.map (CommRingCat.ofHom φ))).obj G,
            System.restrict ((maximalIdeal A).map φ) _ _ f = s.pull φ

set_option maxHeartbeats 1200000 in
/-- Algebraize the transported formal homomorphism over the completion
of a DVR specializing the chosen point to the closed point. -/
theorem completedDvrSpecializationEffectivity :
    CompletedDvrSpecializationEffectivityStatement.{u} := by
  intro A _ _ _ H G _ _ _ hH hG s η hη
  have hle : η.asIdeal ≤ maximalIdeal A := le_maximalIdeal η.isPrime.ne_top
  obtain ⟨D⟩ := nonempty_dvrSpecialization_spec A η (closedPoint A) hle hη
  let V : CommRingCat.{u} := D.ring
  let : IsDomain ↥V := D.domain
  let : IsDiscreteValuationRing ↥V := D.dvr
  let : IsNoetherianRing ↥V := inferInstance
  let : IsLocalRing ↥V := inferInstance
  let φ := (Spec.preimage D.map).hom
  let v := Spec.map (CommRingCat.ofHom φ)
  have hv : v = D.map := Spec.map_preimage D.map
  have hvClosed : v (closedPoint V) = closedPoint A := by
    rw [hv]
    exact D.closed_image
  have hcomap : Ideal.comap φ (maximalIdeal V) = maximalIdeal A :=
    congrArg PrimeSpectrum.asIdeal hvClosed
  have hφ : (maximalIdeal A).map φ ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.mpr hcomap.ge
  let I := (maximalIdeal A).map φ
  let B := AdicCompletion I V
  let d := Spec.map (CommRingCat.ofHom (algebraMap V B))
  let : IsNoetherianRing B := AdicCompletion.isNoetherianRing_of_isNoetherianRing I
  let ψ : A →+* B := (algebraMap V B).comp φ
  let c := Spec.map (CommRingCat.ofHom ψ)
  have hc : c = d ≫ v := by
    change Spec.map (CommRingCat.ofHom ((algebraMap V B).comp φ)) =
      Spec.map (CommRingCat.ofHom (algebraMap V B)) ≫ Spec.map (CommRingCat.ofHom φ)
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hcomplete : IsAdicComplete ((maximalIdeal A).map ψ) B := by
    change IsAdicComplete ((maximalIdeal A).map ((algebraMap V B).comp φ)) B
    rw [← Ideal.map_map]
    exact AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  let ηV : Spec V := ⟨⊥, inferInstance⟩
  let : Surjective d := ((flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap V B))).mpr (faithfullyFlat_adicCompletion I hφ)).2
  have hSurj : Function.Surjective d := d.surjective
  obtain ⟨x, hx⟩ := hSurj ηV
  have hImage : c x = η := by
    rw [hc, Scheme.Hom.comp_apply, hx, hv]
    exact D.generic_image
  let Gv := (baseChange v).obj G
  let Gd := (baseChange d).obj Gv
  let : IsAffineHom Gv.X.hom := G.isAffineHom_dvrPullback_of_residueFibers hG (R := V) v
  let : IsAffineHom Gd.X.hom := by
    change IsAffineHom (pullback.snd Gv.X.hom d)
    infer_instance
  let e : ((baseChange c).obj G).X ≅ Gd.X :=
    (Grp.forget _).mapIso (Descent.pullbackComparison v d c hc.symm G).symm
  let : IsIso e.hom.left :=
    (inferInstance : IsIso ((Over.forget (Spec (CommRingCat.of B))).mapIso e).hom)
  let : IsAffineHom e.hom.left := inferInstance
  have ht : IsAffineHom (e.hom.left ≫ Gd.X.hom) := inferInstance
  have hw : e.hom.left ≫ Gd.X.hom = ((baseChange c).obj G).X.hom := Over.w e.hom
  let : IsAffineHom ((baseChange c).obj G).X.hom := hw ▸ ht
  let : IsAdicComplete ((maximalIdeal A).map ψ) B := hcomplete
  obtain ⟨f, hf⟩ :=
    (AdicDiagonalizable.restrict_bijective_of_isDiagonalizable ((maximalIdeal A).map ψ)
      ((baseChange c).obj H) ((baseChange c).obj G) (hH.baseChange c)).2 (s.pull ψ)
  exact ⟨CommRingCat.of B, ψ, hcomplete, x, hImage, f, hf⟩

end Langlands.GroupScheme.HomScheme.Adic
