import Langlands.ClassField.Global.IdeleFiniteInvariant
import Langlands.ClassField.Global.IdeleSemilocal

/-! # Realizing finite local invariant values in idele cohomology -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory FundamentalClass

universe u

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

attribute [local instance] isGalois_adicCompletion FiniteExtension.local_finite

omit [NumberField F] [NumberField E] [IsGalois F E] in
/-- Places over different base places cannot be Galois conjugate. -/
theorem finitePlaceEquiv_ne_of_base_ne
    (v v' : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v'.asIdeal]
    (hv : v' ≠ v) (g : E ≃ₐ[F] E) :
    finitePlaceEquiv g.toRingEquiv w' ≠ w := by
  intro h
  have hw : w.under (𝓞 F) = v :=
    HeightOneSpectrum.ext (Ideal.over_def w.asIdeal v.asIdeal).symm
  have hw' : w'.under (𝓞 F) = v' :=
    HeightOneSpectrum.ext (Ideal.over_def w'.asIdeal v'.asIdeal).symm
  have he := finitePlaceEquiv_under (RingEquiv.refl F) g.toRingEquiv
    (fun x => g.commutes x) w'
  rw [finitePlaceEquiv_refl, Equiv.refl_apply, h, hw, hw'] at he
  exact hv he

/-- The section at one base place has zero local image at every other base place. -/
theorem ideleLocalSection_comp_ideleLocalMap_of_base_ne
    (v v' : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v'.asIdeal]
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)]
    (hv : v' ≠ v) (n : ℕ) :
    ideleLocalSection v w n ≫ ideleLocalMap v' w' n = 0 :=
  ideleLocalSection_comp_ideleLocalMap_of_ne v v' w w'
    (finitePlaceEquiv_ne_of_base_ne v v' w w' hv) n

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)

/-- The invariant of a section at its defining place is the given local invariant. -/
theorem finiteIdeleInvariant_ideleLocalSection
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal]
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)]
    (x : relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) :
    finiteIdeleInvariant I v w (ideleLocalSection v w 2 x) =
      (I (residuePrime v)).relative (padicField v) (w.adicCompletion E) x := by
  have h := congrArg (fun f => f x) (ideleLocalSection_comp_ideleLocalMap v w 2)
  change ideleLocalMap v w 2 (ideleLocalSection v w 2 x) = x at h
  change (I (residuePrime v)).relative (padicField v) (w.adicCompletion E)
    (ideleLocalMap v w 2 (ideleLocalSection v w 2 x)) = _
  rw [h]

/-- All other base places have zero invariant on the chosen section. -/
theorem finiteIdeleInvariant_ideleLocalSection_of_base_ne
    (v v' : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v'.asIdeal]
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)]
    (hv : v' ≠ v)
    (x : relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) :
    finiteIdeleInvariant I v' w' (ideleLocalSection v w 2 x) = 0 := by
  have h := congrArg (fun f => f x)
    (ideleLocalSection_comp_ideleLocalMap_of_base_ne v v' w w' hv 2)
  change ideleLocalMap v' w' 2 (ideleLocalSection v w 2 x) = 0 at h
  change (I (residuePrime v')).relative (padicField v') (w'.adicCompletion E)
    (ideleLocalMap v' w' 2 (ideleLocalSection v w 2 x)) = 0
  rw [h, map_zero]

/-- The finite sum on a section reduces to the invariant at that section's place. -/
theorem finiteIdeleInvariantSum_ideleLocalSection
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (v : HeightOneSpectrum (𝓞 F))
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (wf v).1).range)]
    (x : relativeCohomology (padicField v).Carrier ((wf v).1.adicCompletion E) 2) :
    finiteIdeleInvariantSum I hI wf (ideleLocalSection v (wf v).1 2 x) =
      (I (residuePrime v)).relative (padicField v) ((wf v).1.adicCompletion E) x := by
  change (∑ᶠ v', haveI := (wf v').2;
    finiteIdeleInvariant I v' (wf v').1 (ideleLocalSection v (wf v).1 2 x)) = _
  rw [finsum_eq_single _ v (fun v' hv =>
    finiteIdeleInvariant_ideleLocalSection_of_base_ne I v v' (wf v).1 (wf v').1 hv x)]
  exact finiteIdeleInvariant_ideleLocalSection I v (wf v).1 x

/-- Realize a local denominator value by the inverse local invariant and the
published section into actual idele cohomology. -/
def finiteIdeleInvariantLift
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal]
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)] :
    denominatorSubgroup (Module.finrank (padicField v).Carrier (w.adicCompletion E)) →+
      relativeIdeleCohomology F E 2 :=
  haveI := isGalois_adicCompletion v w
  haveI := FiniteExtension.local_finite v w
  (ideleLocalSection v w 2).hom.toAddMonoidHom.comp
    ((I (residuePrime v)).relativeInvariantEquiv (hI _) (padicField v)
      (w.adicCompletion E)).symm.toAddMonoidHom

/-- The lift has the requested local invariant. -/
@[simp] theorem finiteIdeleInvariant_finiteIdeleInvariantLift
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal]
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)]
    (y : denominatorSubgroup
      (Module.finrank (padicField v).Carrier (w.adicCompletion E))) :
    finiteIdeleInvariant I v w (finiteIdeleInvariantLift I hI v w y) = y := by
  change finiteIdeleInvariant I v w (ideleLocalSection v w 2
    (((I (residuePrime v)).relativeInvariantEquiv (hI _) (padicField v)
      (w.adicCompletion E)).symm y)) = _
  rw [finiteIdeleInvariant_ideleLocalSection, InvariantFamily.relativeInvariantEquiv_symm_apply]

/-- The finite sum of the lift is the requested denominator value. -/
@[simp] theorem finiteIdeleInvariantSum_finiteIdeleInvariantLift
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (v : HeightOneSpectrum (𝓞 F))
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (wf v).1).range)]
    (y : denominatorSubgroup
      (Module.finrank (padicField v).Carrier ((wf v).1.adicCompletion E))) :
    finiteIdeleInvariantSum I hI wf (finiteIdeleInvariantLift I hI v (wf v).1 y) = y := by
  change finiteIdeleInvariantSum I hI wf (ideleLocalSection v (wf v).1 2
    (((I (residuePrime v)).relativeInvariantEquiv (hI _) (padicField v)
      ((wf v).1.adicCompletion E)).symm y)) = _
  rw [finiteIdeleInvariantSum_ideleLocalSection,
    InvariantFamily.relativeInvariantEquiv_symm_apply]

end Langlands.ClassField.Global
