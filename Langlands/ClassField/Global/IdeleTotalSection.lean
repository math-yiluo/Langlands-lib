import Langlands.ClassField.Global.IdeleFiniteSection
import Langlands.ClassField.Global.IdeleTotalInvariant

/-! # Finite local denominator values in the total idele invariant -/

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

/-- A finite single-coordinate idele has trivial coordinate at every infinite place. -/
@[simp] theorem ideleInfiniteCoordinate_ofAdicCompletion
    (w : HeightOneSpectrum (𝓞 E)) (z : InfinitePlace E)
    (a : (w.adicCompletion E)ˣ) :
    ideleInfiniteCoordinate z (IdeleGroup.ofAdicCompletion (𝓞 E) E w a) = 1 :=
  Units.ext rfl

/-- Every infinite coordinate of the finite semilocal section is zero additively. -/
theorem infiniteCoordinateLinear_ideleSemilocalSection
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal]
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)]
    (z : InfinitePlace E)
    (a : Rep.coind (decompositionHom v w)
      (unitsRepresentation (padicField v).Carrier (w.adicCompletion E))) :
    infiniteCoordinateLinear F z ((ideleSemilocalSection v w).hom a) = 0 := by
  rw [ideleSemilocalSection, Shapiro.coindSum_hom_apply, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  induction c using QuotientGroup.induction_on with | H g => ?_
  change Additive.ofMul (ideleInfiniteCoordinate z (relativeIdeleAut F E g
    (IdeleGroup.ofAdicCompletion (𝓞 E) E w _))) = 0
  exact congrArg Additive.ofMul
    (ideleInfiniteCoordinate_relativeIdeleAut_eq_one g z
      (ideleInfiniteCoordinate_ofAdicCompletion w _ _))

/-- A finite local cohomology section has zero invariant at every infinite place. -/
theorem archimedeanIdeleInvariant_ideleLocalSection
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal]
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v w).range)]
    (z : InfinitePlace E)
    (x : relativeCohomology (padicField v).Carrier (w.adicCompletion E) 2) :
    archimedeanIdeleInvariant F z (ideleLocalSection v w 2 x) = 0 := by
  apply (archimedeanIdeleInvariant_eq_zero_iff _).2 _ z
  obtain ⟨f, hf⟩ := Reciprocity.H2π_surjective
    ((Shapiro.shapiroIsoOf (decompositionHom_injective v w) _ 2).inv x)
  refine ⟨groupCohomology.mapCocycles₂ (MonoidHom.id _) (ideleSemilocalSection v w) f,
    ?_, fun a => ?_⟩
  · rw [← groupCohomology.H2π_comp_map_apply, hf]
    rfl
  · rw [ideleInfinite_eq_one_iff]
    intro z'
    exact congrArg Additive.toMul
      (infiniteCoordinateLinear_ideleSemilocalSection v w z' (f a))

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)

/-- The total invariant on a finite section is precisely its local invariant. -/
theorem totalIdeleInvariant_ideleLocalSection
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (v : HeightOneSpectrum (𝓞 F))
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (wf v).1).range)]
    (x : relativeCohomology (padicField v).Carrier ((wf v).1.adicCompletion E) 2) :
    totalIdeleInvariant I hI wf wi (ideleLocalSection v (wf v).1 2 x) =
      (I (residuePrime v)).relative (padicField v) ((wf v).1.adicCompletion E) x := by
  simp only [totalIdeleInvariant, AddMonoidHom.add_apply, AddMonoidHom.finsetSum_apply]
  rw [finiteIdeleInvariantSum_ideleLocalSection I hI wf v x]
  suffices h : ∑ z, archimedeanIdeleInvariant F (wi z).1
      (ideleLocalSection v (wf v).1 2 x) = 0 by rw [h, add_zero]
  exact Finset.sum_eq_zero fun z _ =>
    archimedeanIdeleInvariant_ideleLocalSection v (wf v).1 (wi z).1 x

/-- The total invariant of a finite local lift is its prescribed denominator value. -/
@[simp] theorem totalIdeleInvariant_finiteIdeleInvariantLift
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (v : HeightOneSpectrum (𝓞 F))
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (wf v).1).range)]
    (y : denominatorSubgroup
      (Module.finrank (padicField v).Carrier ((wf v).1.adicCompletion E))) :
    totalIdeleInvariant I hI wf wi (finiteIdeleInvariantLift I hI v (wf v).1 y) = y := by
  change totalIdeleInvariant I hI wf wi (ideleLocalSection v (wf v).1 2
    (((I (residuePrime v)).relativeInvariantEquiv (hI _) (padicField v)
      ((wf v).1.adicCompletion E)).symm y)) = _
  rw [totalIdeleInvariant_ideleLocalSection, InvariantFamily.relativeInvariantEquiv_symm_apply]

/-- Include the local denominator subgroup into the range of the total invariant,
using the finite local lift as witness. -/
def localDenominatorToTotalInvariantRange
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (v : HeightOneSpectrum (𝓞 F))
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (wf v).1).range)] :
    denominatorSubgroup
      (Module.finrank (padicField v).Carrier ((wf v).1.adicCompletion E)) →+
        (totalIdeleInvariant I hI wf wi).range :=
  { toFun := fun y => ⟨y, ⟨finiteIdeleInvariantLift I hI v (wf v).1 y,
      totalIdeleInvariant_finiteIdeleInvariantLift I hI wf wi v y⟩⟩
    map_zero' := Subtype.ext rfl
    map_add' := fun _ _ => Subtype.ext rfl }

@[simp] theorem localDenominatorToTotalInvariantRange_coe
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v)
    (v : HeightOneSpectrum (𝓞 F))
    [Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (wf v).1).range)]
    (y : denominatorSubgroup
      (Module.finrank (padicField v).Carrier ((wf v).1.adicCompletion E))) :
    (localDenominatorToTotalInvariantRange I hI wf wi v y : RationalModIntegers) = y :=
  rfl

end Langlands.ClassField.Global
