import Langlands.GroupScheme.Descent.FiniteUnramifiedIntegers
import Langlands.Galois.Local.SeparableUnramifiedFiniteArithmetic
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Infinitesimal lifting for maximal unramified integers -/

noncomputable section

open scoped ValuativeRel
open Langlands.GroupScheme.Descent.FiniteUnramified

namespace Langlands.LocalGalois.Separable

universe u v

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance integerLiftNormedField : NontriviallyNormedField F := localNormedField F
local instance integerLiftUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance integerLiftComplete : CompleteSpace F := localNormedField_complete F
local instance integerLiftAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- The integers of a finite unramified intermediate field inside the maximal
unramified integers form an étale algebra over the original integers. -/
theorem integerCoefficients_etale (E : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E] (hE : E ≤ inertiaFixedField F) :
    Algebra.Etale ↥𝒪[F] (integerCoefficients F E) := by
  let R := baseIntegers F
  let S := extensionIntegers F E
  let : Algebra.IsSeparable F E :=
    Algebra.isSeparable_tower_bot_of_isSeparable F E (SeparableClosure F)
  have unramified := ((separableUnramified F).1 E).mp hE
  let : Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    unramified.2
  let : Algebra.FormallyUnramified R S :=
    Algebra.FormallyUnramified.of_map_maximalIdeal unramified.1
  let : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hEtale : (algebraMap R S).Etale := RingHom.etale_algebraMap.mpr
    (Algebra.Etale.of_formallyUnramified_of_flat : Algebra.Etale R S)
  let eR := RingEquiv.subringCongr (localNormedField_integer F)
  let eS := integerCoefficientsEquiv F E hE
  have hMap : (eS.symm.toRingHom.comp (algebraMap R S)).comp eR.symm.toRingHom =
      algebraMap ↥𝒪[F] (integerCoefficients F E) := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  apply RingHom.etale_algebraMap.mp
  rw [← hMap]
  exact RingHom.Etale.respectsIso.2 _ eR.symm (RingHom.Etale.respectsIso.1 _ eS.symm hEtale)

private abbrev FiniteUnramifiedIntermediate :=
  {E : IntermediateField F (SeparableClosure F) //
    FiniteDimensional F E ∧ E ≤ inertiaFixedField F}

private abbrev stage (E : FiniteUnramifiedIntermediate F) := integerCoefficients F E.val

private theorem exists_stage (x : fixedFieldIntegers F) :
    ∃ E : FiniteUnramifiedIntermediate F, x ∈ stage F E := by
  obtain ⟨E, hfin, _, hE, _, hx⟩ := (separableUnramified F).2 {x.val}
  exact ⟨⟨E, hfin, hE⟩, hx _ (Finset.mem_singleton_self _)⟩

private instance : Nonempty (FiniteUnramifiedIntermediate F) := ⟨(exists_stage F 0).choose⟩

private theorem stage_directed : Directed (· ≤ ·) (stage F) := by
  intro E E'
  let := E.property.1
  let := E'.property.1
  exact ⟨⟨E.val ⊔ E'.val, inferInstance, sup_le E.property.2 E'.property.2⟩,
    fun _ hx => (le_sup_left : E.val ≤ E.val ⊔ E'.val) hx,
    fun _ hx => (le_sup_right : E'.val ≤ E.val ⊔ E'.val) hx⟩

variable {B : Type v} [CommRing B] [Algebra ↥𝒪[F] B]

private def stageLift (I : Ideal B) (hI : IsNilpotent I)
    (f : fixedFieldIntegers F →ₐ[↥𝒪[F]] B ⧸ I) (E : FiniteUnramifiedIntermediate F) :
    stage F E →ₐ[↥𝒪[F]] B :=
  haveI := E.property.1
  haveI := integerCoefficients_etale F E.val E.property.2
  Algebra.FormallySmooth.lift I hI (f.comp (stage F E).val)

private theorem stageLift_spec (I : Ideal B) (hI : IsNilpotent I)
    (f : fixedFieldIntegers F →ₐ[↥𝒪[F]] B ⧸ I) (E : FiniteUnramifiedIntermediate F) :
    (Ideal.Quotient.mkₐ ↥𝒪[F] I).comp (stageLift F I hI f E) = f.comp (stage F E).val := by
  let := E.property.1
  let := integerCoefficients_etale F E.val E.property.2
  exact Algebra.FormallySmooth.comp_lift I hI _

/-- Lift an algebra map from the maximal unramified integers across a nilpotent
ideal by gluing the unique lifts of its restrictions to finite étale stages. -/
def fixedFieldIntegerLift (I : Ideal B) (hI : IsNilpotent I)
    (f : fixedFieldIntegers F →ₐ[↥𝒪[F]] B ⧸ I) :
    fixedFieldIntegers F →ₐ[↥𝒪[F]] B := by
  have htop : ⊤ ≤ ⨆ E, stage F E := by
    intro x _
    obtain ⟨E, hx⟩ := exists_stage F x
    exact (le_iSup (stage F) E) hx
  have hcompat (E E' : FiniteUnramifiedIntermediate F) (h : stage F E ≤ stage F E') :
      stageLift F I hI f E = (stageLift F I hI f E').comp (Subalgebra.inclusion h) := by
    let := E.property.1
    let := integerCoefficients_etale F E.val E.property.2
    apply Algebra.FormallyUnramified.lift_unique I hI
    rw [stageLift_spec, ← AlgHom.comp_assoc, stageLift_spec]
    rfl
  exact (Subalgebra.iSupLift (stage F) (stage_directed F) (stageLift F I hI f)
    hcompat ⊤ htop).comp Algebra.toTop

private theorem fixedFieldIntegerLift_apply (I : Ideal B) (hI : IsNilpotent I)
    (f : fixedFieldIntegers F →ₐ[↥𝒪[F]] B ⧸ I) (E : FiniteUnramifiedIntermediate F)
    (x : stage F E) : fixedFieldIntegerLift F I hI f x = stageLift F I hI f E x := by
  unfold fixedFieldIntegerLift
  rw [AlgHom.comp_apply]
  exact Subalgebra.iSupLift_mk (stage F) (T := ⊤) x Algebra.mem_top

@[simp]
theorem comp_fixedFieldIntegerLift (I : Ideal B) (hI : IsNilpotent I)
    (f : fixedFieldIntegers F →ₐ[↥𝒪[F]] B ⧸ I) :
    (Ideal.Quotient.mkₐ ↥𝒪[F] I).comp (fixedFieldIntegerLift F I hI f) = f := by
  ext x
  obtain ⟨E, hx⟩ := exists_stage F x
  let y : stage F E := ⟨x, hx⟩
  change (Ideal.Quotient.mkₐ ↥𝒪[F] I) (fixedFieldIntegerLift F I hI f (y : fixedFieldIntegers F)) = f y
  rw [fixedFieldIntegerLift_apply F I hI f E y]
  exact AlgHom.congr_fun (stageLift_spec F I hI f E) y

/-- Reduction along a nilpotent ideal gives a bijection on maps from the actual
maximal unramified integers. -/
theorem fixedFieldIntegerLift_bijective (I : Ideal B) (hI : IsNilpotent I) :
    Function.Bijective ((Ideal.Quotient.mkₐ ↥𝒪[F] I).comp :
      (fixedFieldIntegers F →ₐ[↥𝒪[F]] B) → fixedFieldIntegers F →ₐ[↥𝒪[F]] B ⧸ I) := by
  refine ⟨?_, fun f => ⟨fixedFieldIntegerLift F I hI f, comp_fixedFieldIntegerLift F I hI f⟩⟩
  intro g g' heq
  ext x
  obtain ⟨E, hx⟩ := exists_stage F x
  let := E.property.1
  let := integerCoefficients_etale F E.val E.property.2
  have h : g.comp (stage F E).val = g'.comp (stage F E).val :=
    Algebra.FormallyUnramified.lift_unique I hI _ _
      (congrArg (fun k : fixedFieldIntegers F →ₐ[↥𝒪[F]] B ⧸ I => k.comp (stage F E).val) heq)
  exact AlgHom.congr_fun h ⟨x, hx⟩

end Langlands.LocalGalois.Separable
