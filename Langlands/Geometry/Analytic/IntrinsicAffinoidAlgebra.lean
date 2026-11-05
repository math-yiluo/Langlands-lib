import Langlands.Geometry.Analytic.AdmissibleEpimorphism
import Langlands.Geometry.Analytic.BoundedQuotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Intrinsic affinoidness and constructed closed-kernel presentations -/

noncomputable section

universe u v w

namespace Langlands.Analytic

namespace BoundedAlgHom

variable {K : Type u} [NormedField K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A]
  {B : Type w} [NormedCommRing B] [NormedAlgebra K B]
  (f : BoundedAlgHom K A B)

instance isClosed_ker : IsClosed ((RingHom.ker f.toAlgHom) : Set A) := by
  change IsClosed {a : A | f a = 0}
  exact isClosed_eq f.continuous continuous_const

/-- An admissible epimorphism constructs an actual bounded equivalence
from its closed-kernel quotient to the unchanged target algebra. -/
def kernelQuotientEquiv (hf : f.IsAdmissibleEpi) :
    BoundedAlgEquiv K (A ⧸ (RingHom.ker f.toAlgHom)) B := by
  let e : (A ⧸ (RingHom.ker f.toAlgHom)) ≃ₐ[K] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := f.toAlgHom) hf.1
  refine {
    toAlgEquiv := e
    bounded := ?_
    inverse_bounded := ?_ }
  · obtain ⟨M, hM, hbound⟩ := f.bounded
    refine ⟨M, hM, quotient_norm_bound (RingHom.ker f.toAlgHom) e.toRingHom M hM ?_⟩
    intro a
    exact (congrArg norm
      (Ideal.quotientKerAlgEquivOfSurjective_mk (f := f.toAlgHom) hf.1 a)).trans_le
        (hbound a)
  · obtain ⟨C, hC, hlifts⟩ := f.isAdmissibleEpi_iff_normControlledLifts.mp hf
    refine ⟨C, hC, fun b => ?_⟩
    obtain ⟨a, ha, hnorm⟩ := hlifts b
    have heq : e.symm b = Ideal.Quotient.mk (RingHom.ker f.toAlgHom) a := by
      apply e.injective
      exact (e.apply_symm_apply b).trans
        ((Ideal.quotientKerAlgEquivOfSurjective_mk (f := f.toAlgHom) hf.1 a).trans ha).symm
    exact (congrArg norm heq).trans_le
      ((Ideal.Quotient.norm_mk_le (RingHom.ker f.toAlgHom) a).trans hnorm)

@[simp]
theorem kernelQuotientEquiv_mk (hf : f.IsAdmissibleEpi) (a : A) :
    f.kernelQuotientEquiv hf (Ideal.Quotient.mk (RingHom.ker f.toAlgHom) a) = f a :=
  Ideal.quotientKerAlgEquivOfSurjective_mk hf.1 a

/-- The constructed equivalence recovers the entire original bounded
epimorphism after the actual quotient map. -/
theorem kernelQuotientEquiv_comp_quotientMap (hf : f.IsAdmissibleEpi) :
    (f.kernelQuotientEquiv hf).toBoundedAlgHom.comp (quotientMap K (RingHom.ker f.toAlgHom)) = f :=
  BoundedAlgHom.ext (f.kernelQuotientEquiv_mk hf)

end BoundedAlgHom

namespace BoundedAlgEquiv

variable {K : Type u} [NormedField K]
  {A : Type v} [NormedCommRing A] [Algebra K A]
  {B : Type w} [NormedCommRing B] [Algebra K B]

/-- The actual bounded inverse makes every bounded equivalence an
admissible epimorphism, without any open mapping argument. -/
theorem isAdmissibleEpi (e : BoundedAlgEquiv K A B) :
    e.toBoundedAlgHom.IsAdmissibleEpi :=
  e.toBoundedAlgHom.isAdmissibleEpi_of_bounded_section e.symm.toBoundedAlgHom
    (BoundedAlgHom.ext e.apply_symm_apply)

end BoundedAlgEquiv

/-- The intrinsic source criterion for a Banach coefficient algebra:
an actual admissible finite positive-radius Tate epimorphism exists. -/
def IsAffinoidAlgebra (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (E : Type v) [NormedCommRing E] [NormedAlgebra K E]
    [IsUltrametricDist E] [CompleteSpace E] : Prop :=
  ∃ n : ℕ, ∃ r : PositivePolyradius (Fin n),
    ∃ f : BoundedAlgHom K (GeneralizedTateAlgebra r K) E, f.IsAdmissibleEpi

namespace IsAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {E : Type v} [NormedCommRing E] [NormedAlgebra K E]
  [IsUltrametricDist E] [CompleteSpace E] (h : IsAffinoidAlgebra K E)

def arity : ℕ := h.choose

def polyradius : PositivePolyradius (Fin h.arity) := h.choose_spec.choose

def quotientMap : BoundedAlgHom K (GeneralizedTateAlgebra h.polyradius K) E :=
  h.choose_spec.choose_spec.choose

theorem quotientMap_admissible : h.quotientMap.IsAdmissibleEpi :=
  h.choose_spec.choose_spec.choose_spec

/-- Construct the closed-kernel finite weighted Tate presentation from
the intrinsic admissible quotient, with no supplied presentation output. -/
def presentation : PresentedAffinoidAlgebra K where
  arity := h.arity
  polyradius := h.polyradius
  ideal := (RingHom.ker h.quotientMap.toAlgHom)
  ideal_closed := h.quotientMap.isClosed_ker

/-- Its actual quotient carrier is bounded equivalent to the original
algebra by the constructed closed-kernel map and norm-controlled inverse. -/
def presentationEquiv : BoundedAlgEquiv K h.presentation E :=
  h.quotientMap.kernelQuotientEquiv h.quotientMap_admissible

@[simp]
theorem presentationEquiv_presentationMap (p : GeneralizedTateAlgebra h.polyradius K) :
    h.presentationEquiv (PresentedAffinoidAlgebra.presentationMap K h.presentation p) =
      h.quotientMap p :=
  h.quotientMap.kernelQuotientEquiv_mk h.quotientMap_admissible p

variable {F : Type w} [NormedCommRing F] [NormedAlgebra K F]
  [IsUltrametricDist F] [CompleteSpace F]

include h in
/-- Intrinsic affinoidness transports along entire bounded algebra
equivalences by composing the original admissible Tate quotient. -/
theorem of_boundedEquiv (e : BoundedAlgEquiv K E F) : IsAffinoidAlgebra K F := by
  obtain ⟨n, r, f, hf⟩ := h
  exact ⟨n, r, e.toBoundedAlgHom.comp f,
    BoundedAlgHom.IsAdmissibleEpi.comp f e.toBoundedAlgHom hf e.isAdmissibleEpi⟩

end IsAffinoidAlgebra

namespace PresentedAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K)

/-- Every actual finite closed weighted Tate quotient satisfies the
intrinsic source affinoid criterion by its genuine admissible quotient. -/
theorem isAffinoidAlgebra : IsAffinoidAlgebra K A :=
  ⟨A.arity, A.polyradius, presentationMap K A, presentationMap_isAdmissibleEpi K A⟩

end PresentedAffinoidAlgebra

end Langlands.Analytic
