import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Langlands.GroupScheme.Torus.GenericSelfCentralizing
import Langlands.GroupScheme.Torus.RelativeGeometry
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement

/-! # Valuative separation of closed torus subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} (G : GroupScheme S)
  {R : Type u} [CommRing R] [IsDomain R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (f : Spec (CommRingCat.of R) ⟶ S)

/-- Two admissible subgroups over an integral affine test agree if their
actual restrictions to its fraction field agree. -/
theorem restrict_injective_of_fractionField :
    Function.Injective
      (restrict (algebraOverBase f K) :
        AdmissibleSubgroup ((baseChange f).obj G) →
          AdmissibleSubgroup ((baseChange (algebraOver f K).hom).obj G)) := by
  intro F F' h
  let a := algebraOverBase f K
  let r := admissibleRepresentative F
  let r' := admissibleRepresentative F'
  let : Smooth r.group.X.hom := r.torus.smooth
  let : Smooth r'.group.X.hom := r'.torus.smooth
  let c := Descent.pullbackComparison f (Spec.algebraMap R K) (algebraOver f K).hom
    (Over.w a) G
  have hEval : evaluate r.hom a = evaluate r'.hom a :=
    congrArg Subtype.val h
  have hGeneric : SubgroupFunctor.range ((baseChange (Spec.algebraMap R K)).map r.hom) =
      SubgroupFunctor.range ((baseChange (Spec.algebraMap R K)).map r'.hom) :=
    (SubgroupFunctor.range_comp_iso_eq_iff _ _ c).mp hEval
  apply Subtype.ext
  rw [← r.represents.2, ← r'.represents.2]
  exact le_antisymm
    (SubgroupFunctor.range_le_of_fractionField K r.hom r'.hom r'.closed hGeneric.le)
    (SubgroupFunctor.range_le_of_fractionField K r'.hom r.hom r.closed hGeneric.ge)

/-- Restriction to the fraction field as an embedding on the actual small
presheaf of closed torus subgroups. -/
def fractionFieldRestriction :
    (smallAdmissiblePresheaf G).obj (op (Over.mk f)) ↪
      (smallAdmissiblePresheaf G).obj (op (algebraOver f K)) where
  toFun := (smallAdmissiblePresheaf G).map (algebraOverBase f K).op
  inj' := by
    intro x y h
    apply (smallAdmissibleEquiv G (Over.mk f)).injective
    apply restrict_injective_of_fractionField G K f
    simpa only [smallAdmissibleEquiv_map] using
      congrArg (smallAdmissibleEquiv G (algebraOver f K)) h

/-- The small presheaf of closed torus subgroups satisfies Murre's valuative
separation condition. -/
theorem valuativeSeparation_smallAdmissiblePresheaf :
    ValuativeSeparation (smallAdmissiblePresheaf G) := by
  intro V _ _ _ b
  exact (fractionFieldRestriction G (FractionRing V) b).injective

end Langlands.GroupScheme.TorusSubgroupModuli
