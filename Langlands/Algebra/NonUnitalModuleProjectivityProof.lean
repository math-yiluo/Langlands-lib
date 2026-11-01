import Langlands.Algebra.NonUnitalModuleEnoughProjectivesStatements
import Langlands.Algebra.NonUnitalModuleDirectSum
import Langlands.Algebra.NondegenerateModuleExactnessConcrete
import Langlands.Algebra.NonUnitalModuleCornerExactnessProof
import Langlands.CategoryTheory.Renard.HomExactnessComparison

/-! Proofs of the published Renard I.5.2 projectivity assertions. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.NonUnitalModuleProjectivityProof

universe uA uM uI

open NonUnitalModuleIdempotentIdeal NonUnitalModuleCorner

variable {A : Type uA} [NonUnitalRing A]

/-- Lift an original map from Ae by lifting its actual fixed generator image. -/
theorem ideal_projective (hA : IsIdempotented A) (e : Idempotent A) :
    Projective (object.{uA, uM} hA e) := by
  let := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
  constructor
  intro E X f p hp
  have hs := (NondegenerateModuleExactnessConcrete.epi_iff hA p).mp hp
  obtain ⟨y, hy⟩ := restrict_surjective e p.hom hs
    (homEquiv.{uA, uM, max uA uM} e f.hom)
  refine ⟨ObjectProperty.homMk (fromFixed.{uA, uM, max uA uM} e y), ?_⟩
  apply ObjectProperty.hom_ext
  apply (homEquiv.{uA, uM, max uA uM} e).injective
  apply Subtype.ext
  change p.hom.toAddMonoidHom
      (fromFixed.{uA, uM, max uA uM} e y (generator.{uA, uM} e)) =
    f.hom.toAddMonoidHom (generator.{uA, uM} e)
  have hyval := congrArg Subtype.val hy
  change p.hom.toAddMonoidHom y.val =
    f.hom.toAddMonoidHom (generator.{uA, uM} e) at hyval
  change p.hom.toAddMonoidHom ((e : A) • y.val) = _
  have hyfixed : (e : A) • y.val = y.val := y.property
  rw [hyfixed]
  exact hyval

/-- Projectivity is preserved by every specified actual coproduct. -/
theorem cofan_projective {I : Type uI}
    (P : I → NondegenerateModuleCat.{uA, uM} A) (c : Cofan P)
    (hc : IsColimit c) (hP : ∀ i, Projective (P i)) : Projective c.pt := by
  let := hP
  constructor
  intro E X f p hp
  refine ⟨Cofan.IsColimit.desc hc (fun i => Projective.factorThru (c.inj i ≫ f) p), ?_⟩
  apply Cofan.IsColimit.hom_ext hc
  intro i
  rw [← Category.assoc, Cofan.IsColimit.fac, Projective.factorThru_comp]

/-- Choose an actual idempotent fixing each original vector. -/
def chosenIdempotent (M : NondegenerateModuleCat.{uA, max uA uM} A) (m : M.obj) :
    Idempotent A :=
  (M.property m).choose

theorem chosenIdempotent_fixed (M : NondegenerateModuleCat.{uA, max uA uM} A)
    (m : M.obj) : (chosenIdempotent M m : A) • m = m :=
  (M.property m).choose_spec

/-- The source's family of actual ideals, indexed by all original vectors. -/
def presentationFamily (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) :
    M.obj → NondegenerateModuleCat.{uA, max uA uM} A :=
  fun m => object.{uA, uM} hA (chosenIdempotent M m)

/-- The actual finite-support sum of those ideals. -/
def presentationObject (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) :
    NondegenerateModuleCat.{uA, max uA uM} A :=
  NonUnitalModuleDirectSum.object hA (presentationFamily hA M)

/-- On the summand indexed by m, send a e_m to a m. -/
def presentationMap (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) :
    presentationObject hA M ⟶ M :=
  ObjectProperty.homMk (NonUnitalModuleDirectSum.desc
    (fun m : M.obj => (presentationFamily hA M m).obj)
    (fun m => fromFixed.{uA, uM, max uA uM}
      (chosenIdempotent M m) ⟨m, chosenIdempotent_fixed M m⟩))

/-- The singleton generator in the summand indexed by m maps to m itself. -/
theorem presentationMap_surjective (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) :
    Function.Surjective (presentationMap hA M).hom.toAddMonoidHom := by
  intro m
  refine ⟨NonUnitalModuleDirectSum.inclusion (A := A)
    (fun n : M.obj => (presentationFamily hA M n).obj) m
    (generator.{uA, uM} (chosenIdempotent M m)), ?_⟩
  change NonUnitalModuleDirectSum.desc
      (fun n : M.obj => (presentationFamily hA M n).obj)
      (fun n => fromFixed.{uA, uM, max uA uM}
        (chosenIdempotent M n) ⟨n, chosenIdempotent_fixed M n⟩)
      (NonUnitalModuleDirectSum.inclusion (A := A)
        (fun n : M.obj => (presentationFamily hA M n).obj) m
        (generator.{uA, uM} (chosenIdempotent M m))) = m
  exact (NonUnitalModuleDirectSum.desc_inclusion
    (fun n : M.obj => (presentationFamily hA M n).obj)
    (fun n => fromFixed.{uA, uM, max uA uM}
      (chosenIdempotent M n) ⟨n, chosenIdempotent_fixed M n⟩)
    m (generator.{uA, uM} (chosenIdempotent M m))).trans (chosenIdempotent_fixed M m)

theorem presentationObject_projective (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) :
    Projective (presentationObject hA M) :=
  cofan_projective (presentationFamily hA M)
    (NonUnitalModuleDirectSum.cofan hA (presentationFamily hA M))
    (NonUnitalModuleDirectSum.cofanIsColimit hA (presentationFamily hA M))
    (fun m => ideal_projective hA (chosenIdempotent M m))

/-- A concrete categorical projective presentation on the original actions. -/
def presentation (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) : ProjectivePresentation M where
  p := presentationObject hA M
  projective := presentationObject_projective hA M
  f := presentationMap hA M
  epi := (NondegenerateModuleExactnessConcrete.epi_iff hA _).mpr
    (presentationMap_surjective hA M)

/-- The source exact-Hom projectivity assertion for the actual Ae objects. -/
theorem idealProjectivity :
    NonUnitalModuleEnoughProjectives.IdealProjectivityStatement.{uA, uM} := by
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
  intro e
  exact (Langlands.Renard.homProjectiveComparison _).mpr (ideal_projective hA e)

/-- The source exact-Hom projectivity assertion for any existing direct sum. -/
theorem directSumProjectivity :
    NonUnitalModuleEnoughProjectives.DirectSumProjectivityStatement.{uA, uM, uI} := by
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
  intro I P c hc hP
  apply (Langlands.Renard.homProjectiveComparison _).mpr
  exact cofan_projective P c hc (fun i =>
    (Langlands.Renard.homProjectiveComparison _).mp (hP i))

/-- Every object has the displayed actual projective presentation. -/
theorem enoughProjectives :
    NonUnitalModuleEnoughProjectives.EnoughProjectivesStatement.{uA, uM} := by
  intro A _ hA
  exact ⟨fun M => ⟨presentation hA M⟩⟩

/-- The presentation also records surjectivity on the original carrier. -/
theorem surjectiveProjectiveCover :
    NonUnitalModuleEnoughProjectives.SurjectiveProjectiveCoverStatement.{uA, uM} := by
  intro A _ hA
  let := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
  intro M
  refine ⟨presentationObject hA M, presentationMap hA M, ?_, ?_,
    presentationMap_surjective hA M⟩
  · exact (Langlands.Renard.homProjectiveComparison _).mpr
      (presentationObject_projective hA M)
  · exact (NondegenerateModuleExactnessConcrete.epi_iff hA _).mpr
      (presentationMap_surjective hA M)

/-- All four focused assertions in the source enough-projectives proof. -/
theorem projectivityAssertions :
    NonUnitalModuleEnoughProjectives.ProjectivityAssertions.{uA, uM, uI} :=
  ⟨idealProjectivity, directSumProjectivity, enoughProjectives, surjectiveProjectiveCover⟩

example : NonUnitalModuleEnoughProjectives.ProjectivityAssertions.{uA, uM, uI} :=
  projectivityAssertions.{uA, uM, uI}

example : NonUnitalModuleEnoughProjectives.ProjectivityAssertions.{0, 1, 2} :=
  projectivityAssertions.{0, 1, 2}

example : NonUnitalModuleEnoughProjectives.ProjectivityAssertions.{1, 0, 2} :=
  projectivityAssertions.{1, 0, 2}

end Langlands.Algebra.NonUnitalModuleProjectivityProof
