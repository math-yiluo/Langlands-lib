import Langlands.GroupScheme.Adjoint.Assembly
import Langlands.GroupScheme.Adjoint.CenterQuotientCenterProof
import Langlands.GroupScheme.Adjoint.CenterQuotientReduction
import Langlands.GroupScheme.Adjoint.InnerAction
import Langlands.GroupScheme.AutomorphicAction.BaseChangeCompatibility
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Supplied relative adjoint quotients and their inner actions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A supplied reductive full-centre fppf quotient over an arbitrary base. -/
structure IsRelativeAdjointQuotient {S : Scheme.{u}} {G A : GroupScheme S}
    (q : G ⟶ A) : Prop where
  isReductive : IsReductive G
  isReductive_target : IsReductive A
  isQuotient : RelativeRoot.IsFppfQuotient (center G) q

namespace IsRelativeAdjointQuotient

variable {S S' : Scheme.{u}} {G A : GroupScheme S} {q : G ⟶ A}
    (hq : IsRelativeAdjointQuotient q)

include hq

/-- The supplied quotient is quasi-compact, even when the base is not affine. -/
theorem quasiCompact : QuasiCompact q.hom.hom.left := by
  let : IsAffineHom G.X.hom := hq.isReductive.isAffineHom
  let : IsAffineHom A.X.hom := hq.isReductive_target.isAffineHom
  have : QuasiCompact (q.hom.hom.left ≫ A.X.hom) := by
    rw [Over.w]
    infer_instance
  exact QuasiCompact.of_comp q.hom.hom.left A.X.hom

/-- Its actual closed kernel represents the entire scheme-theoretic centre. -/
theorem kernelCenter : IsSchemeTheoreticCenter (kernelι q) := by
  let : IsAffineHom A.X.hom := hq.isReductive_target.isAffineHom
  exact isSchemeTheoreticCenter_kernelι_of_range_eq q hq.isQuotient.2.2.2

/-- Conjugation descends to an actual automorphic action of the relative quotient. -/
def innerAction : AutomorphicAction A G := by
  let : QuasiCompact q.hom.hom.left := hq.quasiCompact
  let : Flat q.hom.hom.left := hq.isQuotient.1
  let : Surjective q.hom.hom.left := hq.isQuotient.2.1
  exact (AutomorphicAction.conjugation (𝟙 G)).quotientAction q
    (AutomorphicAction.conjugation_kernelActsTrivially hq.kernelCenter)

/-- Pulling back the quotient action to the original group recovers conjugation. -/
theorem innerAction_restrict :
    hq.innerAction.restrict q = AutomorphicAction.conjugation (𝟙 G) := by
  let : QuasiCompact q.hom.hom.left := hq.quasiCompact
  let : Flat q.hom.hom.left := hq.isQuotient.1
  let : Surjective q.hom.hom.left := hq.isQuotient.2.1
  exact AutomorphicAction.quotientAction_restrict _ _ _

/-- The conjugation restriction determines the relative inner action uniquely. -/
theorem innerAction_unique (a : AutomorphicAction A G)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G)) :
    a = hq.innerAction := by
  let : QuasiCompact q.hom.hom.left := hq.quasiCompact
  let : Flat q.hom.hom.left := hq.isQuotient.1
  let : Surjective q.hom.hom.left := hq.isQuotient.2.1
  exact AutomorphicAction.quotientAction_unique _ _ _ a ha

/-- Every base change is again a reductive full-centre quotient. -/
theorem baseChange (b : S' ⟶ S) :
    IsRelativeAdjointQuotient ((GroupScheme.baseChange b).map q) :=
  ⟨hq.isReductive.baseChange b, hq.isReductive_target.baseChange b,
    hq.isQuotient.baseChange_center b⟩

/-- The relative inner action commutes with every scheme base change. -/
theorem innerAction_baseChange (b : S' ⟶ S) :
    hq.innerAction.baseChange b = (hq.baseChange b).innerAction := by
  apply (hq.baseChange b).innerAction_unique
  rw [← AutomorphicAction.baseChange_restrict, hq.innerAction_restrict,
    AutomorphicAction.baseChange_conjugation, CategoryTheory.Functor.map_id]

/-- At every field-valued point, the actual quotient satisfies the published
field adjoint quotient interface, including both universal properties. -/
theorem fieldQuotient {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsAdjointQuotient ((GroupScheme.baseChange b).map q) := by
  let hG := hq.isReductive.isConnectedReductive_baseChange b
  let hA := hq.isReductive_target.isConnectedReductive_baseChange b
  let hqb := hq.isQuotient.baseChange_center b
  let : Smooth ((GroupScheme.baseChange b).obj A).X.hom := hA.smooth
  have hc := centerQuotientCenterTrivial k
    ((GroupScheme.baseChange b).obj G) ((GroupScheme.baseChange b).obj A)
    ((GroupScheme.baseChange b).map q) hG hA.isAffineHom (by infer_instance) hqb
  exact isAdjointQuotient_of_fppf_kernel_range _
    hG hA hc hqb.1 hqb.2.1 hqb.2.2.1 hqb.2.2.2

/-- The relative action specializes to the published field inner action. -/
theorem innerAction_fieldQuotient {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) :
    hq.innerAction.baseChange b = (hq.fieldQuotient b).innerAction := by
  rw [hq.innerAction_baseChange b]
  rfl

end IsRelativeAdjointQuotient

end Langlands.GroupScheme
