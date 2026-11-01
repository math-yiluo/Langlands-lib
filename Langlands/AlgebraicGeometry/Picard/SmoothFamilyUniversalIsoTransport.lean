import Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalIsoTransportStatement
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.HomFamilyNaturality
import Langlands.AlgebraicGeometry.Picard.HomPicardZeroPullbackProof

/-! # Transport of actual universal smooth families along an isomorphism -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S : Scheme.{u}} {A A' : AbelianScheme S}

/-- An abelian-scheme isomorphism gives the actual underlying group-scheme isomorphism. -/
def smoothFamilyGroupIso (e : A ≅ A') : A.toGrp ≅ A'.toGrp where
  hom := groupHom e.hom
  inv := groupHom e.inv
  hom_inv_id := congrArg (fun f : A ⟶ A ↦ groupHom f) e.hom_inv_id
  inv_hom_id := congrArg (fun f : A' ⟶ A' ↦ groupHom f) e.inv_hom_id

/-- Pullback along an isomorphism preserves and reflects the actual smooth-family condition. -/
lemma isAlgebraicallyTrivialFamilyViaSmoothFamily_homIso_iff
    (e : A ≅ A') (T : Over S) (L : RigidifiedFamily A' T) :
    IsAlgebraicallyTrivialFamilyViaSmoothFamily A ((homFamilyPullback e.hom T).obj L) ↔
      IsAlgebraicallyTrivialFamilyViaSmoothFamily A' L := by
  let d := smoothFamilyGroupIso ((baseChange T.hom).mapIso e)
  exact (isFibrewiseAlgebraicallyTrivialViaSmoothFamily_iff_of_iso _
    (homFamilyLineBundleIso e.hom T L)).symm.trans
      (isFibrewiseAlgebraicallyTrivialViaSmoothFamily_pullback_groupIso_iff
        ((baseChange T.hom).obj A) ((baseChange T.hom).obj A') d
        (familyLineBundle A' L))

/-- Actual rigidified isomorphism classes correspond by pullback along an isomorphism. -/
def homClassesPullbackIsoEquiv (e : A ≅ A') (T : Over S) :
    RigidifiedClasses A' T ≃ RigidifiedClasses A T where
  toFun := homClassesPullback e.hom T
  invFun := homClassesPullback e.inv T
  left_inv q := by
    rw [← homClassesPullback_comp RigidifiedModule.pullbackCoherence,
      e.inv_hom_id, homClassesPullback_id RigidifiedModule.pullbackCoherence]
  right_inv q := by
    rw [← homClassesPullback_comp RigidifiedModule.pullbackCoherence,
      e.hom_inv_id, homClassesPullback_id RigidifiedModule.pullbackCoherence]

/-- The class correspondence preserves and reflects the descended smooth-family predicate. -/
lemma isAlgebraicallyTrivialClassViaSmoothFamily_homIso_iff
    (e : A ≅ A') (T : Over S) (q : RigidifiedClasses A' T) :
    IsAlgebraicallyTrivialClassViaSmoothFamily A (homClassesPullback e.hom T q) ↔
      IsAlgebraicallyTrivialClassViaSmoothFamily A' q := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact isAlgebraicallyTrivialFamilyViaSmoothFamily_homIso_iff e T L

/-- The actual pullback family has the same unique classifying maps on all
quasi-separated tests, with the original unrestricted parameter scheme. -/
theorem isUniversalSmoothFamilyOnQuasiSeparatedTests_homIso
    (e : A ≅ A') {P : Over S} (L : RigidifiedFamily A' P)
    (hL : IsUniversalSmoothFamilyOnQuasiSeparatedTests A' L) :
    IsUniversalSmoothFamilyOnQuasiSeparatedTests A ((homFamilyPullback e.hom P).obj L) := by
  refine ⟨(isAlgebraicallyTrivialFamilyViaSmoothFamily_homIso_iff e P L).mpr hL.1, ?_⟩
  intro T _ q
  let E := homClassesPullbackIsoEquiv e T
  have hq : IsAlgebraicallyTrivialClassViaSmoothFamily A' (E.symm q.val) :=
    (isAlgebraicallyTrivialClassViaSmoothFamily_homIso_iff e.symm T q.val).mpr q.property
  obtain ⟨g, hg, huniq⟩ := hL.2 T ⟨E.symm q.val, hq⟩
  have classify (h : T ⟶ P) :
      RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
          ((homFamilyPullback e.hom P).obj L) T h =
        E (RigidifiedLineBundle.classifyingMap A'.X.hom (unitSection A')
          (unitSection_comp A') L T h) :=
    homClassesPullback_naturality RigidifiedModule.pullbackCoherence e.hom h
      (RigidifiedLineBundle.classOf A'.X.hom (unitSection A') (unitSection_comp A') L)
  refine ⟨g, ?_, ?_⟩
  · dsimp only
    rw [classify, hg]
    exact E.apply_symm_apply q.val
  · intro k hk
    apply huniq k
    apply E.injective
    rw [← classify, hk]
    exact (E.apply_symm_apply q.val).symm

/-- Universality transports to an isomorphic abelian scheme, retaining the same parameter. -/
theorem isUniversalSmoothFamilyOnQuasiSeparatedTests_transport
    (e : A ≅ A') {P : Over S} (L : RigidifiedFamily A' P)
    (hL : IsUniversalSmoothFamilyOnQuasiSeparatedTests A' L) :
    ∃ L' : RigidifiedFamily A P, IsUniversalSmoothFamilyOnQuasiSeparatedTests A L' :=
  ⟨(homFamilyPullback e.hom P).obj L,
    isUniversalSmoothFamilyOnQuasiSeparatedTests_homIso e L hL⟩

/-- The aggregate transport statement for an actual abelian-scheme isomorphism. -/
theorem smoothFamilyUniversalIsoTransport : SmoothFamilyUniversalIsoTransportStatement.{u} := by
  intro S A A' e P L hL
  exact isUniversalSmoothFamilyOnQuasiSeparatedTests_transport e L hL

end Langlands.AbelianScheme
