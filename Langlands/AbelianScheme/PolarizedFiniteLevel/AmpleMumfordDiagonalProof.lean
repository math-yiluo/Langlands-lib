import Langlands.AbelianScheme.PolarizedFiniteLevel.AmpleMumfordDiagonalStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleMumfordProof
import Langlands.AlgebraicGeometry.Picard.AmpleTensorProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleProof

/-! # Ampleness from the Poincaré class at the inverse point -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard.LineBundle (isoClass pullbackHom)

private lemma inversion_inversion {S : Scheme.{u}} (A : AbelianScheme S) :
    (𝟙 A.X)⁻¹ ≫ (𝟙 A.X)⁻¹ = 𝟙 A.X := by
  rw [GrpObj.comp_inv, Category.comp_id, inv_inv]

/-- The diagonal bundle of a map with an actual ample Mumford presentation
is ample over the specified one-point base. -/
theorem ampleMumfordDiagonal : AmpleMumfordDiagonalStatement.{u} := by
  intro P S _ A W f hf
  obtain ⟨L, B, evaluationB, M, evaluation, hL, rfl⟩ := hf
  let f := mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation
    P.square W.hasDual
  let inv : A.X ⟶ A.X := (𝟙 A.X)⁻¹
  let pc := familyPointClass P.preservation A (Z := A.X) (poincareFamily A W.hasDual)
  have hunit : pc f (1 : A.X ⟶ A.X) = 1 := by
    have h := familyPointClass_poincareFamily_mul_right P.preservation A W.hasDual
      P.stability f (1 : A.X ⟶ A.X) 1
    rw [one_mul] at h
    exact mul_eq_left.mp h.symm
  have hinv : pc f inv = (pc f (𝟙 A.X))⁻¹ := by
    have h := familyPointClass_poincareFamily_mul_right P.preservation A W.hasDual
      P.stability f (𝟙 A.X) inv
    change pc f ((𝟙 A.X) * (𝟙 A.X)⁻¹) = _ at h
    rw [mul_inv_cancel] at h
    exact eq_inv_of_mul_eq_one_right (h.symm.trans hunit)
  have hconstant : pullbackHom P.preservation (1 : A.X ⟶ A.X).left
      (isoClass P.preservation L) = 1 :=
    LineBundle.pullbackHom_eq_one_of_factor P.preservation A.X.hom (unitSection A)
      (one_left A A.X).symm (isoClass P.preservation L)
  have hm := familyPointClass_mumfordSchemeMap_of_unique P A W L B evaluationB M
    evaluation (𝟙 A.X) inv
  change pc (𝟙 A.X ≫ f) inv = _ at hm
  rw [Category.id_comp] at hm
  change pc f inv = pullbackHom P.preservation ((𝟙 A.X) * (𝟙 A.X)⁻¹).left
    (isoClass P.preservation L) *
      (pullbackHom P.preservation (𝟙 A.X.left) (isoClass P.preservation L))⁻¹ *
      (pullbackHom P.preservation inv.left (isoClass P.preservation L))⁻¹ at hm
  rw [mul_inv_cancel, hconstant, LineBundle.pullbackHom_id, one_mul] at hm
  have hp : pc f (𝟙 A.X) = isoClass P.preservation L *
      pullbackHom P.preservation inv.left (isoClass P.preservation L) := by
    calc
      _ = (pc f inv)⁻¹ := by rw [hinv, inv_inv]
      _ = _ := by rw [hm, mul_inv, inv_inv, inv_inv]
  have hd := isoClass_pullback_poincareDiagonalBundle P.preservation A W.hasDual f (𝟙 A.X)
  rw [Category.id_comp] at hd
  have hc : isoClass P.preservation (poincareDiagonalBundle A W.hasDual f) =
      isoClass P.preservation (LineBundle.tensor P.preservation L
        ((LineBundle.pullback inv.left).obj L)) := by
    calc
      _ = isoClass P.preservation ((LineBundle.pullback (𝟙 A.X.left)).obj
          (poincareDiagonalBundle A W.hasDual f)) :=
        (LineBundle.isoClass_eq_of_iso ((LineBundle.pullbackId A.X.left).app _)).symm
      _ = _ := hd.trans (hp.trans (LineBundle.isoClass_tensor P.preservation _ _).symm)
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp hc
  let : IsIso inv.left :=
    ⟨inv.left, congrArg CommaMorphism.left (inversion_inversion A),
      congrArg CommaMorphism.left (inversion_inversion A)⟩
  have hi : ((LineBundle.pullback inv.left).obj L).IsAmple :=
    closedImmersionPullbackAmple _ _ inv.left L inferInstance hL
  exact ampleTensor _ L ((LineBundle.pullback inv.left).obj L)
    (poincareDiagonalBundle A W.hasDual f) ⟨(ObjectProperty.ι _).mapIso e.symm⟩ hL hi

/-- A field-ample presentation makes the fixed diagonal bundle ample after
some extension of its presentation field. -/
lemma poincareDiagonal_isAmple_after_fieldExtension (P : Prerequisites.{u})
    (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (W : DualWitness A) (f : A.X ⟶ dualScheme A W.hasDual)
    (hf : HasFieldAmpleMumfordPresentation P.preservation P.square P.universality K A
      W.hasDual f) :
    ∃ (K' : Type u) (_ : Field K') (iota : K →+* K'),
      ((LineBundle.pullback
        (CategoryTheory.Limits.pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom iota)))).obj
          (poincareDiagonalBundle A W.hasDual f)).IsAmple := by
  obtain ⟨K', instK', iota, h⟩ := hf
  let : Field K' := instK'
  let b := Spec.map (CommRingCat.ofHom iota)
  have ham := ampleMumfordDiagonal P (Spec (CommRingCat.of K'))
    ((baseChange b).obj A) (W.pullback P b)
    (dualBaseChangeMap A W.hasDual P.universality b f) h
  exact ⟨K', instK', iota, ham.of_iso ((LineBundle.forget _).mapIso
    (poincareDiagonalBaseChangeIso P.universality b A W.hasDual f))⟩

/-- Ampleness of the actual canonical bundle implies ampleness of its actual cube. -/
lemma Datum.cubicBundle_isAmple_of_canonicalBundle {P : Prerequisites.{u}}
    {S : Scheme.{u}} {g d n : ℕ} (a : Datum P S g d n)
    (ha : a.canonicalBundle.IsAmple) : a.cubicBundle.IsAmple :=
  positiveTensorPowerAmple _ a.canonicalBundle a.cubicBundle 3 (by decide) ha ⟨Iso.refl _⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
