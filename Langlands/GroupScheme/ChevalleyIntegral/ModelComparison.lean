import Langlands.GroupScheme.ChevalleyIntegral.FieldCoordinates
import Langlands.GroupScheme.Reductive.CoordinateRootDatumNormalization
import Langlands.GroupScheme.Reductive.ChevalleyIntegralExistenceStatement
import Langlands.GroupScheme.Reductive.SplitExistence
import Langlands.GroupScheme.IntegralModel.PrincipalOpenFibers
import Langlands.GroupScheme.IntegralModel.StrictHenselianModelPinning
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-! # Integral existence from compatible field Chevalley comparisons -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ChevalleyIntegral

open SplitExistence SplitExistence.ChevalleyData

/-- Smoothness can be checked on all supplied field pullbacks of a flat,
locally finitely presented family over an affine base. -/
theorem smooth_of_fieldSmooth {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ (k : Type u) [Field k] [Algebra R k],
      Smooth (pullback.snd f (algebraBaseMap R k))) : Smooth f := by
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro s
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((Spec (CommRingCat.of R)).fromSpecResidueField s)
  let : Algebra R ((Spec (CommRingCat.of R)).residueField s) := φ.hom.toAlgebra
  change Smooth (pullback.snd f ((Spec (CommRingCat.of R)).fromSpecResidueField s))
  rw [← hφ]
  exact h ((Spec (CommRingCat.of R)).residueField s)

section FieldComparisons

variable {R I J : Type u} [CommRing R] [Fintype I] [DecidableEq I]
  {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base} (D : ChevalleyData P b)
  (G : GroupScheme (Spec (CommRingCat.of R)))
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

/-- The single family and its torus have compatible actual identifications with
field Chevalley groups for every supplied field algebra. -/
def HasFieldComparisons : Prop :=
  ∀ (k : Type u) [Field k] [Algebra R k],
    ∃ (H : D.ChevGroup k) (e : (baseChange (algebraBaseMap R k)).obj G ≅ H.H),
      splitTorus.baseChangeHom (K := k) G I i ≫ e.hom = coordinateTorusHom H

variable {D G i} (h : HasFieldComparisons D G i) [Finite J] [P.IsReduced]

include h

/-- Compatible field comparisons give connected reductivity on every actual fibre. -/
theorem HasFieldComparisons.fieldReductive (k : Type u) [Field k] [Algebra R k] :
    IsConnectedReductive ((baseChange (algebraBaseMap R k)).obj G) := by
  obtain ⟨H, e, -⟩ := h k
  exact IsConnectedReductive.of_iso e H.isConnectedReductive

/-- Flatness and finite presentation upgrade the field comparisons to integral
smoothness and the actual reductive predicate. -/
theorem HasFieldComparisons.isReductive [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [IsAffineHom G.X.hom] : IsReductive G := by
  have hsm : Smooth G.X.hom := smooth_of_fieldSmooth G.X.hom fun k _ _ =>
    (h.fieldReductive k).smooth
  exact isReductive_of_fieldReductive G hsm inferInstance fun k _ _ => h.fieldReductive k

/-- The coordinate torus is maximal on every supplied field fibre. -/
theorem HasFieldComparisons.isMaximalTorus (k : Type u) [Field k] [Algebra R k] :
    IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (splitTorus.baseChangeHom (K := k) G I i) := by
  obtain ⟨H, e, he⟩ := h k
  apply (IsMaximalTorus.comp_iso_iff _ e).mp
  rw [he]
  exact isMaximalTorus_coordinateTorusHom H

/-- The same full standard-pairing coordinate datum is the actual root datum of
every supplied field fibre. -/
theorem HasFieldComparisons.isFibrewiseRootDatumOf [IsAffineHom G.X.hom]
    (hpair : ∀ m n, P.toLinearMap m n = ∑ j, m j * n j) :
    IsFibrewiseRootDatumOf I G i P := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro k _ _
  obtain ⟨H, e, he⟩ := h k
  let : IsAffineHom H.H.X.hom := H.affine
  let : IsAffine H.H.X.left := isAffine_of_isAffineHom H.H.X.hom
  let : Smooth H.H.X.hom := H.smooth
  have hroot := isRootDatumOf_coordinateTorusHom H hpair
  rw [← he] at hroot
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    hroot.comp_iso e.symm

end FieldComparisons

/-- It suffices to construct flat finitely presented affine integral families
with closed tori and compatible field Chevalley comparisons. The hypothesis
retains one group and torus before all fields. -/
theorem integralExistence_of_comparisons
    (H : ∀ (I J : Type u) [Fintype I] [DecidableEq I] [Finite J]
      (P : RootDatum J (I → ℤ) (I → ℤ)) [P.IsReduced] (b : P.Base)
      (D : ChevalleyData P b),
      (∀ m n, P.toLinearMap m n = ∑ j, m j * n j) →
      ∃ (G : GroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ))))
        (i : splitTorus (Spec (CommRingCat.of (ULift.{u} ℤ))) I ⟶ G),
        IsAffineHom G.X.hom ∧ Flat G.X.hom ∧ LocallyOfFinitePresentation G.X.hom ∧
          IsClosedSubgroup i ∧ HasFieldComparisons D G i) :
    ChevalleyIntegralExistenceStatement.{u} := by
  classical
  intro J X Y _ _ _ _ P hP
  obtain ⟨I, hI, Q, hPQ, hQ, hpair⟩ := CoordinateRootDatum.exists_equiv_standard P hP
  let := hI
  let := hQ
  obtain ⟨b⟩ := nonempty_base_int Q
  obtain ⟨D⟩ := nonempty_chevalleyLieData Q b
  obtain ⟨G, i, ha, hf, hfp, hic, hcomp⟩ := H I J Q b D.toChevalleyData hpair
  let := ha
  let := hf
  let := hfp
  exact ⟨G, hcomp.isReductive, I, hI, i, Q, hic, hPQ,
    fun k _ _ => hcomp.isMaximalTorus k, hcomp.isFibrewiseRootDatumOf hpair⟩

end Langlands.GroupScheme.ChevalleyIntegral
