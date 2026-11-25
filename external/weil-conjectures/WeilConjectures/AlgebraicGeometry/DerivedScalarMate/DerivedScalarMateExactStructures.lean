/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateData
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ProEtaleProjectionFirstVariableExact
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateProjectionNormalization
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionGlobalModel
import all WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionGlobalComparison
import all WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact

/-! # Canonical exact structures of the scalar mate

Source: Stacks Project, Tags 03EL, 06YY, 07A4 and 07A6.
(blueprint: lem-sfb-derived-scalar-canonical-exact-structures).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  AlgebraicGeometry.Scheme.ProjectionRestriction.resolving
  AlgebraicGeometry.Scheme.proEtaleFlatRepresentatives
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.DerivedScalarMate

open ProjectionRestriction

private theorem normalized_global {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (t : TensorModel R) [s : TensorShifts t] :
    letI : (Functor.curryObj t.functor).CommShift₂Int := s.shifts
    SheafOfModules.MateCanonicalShiftData (proEtaleOrdinaryTensor W R) DerivedCategory.Q
      t.functor (proEtaleFlatRepresentatives W R)
      (fun P Q hp hq ↦ t.representative.app (⟨P, hp⟩, ⟨Q, hq⟩)) := by
  let : (Functor.curryObj t.functor).CommShift₂Int := s.shifts
  refine ⟨?_, ?_, ?_⟩
  · intro P n hp
    exact (total_tensor_integer_shift_models.{u + 1, u, 0} (ProEt.topology W) R).1 P hp.1 hp.2 n
  · intro P Q hp hq n hpn
    obtain ⟨_, h⟩ := s.first P Q hp hq n
    apply (cancel_mono
      ((shiftFunctor (Der R) n).map (t.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩)))).1
    simp only [Category.assoc, ← Functor.map_comp, Iso.app_hom, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact h
  · intro P Q hp hq n hqn
    obtain ⟨_, h⟩ := s.second P Q hp hq n
    apply (cancel_mono
      ((shiftFunctor (Der R) n).map (t.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩)))).1
    simp only [Category.assoc, ← Functor.map_comp, Iso.app_hom, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact h

private theorem native_shifts {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : ProEtaleTensorModel W R) :
    ∃ s : (Functor.curryObj a.tensor).CommShift₂Int, @CanonicalTensorShifts W R a s := by
  obtain ⟨b, ⟨sb⟩⟩ := tensorModelWithShifts_nonempty R
  let := sb
  let : (Functor.curryObj b.functor).CommShift₂Int := sb.shifts
  obtain ⟨e, he⟩ := tensorModelIso a b
  obtain ⟨s, hL, hR⟩ := SheafOfModules.mateTensorShiftOfIso a.tensor b.functor e
  let := s
  refine ⟨s, ?_⟩
  apply SheafOfModules.mateCanonicalShiftTransport
    (proEtaleOrdinaryTensor W R) DerivedCategory.Q a.tensor b.functor
    (proEtaleFlatRepresentatives W R)
    (fun P Q hp hq ↦ a.representative.app (⟨P, hp⟩, ⟨Q, hq⟩))
    (fun P Q hp hq ↦ b.representative.app (⟨P, hp⟩, ⟨Q, hq⟩)) e
    ?_ hL hR (normalized_global b)
  intro P Q
  have hc := NatTrans.congr_app (congrArg Iso.hom he) (P, Q)
  change e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
    a.representative.inv.app (P, Q) ≫
    b.representative.hom.app (P, Q) at hc
  change a.representative.hom.app (P, Q) ≫ _ = b.representative.hom.app (P, Q)
  rw [hc]
  simp

/-- The restricted scalar functors have compatible canonical exact structures.
Source: Stacks 06YY, 07A4, 0A8D, 0FPT; steps 4--5 of the scalar-mate argument
(blueprint: lem-sfb-derived-scalar-canonical-exact-structures).
Proof: signed totalization and resolving localization supply the canonical tensor
shifts, normalized on flat K-flat representatives. Exact pullback commutes termwise
with shifts; its right adjoint has the unique shift compatible with the geometric
unit and counit. The ordinary tensor symmetry with a coefficient in degree zero has
no shift sign in the first variable, so the representative normalization proves shift
compatibility of the derived tensor identification. Restriction and pullback commute
termwise with shifts. Transposing the shift square of the restriction/direct-image
comparison gives that restriction/pullback square, so adjunction injectivity proves its
shift compatibility. Transport these structures along sourceIso and targetIso.
The derived scalar functors, restriction, and the geometric derived functors are
exact; hence their composites are exact with these transported structures. The
projection first-variable shift equation and the projection normalization identify the
restricted beta shift square with this equation. This proves the asserted CommShift
for the prescribed beta, including all integer coherence. No invertibility of beta
or projection formula is required. -/
theorem scalarMate_canonical_exact_structures
    {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (t : ProEtaleTensorModel T A) (z : ProEtaleTensorModel Z (inverseRing f A)) :
    (∃ (_ : (Functor.curryObj t.tensor).CommShift₂Int)
        (_ : (Functor.curryObj z.tensor).CommShift₂Int)
        (_ : (push f A).CommShift ℤ)
        (_ : ((push f A ⋙ proEtaleRingDerivedExtension a) ⋙
          (restriction a).mapDerivedCategory).CommShift ℤ)
        (_ : ((proEtaleRingDerivedExtension (inverseMap f a) ⋙ push f B) ⋙
          (restriction a).mapDerivedCategory).CommShift ℤ),
      CanonicalTensorShifts t ∧ CanonicalTensorShifts z ∧
      (adjunction f A).CommShift ℤ ∧
      NatTrans.CommShift (sourceIso f a t).hom ℤ ∧
      NatTrans.CommShift (targetIso f a z).hom ℤ ∧
      ((push f A ⋙ proEtaleRingDerivedExtension a) ⋙
        (restriction a).mapDerivedCategory).IsTriangulated ∧
      ((proEtaleRingDerivedExtension (inverseMap f a) ⋙ push f B) ⋙
        (restriction a).mapDerivedCategory).IsTriangulated ∧
      NatTrans.CommShift (Functor.whiskerRight (beta f a)
        (restriction a).mapDerivedCategory) ℤ) := by
  obtain ⟨st, ht⟩ := native_shifts t
  obtain ⟨sz, hz⟩ := native_shifts z
  let := st
  let := sz
  let := (adjunction f A).rightAdjointCommShift ℤ
  let := (adjunction f A).commShift_of_leftAdjoint ℤ
  obtain ⟨hF, hG, pi, hpi, hcomm⟩ := proEtale_projection_first_variable_exact
    f A t z ht hz (DerivedCategory.Q.obj (coefficientComplex a))
  let := hF
  let := hG
  let := hcomm
  let s := sourceIso f a t
  let r := targetIso f a z
  let sF := Functor.CommShift.ofIso s.symm ℤ
  let sG := Functor.CommShift.ofIso r.symm ℤ
  let := sF
  let := sG
  have hs : NatTrans.CommShift s.symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility s.symm ℤ
  have hr : NatTrans.CommShift r.symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility r.symm ℤ
  let := hs
  let := hr
  have hs' : NatTrans.CommShift s.hom ℤ := NatTrans.CommShift.of_iso_inv s.symm ℤ
  have hr' : NatTrans.CommShift r.hom ℤ := NatTrans.CommShift.of_iso_inv r.symm ℤ
  let := hs'
  let := hr'
  have hFt : ((push f A ⋙ proEtaleRingDerivedExtension a) ⋙
      (restriction a).mapDerivedCategory).IsTriangulated :=
    Functor.isTriangulated_of_iso s.symm
  let : ((Functor.curryObj z.tensor).flip.obj
      ((DerivedCategory.Q ⋙ proEtaleRingDerivedPullback f A (inverseRing f A)
        (Iso.refl _)).obj (coefficientComplex a)) ⋙ push f A).IsTriangulated := hG
  have hGt : ((proEtaleRingDerivedExtension (inverseMap f a) ⋙ push f B) ⋙
      (restriction a).mapDerivedCategory).IsTriangulated :=
    Functor.isTriangulated_of_iso r.symm
  have heq : Functor.whiskerRight (beta f a) (restriction a).mapDerivedCategory =
      s.hom ≫ pi ≫ r.inv := by
    ext K
    apply (cancel_epi (s.inv.app K)).1
    apply (cancel_mono (r.hom.app K)).1
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id] using
      (scalarMate_projection_normalization f a t z K).trans (hpi K).symm
  refine ⟨st, sz, inferInstance, sF, sG, ht, hz, inferInstance,
    hs', hr', hFt, hGt, ?_⟩
  rw [heq]
  infer_instance

end AlgebraicGeometry.Scheme.DerivedScalarMate
