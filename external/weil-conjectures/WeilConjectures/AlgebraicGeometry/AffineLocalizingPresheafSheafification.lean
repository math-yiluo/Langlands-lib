/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Module.LocalizedModule.Away

import WeilConjectures.AlgebraicGeometry.AffineLocalizingPresheafBasisSheaf
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Sheafification on affine opens of a localizing module presheaf

Source: Stacks Project, Tags 01HV and 009Q, applied to the principal-open basis.
(blueprint: lem-pc-affine-localizing-presheaf-sheafification).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem isIso_unit_on_basis
    (X : TopCat.{u}) (B : Set (TopologicalSpace.Opens X))
    (hB : TopologicalSpace.Opens.IsBasis B) (P : X.Presheaf AddCommGrpCat.{u})
    (hP : CategoryTheory.Presheaf.IsSheaf
      (((Subtype.mono_coe B).functor).inducedTopology
        (_root_.Opens.grothendieckTopology X))
      (((Subtype.mono_coe B).functor).op ⋙ P)) :
    IsIso (Functor.whiskerLeft ((Subtype.mono_coe B).functor).op
      (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology X) P)) := by
  classical
  let G := (Subtype.mono_coe B).functor
  let K := _root_.Opens.grothendieckTopology X
  let J := G.inducedTopology K
  have hGB : TopologicalSpace.Opens.IsBasis (Set.range G.obj) := by
    convert hB using 1
    ext U
    constructor
    · rintro ⟨⟨U, hU⟩, rfl⟩
      exact hU
    · intro hU
      exact ⟨⟨U, hU⟩, rfl⟩
  let : G.IsCoverDense K := (TopCat.Opens.coverDense_iff_isBasis G).2 hGB
  let : G.Full := ⟨fun f ↦ ⟨homOfLE f.le, Subsingleton.elim _ _⟩⟩
  let E := G.sheafInducedTopologyEquivOfIsCoverDense K AddCommGrpCat.{u}
  let PB : CategoryTheory.Sheaf J AddCommGrpCat.{u} := ⟨G.op ⋙ P, hP⟩
  let F := E.functor.obj PB
  let e : G.op ⋙ F.obj ≅ G.op ⋙ P :=
    (CategoryTheory.sheafToPresheaf J AddCommGrpCat).mapIso (E.unitIso.symm.app PB)
  let η := CategoryTheory.toSheafify K P
  let α : P ⟶ F.obj := Functor.IsCoverDense.restrictHomEquivHom e.inv
  have hα : Functor.whiskerLeft G.op α = e.inv :=
    (Functor.IsCoverDense.restrictHomEquivHom (G := G)).symm_apply_apply e.inv
  let β := CategoryTheory.sheafifyLift K α F.property
  have hβ : η ≫ β = α := CategoryTheory.toSheafify_sheafifyLift K α F.property
  let Q : CategoryTheory.Sheaf K AddCommGrpCat.{u} := (presheafToSheaf K _).obj P
  let δ : F.obj ⟶ Q.obj :=
    Functor.IsCoverDense.restrictHomEquivHom (e.hom ≫ Functor.whiskerLeft G.op η)
  have hδ : Functor.whiskerLeft G.op δ = e.hom ≫ Functor.whiskerLeft G.op η :=
    (Functor.IsCoverDense.restrictHomEquivHom (G := G)).symm_apply_apply _
  have hαδ : α ≫ δ = η := by
    apply (Functor.IsCoverDense.restrictHomEquivHom (G := G) (ℱ' := Q)).symm.injective
    change Functor.whiskerLeft G.op (α ≫ δ) = Functor.whiskerLeft G.op η
    rw [Functor.whiskerLeft_comp, hα, hδ, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hβδ : β ≫ δ = 𝟙 Q.obj := by
    apply CategoryTheory.sheafify_hom_ext K _ _ Q.property
    rw [← Category.assoc, hβ, hαδ, Category.comp_id]
  refine ⟨Functor.whiskerLeft G.op β ≫ e.hom, ?_, ?_⟩
  · rw [← Category.assoc, ← Functor.whiskerLeft_comp, hβ, hα, e.inv_hom_id]
  · rw [Category.assoc, ← hδ, ← Functor.whiskerLeft_comp, hβδ]
    rfl

/-- A module presheaf whose principal restrictions on every affine open are
localizations already has the correct sections on affine opens after sheafification.
Source: Stacks Project, Tags 01HV and 009Q.
(blueprint: lem-pc-affine-localizing-presheaf-sheafification).

Proof: Fix an affine W = Spec A and put N = P(W). For each a in A, the hypothesis
identifies P(D(a)) with N[1/a], carrying restriction from W to the numerator map.
For D(c) contained in D(a), naturality of P and uniqueness of the map from a
localization show that its restriction is the standard localization restriction.
Thus on the principal-open basis of W, P agrees with the associated module sheaf
of N (01HV). In particular it satisfies the sheaf condition on that basis,
including the empty cover since localization at zero is zero. The sheaf-on-basis
extension theorem (009Q) extends this agreement uniquely. Restriction of
sheafification to W is the sheaf associated to the restricted presheaf: both
are universal for maps to sheaves and their stalks agree. Since the basis
presheaf is already a sheaf on a basis, its extension agrees with the associated
sheaf, with the canonical unit giving the agreement on basis opens. W itself
is D(1), so the unit on W is bijective and hence an isomorphism of modules.
The argument only uses affine intersections inside W; T need not be separated.
For empty W, a = 0 = 1 forces P(W) = 0, so the same assertion holds. -/
theorem isIso_sheafificationUnit_app_of_affine_localizing
    (T : Scheme.{u}) (P : _root_.PresheafOfModules.{u} T.ringCatSheaf.obj)
    (hP : ∀ (W : T.Opens), IsAffineOpen W → ∀ a : Γ(T, W),
      IsLocalizedModule.Away a (P.map (homOfLE (T.basicOpen_le a)).op).hom)
    (W : T.Opens) (hW : IsAffineOpen W) :
    IsIso (((PresheafOfModules.sheafificationAdjunction
      (𝟙 T.ringCatSheaf.obj)).unit.app P).app (op W)) := by
  have hB := isSheaf_affineBasis_of_localizing T P hP
  have hη := isIso_unit_on_basis T T.affineOpens T.isBasis_affineOpens P.presheaf hB
  let G := (Subtype.mono_coe T.affineOpens).functor
  have hηW : IsIso ((CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology T)
      P.presheaf).app (op W)) :=
    inferInstanceAs (IsIso ((Functor.whiskerLeft G.op
      (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology T) P.presheaf)).app
        (op (⟨W, hW⟩ : T.affineOpens))))
  apply (isIso_iff_of_reflects_iso _
    (forget₂ (ModuleCat (Γ(T, W))) AddCommGrpCat)).mp
  change IsIso ((CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology T)
    P.presheaf).app (op W))
  exact hηW

end AlgebraicGeometry.Scheme.Modules
