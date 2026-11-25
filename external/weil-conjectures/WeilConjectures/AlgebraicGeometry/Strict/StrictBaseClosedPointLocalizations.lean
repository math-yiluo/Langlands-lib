/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationCanonicalMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.FieldTheory.SeparableClosure
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedLift

/-! # Strict localizations above the closed point of a strict-local base change

Source: Stacks Project, Tags 0GIP (case (2)), 0GJS and 0GJU, first paragraph
(blueprint: lem-weil-pbc-strict-base-closed-point-localizations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluation_local
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) [IsLocalRing (strictHenselizationRing y)] :
    IsLocalHom (strictHenselizationRingPointEvaluation y) := by
  let : Algebra (Y.residueField (y (IsLocalRing.closedPoint Ω))) Ω :=
    (descResidueField (stalkClosedPointTo y)).hom.toAlgebra
  let ψ := strictHenselizationPointEvaluationToSep y rfl
  have : IsLocalHom ψ := IsLocalHom.of_surjective ψ
    (strictHenselizationPointEvaluationToSep_surjective y rfl)
  let ι : separableClosure (Y.residueField (y (IsLocalRing.closedPoint Ω))) Ω →+* Ω :=
    (IntermediateField.val _).toRingHom
  have : IsLocalHom ι := inferInstance
  have : IsLocalHom (smallStrictHenselizationColimitIso y).hom.hom := isLocalHom_of_isIso _
  change IsLocalHom ((ι.comp ψ).comp (smallStrictHenselizationColimitIso y).hom.hom)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem structural_weaklyEtale
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) : WeaklyEtale (strictHenselizationStructuralMap y) := by
  obtain ⟨hlocal, hstrict⟩ := AlgebraicGeometry.strictHenselizationLocalStructure y
  let := hlocal
  have := evaluation_local y
  obtain ⟨R, i, hi, hmem, _⟩ := exists_affine_mem_range_and_range_subset
    (x := y (IsLocalRing.closedPoint Ω)) (U := ⊤) (by simp)
  let := hi
  have hclosed : strictHenselizationStructuralMap y
      (IsLocalRing.closedPoint (strictHenselizationRing y)) =
      y (IsLocalRing.closedPoint Ω) := by
    have h := congrArg (fun f : Spec (.of Ω) ⟶ Y ↦ f (IsLocalRing.closedPoint Ω))
      (strictHenselizationClosedLift_over y)
    have heval : Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation y))
        (IsLocalRing.closedPoint Ω) =
        IsLocalRing.closedPoint (strictHenselizationRing y) :=
      IsLocalRing.comap_closedPoint _
    simpa only [Hom.comp_apply, heval] using! h
  have hrange : Set.range (strictHenselizationStructuralMap y) ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map
      (strictHenselizationStructuralMap y).continuous).mem_open
        (IsOpenImmersion.isOpen_range i) (hclosed.symm ▸ hmem)
  let l := IsOpenImmersion.lift i (strictHenselizationStructuralMap y) hrange
  have hl : l ≫ i = strictHenselizationStructuralMap y :=
    IsOpenImmersion.lift_fac i _ hrange
  let α : R ⟶ strictHenselizationRing y := Spec.preimage l
  have hα : Spec.map α = l := Spec.map_preimage l
  have hind : α.hom.IndEtale :=
    smallStrictHenselization_indEtale_of_affine_chart y R i hmem (Iso.refl _)
      α.hom (by
        change Spec.map α ≫ i = 𝟙 _ ≫ strictHenselizationStructuralMap y
        rw [Category.id_comp, hα]
        exact hl)
  have : WeaklyEtale (Spec.map α) := (WeaklyEtale.Spec_iff α).2 hind.weaklyEtale
  rw [← hl, ← hα]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem weaklyEtale_iso_of_closed
    {R B : CommRingCat.{u}} [IsStrictlyHenselianLocalRing R] [IsLocalRing B]
    (f : Spec B ⟶ Spec R) [WeaklyEtale f]
    (hclosed : f (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint R) :
    IsIso f := by
  let α : R ⟶ B := Spec.preimage f
  have hα : Spec.map α = f := Spec.map_preimage f
  let : Algebra R B := α.hom.toAlgebra
  have : IsLocalHom α.hom := (IsLocalRing.isLocalHom_iff_comap_closedPoint α.hom).2
    (by change (Spec.map α) (IsLocalRing.closedPoint B) = _; rw [hα]; exact hclosed)
  have : Algebra.WeaklyEtale R B := (WeaklyEtale.Spec_iff α).1 (hα.symm ▸ ‹WeaklyEtale f›)
  have hbij := Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing (R := R) (S := B)
  have : IsIso α := (ConcreteCategory.isIso_iff_bijective α).2 hbij
  rw [← hα]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluation_closed
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) [IsLocalRing (strictHenselizationRing y)] :
    Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation y))
      (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint (strictHenselizationRing y) := by
  have := evaluation_local y
  exact IsLocalRing.comap_closedPoint _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem structural_closed
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) [IsLocalRing (strictHenselizationRing y)] :
    strictHenselizationStructuralMap y
      (IsLocalRing.closedPoint (strictHenselizationRing y)) =
      y (IsLocalRing.closedPoint Ω) := by
  have h := congrArg (fun f : Spec (.of Ω) ⟶ Y ↦ f (IsLocalRing.closedPoint Ω))
    (strictHenselizationClosedLift_over y)
  simpa only [Hom.comp_apply, evaluation_closed y] using! h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem strict_pointed_weaklyEtale_iso
    {Y Z : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (z : Spec (.of Ω) ⟶ Z)
    (f : strictHenselizationScheme y ⟶ strictHenselizationScheme z) [WeaklyEtale f]
    (hpoint : Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation y)) ≫ f =
      Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation z))) :
    IsIso f := by
  obtain ⟨hy, _⟩ := AlgebraicGeometry.strictHenselizationLocalStructure y
  obtain ⟨hz, hstrict⟩ := AlgebraicGeometry.strictHenselizationLocalStructure z
  let := hy
  let := hz
  have := hstrict
  apply weaklyEtale_iso_of_closed f
  have h := congrArg (fun g : Spec (.of Ω) ⟶ strictHenselizationScheme z ↦
    g (IsLocalRing.closedPoint Ω)) hpoint
  calc
    f (IsLocalRing.closedPoint (strictHenselizationRing y)) =
        f (Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation y))
          (IsLocalRing.closedPoint Ω)) := congrArg f (evaluation_closed y).symm
    _ = Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation z))
        (IsLocalRing.closedPoint Ω) := h
    _ = _ := evaluation_closed z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem strict_pointed_hom_ext
    {B : CommRingCat.{u}} [IsLocalRing B]
    {Ω : Type u} [Field Ω] (β : B →+* Ω) [IsLocalHom β]
    {Y : Scheme.{u}} {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ]
    (y : Spec (.of Ξ) ⟶ Y)
    (f g : Spec B ⟶ strictHenselizationScheme y)
    (hbase : f ≫ strictHenselizationStructuralMap y =
      g ≫ strictHenselizationStructuralMap y)
    (hpoint : Spec.map (CommRingCat.ofHom β) ≫ f =
      Spec.map (CommRingCat.ofHom β) ≫ g) : f = g := by
  let c := fun j : SmallModel.{u} (strictHenselizationNeighbourhoods y) ↦
    (strictHenselizationCone y).π.app (Opposite.op (Opposite.op j)) ≫
      (Spec (Opposite.unop ((equivSmallModel.{u}
        (strictHenselizationNeighbourhoods y)).inverse.obj j).1.left)).isoSpec.inv
  let p := fun j : SmallModel.{u} (strictHenselizationNeighbourhoods y) ↦
    ((AffineEtale.Spec Y).obj ((equivSmallModel.{u}
      (strictHenselizationNeighbourhoods y)).inverse.obj j).1).hom
  have hc (j) : c j ≫ p j = strictHenselizationStructuralMap y := by
    simpa only [c, p, isoSpec_Spec_inv, Category.assoc] using!
      ((exists_strictHenselizationStructuralMap y).choose_spec j)
  obtain ⟨hl⟩ := (strictHenselization_properties y).2.2
  apply hl.hom_ext
  intro j
  apply (cancel_mono (Spec (Opposite.unop ((equivSmallModel.{u}
    (strictHenselizationNeighbourhoods y)).inverse.obj j.unop.unop).1.left)).isoSpec.inv).1
  change f ≫ c j.unop.unop = g ≫ c j.unop.unop
  apply etalePointedMapRigidity β (p j.unop.unop)
  · simpa only [Category.assoc, hc] using! hbase
  · simpa only [Category.assoc] using! congrArg (fun q ↦ q ≫ c j.unop.unop) hpoint

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Strict-local base change preserves strict localizations above its closed point.
Source: Stacks Project, Tags 0GIP (case (2)), 0GJS and 0GJU, first paragraph
(blueprint: lem-weil-pbc-strict-base-closed-point-localizations).

`hcart` allows any presentation of the specified fibre product. The canonical
closed-point lift is `Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation s))`.
The functorial maps `b`, `d`, `q` are specified by their structural equations and their
compatibility with the canonical geometric-point lifts. By strict-henselization
functoriality these are precisely the canonical maps, not arbitrary maps over the base.
Here `b` is the map from the strict localization of the new base to that of the old
base, `d` is the strict-local map induced by `f`, and `q` is induced by `p`.

Proof:
1. The canonical evaluation factors through a surjection onto the relative separable
closure and its embedding into the geometric-point field. It is therefore local, and
its spectrum sends the field point to the closed point of the strict-local ring.
2. Every strict-local structural map is weakly etale. Indeed it factors through an
   affine open containing the image of the closed point; the affine-chart ind-etale
   lemma makes that factor ind-etale, hence weakly etale. Open immersions are etale.
3. Base change makes p weakly etale. The structural equations hb and hq, together with
   cancellation for weakly etale morphisms, make b and q weakly etale. Their pointed
   equations make the corresponding ring maps local. Olivier's theorem for local
   weakly etale maps out of strictly henselian rings makes b and q isomorphisms.
4. The equation hclosed places the new base point at the closed point of the original
   strict-local ring. Its structural map is thus local and weakly etale, so the same
   theorem makes it an isomorphism. Define e as its inverse followed by b.
5. The two maps in the compatibility equation have the same structural and pointed
   composites, by hcart, hb, hd, hq and the corresponding pointed equations. Compose
   with each pointed etale neighbourhood. Etale pointed-map rigidity makes these
   composites equal; the strict-local limit then identifies the two maps themselves.
6. Apply pullback.map to q, the identity on the geometric point, and e.hom. All three
   maps are isomorphisms, so the induced map is an isomorphism. Its two projection
   equations are exactly the equations asserted here. No field algebraicity is used. -/
theorem strictBaseClosedPointLocalizations
    {X S X' : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (p : X' ⟶ X) (f' : X' ⟶ strictHenselizationScheme s)
    (hcart : IsPullback p f' f (strictHenselizationStructuralMap s))
    {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ] (x' : Spec (.of Ξ) ⟶ X')
    (a : Spec (.of Ξ) ⟶ Spec (.of Ω))
    (hclosed : x' ≫ f' =
      a ≫ Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation s)))
    (b : strictHenselizationScheme (x' ≫ f') ⟶
      strictHenselizationScheme ((x' ≫ p) ≫ f))
    (hb : b ≫ strictHenselizationStructuralMap ((x' ≫ p) ≫ f) =
      strictHenselizationStructuralMap (x' ≫ f') ≫ strictHenselizationStructuralMap s)
    (hbpoint : Spec.map (CommRingCat.ofHom
        (strictHenselizationRingPointEvaluation (x' ≫ f'))) ≫ b =
      Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation ((x' ≫ p) ≫ f))))
    (d : strictHenselizationScheme (x' ≫ p) ⟶
      strictHenselizationScheme ((x' ≫ p) ≫ f))
    (hd : d ≫ strictHenselizationStructuralMap ((x' ≫ p) ≫ f) =
      strictHenselizationStructuralMap (x' ≫ p) ≫ f)
    (hdpoint : Spec.map (CommRingCat.ofHom
        (strictHenselizationRingPointEvaluation (x' ≫ p))) ≫ d =
      Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation ((x' ≫ p) ≫ f))))
    (q : strictHenselizationScheme x' ⟶ strictHenselizationScheme (x' ≫ p))
    (hq : q ≫ strictHenselizationStructuralMap (x' ≫ p) =
      strictHenselizationStructuralMap x' ≫ p)
    (hqpoint : Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation x')) ≫ q =
      Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation (x' ≫ p)))) :
    IsIso (strictHenselizationStructuralMap (x' ≫ f')) ∧ IsIso q ∧
      ∃ e : strictHenselizationScheme s ≅ strictHenselizationScheme ((x' ≫ p) ≫ f),
        strictHenselizationStructuralMap (x' ≫ f') ≫ e.hom = b ∧
        q ≫ d = (strictHenselizationStructuralMap x' ≫ f') ≫ e.hom ∧
        ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
          (t : Spec (.of Ω') ⟶ strictHenselizationScheme s),
          ∃ E : pullback (strictHenselizationStructuralMap x' ≫ f') t ≅
              pullback d (t ≫ e.hom),
            E.hom ≫ pullback.fst d (t ≫ e.hom) =
              pullback.fst (strictHenselizationStructuralMap x' ≫ f') t ≫ q ∧
            E.hom ≫ pullback.snd d (t ≫ e.hom) =
              pullback.snd (strictHenselizationStructuralMap x' ≫ f') t := by
  classical
  have hws := structural_weaklyEtale s
  have hwu' := structural_weaklyEtale (x' ≫ f')
  have hwu := structural_weaklyEtale ((x' ≫ p) ≫ f)
  have hwx := structural_weaklyEtale (x' ≫ p)
  have hwx' := structural_weaklyEtale x'
  have hwp : WeaklyEtale p :=
    MorphismProperty.of_isPullback (P := @WeaklyEtale) hcart.flip hws
  have hwqj : WeaklyEtale (q ≫ strictHenselizationStructuralMap (x' ≫ p)) := by
    rw [hq]
    infer_instance
  have hwq : WeaklyEtale q := WeaklyEtale.of_comp q (strictHenselizationStructuralMap (x' ≫ p))
  have hqiso : IsIso q := strict_pointed_weaklyEtale_iso x' (x' ≫ p) q hqpoint
  have hwbj : WeaklyEtale (b ≫ strictHenselizationStructuralMap ((x' ≫ p) ≫ f)) := by
    rw [hb]
    infer_instance
  have hwb : WeaklyEtale b :=
    WeaklyEtale.of_comp b (strictHenselizationStructuralMap ((x' ≫ p) ≫ f))
  have hbiso : IsIso b :=
    strict_pointed_weaklyEtale_iso (x' ≫ f') ((x' ≫ p) ≫ f) b hbpoint
  obtain ⟨hs, hsstrict⟩ := AlgebraicGeometry.strictHenselizationLocalStructure s
  obtain ⟨hu', _⟩ := AlgebraicGeometry.strictHenselizationLocalStructure (x' ≫ f')
  let := hs
  have := hsstrict
  let := hu'
  have hjiso : IsIso (strictHenselizationStructuralMap (x' ≫ f')) := by
    apply weaklyEtale_iso_of_closed
    apply (structural_closed (x' ≫ f')).trans
    have h := congrArg (fun g : Spec (.of Ξ) ⟶ strictHenselizationScheme s ↦
      g (IsLocalRing.closedPoint Ξ)) hclosed
    have ha : a (IsLocalRing.closedPoint Ξ) = IsLocalRing.closedPoint Ω :=
      Subsingleton.elim _ _
    have h' : (x' ≫ f') (IsLocalRing.closedPoint Ξ) =
        Spec.map (CommRingCat.ofHom (strictHenselizationRingPointEvaluation s))
          (IsLocalRing.closedPoint Ω) := by
      simpa only [Hom.comp_apply, ha] using! h
    exact h'.trans (evaluation_closed s)
  let e : strictHenselizationScheme s ≅ strictHenselizationScheme ((x' ≫ p) ≫ f) :=
    (asIso (strictHenselizationStructuralMap (x' ≫ f'))).symm ≪≫ asIso b
  have he : strictHenselizationStructuralMap (x' ≫ f') ≫ e.hom = b := by
    simp [e]
  have hebase : e.hom ≫ strictHenselizationStructuralMap ((x' ≫ p) ≫ f) =
      strictHenselizationStructuralMap s := by
    dsimp [e]
    rw [Category.assoc, hb, IsIso.inv_hom_id_assoc]
  obtain ⟨hx', _⟩ := AlgebraicGeometry.strictHenselizationLocalStructure x'
  let := hx'
  have := evaluation_local x'
  have hcompat : q ≫ d = (strictHenselizationStructuralMap x' ≫ f') ≫ e.hom := by
    apply strict_pointed_hom_ext (strictHenselizationRingPointEvaluation x')
      ((x' ≫ p) ≫ f)
    · simp only [Category.assoc, hd, hebase]
      rw [← Category.assoc q, hq]
      simpa only [Category.assoc] using
        congrArg (fun g ↦ strictHenselizationStructuralMap x' ≫ g) hcart.w
    · calc
        _ = Spec.map (CommRingCat.ofHom
            (strictHenselizationRingPointEvaluation ((x' ≫ p) ≫ f))) := by
          rw [← Category.assoc, hqpoint, hdpoint]
        _ = Spec.map (CommRingCat.ofHom
            (strictHenselizationRingPointEvaluation (x' ≫ f'))) ≫ b := hbpoint.symm
        _ = (x' ≫ f') ≫ e.hom := by
          rw [← he, ← Category.assoc, strictHenselizationClosedLift_over]
        _ = _ := by
          simpa only [Category.assoc] using
            (congrArg (fun g : Spec (.of Ξ) ⟶ X' ↦ g ≫ f' ≫ e.hom)
              (strictHenselizationClosedLift_over x')).symm
  refine ⟨hjiso, hqiso, e, he, hcompat, ?_⟩
  intro Ω' _ _ t
  let m := pullback.map (strictHenselizationStructuralMap x' ≫ f') t
    d (t ≫ e.hom) q (𝟙 _) e.hom hcompat.symm (by simp)
  exact ⟨asIso m, by simp [m], by simp [m]⟩

end AlgebraicGeometry.Scheme
