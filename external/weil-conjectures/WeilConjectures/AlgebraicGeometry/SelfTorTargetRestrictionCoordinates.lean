/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Modules.Tilde

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

public import WeilConjectures.AlgebraicGeometry.SelfTorAffineSection

public import WeilConjectures.RingTheory.SelfTorRestrictionCertificate

import WeilConjectures.AlgebraicGeometry.SelfTorChosenResolutionCharts
import WeilConjectures.RingTheory.SelfTorRestrictionResolutionIndependence

/-! # Affine Tor coordinates compatible with resolution-induced restriction

Source: Stacks Project, Tags 06YH, 06YG and 00LS.
(blueprint: new-t2-self-tor-target-restriction-coordinates). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrict_homologyπ
    (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B)
    (L : ChainComplex (ModuleCat.{u} B) ℕ) (n : ℕ) :
    (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj L).homologyπ n ≫
      ((L.sc n).mapHomologyIso (ModuleCat.restrictScalars φ)).hom =
    ((L.sc n).mapCyclesIso (ModuleCat.restrictScalars φ)).hom ≫
      (ModuleCat.restrictScalars φ).map (L.homologyπ n) := by
  let S := L.sc n
  let F := ModuleCat.restrictScalars φ
  change (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [(h.map F).homologyπ_comp_homologyIso_hom_assoc]
  change (h.map F).cyclesIso.hom ≫ F.map h.π ≫ F.map h.homologyIso.inv = _
  rw [← F.map_comp, h.π_comp_homologyIso_inv, F.map_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorComparison_cycle_formula
    (A B : Type u) [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (φ : A →+* B) (n : ℕ)
    (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (R : ProjectiveResolution (ModuleCat.of B (B ⧸ J)))
    (k : ((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
        (.down ℕ)).obj P.complex ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
        (((tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex
          (.down ℕ)).obj R.complex)) :
    let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
    let TB := (tensorRight (ModuleCat.of B (B ⧸ J))).mapHomologicalComplex (.down ℕ)
    let e := ((TB.obj R.complex).sc n).mapHomologyIso (ModuleCat.restrictScalars φ)
    let q := fun x ↦
      (R.isoLeftDerivedObj (tensorRight (ModuleCat.of B (B ⧸ J))) n).inv
        (e.hom (HomologicalComplex.homologyMap k n
          ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom x)))
    ∀ (z : (TA.obj P.complex).cycles n) (w : (TB.obj R.complex).cycles n),
      (TB.obj R.complex).iCycles n w = k.f n ((TA.obj P.complex).iCycles n z) →
      (R.isoLeftDerivedObj (tensorRight (ModuleCat.of B (B ⧸ J))) n).hom
        (q ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).inv
          ((TA.obj P.complex).homologyπ n z))) =
        (TB.obj R.complex).homologyπ n w := by
  intro TA TB e q z w hw
  let eP := P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n
  let eR := R.isoLeftDerivedObj (tensorRight (ModuleCat.of B (B ⧸ J))) n
  have hP := congrArg (fun f ↦ f ((TA.obj P.complex).homologyπ n z)) eP.inv_hom_id
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hP
  have hR := congrArg (fun f ↦ f (e.hom (HomologicalComplex.homologyMap k n
    ((TA.obj P.complex).homologyπ n z)))) eR.inv_hom_id
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hR
  change eR.hom (eR.inv (e.hom (HomologicalComplex.homologyMap k n
    (eP.hom (eP.inv ((TA.obj P.complex).homologyπ n z)))))) = _
  rw [hP, hR]
  let zF := HomologicalComplex.cyclesMap k n z
  let ec := ((TB.obj R.complex).sc n).mapCyclesIso (ModuleCat.restrictScalars φ)
  have hπ := congrArg (fun f ↦ f z) (HomologicalComplex.homologyπ_naturality k n)
  simp only [ConcreteCategory.comp_apply] at hπ
  rw [hπ]
  have heπ := congrArg (fun f ↦ f zF) (restrict_homologyπ A B φ (TB.obj R.complex) n)
  simp only [ConcreteCategory.comp_apply] at heπ
  have hec := congrArg (fun f ↦ f zF)
    (((TB.obj R.complex).sc n).mapCyclesIso_hom_iCycles (ModuleCat.restrictScalars φ))
  have hkc := congrArg (fun f ↦ f z) (HomologicalComplex.cyclesMap_i k n)
  simp only [ConcreteCategory.comp_apply] at hec hkc
  have hcw : ec.hom zF = w := by
    apply (ModuleCat.mono_iff_injective ((TB.obj R.complex).iCycles n)).mp inferInstance
    exact hec.trans (hkc.trans hw.symm)
  exact heπ.trans (congrArg ((TB.obj R.complex).homologyπ n) hcw)


/-- The derived-homology coordinates commute with the actual algebraic Tor restriction
on every Tor element, independently of the exterior-conormal comparison.
Source: Stacks Project, Tags 06YH and 06YG (K-flat comparison), 00LS (resolution
comparison), and 01I6 (associated sheaves).
(blueprint: new-t2-self-tor-target-restriction-coordinates).

Proof: For each affine U, resolve A/I by projective A-modules and sheafify its
augmentation using exists_affine_quotient_sheafified_resolution. Projective terms
are summands of free modules, so their associated sheaves are flat. Extend the
chain complex to nonpositive cochain degrees. It is bounded above and K-flat;
its quotient tensor computes the restriction of the fixed derived tensor.
Exact tilde commutes with homology, and the projective-resolution Tor isomorphism
identifies that homology with tilde Tor. The ideal acts trivially on this homology.
Applying tensor pullback therefore gives the required chart isomorphism t_U.
Use the augmentation comparison, rather than an arbitrary chart isomorphism.
For V=D(f), localize the chosen resolution on U and compare it over the quotient
augmentation with the resolution on V. Flat localization preserves its exactness
and projectivity. The resulting tensor chain map induces q. Comparison lifts for
any other pair of resolutions are homotopic, so q has the displayed certificate
for every P,Q. The K-flat augmentation comparisons commute with this map and
restriction, yielding the equation for every homology class x. The tilde unit
sends x to its associated section; naturality of the tensor-pullback unit then
gives exactly the section equation displayed below. All choices are used only
as existential witnesses in this theorem. Degree zero, the empty basic open,
and zero quotient rings are included by the same augmentation construction.

Lean reduction: `exists_selfTor_chosen_resolution_charts` supplies the geometric
comparison for fixed quotient resolutions. The two private helpers construct
the homology map and prove its cycle formula. The proved algebraic theorem
`selfTor_restriction_certificate_of_resolution` then upgrades its explicit
chain comparison to the certificate for every pair of resolutions. -/
theorem exists_selfTor_target_restriction_coordinates
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    let T := fun U : Y.affineOpens ↦
      tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ t : ∀ U : Y.affineOpens,
        ((T U).obj _).over (i ⁻¹ᵁ U.1) ≅ Q.over (i ⁻¹ᵁ U.1),
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
        ∃ q : (((Tor' (ModuleCat.{u} (Γ(Y, U.1) : Type u)) n).obj
            (ModuleCat.of _ ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).obj
            (ModuleCat.of _ ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))) →
          (((Tor' (ModuleCat.{u} (Γ(Y, V.1) : Type u)) n).obj
            (ModuleCat.of _ ((Γ(Y, V.1) : Type u) ⧸ i.ker.ideal V))).obj
            (ModuleCat.of _ ((Γ(Y, V.1) : Type u) ⧸ i.ker.ideal V))),
          IsSelfTorRestrictionMap (Γ(Y, U.1) : Type u) (Γ(Y, V.1) : Type u)
            (i.ker.ideal U) (i.ker.ideal V) (Y.presheaf.map (homOfLE h).op).hom n q ∧
          ∀ x,
            (t U).hom.val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
                (((T U).obj _).val.map (homOfLE (i.preimage_mono h)).op
                  (selfTorAffineSection i U _ x)) =
              (t V).hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
                (selfTorAffineSection i V _ (q x))  := by
  obtain ⟨t, ht⟩ := exists_selfTor_chosen_resolution_charts.{u, w} i n
  refine ⟨t, ?_⟩
  intro V U h hbasic
  obtain ⟨ψ, a, k, hψ, ha, hk, hsections⟩ := ht V U h hbasic
  let A := (Γ(Y, U.1) : Type u)
  let C := (Γ(Y, V.1) : Type u)
  let I := i.ker.ideal U
  let J := i.ker.ideal V
  let φ := (Y.presheaf.map (homOfLE h).op).hom
  let P := projectiveResolution (ModuleCat.of A (A ⧸ I))
  let R := projectiveResolution (ModuleCat.of C (C ⧸ J))
  let TC := (tensorRight (ModuleCat.of C (C ⧸ J))).mapHomologicalComplex (.down ℕ)
  let e := ((TC.obj R.complex).sc n).mapHomologyIso (ModuleCat.restrictScalars φ)
  let q := fun x ↦
    (R.isoLeftDerivedObj (tensorRight (ModuleCat.of C (C ⧸ J))) n).inv
      (e.hom (HomologicalComplex.homologyMap k n
        ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom x)))
  refine ⟨q, ?_, hsections⟩
  apply selfTor_restriction_certificate_of_resolution A C I J φ n q P R
    ψ a k hψ ha hk
  exact tensorComparison_cycle_formula A C I J φ n P R k

end AlgebraicGeometry
