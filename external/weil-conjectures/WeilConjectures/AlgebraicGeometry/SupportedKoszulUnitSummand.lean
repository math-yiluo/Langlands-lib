/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Retract
import WeilConjectures.AlgebraicGeometry.SupportedKoszulRelativeDetector
import WeilConjectures.AlgebraicGeometry.SupportedOpenUnitConeProperties
import WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero

/-! # The supported Koszul summand forces the open unit

Source: Stacks Project, Tag 0A9A.
(blueprint: lem-pc-supported-koszul-unit-summand).
-/

@[expose] public section

set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Adding the supported Koszul summand forces the open-restriction unit to be an
isomorphism under shifted orthogonality. This does not assert detection or use induction.
Source: Stacks Project, Tag 0A9A, supported Koszul construction and unit paragraphs.
(blueprint: lem-pc-supported-koszul-unit-summand).

Proof:
1. Construct a supported Koszul relative detector A on the affine complement. It is
   perfect, has quasi-coherent cohomology supported on T, and restricts to zero on U.
   It detects supported objects which already restrict to zero on U.
2. Set E = Q biproduct A. Homology preserves the biproduct, so E is quasi-coherent.
   The split distinguished triangle gives perfectness by two out of three. Applying
   the additive stalk-homology functor to the biproduct total identity proves support.
   The inclusion and projection exhibit both Q and A as retracts of E.
3. Complete the specified unit of K to a distinguished triangle with cone C. The
   supported open-unit cone lemma gives quasi-coherence, support on T, and zero
   restriction of C to U. Orthogonality to E passes to A through its retract. Since
   A restricts to zero, derived adjunction gives vanishing of maps from its shifts
   into R(K restricted to U). Integer shift equivalence gives vanishing of maps into
   K[1]. Triangle exactness now gives vanishing of all shifted maps from A into C.
4. The relative detector makes C zero. The distinguished-triangle zero-cone criterion
   makes the original, specified unit invertible. No comparison with a different
   right adjoint is required in this combining proof. Empty U, T, or X are allowed. -/
theorem exists_supported_koszul_unit_summand
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : X.Opens) (V : X.affineOpens) (hU : IsCompact (U : Set X))
    (hcover : U ⊔ (V : X.Opens) = ⊤)
    (R : DerivedCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
      schemeDerivedCategory X)
    (adj : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
    (Q : schemeDerivedQCohCategory X) (hQ : Scheme.IsPerfect X Q.obj)
    (hQT : (∀ (n : ℤ) (x : X), x ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj Q.obj).val.presheaf x)))) :
    ∃ E : schemeDerivedQCohCategory X, Scheme.IsPerfect X E.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
      Nonempty (Retract Q.obj E.obj) ∧
      ∀ K : schemeDerivedQCohCategory X,
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
        (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) →
        IsIso (adj.unit.app K.obj) := by
  classical
  obtain ⟨A, hA, hAT, hAU, hdetect⟩ :=
    exists_supported_koszul_relative_detector X T hT hTc U V hU hcover
  let E₀ : schemeDerivedCategory X := Q.obj ⊞ A.obj
  have hE₀ : schemeDerivedQCohProperty X E₀ := by
    intro n
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n
    have : (H.obj Q.obj).IsQuasicoherent := Q.property n
    have : (H.obj A.obj).IsQuasicoherent := A.property n
    have : PreservesBinaryBiproduct Q.obj A.obj H :=
      preservesBinaryBiproduct_of_preservesBinaryProduct H
    have hsum := Scheme.Modules.isQuasicoherent_biprod (H.obj Q.obj) (H.obj A.obj)
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      (H.mapBiprod Q.obj A.obj).symm hsum
  let E : schemeDerivedQCohCategory X := ⟨E₀, hE₀⟩
  have hperfect : Scheme.IsPerfect X E.obj := by
    exact (Scheme.isPerfect_two_out_of_three X
      (Pretriangulated.binaryBiproductTriangle Q.obj A.obj)
      (Pretriangulated.binaryBiproductTriangle_distinguished Q.obj A.obj)).2.2 hQ hA
  have hsupport : ∀ (n : ℤ) (x : X), x ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E.obj).val.presheaf x)) := by
    intro n x hx
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n
    let S := SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.toPresheaf (moduleRings X.toRingedSpace).obj ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    have : H.Additive := inferInstance
    have : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive := inferInstance
    have : S.Additive := by
      dsimp [S]
      infer_instance
    have hQx : IsZero (S.obj (H.obj Q.obj)) := by
      have : Subsingleton (S.obj (H.obj Q.obj)) := hQT n x hx
      exact AddCommGrpCat.isZero_of_subsingleton _
    have hAx : IsZero (S.obj (H.obj A.obj)) := by
      have : Subsingleton (S.obj (H.obj A.obj)) := hAT n x hx
      exact AddCommGrpCat.isZero_of_subsingleton _
    have htotal : 𝟙 (S.obj (H.obj E₀)) = 0 := by
      have h := congrArg (fun f ↦ S.map (H.map f))
        (biprod.total (X := Q.obj) (Y := A.obj))
      simp only [Functor.map_add, Functor.map_comp] at h
      rw [hQx.eq_of_src (S.map (H.map biprod.inl)) 0,
        hAx.eq_of_src (S.map (H.map biprod.inr)) 0, comp_zero, comp_zero, add_zero] at h
      rw [H.map_id, S.map_id] at h
      exact h.symm
    exact AddCommGrpCat.subsingleton_of_isZero ((IsZero.iff_id_eq_zero _).2 htotal)
  let rQ : Retract Q.obj E.obj :=
    { i := biprod.inl, r := biprod.fst, retract := biprod.inl_fst }
  let rA : Retract A.obj E.obj :=
    { i := biprod.inr, r := biprod.snd, retract := biprod.inr_snd }
  refine ⟨E, hperfect, hsupport, ⟨rQ⟩, ?_⟩
  intro K hKT horth
  let L := (SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory
  have horthA (n : ℤ) : Subsingleton (A.obj⟦n⟧ ⟶ K.obj) := by
    let rn := rA.map (shiftFunctor (schemeDerivedCategory X) n)
    refine ⟨fun f g ↦ ?_⟩
    have hfg : rn.r ≫ f = rn.r ≫ g := (horth n).elim _ _
    have h := congrArg (fun k ↦ rn.i ≫ k) hfg
    simpa only [← Category.assoc, rn.retract, Category.id_comp] using h
  obtain ⟨C, g, h, htri⟩ := Pretriangulated.distinguished_cocone_triangle
    (adj.unit.app K.obj)
  let triangle := Pretriangulated.Triangle.mk (adj.unit.app K.obj) g h
  obtain ⟨hqC, hCT, hCU⟩ :=
    supported_open_unit_cone_properties X T hT U hU R adj K hKT C g h htri
  have hB (n : ℤ) : Subsingleton (A.obj⟦n⟧ ⟶ R.obj (L.obj K.obj)) := by
    have hAL : IsZero (L.obj (A.obj⟦n⟧)) :=
      (Functor.map_isZero (shiftFunctor _ n) hAU).of_iso ((L.commShiftIso n).app A.obj)
    have : Subsingleton (L.obj (A.obj⟦n⟧) ⟶ L.obj K.obj) := ⟨hAL.eq_of_src⟩
    exact (adj.homEquiv (A.obj⟦n⟧) (L.obj K.obj)).symm.subsingleton
  have hshift (n : ℤ) : Subsingleton (A.obj⟦n⟧ ⟶ K.obj⟦(1 : ℤ)⟧) := by
    have hs := horthA (n + -1)
    have : Subsingleton (A.obj⟦n⟧⟦(-1 : ℤ)⟧ ⟶ K.obj) := by
      refine ⟨fun f g ↦ ?_⟩
      apply (cancel_epi ((shiftFunctorAdd _ n (-1)).hom.app A.obj)).mp
      exact Subsingleton.elim _ _
    exact @Equiv.subsingleton _ _
      ((shiftEquiv _ (1 : ℤ)).symm.toAdjunction.homEquiv (A.obj⟦n⟧) K.obj).symm this
  have horthC (n : ℤ) : Subsingleton (A.obj⟦n⟧ ⟶ C) := by
    have hz (v : A.obj⟦n⟧ ⟶ C) : v = 0 := by
      obtain ⟨b, hb⟩ := triangle.coyoneda_exact₃ htri v
        (@Subsingleton.elim _ (hshift n) _ 0)
      have hb0 : b = 0 := @Subsingleton.elim _ (hB n) _ 0
      simpa [hb0] using hb
    exact ⟨fun v w ↦ (hz v).trans (hz w).symm⟩
  have hzero : IsZero C := hdetect ⟨C, hqC⟩ hCT hCU horthC
  exact (triangle.isZero₃_iff_isIso₁ htri).mp hzero

end AlgebraicGeometry
