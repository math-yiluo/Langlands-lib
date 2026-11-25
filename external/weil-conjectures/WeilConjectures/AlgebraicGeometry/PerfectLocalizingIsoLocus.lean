/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.CategoryTheory.ShiftSaturatedIsoLocus
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.AlgebraicGeometry.PerfectLocalizingClosure

/-! Application of shift-saturated invertibility to the existing definition of
perfectLocalizingClosure. The proofs of perfect_iso and perfect_shift are
extracted from the private helpers of PerfectTwoOutOfThree.
All other clauses are naturality, coproduct preservation, and the five-term
cone argument from Sheaf.CategoryTheory.ShiftSaturatedIsoLocus.
Source: the defining infimum of perfectLocalizingClosure (Stacks Tag 09IS)
and the bounded strictly-perfect models defining Scheme.IsPerfect.
(blueprint: lem-sc-perfect-localizing-iso-locus). -/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Pretriangulated AlgebraicGeometry
namespace CategoryTheory.ShiftSaturated
/-- Perfection is preserved by isomorphisms.
Proof: compose each local strictly-perfect presentation with the restricted inverse iso.
Source: the definition of Scheme.IsPerfect, Stacks Tag 08C3.
(blueprint: lem-sc-perfect-localizing-iso-locus). -/
theorem perfect_iso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {E F : schemeDerivedCategory X} (e : E ≅ F) (hE : X.IsPerfect E) :
    X.IsPerfect F := by
  intro x
  obtain ⟨U, hx, K, hK, ⟨eK⟩⟩ := hE x
  exact ⟨U, hx, K, hK, ⟨((SheafOfModules.overFunctor.{u}
    (moduleRings X.toRingedSpace) U).mapDerivedCategory.mapIso e.symm) ≪≫ eK⟩⟩

/-- Perfection is preserved by integer shifts.
Proof: translate each local bounded strictly-perfect model; subtract the shift from
both bounds and transport its quotient comparison through the two shift isomorphisms.
Source: the definition of Scheme.IsPerfect, Stacks Tag 08C3.
(blueprint: lem-sc-perfect-localizing-iso-locus). -/
theorem perfect_shift (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {E : schemeDerivedCategory X} (hE : X.IsPerfect E) (n : ℤ) :
    X.IsPerfect (E⟦n⟧) := by
  intro x
  obtain ⟨U, hx, K, ⟨⟨a, b, hb⟩, hf⟩, ⟨eK⟩⟩ := hE x
  refine ⟨U, hx, K⟦n⟧, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨a - n, b - n, fun i hi ↦ ?_⟩
    exact hb (i + n) (by omega)
  · exact fun i ↦ hf (i + n)
  · let F := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    exact ⟨(F.commShiftIso n).app E ≪≫ (shiftFunctor _ n).mapIso eK ≪≫
      ((DerivedCategory.Q.commShiftIso n).app K).symm⟩


/-- The perfect localizing closure lies in the locus of invertibility on all shifts.
Source: perfectLocalizingClosure, Stacks Tag 09IS; five-term triangle exactness.
Proof: use sInf_le with the supplied perfect case. Isomorphisms, shifts and retracts
use naturality. Transport an ambient distinguished triangle into the full D_QCoh
subcategory, then apply the all-shifts five-term cone lemma. Lift the ambient coproduct
cofan and its universal property into D_QCoh, and use the coproduct comparison lemma.
(blueprint: lem-sc-perfect-localizing-iso-locus). -/
theorem perfectClosure_le_isoOnAllShifts
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [(schemeDerivedQCohProperty X).IsTriangulated]
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F G : schemeDerivedQCohCategory X ⥤ D)
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (τ : F ⟶ G)
    (hF : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F)
    (hG : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) G)
    (hperfect : ∀ E : schemeDerivedQCohCategory X,
      Scheme.perfectSubcategory X E.obj → isoOnAllShifts F G τ E) :
    perfectLocalizingClosure X ≤ isoOnAllShifts F G τ := by
  apply sInf_le
  refine ⟨hperfect, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B hA ⟨e⟩
    exact isoOnAllShifts_of_iso F G τ e hA
  · intro A n hA B ⟨e⟩
    let I := (schemeDerivedQCohProperty X).ι
    let e' : B ≅ A⟦n⟧ := (schemeDerivedQCohProperty X).isoMk
      (e ≪≫ ((I.commShiftIso n).app A).symm)
    exact isoOnAllShifts_of_iso F G τ e'.symm (isoOnAllShifts_shift F G τ hA n)
  · intro A B hA hB T hT ⟨eA⟩ ⟨eB⟩ C ⟨eC⟩
    let I := (schemeDerivedQCohProperty X).ι
    let S : Triangle (schemeDerivedQCohCategory X) :=
      Triangle.mk (X := A) (Y := B) (Z := C)
        (ObjectProperty.homMk (eA.inv ≫ T.mor₁ ≫ eB.hom))
        (ObjectProperty.homMk (eB.inv ≫ T.mor₂ ≫ eC.hom))
        (ObjectProperty.homMk (eC.inv ≫ T.mor₃ ≫ eA.hom⟦(1 : ℤ)⟧' ≫
          (I.commShiftIso (1 : ℤ)).inv.app A))
    have e : T ≅ I.mapTriangle.obj S :=
      Triangle.isoMk _ _ eA eB eC
        (by simp [S, I, Functor.mapTriangle, Triangle.mk])
        (by simp [S, I, Functor.mapTriangle, Triangle.mk])
        (by simp [S, I, Functor.mapTriangle, Triangle.mk])
    have hS : S ∈ distinguishedTriangles :=
      Pretriangulated.isomorphic_distinguished T hT _ e.symm
    exact isoOnAllShifts_cone F G τ S hS hA hB
  · intro A B hB ⟨r⟩
    let r' : Retract A B :=
      { i := ObjectProperty.homMk r.i
        r := ObjectProperty.homMk r.r
        retract := ObjectProperty.hom_ext _ r.retract }
    exact isoOnAllShifts_retract F G τ r' hB
  · intro J E S ι hc B ⟨e⟩ hE
    let q : Cofan E := Cofan.mk B (fun j ↦ ObjectProperty.homMk (ι j ≫ e.inv))
    have hq : IsColimit q := by
      refine Cofan.IsColimit.mk q
        (fun s ↦ ObjectProperty.homMk (e.hom ≫
          hc.desc (Cofan.mk s.pt.obj (fun j ↦ (s.inj j).hom)))) ?_ ?_
      · intro s j
        apply ObjectProperty.hom_ext _
        simpa [q, Category.assoc] using hc.fac
          (Cofan.mk s.pt.obj (fun j ↦ (s.inj j).hom)) ⟨j⟩
      · intro s m hm
        apply ObjectProperty.hom_ext _
        apply (cancel_epi e.inv).mp
        change e.inv ≫ m.hom = e.inv ≫ e.hom ≫ _
        rw [Iso.inv_hom_id_assoc]
        apply hc.hom_ext
        intro ⟨j⟩
        simpa [q, Category.assoc] using (congrArg (fun φ ↦ φ.hom) (hm j)).trans
          (hc.fac (Cofan.mk s.pt.obj (fun j ↦ (s.inj j).hom)) ⟨j⟩).symm
    let : PreservesColimitsOfShape (Discrete J) F := hF J
    let : PreservesColimitsOfShape (Discrete J) G := hG J
    exact isoOnAllShifts_coproduct F G τ E q hq hE

end CategoryTheory.ShiftSaturated
