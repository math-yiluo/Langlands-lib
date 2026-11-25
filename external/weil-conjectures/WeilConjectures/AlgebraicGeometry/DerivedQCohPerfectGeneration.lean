/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectLocalizingClosure
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux
import WeilConjectures.AlgebraicGeometry.SupportedDerivedGeneratedPerfect
import WeilConjectures.AlgebraicGeometry.SupportedPerfectGenerator

/-! # Perfect complexes generate the quasi-coherent derived category

Source: literature/stacks-project/derived-categories-of-schemes.tex, Theorem
perfect-theorem-bondal-van-den-Bergh (blueprint: lem-pc-derived-qcoh-perfect-generation).
-/

@[expose] public section

universe u1 w1

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For every quasi-compact and quasi-separated scheme, the localizing closure of all perfect
complexes is the whole quasi-coherent derived category
Source: Stacks Project, Theorem 09IS (perfect-theorem-bondal-van-den-Bergh),
with Derived Categories, Lemma 09SN (lemma-write-as-colimit).
(blueprint: lem-pc-derived-qcoh-perfect-generation).

Proof:
1. On an affine scheme, the structure sheaf is a perfect generator detecting zero by
   all shifted Hom groups (`lem-pc-perfect-generation-affine-base`, Tags 09IS and 06Z0).
2. For an open cover by a quasi-compact open U and an affine open V, extend a perfect
   generator from U and add a perfect Koszul object supported on V minus U. Their sum
   is perfect and detects zero (`lem-pc-perfect-generation-open-induction-step`).
3. Apply the qcqs open-cover induction principle (`lem-sc-invert-s-cohomology-induction`,
   Tag 08DR) to the property of having a perfect generator, obtaining such a G on X.
4. The category has direct sums (`lem-pc-derived-qcoh-direct-sums`) and G is compact
   (`lem-pc-perfect-object-compact`). The singleton family G generates in the sense of
   `def-pc-generators`. By `lem-pc-compact-generators-build-objects` (Tag 09SN), every Y
   is a homotopy colimit: the first stage and the attaching objects are direct sums of
   shifts of G, successive stages are cones, and Y is the cone of a map between sums
   of the stages. Every stage and then Y lie in the stated closure. Thus it is all
   of the quasi-coherent derived category. -/
theorem derivedQCohPerfectGeneration (X : Scheme.{u1}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w1} (SheafOfModules.{u1} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w1} (SheafOfModules.{u1} ((moduleRings X.toRingedSpace).over U))] :
    perfectLocalizingClosure X = (⊤ : ObjectProperty (schemeDerivedQCohCategory X)) := by
  classical
  let : Zero (schemeDerivedCategory X) := HasZeroObject.zero' (schemeDerivedCategory X)
  have htri : (schemeDerivedQCohProperty X).IsTriangulated := by
    simpa using (supported_perfect_generator X Set.univ isClosed_univ (by simp)).1
  let := htri
  have hqciso : (schemeDerivedQCohProperty X).IsClosedUnderIsomorphisms := by
    constructor
    intro A B e hA n
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u1} (moduleRings X.toRingedSpace)) n).mapIso e) (hA n)
  let := hqciso
  obtain ⟨G, hG, _, hbuild⟩ := supported_derived_generated_perfect X ⊥ (by simp)
  apply top_unique
  intro Y _
  simp only [perfectLocalizingClosure, sInf_apply, iInf_Prop_eq]
  intro ⟨P, hP⟩
  rcases hP with ⟨hperfect, hiso, hshift, hcone, _, hsum⟩
  -- Lift the property to the ambient category so its triangle API applies directly.
  let R : ObjectProperty (schemeDerivedCategory X) :=
    fun A ↦ ∃ hA : schemeDerivedQCohProperty X A, P ⟨A, hA⟩
  have hRiso : R.IsClosedUnderIsomorphisms := by
    constructor
    rintro A B e ⟨hA, hpA⟩
    let hB := (schemeDerivedQCohProperty X).prop_of_iso e hA
    exact ⟨hB, hiso ⟨A, hA⟩ ⟨B, hB⟩ hpA ⟨(schemeDerivedQCohProperty X).isoMk e⟩⟩
  let := hRiso
  have hRshift : R.IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    rintro A ⟨hA, hpA⟩
    let hB := (schemeDerivedQCohProperty X).le_shift n A hA
    exact ⟨hB, hshift ⟨A, hA⟩ n hpA ⟨A⟦n⟧, hB⟩ ⟨Iso.refl _⟩⟩
  let := hRshift
  have hRcone : R.IsTriangulatedClosed₃ := by
    apply ObjectProperty.IsTriangulatedClosed₃.mk'
    rintro T hT ⟨hA, hpA⟩ ⟨hB, hpB⟩
    let hC := (schemeDerivedQCohProperty X).ext_of_isTriangulatedClosed₃ T hT hA hB
    exact ⟨hC, hcone ⟨T.obj₁, hA⟩ ⟨T.obj₂, hB⟩ hpA hpB T hT
      ⟨Iso.refl _⟩ ⟨Iso.refl _⟩ ⟨T.obj₃, hC⟩ ⟨Iso.refl _⟩⟩
  let := hRcone
  have hRG : R G.obj := ⟨G.property, hperfect G hG⟩
  -- The contractible triangle of G supplies zero without a separate perfection lemma.
  have hRzero : R.ContainsZero := by
    refine ⟨0, isZero_zero _, ?_⟩
    exact R.ext_of_isTriangulatedClosed₃ _
      (Pretriangulated.contractible_distinguished G.obj) hRG hRG
  let := hRzero
  have hRtri : R.IsTriangulated :=
    { toContainsZero := hRzero
      toIsStableUnderShift := hRshift
      toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃ }
  let := hRtri
  have hRsum (I : Type u1) (A : I → schemeDerivedCategory X)
      (c : Cofan A) (hc : IsColimit c) (hA : ∀ i, R (A i)) : R c.pt := by
    choose hqc hp using hA
    let hclosed := schemeDerivedQCohClosedUnderCoproducts X I
    let := hclosed
    let hpt := (schemeDerivedQCohProperty X).prop_of_isColimit hc (fun i ↦ hqc i.as)
    have hc' : IsColimit (Cofan.mk c.pt c.inj) :=
      IsColimit.ofIsoColimit hc
        (Cocone.ext (Iso.refl _) (by intro j; cases j; simp; rfl))
    refine ⟨hpt, ?_⟩
    exact hsum I (fun i ↦ ⟨A i, hqc i⟩) c.pt c.inj
      hc' ⟨c.pt, hpt⟩ ⟨Iso.refl _⟩ hp
  obtain ⟨K, t, hzero, hsteps, S, ⟨hS⟩, s, q, r, _, hT⟩ :=
    hbuild Y (by simp)
  -- Rotate each transition triangle: the previous stage and its attaching sum
  -- determine the next stage.
  have hK : ∀ n, R (K n).obj := by
    intro n
    induction n with
    | zero => exact R.prop_of_isZero hzero
    | succ n ih =>
      obtain ⟨I, m, c, ⟨hc⟩, a, b, ht⟩ := hsteps n
      have hC : R c.pt := hRsum I _ c hc (fun i ↦ R.le_shift (m i) _ hRG)
      exact R.ext_of_isTriangulatedClosed₂ _ ht ih hC
  -- Reindex the countable coproduct into Type u1, the closure's indexing universe.
  let S' : Cofan (fun n : ULift.{u1} ℕ ↦ (K n.down).obj) :=
    Cofan.mk S.pt (fun n ↦ S.inj n.down)
  have hS' : IsColimit S' := (Cofan.isColimitEquivOfEquiv Equiv.ulift S) hS
  have hRS : R S.pt := hRsum (ULift.{u1} ℕ) _ S' hS' (fun n ↦ hK n.down)
  exact (R.ext_of_isTriangulatedClosed₃ _ hT hRS hRS).choose_spec

end AlgebraicGeometry
