/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
public import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernQSplittingExists
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalRankOneIso
import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists

/-! # Homological criterion for the scalar q splitting
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange
attribute [local irreducible] diagram trace singleUnitIso

private theorem line_epi_end_isIso
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (q : End (line l c X)) [Epi q.asHom] : IsIso q.asHom := by
  let B := condensedRingObj (coefficient l c).X X
  let J := Scheme.ProEt.topology X
  let O := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J B
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
  let S := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J B
  let f := S.functor.map q.asHom
  have : Epi f := inferInstance
  obtain ⟨I, U, v, _, _, hc, _, _, _, hrat, hcl⟩ := spTwists_commonCover X l
  have hU : J.CoversTop U := by
    let hT : IsTerminal (Scheme.ProEt.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    rw [← Sieve.ofArrows_eq_ofObjects hT U v]
    exact Precoverage.generate_mem_toGrothendieck hc
  have he (i : I) : Nonempty ((S.functor.obj (line l c X)).over (U i) ≅
      (SheafOfModules.unit R).over (U i)) := by
    cases c with
    | none =>
      simpa only [B, S, R, O, J, coefficient, line, spSignedTwist,
        WeilConjectures.coefficientTwistLine, WeilConjectures.coefficientTwistPower,
        SheafOfModules.scalarTensorPower] using hcl i
    | some E =>
      simpa only [B, S, R, O, J, coefficient, line, spSignedTwist,
        WeilConjectures.coefficientTwistLine, WeilConjectures.coefficientTwistPower,
        SheafOfModules.scalarTensorPower] using (hrat E i).2
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    obtain ⟨e⟩ := he i
    have := diagonalLocalRankOne_isIso X O (U i) f e e
    change IsIso ((SheafOfModules.toSheaf (R.over (U i))).map (f.over (U i)))
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf R)
  exact isIso_of_reflects_iso q.asHom S.functor

private theorem line_splitMono_isIso
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    {M N : Modules (coefficient l c).X X} (f : M ⟶ N) [IsSplitMono f]
    (e : M ≅ line l c X) (d : N ≅ line l c X) : IsIso f := by
  let q := d.inv ≫ retraction f ≫ e.hom
  have : Epi q := inferInstance
  have : IsIso q := line_epi_end_isIso l c X (.of q)
  have heq : retraction f = d.hom ≫ q ≫ e.inv := by
    simp only [q, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsIso (retraction f) := by rw [heq]; infer_instance
  exact IsIso.of_mono_retraction f

private theorem adj_unit_splitMono
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : D ⥤ E} {R' : E ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') [(L ⋙ L').Full] [(L ⋙ L').Faithful]
    (M : C) : IsSplitMono (a.unit.app M) := by
  let adj := a.comp b
  refine ⟨⟨R.map (b.unit.app _) ≫ inv (adj.unit.app M), ?_⟩⟩
  rw [← Category.assoc, ← Adjunction.comp_unit_app a b M, IsIso.hom_inv_id]

attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

private theorem scalar_q_unit_splitMono
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (T : DerivedCategory (Modules Λ Y))
    (T' : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (e : (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj T ≅ T') :
    IsSplitMono (scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) T T' e) := by
  let a : moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y) ⊣
      moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y) := by
    unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
    exact CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y)
  let b : moduleObjectDerivedPullback Λ (ProjectiveLine.infinity Y) ⊣
      moduleObjectDerivedPushforward Λ (ProjectiveLine.infinity Y) := by
    unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
    exact CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine.infinity Y)
  have : ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)) ⋙
      (moduleObjectDerivedPullback Λ (ProjectiveLine.infinity Y))).Full := by
    unfold moduleObjectDerivedPullback
    let F := (CondensedRing.upperStar Λ (ProjectiveLine Y ↘ Y)).leftDerivedFunctor
    let G := (CondensedRing.upperStar Λ (ProjectiveLine.infinity Y)).leftDerivedFunctor
    let e : F ⋙ G ≅ 𝟭 _ :=
      (CondensedRing.leftDerivedUpperStarComp Λ
        (ProjectiveLine.infinity Y) (ProjectiveLine Y ↘ Y)).symm ≪≫
      eqToIso (congrArg
        (fun f : Y ⟶ Y ↦ (CondensedRing.upperStar Λ f).leftDerivedFunctor)
        ProjectiveLine.infinity_over) ≪≫ CondensedRing.leftDerivedUpperStarId Λ Y
    exact Functor.Full.of_iso e.symm
  have : ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)) ⋙
      (moduleObjectDerivedPullback Λ (ProjectiveLine.infinity Y))).Faithful := by
    unfold moduleObjectDerivedPullback
    let F := (CondensedRing.upperStar Λ (ProjectiveLine Y ↘ Y)).leftDerivedFunctor
    let G := (CondensedRing.upperStar Λ (ProjectiveLine.infinity Y)).leftDerivedFunctor
    let e : F ⋙ G ≅ 𝟭 _ :=
      (CondensedRing.leftDerivedUpperStarComp Λ
        (ProjectiveLine.infinity Y) (ProjectiveLine Y ↘ Y)).symm ≪≫
      eqToIso (congrArg
        (fun f : Y ⟶ Y ↦ (CondensedRing.upperStar Λ f).leftDerivedFunctor)
        ProjectiveLine.infinity_over) ≪≫ CondensedRing.leftDerivedUpperStarId Λ Y
    exact Functor.Faithful.of_iso e.symm
  have : IsSplitMono (a.unit.app T) := adj_unit_splitMono a b T
  have : IsIso ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map e.hom) :=
    Functor.map_isIso _ e.hom
  unfold scalarTwistedUnit
  change IsSplitMono (a.unit.app T ≫
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map e.hom)
  infer_instance

attribute [local irreducible] derivedScalars Functor.mapDerivedCategory RestrictionSquare.mate

private theorem map_desc_isZero
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {V U K : C} (v : V ⟶ K) (b : U ⟶ K)
    [IsIso (biprod.desc v b)] (hV : IsZero (F.obj V)) (hU : IsZero (F.obj U)) :
    IsZero (F.obj K) := by
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hB : IsZero (F.obj (V ⊞ U)) :=
    IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨hV, hU⟩) (F.mapBiprod V U)
  exact IsZero.of_iso hB (F.mapIso (asIso (biprod.desc v b))).symm

private theorem map_desc_right_iso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive]
    {V U K : C} (v : V ⟶ K) (b : U ⟶ K) [IsIso (biprod.desc v b)]
    (hV : IsZero (F.obj V)) : IsIso (F.map b) := by
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have he : (isoZeroBiprod (Y := F.obj U) hV).hom ≫
      (F.mapBiprod V U).inv ≫ F.map (biprod.desc v b) = F.map b := by
    rw [isoZeroBiprod_hom, Functor.mapBiprod_inv, biprod.inr_desc_assoc,
      ← F.map_comp, biprod.inr_desc]
  rw [← he]
  infer_instance

private theorem map_desc_left_iso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive]
    {V U K : C} (v : V ⟶ K) (b : U ⟶ K) [IsIso (biprod.desc v b)]
    (hU : IsZero (F.obj U)) : IsIso (F.map v) := by
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have he : (isoBiprodZero (X := F.obj V) hU).hom ≫
      (F.mapBiprod V U).inv ≫ F.map (biprod.desc v b) = F.map v := by
    rw [isoBiprodZero_hom, Functor.mapBiprod_inv, biprod.inl_desc_assoc,
      ← F.map_comp, biprod.inl_desc]
  rw [← he]
  infer_instance

/-- The componentwise homological data needed by the abstract q biproduct criterion. -/
theorem scalar_q_chern_homology_criterion
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l r.tq.toPresentation a)
    (b : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧))
    (hb : CompletedChernNormalized l r.t₂.toPresentation b) :
    let Λ := (coefficient l c).X
    let T := fun X : Scheme.{u} ↦
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (line l c X)) ⟦(2 : ℤ)⟧
    let uq := scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) (T Y) (T (ProjectiveLine Y))
      (scalarQLineIso l c k p hpl Y)
    let cq := scalarQChern l c Y r a
    let U := unit Λ Y
    let V := T Y
    let K := (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
      (T (ProjectiveLine Y))
    (∀ n : ℤ, n ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (Modules Λ Y) n).obj U)) ∧
      (∀ n : ℤ, n ≠ -2 → IsZero
        ((DerivedCategory.homologyFunctor (Modules Λ Y) n).obj V)) ∧
      (∀ n : ℤ, n ≠ 0 → n ≠ -2 → IsZero
        ((DerivedCategory.homologyFunctor (Modules Λ Y) n).obj K)) ∧
      IsIso ((DerivedCategory.homologyFunctor (Modules Λ Y) 0).map cq) ∧
      IsIso ((DerivedCategory.homologyFunctor (Modules Λ Y) (-2)).map uq) := by
  have _ := ha
  have _ := hb
  let Λ := (coefficient l c).X
  let C := Modules Λ Y
  let U := unit Λ Y
  let V := ((DerivedCategory.singleFunctor C 0).obj
    (line l c Y)) ⟦(2 : ℤ)⟧
  let K := (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)
  let cq := scalarQChern l c Y r a
  let uq := scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) V _
    (scalarQLineIso l c k p hpl Y)
  change (∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor C n).obj U)) ∧
    (∀ n : ℤ, n ≠ -2 → IsZero ((DerivedCategory.homologyFunctor C n).obj V)) ∧
    (∀ n : ℤ, n ≠ 0 → n ≠ -2 → IsZero ((DerivedCategory.homologyFunctor C n).obj K)) ∧
    IsIso ((DerivedCategory.homologyFunctor C 0).map cq) ∧
    IsIso ((DerivedCategory.homologyFunctor C (-2)).map uq)
  have hU (n : ℤ) (hn : n ≠ 0) : IsZero ((DerivedCategory.homologyFunctor C n).obj U) := by
    rcases lt_or_gt_of_ne hn with h | h
    · exact DerivedCategory.isZero_of_isGE U 0 n h
    · exact DerivedCategory.isZero_of_isLE U 0 n h
  have hV (n : ℤ) (hn : n ≠ -2) : IsZero ((DerivedCategory.homologyFunctor C n).obj V) := by
    have : V.IsGE (-2) := DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2)
    have : V.IsLE (-2) := DerivedCategory.TStructure.t.isLE_shift _ 0 2 (-2)
    rcases lt_or_gt_of_ne hn with h | h
    · exact DerivedCategory.isZero_of_isGE V (-2) n h
    · exact DerivedCategory.isZero_of_isLE V (-2) n h
  have hY : IsUnit (l : Γ(Y, ⊤)) := by
    have hl : IsUnit (l : k) :=
      (CharP.isUnit_natCast_iff (Fact.out : p.Prime)).2
        (fun h ↦ hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
          (Fact.out : l.Prime)).1 h))
    simpa only [map_natCast] using
      hl.map ((Y ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  obtain ⟨v, hv⟩ := scalar_q_chern_splitting_exists l c Y hY δ family r a ha
  refine ⟨hU, hV, ?_, ?_, ?_⟩
  · intro n hn₀ hn₂
    exact map_desc_isZero (DerivedCategory.homologyFunctor C n) v cq (hV n hn₂) (hU n hn₀)
  · exact map_desc_right_iso (DerivedCategory.homologyFunctor C 0) v cq
      (hV 0 (by decide))
  · let H := DerivedCategory.homologyFunctor C (-2)
    have : IsIso (H.map v) := map_desc_left_iso H v cq (hU (-2) (by decide))
    let eV : H.obj V ≅ line l c Y :=
      ((DerivedCategory.homologyFunctor C 0).shiftIso (2 : ℤ) (-2) 0 (by decide)).app
        ((DerivedCategory.singleFunctor C 0).obj (line l c Y)) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _
    let eK : H.obj K ≅ line l c Y := (asIso (H.map v)).symm ≪≫ eV
    have : IsSplitMono uq := scalar_q_unit_splitMono Λ Y V _ _
    have : IsSplitMono (H.map uq) := inferInstance
    let : ∀ x : Y, Invertible (l : Y.residueField x) :=
      fun x ↦ (residueIsUnit l k p hpl _ (Y ↘ Spec (.of k)) x).invertible
    exact line_splitMono_isIso l c Y (H.map uq) eV eK

end AlgebraicGeometry.ProEtale.RationalP1
