/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretrace
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalCompletedChernLift
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernSplittings
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernDegree
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernBaseChange
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Scalar trace base change for the second projective projection
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line diagram trace singleUnitIso
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

private theorem shifted_single_to_single_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] (X Y : C)
    (f : ((DerivedCategory.singleFunctor C 0).obj X) ⟦(2 : ℤ)⟧ ⟶
      (DerivedCategory.singleFunctor C 0).obj Y) : f = 0 := by
  have := DerivedCategory.TStructure.t.isLE_shift
    ((DerivedCategory.singleFunctor C 0).obj X) 0 (2 : ℤ) (-2) (by decide)
  exact DerivedCategory.TStructure.t.zero f (-2) 0 (by decide)

private theorem trace_square_of_generators
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive]
    {A B Z : C} {A' B' Z' : D}
    (u : A ⟶ Z) (c : B ⟶ Z) (u' : A' ⟶ Z') (c' : B' ⟶ Z')
    (a : F.obj A ≅ A') (e : F.obj B ≅ B') (β : F.obj Z ⟶ Z')
    (t : Z ⟶ B) (t' : Z' ⟶ B')
    [IsIso (biprod.desc u c)] [IsIso (biprod.desc u' c')]
    (hu : F.map u ≫ β = a.hom ≫ u') (hc : F.map c ≫ β = e.hom ≫ c')
    (hut : u ≫ t = 0) (hct : c ≫ t = 𝟙 B)
    (hut' : u' ≫ t' = 0) (hct' : c' ≫ t' = 𝟙 B') :
    IsIso β ∧ β ≫ t' = F.map t ≫ e.hom := by
  let : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  let d := biprod.desc (F.map u) (F.map c)
  have hd : d = (F.mapBiprod A B).inv ≫ F.map (biprod.desc u c) :=
    (biprod.mapBiprod_inv_map_desc F A B u c).symm
  have : IsIso d := by rw [hd]; infer_instance
  have hs : d ≫ β = biprod.map a.hom e.hom ≫ biprod.desc u' c' := by
    apply biprod.hom_ext' <;> simp only [d, biprod.inl_desc_assoc,
      biprod.inr_desc_assoc, biprod.inl_map_assoc, biprod.inr_map_assoc,
      biprod.inl_desc, biprod.inr_desc]
    · exact hu
    · exact hc
  have : IsIso (d ≫ β) := by
    rw [hs]
    change IsIso ((biprod.mapIso a e).hom ≫ biprod.desc u' c')
    infer_instance
  refine ⟨IsIso.of_isIso_comp_left d β, ?_⟩
  apply (cancel_epi d).mp
  apply biprod.hom_ext'
  · simp only [d, biprod.inl_desc_assoc]
    rw [reassoc_of% hu, hut', comp_zero,
      ← F.map_comp_assoc, hut, F.map_zero, zero_comp]
  · simp only [d, biprod.inr_desc_assoc]
    rw [reassoc_of% hc, hct', Category.comp_id,
      ← F.map_comp_assoc, hct, F.map_id, Category.id_comp]

/-- The scalar exchange is invertible and carries the normalized second trace to
pullback of the normalized q trace. There is no arbitrary object K or tensor action
in this assertion. -/
theorem second_scalar_trace
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
    (family : Family l Y) (_reference : Reference l Y δ family) :
    IsIso (secondTraceExchange l c k p hpl Y) ∧
      secondTraceExchange l c k p hpl Y ≫
        (secondDiagramPushIso (coefficient l c).X Y (line l c) (diagram l c Y family)).inv.app
          (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
            0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ≫
        (diagram l c Y family).trace₂ ≫
        (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom =
      (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        (trace (coefficient l c).X Y (line l c) (diagram l c Y family) ≫
          (singleUnitIso (coefficient l c).X Y).hom) ≫
        (secondTraceUnitIso (coefficient l c).X Y).hom := by
  have hY : IsUnit (l : Γ(Y, ⊤)) := by
    have hl : IsUnit (l : k) :=
      (CharP.isUnit_natCast_iff (Fact.out : p.Prime)).2
        (fun h ↦ hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
          (Fact.out : l.Prime)).1 h))
    simpa only [map_natCast] using
      hl.map ((Y ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  obtain ⟨a, ha⟩ := DiagonalTrace.diagonalTrace_completedChern_lift l
    _reference.tq.toPresentation hY
  obtain ⟨b, hb⟩ := DiagonalTrace.diagonalTrace_completedChern_lift l
    _reference.t₂.toPresentation hP
  have ha' : CompletedChernNormalized l _reference.tq.toPresentation a := by
    exact ha
  have hb' : CompletedChernNormalized l _reference.t₂.toPresentation b := by
    exact hb
  let Λ := (coefficient l c).X
  let L := line l c
  let d := diagram l c Y family
  let T := fun X : Scheme.{u} ↦
    ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (L X)) ⟦(2 : ℤ)⟧
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let uq := scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) (T Y) (T (ProjectiveLine Y))
    (scalarQLineIso l c k p hpl Y)
  let u₂ := scalarTwistedUnit Λ (secondProjection Y) (T (ProjectiveLine Y))
    (T (diagonalSurface Y)) (secondLineComparison l c k p hpl Y)
  let cq := scalarQChern l c Y _reference a
  let c₂ := scalarP2Chern l c Y _reference b
  let tq := trace Λ Y L d
  let t₂ := (secondDiagramPushIso Λ Y L d).inv.app (T (diagonalSurface Y)) ≫ d.trace₂
  have hs : IsIso (biprod.desc uq cq) ∧ IsIso (biprod.desc u₂ c₂) :=
    scalar_chern_splittings l c k p hpl Y δ family _reference a ha' b hb'
  have hq0 : uq ≫ tq = 0 := shifted_single_to_single_zero _ _ _
  have h₂0 : u₂ ≫ t₂ = 0 := shifted_single_to_single_zero _ _ _
  have hd : cq ≫ tq = 𝟙 _ ∧ c₂ ≫ t₂ = 𝟙 _ :=
    scalar_chern_degree l c Y hY δ family _reference a ha' b hb'
  have hc : F.map uq ≫ secondTraceExchange l c k p hpl Y =
        (scalarQLineIso l c k p hpl Y).hom ≫ u₂ ∧
      F.map cq ≫ secondTraceExchange l c k p hpl Y = (scalarUnitPullIso Λ Y).hom ≫ c₂ :=
    scalar_chern_base_change l c k p hpl Y δ family _reference a ha' b hb'
  have : IsIso (biprod.desc uq cq) := hs.1
  have : IsIso (biprod.desc u₂ c₂) := hs.2
  have : F.Additive := by
    dsimp only [F]
    unfold moduleObjectDerivedPullback
    exact Functor.additive_of_iso
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ (ProjectiveLine Y ↘ Y)).symm
  have ht : IsIso (secondTraceExchange l c k p hpl Y) ∧
      secondTraceExchange l c k p hpl Y ≫ t₂ = F.map tq ≫ (scalarUnitPullIso Λ Y).hom :=
    trace_square_of_generators F uq cq u₂ c₂
      (scalarQLineIso l c k p hpl Y) (scalarUnitPullIso Λ Y)
      (secondTraceExchange l c k p hpl Y) tq t₂ hc.1 hc.2 hq0 hd.1 h₂0 hd.2
  refine ⟨ht.1, ?_⟩
  have ht' := congrArg (fun z ↦ z ≫ (singleUnitIso Λ (ProjectiveLine Y)).hom) ht.2
  simpa only [t₂, F, tq, Λ, L, d, T, scalarUnitPullIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Functor.map_comp] using ht'

end AlgebraicGeometry.ProEtale.RationalP1
