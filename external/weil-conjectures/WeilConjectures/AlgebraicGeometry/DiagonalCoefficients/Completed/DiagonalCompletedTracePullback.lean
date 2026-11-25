/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullbackEndpoints
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedChernHighCoordinate
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalDerivedLineExchangeCoordinate
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRealizedTraceSplitting
import all WeilConjectures.AlgebraicGeometry.RationalP1.DiagonalCompletedChernSplitting

/-! # Geometric inverse image of a normalized completed projective-line trace

Source: the latest blueprint, diagonal coefficient changes, proof paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem triangular_trace
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {A B K A' B' K' : C} (a : A ⟶ K) (b : B ⟶ K)
    (a' : A' ⟶ K') (b' : B' ⟶ K')
    [IsIso (biprod.desc a b)] [IsIso (biprod.desc a' b')]
    (e : K ⟶ K') (dA : A ≅ A') (dB : B ≅ B') (β : B ⟶ A')
    (ha : a ≫ e = dA.hom ≫ a')
    (hb : b ≫ e = β ≫ a' + dB.hom ≫ b')
    (t : K ⟶ B) (t' : K' ⟶ B')
    (hat : a ≫ t = 0) (hbt : b ≫ t = 𝟙 B)
    (hat' : a' ≫ t' = 0) (hbt' : b' ≫ t' = 𝟙 B') :
    IsIso e ∧ t ≫ dB.hom = e ≫ t' := by
  let m : A ⊞ B ⟶ A' ⊞ B' :=
    Biprod.ofComponents dA.hom 0 β dB.hom
  have hm : m = (biprod.mapIso dA dB).hom ≫
      (Biprod.unipotentLower (dB.inv ≫ β)).hom := by
    ext <;> simp [m, Biprod.unipotentLower_hom, Category.assoc]
  have : IsIso m := by rw [hm]; infer_instance
  have he : e = inv (biprod.desc a b) ≫ m ≫ biprod.desc a' b' := by
    apply (cancel_epi (biprod.desc a b)).mp
    simp only [IsIso.hom_inv_id_assoc]
    apply biprod.hom_ext'
    · rw [← Category.assoc biprod.inl (biprod.desc a b),
        ← Category.assoc biprod.inl m, biprod.inl_desc]
      dsimp only [m]
      rw [Biprod.inl_ofComponents]
      simpa only [zero_comp, add_zero, Category.assoc, biprod.inl_desc] using ha
    · rw [← Category.assoc biprod.inr (biprod.desc a b),
        ← Category.assoc biprod.inr m, biprod.inr_desc]
      dsimp only [m]
      rw [Biprod.inr_ofComponents, Preadditive.add_comp]
      simpa only [Category.assoc, biprod.inl_desc, biprod.inr_desc] using hb
  refine ⟨?_, ?_⟩
  · rw [he]
    infer_instance
  · apply (cancel_epi (biprod.desc a b)).mp
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc]
      rw [← Category.assoc a t, hat, zero_comp, ← Category.assoc a e, ha]
      simp only [Category.assoc, hat', comp_zero]
    · simp only [biprod.inr_desc_assoc]
      rw [← Category.assoc b t, hbt, Category.id_comp, ← Category.assoc b e, hb]
      simp only [Preadditive.add_comp, Category.assoc, hat', hbt', comp_zero,
        Category.comp_id, zero_add]

private theorem splitting_coordinates
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {A B K : C} (a : A ⟶ K) (b : B ⟶ K) [IsIso (biprod.desc a b)]
    (t : K ⟶ B) (ha : a ≫ t = 0) (hb : b ≫ t = 𝟙 B)
    {W : C} (k : W ⟶ K) :
    k = (k ≫ inv (biprod.desc a b) ≫ biprod.fst) ≫ a + (k ≫ t) ≫ b := by
  have ht : inv (biprod.desc a b) ≫ biprod.snd = t := by
    apply (cancel_epi (biprod.desc a b)).mp
    simp only [IsIso.hom_inv_id_assoc]
    apply biprod.hom_ext'
    · simpa only [biprod.inl_snd, biprod.inl_desc_assoc] using ha.symm
    · simpa only [biprod.inr_snd, biprod.inr_desc_assoc] using hb.symm
  rw [← ht]
  calc
    _ = k ≫ inv (biprod.desc a b) ≫ biprod.desc a b := by
      simp only [IsIso.inv_hom_id, Category.comp_id]
    _ = _ := by
      simpa only [Preadditive.comp_add, Category.assoc] using
        congrArg (fun z ↦ k ≫ inv (biprod.desc a b) ≫ z)
          (biprod.desc_eq (f := a) (g := b))

private theorem trace_of_diagonal_components
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {A B K A' B' K' : C} (a : A ⟶ K) (b : B ⟶ K)
    (a' : A' ⟶ K') (b' : B' ⟶ K')
    [IsIso (biprod.desc a b)] [IsIso (biprod.desc a' b')]
    (e : K ⟶ K') (dB : B ≅ B')
    (t : K ⟶ B) (t' : K' ⟶ B')
    (hat : a ≫ t = 0) (hbt : b ≫ t = 𝟙 B)
    (hat' : a' ≫ t' = 0) (hbt' : b' ≫ t' = 𝟙 B')
    (hzero : a ≫ e ≫ t' = 0)
    (hlow : IsIso (a ≫ e ≫ inv (biprod.desc a' b') ≫ biprod.fst))
    (hhigh : b ≫ e ≫ t' = dB.hom) :
    IsIso e ∧ t ≫ dB.hom = e ≫ t' := by
  let dA := asIso (a ≫ e ≫ inv (biprod.desc a' b') ≫ biprod.fst)
  let β := b ≫ e ≫ inv (biprod.desc a' b') ≫ biprod.fst
  apply triangular_trace a b a' b' e dA dB β ?_ ?_ t t' hat hbt hat' hbt'
  · simpa only [Category.assoc, hzero, zero_comp, add_zero, dA, asIso_hom] using
      splitting_coordinates a' b' t' hat' hbt' (a ≫ e)
  · simpa only [Category.assoc, hhigh, β] using
      splitting_coordinates a' b' t' hat' hbt' (b ≫ e)

private theorem trace_of_mapped_diagonal_components
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive]
    {A B K : C} {A' B' K' : D} (a : A ⟶ K) (b : B ⟶ K)
    (a' : A' ⟶ K') (b' : B' ⟶ K')
    [IsIso (biprod.desc a b)] [IsIso (biprod.desc a' b')]
    (e : F.obj K ⟶ K') (dB : F.obj B ≅ B') (t : K ⟶ B) (t' : K' ⟶ B')
    (hat : a ≫ t = 0) (hbt : b ≫ t = 𝟙 B)
    (hat' : a' ≫ t' = 0) (hbt' : b' ≫ t' = 𝟙 B')
    (hzero : F.map a ≫ e ≫ t' = 0)
    (hlow : IsIso (F.map a ≫ e ≫ inv (biprod.desc a' b') ≫ biprod.fst))
    (hhigh : F.map b ≫ e ≫ t' = dB.hom) :
    IsIso e ∧ F.map t ≫ dB.hom = e ≫ t' := by
  have : IsIso (biprod.desc (F.map a) (F.map b)) := by
    simpa only [Iso.refl_inv, Iso.refl_hom, Functor.map_id, Category.id_comp,
      Category.comp_id] using
      RationalP1.map_split F a b (Iso.refl _) (Iso.refl _) (Iso.refl _)
  have ha : F.map a ≫ F.map t = 0 := by rw [← F.map_comp, hat, F.map_zero]
  have hb : F.map b ≫ F.map t = 𝟙 _ := by rw [← F.map_comp, hbt, F.map_id]
  exact trace_of_diagonal_components (F.map a) (F.map b) a' b' e dB
    (F.map t) t' ha hb hat' hbt' hzero hlow hhigh

-- Cancel an invertible endpoint comparison while the splitting maps are still abstract.
private theorem trace_of_mapped_diagonal_components_factor
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive]
    {A B K : C} {A' B' K' L : D} (a : A ⟶ K) (b : B ⟶ K)
    (a' : A' ⟶ K') (b' : B' ⟶ K')
    [IsIso (biprod.desc a b)] [IsIso (biprod.desc a' b')]
    (e : F.obj K ⟶ L) (q : L ⟶ K') [IsIso q] (dB : F.obj B ≅ B')
    (t : K ⟶ B) (t' : K' ⟶ B')
    (hat : a ≫ t = 0) (hbt : b ≫ t = 𝟙 B)
    (hat' : a' ≫ t' = 0) (hbt' : b' ≫ t' = 𝟙 B')
    (hzero : F.map a ≫ (e ≫ q) ≫ t' = 0)
    (hlow : IsIso (F.map a ≫ (e ≫ q) ≫ inv (biprod.desc a' b') ≫ biprod.fst))
    (hhigh : F.map b ≫ (e ≫ q) ≫ t' = dB.hom) :
    IsIso e ∧ F.map t ≫ dB.hom = e ≫ q ≫ t' := by
  have htrace := trace_of_mapped_diagonal_components F a b a' b' (e ≫ q) dB t t'
    hat hbt hat' hbt' hzero hlow hhigh
  have : IsIso (e ≫ q) := htrace.1
  refine ⟨IsIso.of_isIso_comp_right e q, ?_⟩
  simpa only [Category.assoc] using htrace.2

/-- The canonical realization of the shifted positive line is an isomorphism.
Source: the exact realization's single and shift comparisons
(blueprint: lem-diagonal-completed-trace-pullback).
Proof: each of the three factors in shiftedLine is the image of an isomorphism. -/
theorem completedRealization_shiftedLine_isIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [DiagonalTraceLocalizations l X] (e : CompletedRealization l X) :
    IsIso (e.shiftedLine l X) := by
  unfold CompletedRealization.shiftedLine
  infer_instance

attribute [local instance] completedRealization_shiftedLine_isIso

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  CondensedRing.upperStar CondensedRing.lowerStar
  CompletedRealization.singleUnit CompletedRealization.shiftedLine
  modelExchange TracePullback

-- Use global invertibility in the coordinate criterion before specializing the splitting maps.
private theorem completedTrace_lowCoordinate (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (hunit : IsUnit (l : Γ(S, ⊤))) (hunit' : IsUnit (l : Γ(S', ⊤)))
    (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) (s' : S' ⟶ X') (hs' : s' ≫ f' = 𝟙 S')
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (D' : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f'))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (canonical' : D'.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f')
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hX
      (zlLine l X) (zlLine l X') (spIntegralComparison hX l (bottomField l)))
    (v : diagonalShiftedIntegralLine l S ⟶ D.R.obj (diagonalShiftedIntegralLine l X))
    (b : unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S ⟶
      D.R.obj (diagonalShiftedIntegralLine l X))
    (v' : diagonalShiftedIntegralLine l S' ⟶ D'.R.obj (diagonalShiftedIntegralLine l X'))
    (b' : unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S' ⟶
      D'.R.obj (diagonalShiftedIntegralLine l X'))
    [IsIso (biprod.desc v b)] [IsIso (biprod.desc v' b')]
    (τ : D.R.obj (diagonalShiftedIntegralLine l X) ⟶
      unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S)
    (τ' : D'.R.obj (diagonalShiftedIntegralLine l X') ⟶
      unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S')
    (hv : v ≫ τ = 0) (hb : b ≫ τ = 𝟙 _)
    (hv' : v' ≫ τ' = 0) (hb' : b' ≫ τ' = 𝟙 _) :
    IsIso ((derivedUpper _ hS).map v ≫
      modelExchange _ f f' hX hS h D D' canonical canonical' (diagonalShiftedIntegralLine l X) ≫
      D'.R.map line.shift ≫ inv (biprod.desc v' b') ≫ biprod.fst) := by
  let residue (T : Scheme.{u}) (hu : IsUnit (l : Γ(T, ⊤))) :
      ∀ x : T, Invertible (l : T.residueField x) := fun x ↦
    (show IsUnit (l : T.residueField x) from by
      let ψ := (T.residue x).hom.comp (T.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hu.map ψ).invertible
  let instS := residue S hunit
  let instS' := residue S' hunit'
  let instX := residue X (by simpa only [map_natCast] using hunit.map f.appTop.hom)
  let instX' := residue X' (by simpa only [map_natCast] using hunit'.map f'.appTop.hom)
  exact @diagonalDerivedLineExchange_coordinate l ‹Fact l.Prime› X S X' S'
    instX instS instX' instS' f f' hX hS h s hs s' hs'
    D D' canonical canonical' line v b v' b' ‹_› ‹_› τ τ' hv hb hv' hb'

-- Compare the independently normalized derived functor endpoints.
/-- Pullback of one completed projective-line trace, expressed in its normalized
condensed realization. This is a trace-only assertion for a Cartesian square of
arbitrary projective-line models; no diagonal class or coefficient family occurs.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3),
the base-changed unit/Chern decomposition and passage to its trace.
(blueprint: lem-diagonal-completed-trace-pullback).

Proof: form the unit/Chern decomposition for the two projective-line models as a
single morphism of strict Kummer systems. On the Cartesian square, the unit is
natural and the section class pulls back to the positive section class. If the
chosen models differ by a projective-line automorphism, the hyperplane classes
differ by a class from the base; this changes only the first summand and is killed
by the trace projection. Thus the twisted splitting square commutes after its
canonical coefficient identifications. Apply the normalized inverse-image/derived-
limit comparison to the entire splitting. Cartesian coefficients identify its
endpoints, so this comparison and the splitting are invertible. Consequently the
derived direct-image mate is invertible on the shifted positive line. Invert the
commuting splitting square and project to its constant summand to get the trace
square. The construction equations in t and t' identify these as the completed
traces. Transport by the four completed realizations and the two normalized
push squares. Their full universal-unit equations hcanonical and hcanonical'
identify the transported direct-image mate with modelExchange, rather than an
arbitrarily rescaled comparison. The displayed inverse factors just solve each
CompletedTraceCompatibility equation for its condensed trace. This argument
applies to q and to either projective model of a product projection. -/
theorem diagonalCompletedTrace_pullback (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian X'] [IsNoetherian S']
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (square : IsPullback hX f' f hS)
    (hunit : IsUnit (l : Γ(S, ⊤))) (hunit' : IsUnit (l : Γ(S', ⊤)))
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (eX' : CompletedRealization l X') (eS' : CompletedRealization l S')
    (t : DiagonalTrace.Result l (ULift.{u} (Padic l)) f)
    (t' : DiagonalTrace.Result l (ULift.{u} (Padic l)) f')
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (D' : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f'))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (canonical' : D'.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f')
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) D canonical)
    (hcanonical' : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f') D' canonical')
    (push : CompletedPushSquare l f eX eS t.Rc D)
    (push' : CompletedPushSquare l f' eX' eS' t'.Rc D')
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hX
      (zlLine l X) (zlLine l X') (spIntegralComparison hX l (bottomField l)))
    (c : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hS) :
    let trace := inv (D.R.map (eX.shiftedLine l X)) ≫
      push.derived.iso.inv.app _ ≫ eS.F.mapDerivedCategory.map t.trace ≫ eS.singleUnit l S
    let trace' := inv (D'.R.map (eX'.shiftedLine l X')) ≫
      push'.derived.iso.inv.app _ ≫ eS'.F.mapDerivedCategory.map t'.trace ≫ eS'.singleUnit l S'
    TracePullback (Profinite.continuousMapRingObj.{u} ℤ_[l]) f f' hX hS square.w.symm
      D D' canonical canonical' line c trace trace' := by
  let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
  let V (T : Scheme.{u}) := ((DerivedCategory.singleFunctor (Modules Λ T) 0).obj
    (zlLine l T))⟦(2 : ℤ)⟧
  let F := derivedUpper Λ hS
  let τ := inv (D.R.map (eX.shiftedLine l X)) ≫
    push.derived.iso.inv.app _ ≫ eS.F.mapDerivedCategory.map t.trace ≫ eS.singleUnit l S
  let τ' := inv (D'.R.map (eX'.shiftedLine l X')) ≫
    push'.derived.iso.inv.app _ ≫ eS'.F.mapDerivedCategory.map t'.trace ≫ eS'.singleUnit l S'
  let E₀ := modelExchange Λ f f' hX hS square.w.symm D D' canonical canonical' (V X)
  let E := E₀ ≫ D'.R.map line.shift
  obtain ⟨b, hb⟩ := DiagonalTrace.diagonalTrace_completedChern_lift l t.toPresentation hunit
  obtain ⟨b', hb'⟩ := DiagonalTrace.diagonalTrace_completedChern_lift l t'.toPresentation hunit'
  let B := RationalP1.realizeScalarChern l f eX eS t.Rc D push b
  let B' := RationalP1.realizeScalarChern l f' eX' eS' t'.Rc D' push' b'
  obtain ⟨v, hv, hvt, hBt⟩ := realizedTrace_splitting l f hunit eX eS t D push b hb
  obtain ⟨v', hv', hvt', hBt'⟩ :=
    realizedTrace_splitting l f' hunit' eX' eS' t' D' push' b' hb'
  have : F.Additive :=
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ hS).left_adjoint_additive
  have : IsIso c.derived := by unfold PullEndpoint.derived; infer_instance
  have hzero : F.map v ≫ E ≫ τ' = 0 := by
    let i : F.obj (V S) ≅
        ((DerivedCategory.singleFunctor (Modules Λ S') 0).obj
          ((CondensedRing.upperStar Λ hS).obj (zlLine l S)))⟦(2 : ℤ)⟧ :=
      ((derivedUpper Λ hS).commShiftIso (2 : ℤ)).app _ ≪≫
        (shiftFunctor _ (2 : ℤ)).mapIso (singlePullback Λ hS (zlLine l S))
    have : (((DerivedCategory.singleFunctor (Modules Λ S') 0).obj
        ((CondensedRing.upperStar Λ hS).obj (zlLine l S)))⟦(2 : ℤ)⟧).IsLE (-2) :=
      DerivedCategory.TStructure.t.isLE_shift _ 0 2 (-2) (by decide)
    have : (F.obj (V S)).IsLE (-2) :=
      DerivedCategory.TStructure.t.isLE_of_iso i.symm (-2)
    exact DerivedCategory.TStructure.t.zero _ (-2) 0 (by decide)
  have hlow : IsIso (F.map v ≫ E ≫ inv (biprod.desc v' B') ≫ biprod.fst) := by
    let s := ProjectiveLine.infinity S ≫ t.model.model.inv
    let s' := ProjectiveLine.infinity S' ≫ t'.model.model.inv
    have hs : s ≫ f = 𝟙 S := by
      rw [← t.model.over_eq]
      simp only [s, Category.assoc, Iso.inv_hom_id_assoc, ProjectiveLine.infinity_over]
    have hs' : s' ≫ f' = 𝟙 S' := by
      rw [← t'.model.over_eq]
      simp only [s', Category.assoc, Iso.inv_hom_id_assoc, ProjectiveLine.infinity_over]
    simpa only [E, E₀, Category.assoc] using
      completedTrace_lowCoordinate l f f' hX hS square.w.symm hunit hunit' s hs s' hs'
        D D' canonical canonical' line v B v' B' τ τ' hvt hBt hvt' hBt'
  have hhigh : F.map B ≫ E ≫ τ' = c.derived := by
    simpa only [E, E₀, Category.assoc] using
      diagonalCompletedChern_highCoordinate l f f' hX hS square hunit hunit'
        eX eS eX' eS' t.toPresentation t'.toPresentation D D' canonical canonical'
        hcanonical hcanonical' push push' line c b hb b' hb' τ' hBt'
  have : IsIso line.shift := by unfold PullEndpoint.shift PullEndpoint.derived; infer_instance
  unfold TracePullback
  exact trace_of_mapped_diagonal_components_factor F v B v' B'
    E₀ (D'.R.map line.shift) (asIso c.derived) τ τ'
    hvt hBt hvt' hBt' hzero hlow hhigh

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
