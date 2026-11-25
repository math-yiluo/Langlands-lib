/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local irreducible] ordinaryFinitePullback ordinaryFinitePushforward ordinaryFiniteTensor

private theorem inverse_biprod_projection_square
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasBinaryBiproducts C]
    [HasBinaryBiproducts D] (F : C ⥤ D) {L U V : C} {L' U' V' : D}
    (b : L ⊞ U ≅ V) (b' : L' ⊞ U' ≅ V')
    (e : F.obj V ⟶ V') (s : F.obj (L ⊞ U) ⟶ L' ⊞ U') (v : F.obj U ⟶ U')
    (hs : F.map b.hom ≫ e = s ≫ b'.hom)
    (hv : s ≫ biprod.snd = F.map biprod.snd ≫ v) :
    F.map (b.inv ≫ biprod.snd) ≫ v = e ≫ b'.inv ≫ biprod.snd := by
  apply (cancel_epi (F.map b.hom)).1
  calc
    F.map b.hom ≫ (F.map (b.inv ≫ biprod.snd) ≫ v) =
        F.map biprod.snd ≫ v := by
      rw [← Category.assoc, ← F.map_comp, Iso.hom_inv_id_assoc]
    _ = s ≫ biprod.snd := hv.symm
    _ = F.map b.hom ≫ (e ≫ b'.inv ≫ biprod.snd) := by
      rw [← Category.assoc, hs]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem biprod_trace_components
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y Z : C} [HasBinaryBiproduct X Y]
    (b : X ⊞ Y ≅ Z) (v : X ⟶ Z) (w : Y ⟶ Z)
    (hb : b.hom = biprod.desc v w) :
    (v ≫ (b.inv ≫ biprod.snd) = 0) ∧
      (w ≫ (b.inv ≫ biprod.snd) = 𝟙 Y) := by
  have hv : biprod.inl ≫ b.hom = v := by rw [hb, biprod.inl_desc]
  have hw : biprod.inr ≫ b.hom = w := by rw [hb, biprod.inr_desc]
  constructor
  · rw [← hv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, biprod.inl_snd]
  · rw [← hw]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, biprod.inr_snd]

section TraceSquare

variable (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
  (t : OrdinaryFiniteTwistTransport A N hA) (c : OrdinaryFiniteP1ChernFamily A N hA)
  (b : ∀ (S : Scheme.{u}) [IsNoetherian S] (_hS : IsUnit (N : Γ(S, ⊤))),
    ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
  (hb : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
    (b S hS).hom = ordinaryFiniteP1KummerMap A N hA t c S hS)
  (hbc : OrdinaryFiniteP1KummerMapBaseChange A N hA t c)

include c hb hbc in
theorem ordinaryFiniteP1_scalarTrace_baseChange
    {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))) :
    (ordinaryFinitePullback A f).map ((b S hS).inv ≫ biprod.snd) ≫
        (ordinaryFiniteUnitPullback A f).hom =
      ordinaryFiniteP1Exchange A f
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
            (affineTraceProjectiveInvertible N S hS)).hom ≫
        (b S' hS').inv ≫ biprod.snd := by
  have hs := hbc f hS hS'
  rw [← hb S hS, ← hb S' hS'] at hs
  simpa only [Category.assoc] using inverse_biprod_projection_square (ordinaryFinitePullback A f)
    (b S hS) (b S' hS')
    (ordinaryFiniteP1Exchange A f
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
        (ordinaryFiniteShiftedLinePullback A N hA t
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
          (affineTraceProjectiveInvertible N S hS)).hom)
    (ordinaryFiniteP1DecompositionSourceMap A N hA t f hS)
    (ordinaryFiniteUnitPullback A f).hom
    (by simpa only [Category.assoc] using hs)
    (by simp only [ordinaryFiniteP1DecompositionSourceMap, biprod.lift_snd])

include c hb in
theorem ordinaryFiniteP1_diagonal_integral (hN : 0 < N) [Finite A]
    (hc : OrdinaryFiniteP1ChernFamilySpec A N hA c)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    have : IsLocallyNoetherian (ProjectiveLine S) :=
      LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
    have : CompactSpace (ProjectiveLine S) :=
      QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
    have : IsNoetherian (ProjectiveLine S) := ⟨⟩
    ∃ hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible,
      ∃ κ : CategoryTheory.Abelian.Ext
        ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteConstant A (ProjectiveLine S)))
        (Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2,
        SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) hI
          (by simpa using (hS.map
            ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
              (ProjectiveLine S ↘ S)).appTop.hom)) κ ∧
        ∀ a : Bool,
          ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ ≫
            ordinaryFiniteP1DiagonalChartMap A N hA t S hS a ≫
              (b (ProjectiveLine S) (affineTraceProjectiveInvertible N S hS)).inv ≫ biprod.snd =
            𝟙 (ordinaryFiniteUnit A (ProjectiveLine S)) := by
  have : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  have : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  have : IsNoetherian (ProjectiveLine S) := ⟨⟩
  let hP := affineTraceProjectiveInvertible N S hS
  let hPP := affineTraceProjectiveInvertible N (ProjectiveLine S) hP
  let hW : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S), ⊤)) := by
    simpa using (hS.map
      ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
        (ProjectiveLine S ↘ S)).appTop.hom)
  let hI := projectiveLine_diagonal_ker_isInvertible S
  obtain ⟨κ, hκ, _⟩ := supported_cartier_boundary_existsUnique
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N hN A hA hW
    (pullback.diagonal (ProjectiveLine S ↘ S)) hI
  refine ⟨hI, κ, hκ, ?_⟩
  intro a
  obtain ⟨β, hβ⟩ := ordinaryFiniteP1_diagonal_kummer_component_formula N hN A hA t
    S hS hP hPP hW (c (ProjectiveLine S) hP) (hc (ProjectiveLine S) hP) hI κ hκ a
  have htrace := biprod_trace_components
    (b (ProjectiveLine S) hP)
    (ordinaryFiniteP1Unit A N hA t (ProjectiveLine S) hP)
    (ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S) (c (ProjectiveLine S) hP))
    (hb (ProjectiveLine S) hP)
  have hh := congrArg
    (fun f ↦ f ≫ (b (ProjectiveLine S) hP).inv ≫ biprod.snd) hβ
  simpa only [Preadditive.add_comp, Category.assoc, htrace.1, htrace.2,
    comp_zero, zero_add] using hh

end TraceSquare
end AlgebraicGeometry.Etale
