/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import WeilConjectures.RingTheory.FormalGlueingData
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineChartCoherence

/-! # Affine localization coordinates and their restriction squares

## References

* Stacks Project, Tag 0BLH, first two proof paragraphs
* Tag 05EL, item (1)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

private theorem chart_scalar
    {A : Type u} [CommRing A] {Y : Scheme.{u}} (h : Y ⟶ Spec (.of A))
    (V : Y.Opens) (f : A) (M : ModuleCat.{u} A)
    (c : M ≃+ Γ(Y, V))
    (b : FormalGlueing.localize f M ≃+ Γ(Y, V ⊓ V))
    (hb : ∀ m, b (LocalizedModule.mk m 1) =
      Y.presheaf.map (homOfLE (inf_le_right : V ⊓ V ≤ V)).op (c m))
    (hscalar : ∀ (a : A) m, b (a • m) =
      ((ΓSpecIso (.of A)).inv ≫ h.appTop ≫
        Y.presheaf.map (homOfLE (le_top : V ⊓ V ≤ ⊤)).op).hom a * b m)
    (a : A) (m : M) :
    c (a • m) = ((ΓSpecIso (.of A)).inv ≫ h.appTop ≫
      Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a * c m := by
  have hinj : Function.Injective
      (Y.presheaf.map (homOfLE (inf_le_right : V ⊓ V ≤ V)).op).hom := by
    have : IsIso (homOfLE (inf_le_right : V ⊓ V ≤ V)) :=
      homOfLE_isIso_of_eq _ (inf_idem V)
    exact (ConcreteCategory.bijective_of_isIso _).injective
  apply hinj
  rw [← hb, ← LocalizedModule.smul'_mk, hscalar]
  rw [map_mul, ← hb]
  congr 1
  rw [← CommRingCat.comp_apply]
  apply congrArg (fun k : CommRingCat.of A ⟶ Γ(Y, V ⊓ V) ↦ k.hom a)
  rw [Category.assoc, Category.assoc, ← Functor.map_comp]
  rfl

/-- Affine localization gives coordinates on chart intersections and completed charts,
with all four maps from the original section modules commuting with restriction. -/
theorem exists_affine_coordinate_squares
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (t : ℕ) (g : Fin t → A)
    (hcharts : ∀ j, PrimeSpectrum.basicOpen (g j) ≤ U) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let V : Fin t → Y.Opens := fun j ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (g j)
    let aY := ((ΓSpecIso (.of A)).inv ≫ (q ≫ U.ι).appTop).hom
    let aE := ((ΓSpecIso (.of A)).inv ≫ (s ≫ completionSpecMap A).appTop).hom
    letI : Algebra A Γ(Y, ⊤) := aY.toAlgebra
    letI : Algebra A Γ(E, ⊤) := aE.toAlgebra
    letI : ∀ j, Algebra A Γ(Y, V j) := fun j ↦
      ((Y.presheaf.map (homOfLE (le_top : V j ≤ ⊤)).op).hom.comp aY).toAlgebra
    let O := pullback q (completionSpecMap A ∣_ U)
    let p : O ⟶ Y := pullback.fst q (completionSpecMap A ∣_ U)
    letI : Algebra A C := φ.toAlgebra
    ∃ (X : FormalGlueing.Data.{u, u, u} φ g)
      (e : FormalGlueing.restrict φ X.M' ≃ₗ[A] Γ(E, ⊤))
      (d : ∀ j, FormalGlueing.piece (g j) (X.M j) ≃ₗ[A] Γ(Y, V j))
      (b : ∀ j, FormalGlueing.restrict φ
        (FormalGlueing.extend φ (FormalGlueing.piece (g j) (X.M j))) ≃ Γ(O, p ⁻¹ᵁ V j))
      (c : ∀ i j, FormalGlueing.localize (g i)
        (FormalGlueing.piece (g j) (X.M j)) ≃ Γ(Y, V i ⊓ V j)),
      (∀ j m, b j (X.alpha j (LocalizedModule.mk m 1)) =
        O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V j ≤ ⊤)).op
          (D.toCompleted.appTop (e m))) ∧
      (∀ j m, b j (TensorProduct.tmul A (1 : C) m) = p.app (V j) (d j m)) ∧
      (∀ i j m, c i j (X.alpha_overlap i j (LocalizedModule.mk m 1)) =
        Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (d i m)) ∧
      (∀ i j m, c i j (LocalizedModule.mk m 1) =
        Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (d j m)) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let φ := algebraMap A C
  let V : Fin t → Y.Opens := fun j ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (g j)
  let aY := ((ΓSpecIso (.of A)).inv ≫ (q ≫ U.ι).appTop).hom
  let aE := ((ΓSpecIso (.of A)).inv ≫ (s ≫ completionSpecMap A).appTop).hom
  let : Algebra A Γ(Y, ⊤) := aY.toAlgebra
  let : Algebra A Γ(E, ⊤) := aE.toAlgebra
  let : ∀ j, Algebra A Γ(Y, V j) := fun j ↦
    ((Y.presheaf.map (homOfLE (le_top : V j ≤ ⊤)).op).hom.comp aY).toAlgebra
  let : Algebra A C := φ.toAlgebra
  let : IsAffine E := isAffine_of_isAffineHom s
  have hV : ∀ j, IsAffineOpen (V j) := by
    intro j
    change IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (g j))
    rw [Scheme.Hom.comp_preimage]
    have hbase : IsAffineOpen (X := Spec (.of A)) (PrimeSpectrum.basicOpen (g j)) :=
      IsAffineOpen.Spec_basicOpen (R := .of A) (g j)
    have hsub : PrimeSpectrum.basicOpen (g j) ≤ U.ι.opensRange := by
      rw [Scheme.Opens.opensRange_ι]
      exact hcharts j
    exact (hbase.preimage_of_isOpenImmersion U.ι hsub).preimage q
  obtain ⟨T⟩ := exists_affine_chart_transitions D t g hcharts hV
  obtain ⟨hsquare, hcocycle⟩ := affine_chart_transition_coherence D t g hcharts hV T
  let X : FormalGlueing.Data.{u, u, u} φ g :=
    { M' := T.F.M'
      M := T.F.M
      alpha := T.F.alpha
      alpha_smul := T.F.alpha_smul
      alpha_overlap := T.F.alpha_overlap
      square := hsquare
      cocycle := hcocycle }
  have hc : ∀ j (a : A) m, T.c j (a • m) = a • T.c j m := by
    intro j a m
    exact chart_scalar (q ≫ U.ι) (V j) (g j)
      (FormalGlueing.piece (g j) (T.F.M j)) (T.c j) (T.b j j)
      (T.b_right j j) (T.b_scalar j j) a m
  let d : ∀ j, FormalGlueing.piece (g j) (X.M j) ≃ₗ[A] Γ(Y, V j) := fun j ↦
    { T.c j with map_smul' := hc j }
  let : Module C Γ(E, ⊤) := completedChartModule s
  have he : ∀ (a : A) (m : FormalGlueing.restrict φ X.M'),
      T.e (a • m) = a • T.e m := by
    intro a m
    change T.e ((φ a) • (m : T.F.M')) = aE a * T.e m
    rw [T.e.map_smul]
    change (((ΓSpecIso (.of C)).inv ≫ s.appTop).hom (φ a)) * T.e m = _
    have hmap : (CommRingCat.ofHom φ) ≫ (ΓSpecIso (.of C)).inv ≫ s.appTop =
        (ΓSpecIso (.of A)).inv ≫ (s ≫ completionSpecMap A).appTop := by
      rw [Hom.comp_appTop, ΓSpecIso_inv_naturality_assoc]
    exact congrArg (fun z ↦ z * T.e m)
      (congrArg (fun h : CommRingCat.of A ⟶ Γ(E, ⊤) ↦ h.hom a) hmap)
  let e : FormalGlueing.restrict φ X.M' ≃ₗ[A] Γ(E, ⊤) :=
    { T.e.toAddEquiv with map_smul' := he }
  refine ⟨X, e, d, (fun j ↦ (T.d j).toEquiv),
    (fun i j ↦ (T.b i j).toEquiv), ?_⟩
  exact ⟨T.d_prime, T.d_chart, T.b_left, T.b_right⟩

end AlgebraicGeometry.Scheme.CompletionGluingData
