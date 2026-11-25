/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafModule
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomology
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint

/-!
# Endomorphisms of the constant complex of the projective line

For the projective line `q : ℙ¹_S ⟶ S` and its section at infinity `ι : Z ⟶ ℙ¹_S`, an
endomorphism of the constant complex `Λ_{ℙ¹_S}` is determined by its pullback along `ι`
(`AlgebraicGeometry.Etale.eq_of_leftDerivedUpperStar_lineInfinityι_map_eq`).

## The argument

Over a separably closed field `Ω`, with `T = Spec Ω`, every endomorphism of `Λ_{ℙ¹_T}` is pulled
back from an endomorphism of `Λ_T`
(`AlgebraicGeometry.Etale.exists_constantComplexEndPullback_eq`): by the decomposition
`(1, h) : Λ_T(1)[2] ⊕ Λ_T ≅ Rq_*(Λ_{ℙ¹_T}(1)[2])`
(`AlgebraicGeometry.Etale.isIso_projectiveLineDecompositionMap`), whose first component is the
unit of `Lq^* ⊣ Rq_*`, and the vanishing of `Hom(Λ_T(1)[2], Λ_T)`, every endomorphism of
`Lq^*(Λ_T(1)[2])` is `Lq^*` of an endomorphism of `Λ_T(1)[2]`
(`CategoryTheory.Adjunction.exists_map_eq_of_isIso_biprodDesc`). One untwists using
`Λ_T(1) ≅ Λ_T` and unshifts. Consequently two maps `σ τ : X ⟶ ℙ¹_T` with `σ ≫ q = τ ≫ q` pull
back an endomorphism of `Λ_{ℙ¹_T}` to the same endomorphism of `Λ_X`.

A geometric point `x : Spec Ω ⟶ ℙ¹_S` is a section of `ℙ¹_Ω` followed by the base change
`ℙ¹_Ω ⟶ ℙ¹_S`; comparing it with the point at infinity of `ℙ¹_Ω`, which lies over the section
at infinity of `ℙ¹_S`, the pullback along `x` of an endomorphism of `Λ_{ℙ¹_S}` is determined by
its pullback along `ι`. Morphisms between sheaves placed in degree zero are detected at the
geometric points (`AlgebraicGeometry.Etale.hom_ext_of_leftDerivedUpperStar_map_eq`).

## Main statements

- `AlgebraicGeometry.Etale.exists_constantComplexEndPullback_eq`
- `AlgebraicGeometry.Etale.eq_of_leftDerivedUpperStar_lineInfinityι_map_eq`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory

section Surjective

variable {C D : Type*} [Category* C] [Category* D]

/-- If an endomorphism of `F M` lifts along `F` for some `M` isomorphic to `M'`, every
endomorphism of `F M'` lifts along `F`. -/
lemma Functor.exists_map_eq_of_iso (F : C ⥤ D) {M M' : C} (e : M ≅ M')
    (h : ∀ f : F.obj M ⟶ F.obj M, ∃ g : M ⟶ M, F.map g = f) (f : F.obj M' ⟶ F.obj M') :
    ∃ g : M' ⟶ M', F.map g = f := by
  obtain ⟨g, hg⟩ := h (F.map e.hom ≫ f ≫ F.map e.inv)
  refine ⟨e.inv ≫ g ≫ e.hom, ?_⟩
  simp [hg]

/-- For a functor `F` commuting with shifts, if every endomorphism of `F (M⟦n⟧)` lifts along
`F`, so does every endomorphism of `F M`. -/
lemma Functor.exists_map_eq_of_shift {A : Type*} [AddGroup A] [HasShift C A] [HasShift D A]
    (F : C ⥤ D) [F.CommShift A] (M : C) (n : A)
    (h : ∀ f : F.obj (M⟦n⟧) ⟶ F.obj (M⟦n⟧), ∃ g : M⟦n⟧ ⟶ M⟦n⟧, F.map g = f)
    (f : F.obj M ⟶ F.obj M) : ∃ g : M ⟶ M, F.map g = f := by
  obtain ⟨g, hg⟩ := h ((F.commShiftIso n).hom.app M ≫ f⟦n⟧' ≫ (F.commShiftIso n).inv.app M)
  refine ⟨(shiftFunctor C n).preimage g, (shiftFunctor D n).map_injective ?_⟩
  have hn := F.commShiftIso_hom_naturality ((shiftFunctor C n).preimage g) n
  rw [Functor.map_preimage, hg] at hn
  simpa using hn.symm

variable [Preadditive C] [HasBinaryBiproducts C] {F : C ⥤ D} {G : D ⥤ C}

/-- Let `F ⊣ G`, `e : F M ≅ K`, and suppose that `(η_M ≫ G e, b) : M ⊞ N ⟶ G K` is an
isomorphism and that every morphism `M ⟶ N` vanishes. Then every endomorphism of `F M` is `F` of
an endomorphism of `M`: its adjoint factors through the unit. -/
theorem Adjunction.exists_map_eq_of_isIso_biprodDesc (adj : F ⊣ G) {M N : C} {K : D}
    (e : F.obj M ≅ K) (b : N ⟶ G.obj K)
    (hd : IsIso (biprod.desc (adj.unit.app M ≫ G.map e.hom) b)) (hMN : ∀ f : M ⟶ N, f = 0)
    (f : F.obj M ⟶ F.obj M) : ∃ g : M ⟶ M, F.map g = f := by
  set d := biprod.desc (adj.unit.app M ≫ G.map e.hom) b
  set x := adj.unit.app M ≫ G.map (f ≫ e.hom)
  refine ⟨x ≫ inv d ≫ biprod.fst, ?_⟩
  have hx : x = (x ≫ inv d ≫ biprod.fst) ≫ adj.unit.app M ≫ G.map e.hom := by
    have h₁ : x ≫ inv d = (x ≫ inv d ≫ biprod.fst) ≫ biprod.inl := by
      apply biprod.hom_ext
      · simp
      · simp only [Category.assoc, biprod.inl_snd, comp_zero]
        exact hMN _
    calc x = (x ≫ inv d) ≫ d := by simp
      _ = _ := by rw [h₁, Category.assoc, biprod.inl_desc]
  have h₂ : adj.homEquiv _ _ (f ≫ e.hom) =
      adj.homEquiv _ _ (F.map (x ≫ inv d ≫ biprod.fst) ≫ e.hom) := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    refine hx.trans ?_
    rw [Functor.map_comp, adj.unit_naturality_assoc]
    rfl
  rw [← cancel_mono e.hom]
  exact ((adj.homEquiv _ _).injective h₂).symm

end Surjective

/-- In the derived category, there are no nonzero morphisms `X⟦2⟧ ⟶ Y` between objects
isomorphic to objects placed in degree zero. -/
lemma DerivedCategory.eq_zero_of_shift_two {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {X Y : DerivedCategory C} {A B : C}
    (eX : X ≅ (DerivedCategory.singleFunctor C 0).obj A)
    (eY : Y ≅ (DerivedCategory.singleFunctor C 0).obj B) (f : X⟦(2 : ℤ)⟧ ⟶ Y) : f = 0 := by
  have : X.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso eX.symm 0
  have : Y.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso eY.symm 0
  have := DerivedCategory.TStructure.t.isLE_shift X 0 2 (-2)
  exact DerivedCategory.TStructure.t.zero f (-2) 0

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section SepClosed

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

omit [Finite Λ] in
/-- Over a separably closed field `Ω`, the Tate twist `Λ_Ω(m)` is the constant complex. -/
theorem nonempty_tateObject_spec_iso_constantComplex [HasTateTwist Λ]
    [HasInvertibleExponent Λ (Spec (.of Ω))] (m : ℤ) :
    Nonempty (tateObject Λ (Spec (.of Ω)) m ≅ constantComplex Λ (Spec (.of Ω))) := by
  obtain ⟨L, -, hL, ⟨eL⟩⟩ :=
    HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) (Spec (.of Ω)) m
  obtain ⟨e₁⟩ := hL Ω (𝟙 _)
  obtain ⟨e₂⟩ := Scheme.nonempty_iso_constantSheaf_of_sheafFiber_iso L e₁
  exact ⟨eL ≪≫ (_root_.DerivedCategory.singleFunctor _ 0).mapIso e₂ ≪≫
    (constantComplexIsoSingleFunctor Λ (Spec (.of Ω))).symm⟩

end SepClosed

section Untwisted

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] {T : Scheme.{u}}
  [HasInvertibleExponent Λ T]

/-- If `Λ_T(1) ≅ Λ_T` (e.g. `T = Spec Ω` for `Ω` separably closed), with `q : ℙ¹_T ⟶ T`, every
endomorphism of `Lq^* Λ_T` is `Lq^*` of an endomorphism of `Λ_T`. -/
theorem exists_leftDerivedUpperStar_projectiveLine_map_eq
    (hT : Nonempty (tateObject Λ T 1 ≅ constantComplex Λ T))
    (f : (L((ℙ(Option (ULift.{u} (Fin 1)); T) ↘ T)^*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ T) ⟶
      (L((ℙ(Option (ULift.{u} (Fin 1)); T) ↘ T)^*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ T)) :
    ∃ g, (L((ℙ(Option (ULift.{u} (Fin 1)); T) ↘ T)^*[ModuleCat.{u + 1} Λ])).map g = f := by
  obtain ⟨θ⟩ := hT
  refine Functor.exists_map_eq_of_iso _ θ (Functor.exists_map_eq_of_shift _ _ (2 : ℤ) ?_) f
  exact Adjunction.exists_map_eq_of_isIso_biprodDesc
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (ℙ(Option (ULift.{u} (Fin 1)); T) ↘ T))
    (((L((ℙ(Option (ULift.{u} (Fin 1)); T) ↘ T)^*[ModuleCat.{u + 1} Λ])).commShiftIso
        (2 : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso (leftDerivedUpperStarTateObjectIso
        (ℙ(Option (ULift.{u} (Fin 1)); T) ↘ T) 1))
    _ (isIso_projectiveLineDecompositionMapAux Λ T)
    (DerivedCategory.eq_zero_of_shift_two (θ ≪≫ constantComplexIsoSingleFunctor Λ T)
      (constantComplexIsoSingleFunctor Λ T))

/-- If `Λ_T(1) ≅ Λ_T`, every endomorphism of `Λ_{ℙ¹_T}` is pulled back from an endomorphism of
`Λ_T`. -/
theorem exists_constantComplexEndPullback_eq
    (hT : Nonempty (tateObject Λ T 1 ≅ constantComplex Λ T))
    (φ : constantComplex Λ ℙ(Option (ULift.{u} (Fin 1)); T) ⟶
      constantComplex Λ ℙ(Option (ULift.{u} (Fin 1)); T)) :
    ∃ g, constantComplexEndPullback Λ (ℙ(Option (ULift.{u} (Fin 1)); T) ↘ T) g = φ := by
  obtain ⟨g, hg⟩ := exists_leftDerivedUpperStar_projectiveLine_map_eq Λ hT
    ((leftDerivedUpperStarConstantComplexIso Λ _).hom ≫ φ ≫
      (leftDerivedUpperStarConstantComplexIso Λ _).inv)
  refine ⟨g, ?_⟩
  simp [constantComplexEndPullback, hg]

/-- If `Λ_T(1) ≅ Λ_T`, two maps `σ τ : X ⟶ ℙ¹_T` lying over the same map to `T` pull back every
endomorphism of `Λ_{ℙ¹_T}` to the same endomorphism of `Λ_X`. -/
theorem constantComplexEndPullback_eq_of_comp_eq
    (hT : Nonempty (tateObject Λ T 1 ≅ constantComplex Λ T)) {X : Scheme.{u}}
    (σ τ : X ⟶ ℙ(Option (ULift.{u} (Fin 1)); T))
    (hστ : σ ≫ ℙ(Option (ULift.{u} (Fin 1)); T) ↘ T = τ ≫ ℙ(Option (ULift.{u} (Fin 1)); T) ↘ T)
    (φ : constantComplex Λ ℙ(Option (ULift.{u} (Fin 1)); T) ⟶
      constantComplex Λ ℙ(Option (ULift.{u} (Fin 1)); T)) :
    constantComplexEndPullback Λ σ φ = constantComplexEndPullback Λ τ φ := by
  obtain ⟨g, rfl⟩ := exists_constantComplexEndPullback_eq Λ hT φ
  rw [constantComplexEndPullback_constantComplexEndPullback σ _ _ rfl,
    constantComplexEndPullback_constantComplexEndPullback τ _ _ rfl, hστ]

end Untwisted

/-- The pullback of an endomorphism of `Λ_{ℙ¹_S}` along a geometric point
`x : Spec Ω ⟶ ℙ¹_S` is determined by its pullback along the section at infinity: it is the
pullback along some `x' : Spec Ω ⟶ Z`, depending only on `x`, of the latter. The point `x` is a
section of `ℙ¹_Ω` followed by the base change `ℙ¹_Ω ⟶ ℙ¹_S`, and this section may be replaced by
the point at infinity of `ℙ¹_Ω`
(`AlgebraicGeometry.Etale.constantComplexEndPullback_eq_of_comp_eq`),
which lies over the section at infinity of `ℙ¹_S`. -/
theorem exists_constantComplexEndPullback_eq_lineInfinityι [HasKummerClass Λ]
    [HasKummerClass.IsNormalized Λ] (S : Scheme.{u}) [HasInvertibleExponent Λ S]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ ℙ(Option (ULift.{u} (Fin 1)); S)) :
    ∃ x' : Spec (.of Ω) ⟶ ProjectiveSpace.lineInfinity S,
      ∀ φ : constantComplex Λ ℙ(Option (ULift.{u} (Fin 1)); S) ⟶
        constantComplex Λ ℙ(Option (ULift.{u} (Fin 1)); S),
      constantComplexEndPullback Λ x φ = constantComplexEndPullback Λ x'
        (constantComplexEndPullback Λ (ProjectiveSpace.lineInfinityι S) φ) := by
  have : HasInvertibleExponent Λ (Spec (.of Ω)) := .of_hom x
  have sq := ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1)))
    (x ≫ ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
  obtain ⟨gZ, hgZ⟩ := ProjectiveSpace.exists_isPullback_lineInfinityι_map
    (x ≫ ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
  have hσ : (inv (ProjectiveSpace.lineInfinityι (Spec (.of Ω)) ≫
      ℙ(Option (ULift.{u} (Fin 1)); Spec (.of Ω)) ↘ Spec (.of Ω)) ≫
        ProjectiveSpace.lineInfinityι (Spec (.of Ω))) ≫
      ℙ(Option (ULift.{u} (Fin 1)); Spec (.of Ω)) ↘ Spec (.of Ω) = 𝟙 _ := by
    rw [Category.assoc, IsIso.inv_hom_id]
  refine ⟨inv (ProjectiveSpace.lineInfinityι (Spec (.of Ω)) ≫
      ℙ(Option (ULift.{u} (Fin 1)); Spec (.of Ω)) ↘ Spec (.of Ω)) ≫ gZ, fun φ ↦ ?_⟩
  rw [← constantComplexEndPullback_constantComplexEndPullback
      (sq.lift x (𝟙 _) (Category.id_comp _).symm) _ x (sq.lift_fst _ _ _).symm,
    constantComplexEndPullback_eq_of_comp_eq Λ (nonempty_tateObject_spec_iso_constantComplex Λ Ω 1)
      _ _ ((sq.lift_snd _ _ _).trans hσ.symm),
    constantComplexEndPullback_constantComplexEndPullback _ _ _ rfl,
    constantComplexEndPullback_constantComplexEndPullback _ (ProjectiveSpace.lineInfinityι S) _
      rfl]
  congr 1
  simp only [Category.assoc, hgZ.w]

/-- An endomorphism of the constant complex `Λ_{ℙ¹_S}` of the projective line is determined by
its pullback along the section at infinity `ι : Z ⟶ ℙ¹_S`. It is checked at the geometric points
`x : Spec Ω ⟶ ℙ¹_S`, where the pullback along `x` is determined by the pullback along `ι`
(`AlgebraicGeometry.Etale.exists_constantComplexEndPullback_eq_lineInfinityι`). -/
theorem eq_of_leftDerivedUpperStar_lineInfinityι_map_eq [HasKummerClass Λ]
    [HasKummerClass.IsNormalized Λ]
    (S : Scheme.{u}) [HasInvertibleExponent Λ S]
    {φ ψ : constantComplex Λ ℙ(Option (ULift.{u} (Fin 1)); S) ⟶
      constantComplex Λ ℙ(Option (ULift.{u} (Fin 1)); S)}
    (h : (L((ProjectiveSpace.lineInfinityι S)^*[ModuleCat.{u + 1} Λ])).map φ =
      (L((ProjectiveSpace.lineInfinityι S)^*[ModuleCat.{u + 1} Λ])).map ψ) : φ = ψ := by
  refine hom_ext_of_leftDerivedUpperStar_map_eq (constantComplexIsoSingleFunctor Λ _)
    (constantComplexIsoSingleFunctor Λ _) fun Ω _ _ x ↦ ?_
  obtain ⟨x', hx'⟩ := exists_constantComplexEndPullback_eq_lineInfinityι Λ S Ω x
  have hxφψ : constantComplexEndPullback Λ x φ = constantComplexEndPullback Λ x ψ := by
    rw [hx', hx']
    unfold constantComplexEndPullback
    rw [h]
  simpa [constantComplexEndPullback] using
    (leftDerivedUpperStarConstantComplexIso Λ x).hom ≫= hxφψ =≫
      (leftDerivedUpperStarConstantComplexIso Λ x).inv

end Etale

end AlgebraicGeometry
