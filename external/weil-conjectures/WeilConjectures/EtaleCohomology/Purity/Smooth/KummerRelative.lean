/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerGenerator

/-!
# The Kummer class generates `R¹π_* Λ(1)` over a base

Let `k` be an algebraically closed field, `Y` a separated `k`-scheme of finite type and
`π : 𝔾_{m,Y} ⟶ Y` the complement of the zero section of `𝔸¹_Y`, with coordinate `t`. For a
rank-one datum whose Kummer class of the coordinate of `𝔾_{m,Ω}` is free of rank one over every
algebraically closed field `Ω`, the adjoint `Λ_Y ⟶ Rπ_*(Λ(1)[1])` of the Kummer class `κ(t)`
is an isomorphism on `H⁰`: `R¹π_* Λ(1)` is free of rank one on `κ(t)`
(`AlgebraicGeometry.Etale.isIso_homology_zero_kummerClassAdjoint_of_cohomology`).

The isomorphism is checked after pullback to the geometric points `x : Spec Ω ⟶ Y`. There the
derived base change map to the fibre `𝔾_{m,Ω}` carries the pulled-back adjoint of `κ(t)` to
the adjoint of `κ(t_Ω)` (`AlgebraicGeometry.Etale.derivedBaseChangeMap_app_homEquiv`), so the
fibre map on `H⁰` is injective (`AlgebraicGeometry.Etale.mono_homologyFunctor_zero_map`); both
sides are `Λ` by the Künneth computation of `Rπ_* Λ(1)`, so it is bijective.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The adjunction `Lf^* ⊣ Rf_*` is `Λ`-linear on hom sets. -/
lemma derivedUpperStarLowerStarAdjunction_homEquiv_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (c : Λ) (α : (L((f)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ K) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _ (c • α) =
      c • (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _ α := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_smul, Linear.comp_smul]

omit [CommRing Λ] in
/-- If `e⁻¹ ≫ f ≫ g` is a monomorphism, so is `f`. -/
lemma mono_of_mono_iso_inv_comp {𝒞 : Type*} [Category 𝒞] {A B D E : 𝒞} (e : B ≅ A) (f : B ⟶ D)
    (g : D ⟶ E) (h : Mono (e.inv ≫ f ≫ g)) : Mono f :=
  ⟨fun a b hab ↦ by
    have := h.right_cancellation (a ≫ e.hom) (b ≫ e.hom) (by simp [reassoc_of% hab])
    simpa using this⟩

variable [Finite Λ] [HasKummerClass Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
  [QuasiCompact aY]

include aY in
/-- `R¹π_* Λ(1)` is the sheaf `L` underlying `Λ_Y(1)`, by the Künneth computation of
`Rπ_* Λ(1) ≅ Λ_Y(1) ⊕ Λ_Y(1)[-1]`. -/
theorem exists_iso_homology_zero_rightDerivedLowerStar_tateObject
    {G₀ : Scheme.{u}} (j₀ : G₀ ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j₀]
    (hj₀ : Set.range j₀.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).base)ᶜ)
    (hG : ∀ q : ℤ, q ≠ 0 → q ≠ 1 →
      IsZero ((cohomology (ModuleCat.{u + 1} Λ) G₀ q).obj (constantComplex Λ _)))
    (eG₀ : (cohomology (ModuleCat.{u + 1} Λ) G₀ 0).obj (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    (eG₁ : (cohomology (ModuleCat.{u + 1} Λ) G₀ 1).obj (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ G] :
    ∃ L : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty ((_root_.DerivedCategory.homologyFunctor _ 0).obj
        ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
          ((tateObject Λ G 1)⟦(1 : ℤ)⟧)) ≅ L) := by
  let π := j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y
  obtain ⟨LT, -, hLT, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y 1
  have hQ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y (tateObject Λ Y 1) :=
    boundedConstructibleFiniteTor_tateObject Λ Y 1
  obtain ⟨eK⟩ := nonempty_iso_rightDerivedLowerStar_multiplicativeGroup_of_cohomology Λ aY j₀
    hj₀ hG eG₀ eG₁ j hj hQ
  have hTz := (homology_props_of_iso_singleFunctor Λ eTY hLT).1
  exact ⟨LT, hLT, ⟨(_root_.DerivedCategory.homologyFunctor _ 0).mapIso
        (((R((π)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).app (tateObject Λ G 1)) ≪≫
      ((_root_.DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)) 0).shiftIso (1 : ℤ) 0 1 (by norm_num)).app _ ≪≫
      (_root_.DerivedCategory.homologyFunctor _ 1).mapIso
        ((R((π)_*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateObjectIso π 1).symm ≪≫
          eK) ≪≫
      homologyOneBiprodShiftIso Λ (tateObject Λ Y 1) hTz ≪≫
      _root_.DerivedCategory.homologyFunctorObjIsoOfIsoSingleFunctor eTY⟩⟩

-- the composites of derived functors between the derived categories of the two bases are large
include aY in
/-- **The Kummer class generates `R¹π_* Λ(1)`.** Suppose that over every algebraically closed
field `Ω` the Kummer class of the coordinate of `𝔾_{m,Ω}` is free of rank one
(`c • κ(t) = 0 → c = 0`), and that `H^q(𝔾_{m,k}, Λ)` is `Λ` for `q = 0, 1` and vanishes
otherwise. Then for the complement `j : G ⟶ 𝔸¹_Y` of the zero section, `π = j ≫ p`, the
adjoint `Λ_Y ⟶ Rπ_*(Λ(1)[1])` of `κ(t)` is an isomorphism on `H⁰`. -/
theorem isIso_homology_zero_kummerClassAdjoint_of_cohomology
    (hKum : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [HasInvertibleExponent Λ (Spec (.of Ω))]
      (G' : Scheme.{u}) (j' : G' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of Ω))) [IsOpenImmersion j']
      (hj' : Set.range j'.base =
        (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of Ω))).base)ᶜ)
      [HasInvertibleExponent Λ G'] (c : Λ),
      c • kummerClass Λ (AffineSpace.unitLineCoord j' hj') = 0 → c = 0)
    {G₀ : Scheme.{u}} (j₀ : G₀ ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j₀]
    (hj₀ : Set.range j₀.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).base)ᶜ)
    (hG : ∀ q : ℤ, q ≠ 0 → q ≠ 1 →
      IsZero ((cohomology (ModuleCat.{u + 1} Λ) G₀ q).obj (constantComplex Λ _)))
    (eG₀ : (cohomology (ModuleCat.{u + 1} Λ) G₀ 0).obj (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    (eG₁ : (cohomology (ModuleCat.{u + 1} Λ) G₀ 1).obj (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ G]
    (B : (L((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y) ≅
      constantComplex Λ G) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).homEquiv _ _
          (B.hom ≫ kummerClass Λ (AffineSpace.unitLineCoord j hj)))) := by
  let π := j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y
  let κ := kummerClass Λ (AffineSpace.unitLineCoord j hj)
  let κb := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π).homEquiv _ _ (B.hom ≫ κ)
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (fun y : Y ↦ Y.algClosurePoint y)
    (fun y ↦ ⟨y, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩) _ fun y ↦ ?_
  let Ω := AlgebraicClosure (Y.residueField y)
  let x : Spec (.of Ω) ⟶ Y := Y.algClosurePoint y
  have : HasInvertibleExponent Λ (Spec (.of Ω)) := .of_hom x
  change IsIso ((_root_.DerivedCategory.homologyFunctor _ 0 ⋙ (x)^*[ModuleCat.{u + 1} Λ]).map κb)
  rw [NatIso.isIso_map_iff (leftDerivedUpperStarHomologyFunctorIso _ x 0)]
  -- the fibre `G_Ω` of `π` at `x`
  let j' := pullback.snd j (AffineSpace.map (ULift.{u} (Fin 1)) x)
  have hj' := AffineSpace.range_pullback_snd_map x j hj
  let q := pullback.fst j (AffineSpace.map (ULift.{u} (Fin 1)) x)
  have : HasInvertibleExponent Λ (pullback j (AffineSpace.map (ULift.{u} (Fin 1)) x)) :=
    .of_hom q
  let π' := j' ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) ↘ Spec (.of Ω)
  have sq : CommSq q π' π x := ⟨by
    simp only [π, π', j', q, Category.assoc]
    rw [pullback.condition_assoc, AffineSpace.map_over]⟩
  let BC := (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app ((tateObject Λ G 1)⟦(1 : ℤ)⟧)
  let θx := leftDerivedUpperStarConstantComplexIso Λ x
  let β := θx.inv ≫ (L((x)^*[ModuleCat.{u + 1} Λ])).map κb ≫ BC
  let A := (L((π')^*[ModuleCat.{u + 1} Λ])).map θx.inv ≫
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app _ ≫
      (L((q)^*[ModuleCat.{u + 1} Λ])).map B.hom
  have hβ' : β = (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π').homEquiv _ _
      (A ≫ (L((q)^*[ModuleCat.{u + 1} Λ])).map κ) := by
    simp only [β, κb, A]
    rw [derivedBaseChangeMap_app_homEquiv, ← Adjunction.homEquiv_naturality_left]
    simp only [Functor.map_comp, Category.assoc]
  have hβ : ∀ c : Λ, c • β = 0 → c = 0 := by
    intro c hc
    rw [hβ', ← derivedUpperStarLowerStarAdjunction_homEquiv_smul] at hc
    have h₂ : c • (A ≫ (L((q)^*[ModuleCat.{u + 1} Λ])).map κ) = 0 :=
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) π').homEquiv _ _).injective
        (by rw [hc, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero])
    have h₃ : c • (L((q)^*[ModuleCat.{u + 1} Λ])).map κ = 0 := by
      rw [← cancel_epi A, comp_zero, Linear.comp_smul]
      exact h₂
    have hnat := leftDerivedUpperStar_map_kummerClass Λ q (AffineSpace.unitLineCoord j hj)
    rw [units_map_unitLineCoord x j hj j' hj' q pullback.condition] at hnat
    refine hKum Ω _ j' hj' c ?_
    rw [← cancel_epi (leftDerivedUpperStarConstantComplexIso Λ q).hom, comp_zero,
      Linear.comp_smul, ← hnat, ← Linear.smul_comp]
    change (c • (L((q)^*[ModuleCat.{u + 1} Λ])).map κ) ≫ _ = 0
    rw [h₃, zero_comp]
  let H' := _root_.DerivedCategory.homologyFunctor
    (Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0
  have hmono : Mono (H'.map (θx.inv ≫ (L((x)^*[ModuleCat.{u + 1} Λ])).map κb ≫ BC)) :=
    mono_homologyFunctor_zero_map Λ β hβ
  rw [Functor.map_comp, Functor.map_comp] at hmono
  have hm := mono_of_mono_iso_inv_comp (H'.mapIso θx) _ _ hmono
  -- the sections of both sides are `Λ`
  obtain ⟨LT, hLT, ⟨eT⟩⟩ := exists_iso_homology_zero_rightDerivedLowerStar_tateObject Λ aY j₀
    hj₀ hG eG₀ eG₁ j hj
  obtain ⟨E₂⟩ := nonempty_sepClosedSections_homology_iso Λ eT hLT x
  obtain ⟨L₀, -, hL₀, ⟨e₀⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y 0
  obtain ⟨E₁⟩ := nonempty_sepClosedSections_homology_iso Λ
    (_root_.DerivedCategory.homologyFunctorObjIsoOfIsoSingleFunctor
      ((HasTateTwist.twistObjectZeroIso (Λ := Λ) Y).symm ≪≫ e₀)) hL₀ x
  have := Finite.of_equiv _ E₁.toLinearEquiv.toEquiv.symm
  have := Finite.of_equiv _ E₂.toLinearEquiv.toEquiv.symm
  change IsIso (H'.map ((L((x)^*[ModuleCat.{u + 1} Λ])).map κb))
  exact isIso_of_mono_of_card_sections Λ _ (by
    rw [Nat.card_congr E₁.toLinearEquiv.toEquiv, Nat.card_congr E₂.toLinearEquiv.toEquiv])

end Etale

end AlgebraicGeometry
