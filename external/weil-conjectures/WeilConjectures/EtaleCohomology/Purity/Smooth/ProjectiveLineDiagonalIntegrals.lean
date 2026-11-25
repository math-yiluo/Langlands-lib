/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDiagonal
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CartierKummerClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryProductOne
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineConstantEnd
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineTraceBaseChange

/-!
# The two integrals of the diagonal class

Blueprint `lemma-class-diagonal-projective-line` (and `det-sp-p1-trace` (3)). Let `P = ℙ¹_S` and
`W = ℙ¹_P`, which is `P ×_S P` (`AlgebraicGeometry.ProjectiveSpace.isPullback_map`) with first
projection `p₁ = W ↘ P` and second projection `p₂ = map (P ↘ S)`. The diagonal
`Δ : P ⟶ W` (`AlgebraicGeometry.ProjectiveSpace.diagonal`) is an effective Cartier divisor; given
the purity hypothesis `AlgebraicGeometry.Etale.SupportedTatePure` for it, it has a cycle class
`δ : Λ_W ⟶ Λ_W(1)[2]` (`AlgebraicGeometry.Etale.cartierKummerCycleClass`, the class
`AlgebraicGeometry.Etale.cartierKummerClass` with supports forgotten). We show

`Λ_P ⟶ Rp₁_* Λ_W ⟶ Rp₁_*(Λ_W(1)[2]) ⟶ Λ_P`

(the adjoint of `δ`, followed by the trace `AlgebraicGeometry.Etale.projectiveLineTrace` of
`p₁ : ℙ¹_P ⟶ P`) is the identity, and the same for `p₂`, through the automorphism of `W`
exchanging the factors (`AlgebraicGeometry.Etale.projectiveLineDiagonalSwap`).

*Signs.* The auxiliary classes `δ_aux` (`AlgebraicGeometry.Etale.cartierKummerCycleClassAux`) and
`-h` (`AlgebraicGeometry.Etale.projectiveLineHyperplaneClassAux`) are built from Kummer boundaries
`∂κ(f)` of local equations, which forget supports to `c₁(𝒪(-D))`; the classes of the notes
`δ = c₁(𝒪(Δ))` (`AlgebraicGeometry.Etale.cartierKummerCycleClass`) and `h = c₁(𝒪(1))`
(`AlgebraicGeometry.Etale.projectiveLineHyperplaneClass`) are their negatives, and the trace of the
notes (`AlgebraicGeometry.Etale.projectiveLineTrace`) is the negative of the auxiliary trace
normalized by `-h`. The two signs cancel: the diagonal integrals are `1` for the conventions of the
notes as for the auxiliary ones.

## The argument

The composite `φ` is an endomorphism of `Λ_P`. Endomorphisms of `Λ_{ℙ¹_S}` are determined by
their restriction to the section at infinity `ι : Z ⟶ ℙ¹_S`
(`AlgebraicGeometry.Etale.eq_of_leftDerivedUpperStar_lineInfinityι_map_eq`: they are pulled back
from `S`, by the decomposition `lemma-cohomology-projective-line-trace` on geometric fibres). By the
base change of the trace (`AlgebraicGeometry.Etale.projectiveLineTrace_baseChange`) the restriction
of `φ` along `ι` is the trace on `ℙ¹_Z` of the restriction of `δ`. The diagonal meets `ℙ¹_Z` in its
section at infinity (`AlgebraicGeometry.ProjectiveSpace.isPullback_lineInfinityι_diagonal`),
and near the point `(∞, ∞)` it is cut out by `z - t`
(`AlgebraicGeometry.ProjectiveSpace.exists_isPullback_diagonalChart`), which restricts to the
coordinate `T_∞ / T₀` of `ℙ¹_Z`. Hence the restriction of `δ` is the class of the section at
infinity, i.e. the hyperplane class `h` of `ℙ¹_Z`
(`AlgebraicGeometry.Etale.restrictSupportedClass_cartierKummerClass_diagonal`), whose trace is `1`
by the normalization of the trace.

## Main statements

- `AlgebraicGeometry.Etale.projectiveLineTrace_diagonal`: the case `a = 1`.
- `AlgebraicGeometry.Etale.projectiveLineTrace_diagonal_swap`: the case `a = 2`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] HasInvertibleExponent.opens

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The characteristic of `Λ` is invertible on the section at infinity of `ℙ¹_S`. -/
instance hasInvertibleExponent_lineInfinity {S : Scheme.{u}} [HasInvertibleExponent Λ S] :
    HasInvertibleExponent Λ (ProjectiveSpace.lineInfinity S) :=
  .of_hom (ProjectiveSpace.lineInfinityι S)

variable [HasKummerClass Λ]

section CycleClass

variable [HasKummerClass.IsNormalized Λ] {T D : Scheme.{u}} [HasInvertibleExponent Λ T]
  (i : D ⟶ T) [IsRegularImmersion 1 i]

/-- The *auxiliary cycle class* `δ_aux : Λ_T ⟶ Λ_T(1)[2]` of an effective Cartier divisor
`i : D ⟶ T` satisfying the purity hypothesis: the class `AlgebraicGeometry.Etale.cartierKummerClass`
with supports forgotten. With the conventions of `AlgebraicGeometry.Etale.kummerBoundary` it is
`c₁(𝒪_T(-D))`, the same convention as the auxiliary hyperplane class
`AlgebraicGeometry.Etale.projectiveLineHyperplaneClassAux`; the cycle class `δ = c₁(𝒪_T(D))` of
the notes is its negative (`AlgebraicGeometry.Etale.cartierKummerCycleClass`). -/
noncomputable def cartierKummerCycleClassAux (hP : SupportedTatePure Λ 1 i) :
    constantComplex Λ T ⟶ (tateObject Λ T 1)⟦(2 : ℤ)⟧ :=
  cartierKummerClass Λ i hP ≫
    (rightDerivedUpperShriekAdjunction Λ i).counit.app ((tateObject Λ T 1)⟦(2 : ℤ)⟧)

/-- The *cycle class* `δ = c₁(𝒪_T(D)) : Λ_T ⟶ Λ_T(1)[2]` of an effective Cartier divisor
`i : D ⟶ T` satisfying the purity hypothesis, with the sign of the notes (the class of `𝒪(D)`,
as in the notes' cycle class of a Cartier divisor): the negative of the
forgotten-supports Kummer class `AlgebraicGeometry.Etale.cartierKummerCycleClassAux`, which is
`c₁(𝒪_T(-D))`. -/
noncomputable def cartierKummerCycleClass (hP : SupportedTatePure Λ 1 i) :
    constantComplex Λ T ⟶ (tateObject Λ T 1)⟦(2 : ℤ)⟧ :=
  -cartierKummerCycleClassAux Λ i hP

end CycleClass

section Diagonal

variable [HasKummerClass.IsNormalized Λ] (S : Scheme.{u}) [HasInvertibleExponent Λ S]

omit [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] in
/-- The diagonal `ℙ¹_S ⟶ ℙ¹_{ℙ¹_S}` is a regular immersion of codimension one if the diagonal
`ℙ¹_S ⟶ ℙ¹_S ×_S ℙ¹_S` is (for instance by `AlgebraicGeometry.isRegularImmersion_diagonal`). -/
theorem isRegularImmersion_projectiveSpaceDiagonal
    [IsRegularImmersion 1 (pullback.diagonal (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))] :
    IsRegularImmersion 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S) := by
  rw [← Category.comp_id (ProjectiveSpace.diagonal _ S),
    ← (ProjectiveSpace.isoPullback (Option (ULift.{u} (Fin 1))) S).hom_inv_id,
    ProjectiveSpace.diagonal_isoPullback_hom_assoc]
  infer_instance

omit [HasKummerClass.IsNormalized Λ] in
/-- The purity hypothesis for the diagonal `ℙ¹_S ⟶ ℙ¹_{ℙ¹_S}` follows from the one for the
diagonal `ℙ¹_S ⟶ ℙ¹_S ×_S ℙ¹_S`, through `ℙ¹_{ℙ¹_S} ≅ ℙ¹_S ×_S ℙ¹_S`
(`AlgebraicGeometry.ProjectiveSpace.isoPullback`). -/
theorem supportedTatePure_projectiveSpaceDiagonal
    [HasInvertibleExponent Λ
      (pullback (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))]
    [IsClosedImmersion (pullback.diagonal (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))]
    [IsClosedImmersion (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)]
    (h : SupportedTatePure Λ 1 (pullback.diagonal (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))) :
    SupportedTatePure Λ 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S) :=
  h.of_etale (ProjectiveSpace.isoPullback (Option (ULift.{u} (Fin 1))) S).hom _ (𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩)

/-- **The diagonal class restricted to `ℙ¹_Z`.** For the section at infinity `ι : Z ⟶ ℙ¹_S`, the
restriction of the class with supports of the diagonal of `ℙ¹_S` along
`map ι : ℙ¹_Z ⟶ ℙ¹_{ℙ¹_S}` is the class with supports of the section at infinity of `ℙ¹_Z`
(`AlgebraicGeometry.Etale.chartBoundarySupportedClass`). -/
theorem restrictSupportedClass_cartierKummerClass_diagonal
    [IsRegularImmersion 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)]
    (hP : SupportedTatePure Λ 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)) :
    restrictSupportedClass Λ
        (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) (ProjectiveSpace.lineInfinityι S))
        (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)
        (ProjectiveSpace.lineInfinityι (ProjectiveSpace.lineInfinity S)) _
        (ProjectiveSpace.isPullback_lineInfinityι_diagonal S)
        (leftDerivedUpperStarConstantComplexIso Λ _).inv (leftDerivedUpperStarTateTwoIso Λ _)
        (cartierKummerClass Λ _ hP) =
      chartBoundarySupportedClass Λ
        (ProjectiveSpace.lineInfinityOpen (ProjectiveSpace.lineInfinity S))
        (ProjectiveSpace.coordRatio (Option (ULift.{u} (Fin 1))) (ProjectiveSpace.lineInfinity S)
          (some ⟨0⟩) none) := by
  set Z := ProjectiveSpace.lineInfinity S
  set V := ProjectiveSpace.lineInfinityOpen Z
  set s := ProjectiveSpace.lineInfinityCoord Z
  set Δ := ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S
  set ι' := ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) (ProjectiveSpace.lineInfinityι S)
  have hid := isPullback_id_comp_of_mono (V.toScheme.zeroLocusSubschemeι {s}) V.ι
  refine restrictSupportedClass_injective_of_isOpenImmersion Λ
    (V.toScheme.zeroLocusSubschemeι {s}) V.ι (leftDerivedUpperStarTateTwoIso Λ V.ι) ?_
  rw [restrictSupportedClass_chartBoundarySupportedClass]
  refine Eq.trans (restrictSupportedClass_comp_tateShift Λ (c := 1) V.ι ι' (V.ι ≫ ι') rfl Δ
    (ProjectiveSpace.lineInfinityι Z) (V.toScheme.zeroLocusSubschemeι {s}) _
    (ProjectiveSpace.isPullback_lineInfinityι_diagonal S) (𝟙 _) hid _
    (hid.paste_horiz (ProjectiveSpace.isPullback_lineInfinityι_diagonal S)) _).symm ?_
  -- the frame of the diagonal at `(∞, ∞)`
  obtain ⟨toZ, hF⟩ := ProjectiveSpace.exists_isPullback_diagonalChart S
  let F : Δ.EtaleFrame 1 :=
    { U := 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin 1); S))
      e := ProjectiveSpace.diagonalChart S
      etale := inferInstance
      f := fun _ ↦ ProjectiveSpace.diagonalChartEquation S
      toZ := toZ
      isPullback := hF }
  have hs : (ProjectiveSpace.lineInfinityDiagonalLift S).appTop '' Set.range F.f = {s} := by
    rw [Set.range_const, Set.image_singleton, ProjectiveSpace.lineInfinityDiagonalLift_appTop]
  have hm := Scheme.isPullback_zeroLocusSubschemeι (ProjectiveSpace.lineInfinityDiagonalLift S)
    (Set.range F.f) {s} hs
  have hout : IsPullback (Scheme.Hom.zeroLocusSubschemeMap _ _ _ hs ≫ toZ)
      (V.toScheme.zeroLocusSubschemeι {s}) Δ (V.ι ≫ ι') := by
    rw [← ProjectiveSpace.lineInfinityDiagonalLift_diagonalChart]
    exact hm.paste_horiz hF
  have key (g' : V.toScheme.zeroLocusSubscheme {s} ⟶ ℙ(Option (ULift.{u} (Fin 1)); S))
      (hg' : IsPullback g' (V.toScheme.zeroLocusSubschemeι {s}) Δ (V.ι ≫ ι')) :
      restrictSupportedClass Λ (V.ι ≫ ι') Δ _ g' hg'
          (leftDerivedUpperStarConstantComplexIso Λ _).inv
          (leftDerivedUpperStarTateShiftIso Λ _ ((1 : ℕ) : ℤ)) (cartierKummerClass Λ Δ hP) =
        shiftSupportedClass Λ _ 2 (kummerBoundary Λ s) := by
    obtain rfl : g' = Scheme.Hom.zeroLocusSubschemeMap _ _ _ hs ≫ toZ := by
      rw [← cancel_mono Δ, hg'.w, hout.w]
    have hfr := frameRestriction_cartierKummerClass Λ Δ hP F
    dsimp only [frameRestriction, F] at hfr
    rw [restrictSupportedClass_comp_tateShift Λ (c := 1)
      (ProjectiveSpace.lineInfinityDiagonalLift S)
      (ProjectiveSpace.diagonalChart S) (V.ι ≫ ι')
      (ProjectiveSpace.lineInfinityDiagonalLift_diagonalChart S).symm Δ _ _ toZ hF _ hm _ hg',
      hfr]
    have hA := restrictSupportedClass_kummerBoundaryProduct_one Λ _ _ s
      (ProjectiveSpace.lineInfinityDiagonalLift_appTop S) _ hm
    have hτ : leftDerivedUpperStarTateShiftIso Λ (ProjectiveSpace.lineInfinityDiagonalLift S)
        ((1 : ℕ) : ℤ) ≪≫ eqToIso (by norm_num) =
        leftDerivedUpperStarTateShiftIso Λ (ProjectiveSpace.lineInfinityDiagonalLift S)
          ((1 : ℕ) : ℤ) :=
      Iso.ext (Category.comp_id _)
    rw [hτ] at hA
    exact hA
  exact key _ _

/-- **The diagonal cycle class restricted to `ℙ¹_Z`.** For the section at infinity
`ι : Z ⟶ ℙ¹_S`, the pullback along `map ι : ℙ¹_Z ⟶ ℙ¹_{ℙ¹_S}` of the cycle class of the diagonal
is the hyperplane class of `ℙ¹_Z`. -/
theorem cartierKummerCycleClass_diagonal_baseChange
    [IsRegularImmersion 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)]
    (hP : SupportedTatePure Λ 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)) :
    (leftDerivedUpperStarConstantComplexIso Λ
        (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) (ProjectiveSpace.lineInfinityι S))).inv ≫
      (L((ProjectiveSpace.map (Option (ULift.{u} (Fin 1)))
          (ProjectiveSpace.lineInfinityι S))^*[ModuleCat.{u + 1} Λ])).map
        (cartierKummerCycleClassAux Λ _ hP) ≫
      (leftDerivedUpperStarTateTwoIso Λ
        (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) (ProjectiveSpace.lineInfinityι S))).hom =
    projectiveLineHyperplaneClassAux Λ (ProjectiveSpace.lineInfinity S) := by
  rw [projectiveLineHyperplaneClassAux, chartBoundaryClass_eq,
    ← restrictSupportedClass_cartierKummerClass_diagonal Λ S hP, restrictSupportedClass_comp_counit,
    cartierKummerCycleClassAux]

/-- The auxiliary trace of `ℙ¹_S` is normalized by `Tr_q^{aux} ∘ (-h)♭ = 1`, for the adjoint
`(-h)♭ : Λ_S ⟶ Rq_*(Λ_{ℙ¹_S}(1)[2])` of the auxiliary hyperplane class. -/
lemma homEquiv_projectiveLineHyperplaneClassAux_comp_projectiveLineTraceAux :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).hom ≫
          projectiveLineHyperplaneClassAux Λ S) ≫
      projectiveLineTraceAux Λ S = 𝟙 _ := by
  have h : (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).hom ≫
          projectiveLineHyperplaneClassAux Λ S) =
      biprod.inr ≫ projectiveLineDecompositionMapAux Λ S := by
    rw [projectiveLineDecompositionMapAux, biprod.inr_desc]
  rw [h, projectiveLineTraceAux, Category.assoc, IsIso.hom_inv_id_assoc, biprod.inr_snd]

/-- **The restriction of the diagonal integral to the section at infinity.** The pullback along
the section at infinity `ι : Z ⟶ ℙ¹_S` of the endomorphism
`Λ_P ⟶ Rp_* Λ_W ⟶ Rp_*(Λ_W(1)[2]) ⟶ Λ_P` of `Λ_P`, `P = ℙ¹_S`, `W = ℙ¹_P`, given by the cycle
class of the diagonal and the trace of `p : W ⟶ P`, is the identity. -/
theorem leftDerivedUpperStar_lineInfinityι_map_diagonalIntegral
    [IsRegularImmersion 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)]
    (hP : SupportedTatePure Λ 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)) :
    (L((ProjectiveSpace.lineInfinityι S)^*[ModuleCat.{u + 1} Λ])).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
            ℙ(Option (ULift.{u} (Fin 1)); S))).homEquiv _ _
          ((leftDerivedUpperStarConstantComplexIso Λ
              (ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
                ℙ(Option (ULift.{u} (Fin 1)); S))).hom ≫
            cartierKummerCycleClassAux Λ _ hP) ≫
        projectiveLineTraceAux Λ ℙ(Option (ULift.{u} (Fin 1)); S)) = 𝟙 _ := by
  have sq := ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1)))
    (ProjectiveSpace.lineInfinityι S)
  have hC := leftDerivedUpperStar_map_unit_comp_map_comp_derivedBaseChangeMap_comp sq.toCommSq
    ((leftDerivedUpperStarConstantComplexIso Λ
        (ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
          ℙ(Option (ULift.{u} (Fin 1)); S))).hom ≫ cartierKummerCycleClassAux Λ _ hP)
    ((leftDerivedUpperStarConstantComplexIso Λ
        (ℙ(Option (ULift.{u} (Fin 1)); ProjectiveSpace.lineInfinity S) ↘
          ProjectiveSpace.lineInfinity S)).hom ≫
      projectiveLineHyperplaneClassAux Λ (ProjectiveSpace.lineInfinity S))
    (leftDerivedUpperStarConstantComplexIso Λ (ProjectiveSpace.lineInfinityι S)).hom
    (leftDerivedUpperStarTateTwoIso Λ
      (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) (ProjectiveSpace.lineInfinityι S))).hom
    (by
      rw [← cartierKummerCycleClass_diagonal_baseChange Λ S hP, Functor.map_comp, Category.assoc,
        ← reassoc_of% (derivedSquareUpperStarIso_hom_app_constantComplex Λ sq.toCommSq),
        Iso.hom_inv_id_assoc])
  have hD := homEquiv_projectiveLineHyperplaneClassAux_comp_projectiveLineTraceAux Λ
    (ProjectiveSpace.lineInfinity S)
  rw [Adjunction.homEquiv_unit, Category.assoc] at hD
  rw [Functor.map_comp, projectiveLineTraceAux_baseChange Λ (ProjectiveSpace.lineInfinityι S),
    Adjunction.homEquiv_unit, reassoc_of% hC,
    reassoc_of% hD, Iso.hom_inv_id]

/-- Blueprint `lemma-class-diagonal-projective-line` (`lemma-class-diagonal-projective-line--1`
(3)), *the first integral of the diagonal class*: for `P = ℙ¹_S`, `W = ℙ¹_P ≅ P ×_S P` with first
projection `p : W ⟶ P`, and the diagonal `Δ : P ⟶ W` satisfying the purity hypothesis, the composite

`Λ_P ⟶ Rp_* Lp^* Λ_P ≅ Rp_* Λ_W ⟶ Rp_*(Λ_W(1)[2]) ⟶ Λ_P`

of the adjoint of the cycle class `δ` of `Δ` (`AlgebraicGeometry.Etale.cartierKummerCycleClassAux`)
and the trace of `p` (`AlgebraicGeometry.Etale.projectiveLineTraceAux`) is the identity. -/
theorem projectiveLineTraceAux_diagonal
    [IsRegularImmersion 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)]
    (hP : SupportedTatePure Λ 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
          ℙ(Option (ULift.{u} (Fin 1)); S))).homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ
            (ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
              ℙ(Option (ULift.{u} (Fin 1)); S))).hom ≫
          cartierKummerCycleClassAux Λ _ hP) ≫
      projectiveLineTraceAux Λ ℙ(Option (ULift.{u} (Fin 1)); S) = 𝟙 _ :=
  eq_of_leftDerivedUpperStar_lineInfinityι_map_eq Λ S (by
    rw [leftDerivedUpperStar_lineInfinityι_map_diagonalIntegral Λ S hP,
    CategoryTheory.Functor.map_id])

/-- The exchange of the factors of `W = ℙ¹_P ≅ P ×_S P`
(`AlgebraicGeometry.ProjectiveSpace.diagonalSwap`) fixes the cycle class of the diagonal. -/
theorem cartierKummerCycleClass_diagonalSwap
    [IsRegularImmersion 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)]
    (hP : SupportedTatePure Λ 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)) :
    (leftDerivedUpperStarConstantComplexIso Λ
        (ProjectiveSpace.diagonalSwap (Option (ULift.{u} (Fin 1))) S)).inv ≫
      (L((ProjectiveSpace.diagonalSwap (Option (ULift.{u} (Fin 1))) S)^*[ModuleCat.{u + 1} Λ])).map
        (cartierKummerCycleClassAux Λ _ hP) ≫
      (leftDerivedUpperStarTateTwoIso Λ
        (ProjectiveSpace.diagonalSwap (Option (ULift.{u} (Fin 1))) S)).hom =
    cartierKummerCycleClassAux Λ _ hP := by
  have hsq : IsPullback (𝟙 _) (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)
      (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)
      (ProjectiveSpace.diagonalSwap (Option (ULift.{u} (Fin 1))) S) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h₁ := restrictSupportedClass_comp_counit
    (ProjectiveSpace.diagonalSwap (Option (ULift.{u} (Fin 1))) S) _ _ _ hsq
    (leftDerivedUpperStarConstantComplexIso Λ _).inv
    (leftDerivedUpperStarTateShiftIso Λ _ 1) (cartierKummerClass Λ _ hP)
  rw [restrictSupportedClass_cartierKummerClass Λ _ hP _ _ _ hsq hP] at h₁
  exact h₁.symm

/-- Blueprint `lemma-class-diagonal-projective-line` (`lemma-class-diagonal-projective-line--1`
(3)), *the second integral of the diagonal class*. The second projection `p₂ = map (P ↘ S) : W ⟶ P`
of `W = ℙ¹_P ≅ P ×_S P` is the first projection `p₁ = W ↘ P` composed with the exchange `σ` of the
factors (`AlgebraicGeometry.ProjectiveSpace.diagonalSwap`), an isomorphism of `P`-schemes
`(W, p₂) ≅ (W, p₁)`. Transported along `σ`, the trace of `p₂` is the trace of `p₁` and the cycle
class `δ` of the diagonal becomes `σ^* δ`; the composite

`Λ_P ⟶ Rp₁_* Λ_W ⟶ Rp₁_*(Λ_W(1)[2]) ⟶ Λ_P`

of the adjoint of `σ^* δ` and the trace of `p₁` is the identity. -/
theorem projectiveLineTraceAux_diagonal_swap
    [IsRegularImmersion 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)]
    (hP : SupportedTatePure Λ 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
          ℙ(Option (ULift.{u} (Fin 1)); S))).homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ
            (ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
              ℙ(Option (ULift.{u} (Fin 1)); S))).hom ≫
          (leftDerivedUpperStarConstantComplexIso Λ
            (ProjectiveSpace.diagonalSwap (Option (ULift.{u} (Fin 1))) S)).inv ≫
          (L((ProjectiveSpace.diagonalSwap (Option (ULift.{u} (Fin 1))) S)^*[ModuleCat.{u + 1}
            Λ])).map (cartierKummerCycleClassAux Λ _ hP) ≫
          (leftDerivedUpperStarTateTwoIso Λ
            (ProjectiveSpace.diagonalSwap (Option (ULift.{u} (Fin 1))) S)).hom) ≫
      projectiveLineTraceAux Λ ℙ(Option (ULift.{u} (Fin 1)); S) = 𝟙 _ := by
  rw [cartierKummerCycleClass_diagonalSwap Λ S hP]
  exact projectiveLineTraceAux_diagonal Λ S hP

/-- The trace of `ℙ¹_S` is normalized by `Tr_q ∘ h♭ = 1`, for the adjoint
`h♭ : Λ_S ⟶ Rq_*(Λ_{ℙ¹_S}(1)[2])` of the hyperplane class `h = c₁(𝒪(1))` of the notes: from the
auxiliary normalisation by the two signs. -/
lemma homEquiv_projectiveLineHyperplaneClass_comp_projectiveLineTrace :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)).hom ≫
          projectiveLineHyperplaneClass Λ S) ≫
      projectiveLineTrace Λ S = 𝟙 _ := by
  have := homEquiv_projectiveLineHyperplaneClassAux_comp_projectiveLineTraceAux Λ S
  simp only [projectiveLineHyperplaneClass, projectiveLineTrace_eq_neg, Preadditive.comp_neg,
    Adjunction.homEquiv_unit, Functor.map_neg, Preadditive.neg_comp, neg_neg] at this ⊢
  exact this

/-- *The first diagonal integral*, with the cycle
class `δ = c₁(𝒪(Δ))` and the trace of the notes: `Tr_p(δ) = 1`. From the auxiliary statement
`AlgebraicGeometry.Etale.projectiveLineTraceAux_diagonal` by the two signs. -/
theorem projectiveLineTrace_diagonal
    [IsRegularImmersion 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)]
    (hP : SupportedTatePure Λ 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
          ℙ(Option (ULift.{u} (Fin 1)); S))).homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ
            (ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
              ℙ(Option (ULift.{u} (Fin 1)); S))).hom ≫
          cartierKummerCycleClass Λ _ hP) ≫
      projectiveLineTrace Λ ℙ(Option (ULift.{u} (Fin 1)); S) = 𝟙 _ := by
  have := projectiveLineTraceAux_diagonal Λ S hP
  simp only [cartierKummerCycleClass, projectiveLineTrace_eq_neg, Adjunction.homEquiv_unit,
    Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp, neg_neg] at this ⊢
  exact this

/-- *The second diagonal integral* (the swapped
factor), with the cycle class and the trace of the notes. From
`AlgebraicGeometry.Etale.projectiveLineTraceAux_diagonal_swap` by the two signs. -/
theorem projectiveLineTrace_diagonal_swap
    [IsRegularImmersion 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)]
    (hP : SupportedTatePure Λ 1 (ProjectiveSpace.diagonal (Option (ULift.{u} (Fin 1))) S)) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
          ℙ(Option (ULift.{u} (Fin 1)); S))).homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ
            (ℙ(Option (ULift.{u} (Fin 1)); ℙ(Option (ULift.{u} (Fin 1)); S)) ↘
              ℙ(Option (ULift.{u} (Fin 1)); S))).hom ≫
          (leftDerivedUpperStarConstantComplexIso Λ
            (ProjectiveSpace.diagonalSwap (Option (ULift.{u} (Fin 1))) S)).inv ≫
          (L((ProjectiveSpace.diagonalSwap (Option (ULift.{u} (Fin 1))) S)^*[ModuleCat.{u + 1}
            Λ])).map (cartierKummerCycleClass Λ _ hP) ≫
          (leftDerivedUpperStarTateTwoIso Λ
            (ProjectiveSpace.diagonalSwap (Option (ULift.{u} (Fin 1))) S)).hom) ≫
      projectiveLineTrace Λ ℙ(Option (ULift.{u} (Fin 1)); S) = 𝟙 _ := by
  have := projectiveLineTraceAux_diagonal_swap Λ S hP
  simp only [cartierKummerCycleClass, projectiveLineTrace_eq_neg, Adjunction.homEquiv_unit,
    Functor.map_neg, Preadditive.comp_neg, Preadditive.neg_comp, neg_neg] at this ⊢
  exact this

end Diagonal

end Etale

end AlgebraicGeometry
