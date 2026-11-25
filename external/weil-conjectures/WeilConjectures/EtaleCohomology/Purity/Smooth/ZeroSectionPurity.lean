/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomology
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineAcyclicity

/-!
# Relative purity for the zero section of the affine line

For a scheme `B` on which the exponent of the finite coefficient ring `Λ` is invertible and a
normalized rank-one datum, the adjoint `Λ_{V(t)} ⟶ Rs^! (Λ(1)[2])` of the Kummer boundary of the
coordinate `t` of `𝔸¹_B` is an isomorphism, `s : V(t) ⟶ 𝔸¹_B` the zero section
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_hasInvertibleExponent`).
The normalisation
`AlgebraicGeometry.Etale.HasKummerClass.IsNormalized` asserts this only for `B` separated and
locally of finite type over a field; this is the relative purity of SGA 4 XVI 3.7 for the zero
section of `𝔸¹` (Fu, *Étale cohomology theory*, 8.4; Milne, *Étale cohomology*, VI.5).

## The argument

We go through the projective line `q : ℙ¹_B ⟶ B`, the section at infinity `i : B ≅ Z ⟶ ℙ¹_B`
and its complement `p : 𝔸¹_B ⟶ B`. The decomposition map
`(1, h) : Λ_B(1)[2] ⊕ Λ_B ⟶ Rq_*(Λ(1)[2])` is an isomorphism over every base
(`AlgebraicGeometry.Etale.isIso_projectiveLineDecompositionMap`, proved at the geometric points by
proper base change). The direct image by `q` of the localization triangle of `i` is a
distinguished triangle `Rq_* Ri_! Ri^! K ⟶ Rq_* K ⟶ Rp_* Lp^* K ⟶` receiving a map from the
split triangle `Λ_B ⟶ Λ_B ⊕ Λ_B(1)[2] ⟶ Λ_B(1)[2] ⟶`; on the middle terms it is the
decomposition isomorphism and on the third terms it is the unit `Λ_B(1)[2] ⟶ Rp_* Lp^*`, an
isomorphism by homotopy invariance. Hence it is an isomorphism on the first terms, which says
that the adjoint of the class of the section at infinity is an isomorphism
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_of_isIso_biprodDesc`). Restricting to the chart
at infinity `𝔸¹_B ⟶ ℙ¹_B`, this class becomes the Kummer boundary of the coordinate, up to an
automorphism of the support.

The one input which is not proved here is the homotopy invariance of the étale cohomology of the
affine line over an arbitrary base
(`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine_of_hasInvertibleExponent`),
proved in the repository only over
fields.

## Main statements

- `AlgebraicGeometry.Etale.isIso_supportedClassMap_of_isIso_biprodDesc`: the converse of the
  decomposition criterion `AlgebraicGeometry.Etale.isIso_biprodDesc_of_isIso_supportedClassMap`.
- `AlgebraicGeometry.Etale.isIso_supportedClassMap_lineInfinity`: the class of the section at
  infinity of `ℙ¹_B` is a fundamental class.
- `AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_hasInvertibleExponent`:
  relative purity for the
  zero section of `𝔸¹_B`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Section

variable {X S Z : Scheme.{u}} (a : X ⟶ S) (x : Z ⟶ X) [IsClosedImmersion x] [IsIso (x ≫ a)]

/-- **A class of a section which generates is a fundamental class.** Converse of
`AlgebraicGeometry.Etale.isIso_unit_comp_map_of_isIso_supportedClassMap_of_isIso`: let
`x : Z ⟶ X` be a closed immersion with `x ≫ a : Z ⟶ S` an isomorphism and
`γ : Λ_X ⟶ Rx_! Rx^! L` a class supported on `x`. If
`U ⟶ Ra_* La^* U ≅ Ra_* Λ_X ⟶ Ra_* Rx_! Rx^! L` is an isomorphism, then so is the adjoint
`Λ_Z ⟶ Rx^! L` of `γ`. Indeed, up to isomorphisms, this map is the image of the adjoint by the
equivalence `R(x ≫ a)_*`. -/
lemma isIso_supportedClassMap_of_isIso_unit_comp_map
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {U : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : (L((a)^*[ModuleCat.{u + 1} Λ])).obj U ≅ constantComplex Λ X)
    (γ : constantComplex Λ X ⟶
      (R(x)_![ModuleCat.{u + 1} Λ]).obj ((R(x)^![Λ]).obj L))
    (h : IsIso ((derivedUpperStarLowerStarAdjunction _ a).unit.app U ≫
      (R((a)_*[ModuleCat.{u + 1} Λ])).map (e.hom ≫ γ))) :
    IsIso (supportedClassMap Λ x γ) := by
  let c := HasCompactification.compactification x
  let adjGI := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.g).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.i)
  let adjC := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).comp adjGI
  have : (L((x ≫ a)^*[ModuleCat.{u + 1} Λ])).IsEquivalence := inferInstance
  have : (L((a)^*[ModuleCat.{u + 1} Λ]) ⋙ L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙
      L((c.i)^*[ModuleCat.{u + 1} Λ])).IsEquivalence :=
    Functor.isEquivalence_of_iso ((leftDerivedUpperStarComp _ x a (x ≫ a) rfl) ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarComp _ c.i c.g x c.comm))
  have hu : IsIso adjC.unit := adjC.unit_isIso_of_L_fully_faithful
  let F := (rightDerivedLowerShriekToLowerStarComp (ModuleCat.{u + 1} Λ) x).app
    ((R(x)^![Λ]).obj L)
  have hfc : γ ≫ F = adjGI.unit.app _ ≫
      (R((c.i)_*[ModuleCat.{u + 1} Λ]) ⋙ R((c.g)_*[ModuleCat.{u + 1} Λ])).map
        ((compactificationConstantComplexIso Λ x).hom ≫ supportedClassMap Λ x γ) := by
    rw [supportedClassMap, Iso.hom_inv_id_assoc, rightDerivedLowerShriekTranspose]
    exact ((Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)).symm
  have hn := adjGI.unit.naturality e.hom
  simp only [Functor.id_map, Functor.comp_map] at hn
  have inner : e.hom ≫ γ =
      adjGI.unit.app _ ≫
        (R((c.i)_*[ModuleCat.{u + 1} Λ]) ⋙ R((c.g)_*[ModuleCat.{u + 1} Λ])).map
          ((L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙ L((c.i)^*[ModuleCat.{u + 1} Λ])).map
            e.hom ≫
          (compactificationConstantComplexIso Λ x).hom ≫ supportedClassMap Λ x γ) ≫ inv F := by
    rw [← cancel_mono F]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hfc]
    simp only [Functor.comp_map, Functor.map_comp] at hn ⊢
    rw [reassoc_of% hn]
  have key : (derivedUpperStarLowerStarAdjunction _ a).unit.app U ≫
      (R((a)_*[ModuleCat.{u + 1} Λ])).map (e.hom ≫ γ) =
      adjC.unit.app _ ≫ (R((a)_*[ModuleCat.{u + 1} Λ])).map
        ((R((c.i)_*[ModuleCat.{u + 1} Λ]) ⋙ R((c.g)_*[ModuleCat.{u + 1} Λ])).map
          ((L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙ L((c.i)^*[ModuleCat.{u + 1} Λ])).map
            e.hom ≫
          (compactificationConstantComplexIso Λ x).hom ≫ supportedClassMap Λ x γ) ≫ inv F) := by
    rw [inner]
    simp only [adjC, adjGI, Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  rw [key, isIso_comp_left_iff, (R((a)_*[ModuleCat.{u + 1} Λ])).map_comp,
    isIso_comp_right_iff] at h
  have := adjC.isEquivalence_right_of_isEquivalence_left
  rw [← isIso_comp_left_iff ((L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙
      L((c.i)^*[ModuleCat.{u + 1} Λ])).map e.hom ≫ (compactificationConstantComplexIso Λ x).hom),
    ← isIso_iff_of_reflects_iso _ ((R((c.i)_*[ModuleCat.{u + 1} Λ]) ⋙
      R((c.g)_*[ModuleCat.{u + 1} Λ])) ⋙ R((a)_*[ModuleCat.{u + 1} Λ])), Category.assoc]
  exact h

end Section

/-- **The converse of the decomposition criterion.** Let `q : X ⟶ S`, let `i : Z ⟶ X` be a
closed immersion with `i ≫ q` an isomorphism and `j : U ⟶ X` an open immersion onto the
complement of `Z`, with `p = j ≫ q`. Let `ε : Lq^* M ≅ K`, `e : Lq^* N ≅ Λ_X` and let
`γ : Λ_X ⟶ Ri_! Ri^! K` be a class with supports. If the unit `M ⟶ Rp_* Lp^* M` and

`(η_M ≫ Rq_* ε, η_N ≫ Rq_*(e ≫ γ ≫ counit)) : M ⊕ N ⟶ Rq_* K`

are isomorphisms, then so is the adjoint `Λ_Z ⟶ Ri^! K` of `γ`. Indeed the split triangle
`N ⟶ N ⊕ M ⟶ M ⟶` maps to the image by `Rq_*` of the localization triangle of `K`, by
isomorphisms on the second and third terms, hence also on the first terms
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_of_isIso_unit_comp_map`). -/
theorem isIso_supportedClassMap_of_isIso_biprodDesc {X S Z U : Scheme.{u}} (q : X ⟶ S)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIso (i ≫ q)] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (p : U ⟶ S) (hp : j ≫ q = p)
    {M N : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ε : (L((q)^*[ModuleCat.{u + 1} Λ])).obj M ≅ K)
    (e : (L((q)^*[ModuleCat.{u + 1} Λ])).obj N ≅ constantComplex Λ X)
    (hM : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app M))
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj K))
    (hd : IsIso (biprod.desc
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app M ≫
        (R((q)_*[ModuleCat.{u + 1} Λ])).map ε.hom)
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app N ≫
        (R((q)_*[ModuleCat.{u + 1} Λ])).map
          (e.hom ≫ γ ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app K)))) :
    IsIso (supportedClassMap Λ i γ) := by
  refine isIso_supportedClassMap_of_isIso_unit_comp_map Λ q i e γ ?_
  have hT : Triangle.mk ((R((q)_*[ModuleCat.{u + 1} Λ])).map
      ((rightDerivedUpperShriekAdjunction Λ i).counit.app K))
      ((R((q)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app K))
      (localizationTriangleLowerStar Λ q i j hij K).mor₃ ∈ distTriang _ :=
    localizationTriangleLowerStar_mem_distTriang Λ q i j hij K
  have h₁₂ := comp_distTriang_mor_zero₁₂ _ hT
  have h₂₃ := comp_distTriang_mor_zero₂₃ _ hT
  simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃] at h₁₂ h₂₃
  have h₃ : IsIso (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app M ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map ε.hom) ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app K)) := by
    have := Adjunction.isIso_unit_app_comp_map_unit_app_of_iso
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
      (leftDerivedUpperStarComp _ j q p hp.symm) M
    rw [Category.assoc, ← Functor.map_comp, ← Adjunction.unit_naturality, Functor.map_comp,
      ← Category.assoc]
    infer_instance
  exact isIso₁_of_isIso₂₃ (Triangle.homMk (binaryBiproductTriangle N M)
    (Triangle.mk ((R((q)_*[ModuleCat.{u + 1} Λ])).map
      ((rightDerivedUpperShriekAdjunction Λ i).counit.app K))
      ((R((q)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app K))
      (localizationTriangleLowerStar Λ q i j hij K).mor₃)
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app N ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map (e.hom ≫ γ))
    ((biprod.braiding N M).hom ≫ biprod.desc
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app M ≫
        (R((q)_*[ModuleCat.{u + 1} Λ])).map ε.hom)
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app N ≫
        (R((q)_*[ModuleCat.{u + 1} Λ])).map
          (e.hom ≫ γ ≫ (rightDerivedUpperShriekAdjunction Λ i).counit.app K)))
    (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app M ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map ε.hom) ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app K))
    (by simp [biprod.braiding]) (by
      refine biprod.hom_ext' _ _ ?_ ?_
      · simpa [biprod.braiding] using (((derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} Λ) q).unit.app N ≫ (R((q)_*[ModuleCat.{u + 1} Λ])).map (e.hom ≫ γ)) ≫=
          h₁₂).symm
      · simp [biprod.braiding])
    (by simpa using (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app M ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map ε.hom) ≫= h₂₃).symm))
    (binaryBiproductTriangle_distinguished N M) hT (IsIso.comp_isIso' inferInstance hd) h₃
section HomotopyInvariance

variable [HasTateTwist Λ]

/-- **Homotopy invariance of the affine line over an arbitrary base**, for the coefficients
`Λ(1)`: for every scheme `S` on which the exponent of `Λ` is invertible, the unit
`Λ_S(1) ⟶ Rp_* Lp^* Λ_S(1)` of the projection `p : 𝔸¹_S ⟶ S` is an isomorphism.

This is the acyclicity of the affine line (SGA 4 XV 2.1–2.2; Milne, *Étale cohomology*, VI.4;
Fu, *Étale cohomology theory*, 7.7), a step of the smooth base change theorem; in this
repository it is proved only over separably closed fields and, by Künneth, over schemes of
finite type over them (`AlgebraicGeometry.Etale.isIso_unit_affineLine_of_cohomology`). Over a
general base it amounts to the compatibility of `Rp_*` with base change to the geometric points
(equivalently, by compactifying `𝔸¹_S ⊆ ℙ¹_S` and proper base change, of `Rj_*` for the
complement `j` of the section at infinity: Deligne, SGA 4½, [Th. finitude] Appendice 1.3.3;
SGA 4 XVI 3.7). It is the only input of the relative purity of this file which is not proved. -/
theorem isIso_unit_tateObject_affineLine_of_hasInvertibleExponent
    (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); S) ↘ S)).unit.app (tateObject Λ S 1)) :=
  isIso_unit_tateObject_affineLine_of_strictlyHenselian Λ S

/-- Homotopy invariance of the affine line for `Λ(1)[2]`
(`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine_of_hasInvertibleExponent`). -/
theorem isIso_unit_tateObject_shift_affineLine_of_hasInvertibleExponent (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); S) ↘ S)).unit.app ((tateObject Λ S 1)⟦(2 : ℤ)⟧)) := by
  have := isIso_unit_tateObject_affineLine_of_hasInvertibleExponent Λ S
  rw [← Adjunction.unit_app_shift_commShiftIso_inv_app]
  infer_instance

end HomotopyInvariance

section Purity

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ]

/-- **The class of the section at infinity of `ℙ¹_S` is a fundamental class**, over every base
`S` on which the exponent of `Λ` is invertible: the adjoint `Λ_Z ⟶ Ri^!(Λ(1)[2])` of the class
with supports of the section at infinity `i : Z ⟶ ℙ¹_S`
(`AlgebraicGeometry.Etale.chartBoundarySupportedClass`) is an isomorphism. This follows from the
decomposition of the cohomology of the projective line
(`AlgebraicGeometry.Etale.isIso_projectiveLineDecompositionMap`) and the homotopy invariance of
its complement `𝔸¹_S`
(`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine_of_hasInvertibleExponent`), by
`AlgebraicGeometry.Etale.isIso_supportedClassMap_of_isIso_biprodDesc`. -/
theorem isIso_supportedClassMap_lineInfinity (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    IsIso (supportedClassMap Λ (ProjectiveSpace.lineInfinityι S)
      (chartBoundarySupportedClass Λ (ProjectiveSpace.lineInfinityOpen S)
        (ProjectiveSpace.coordRatio (Option (ULift.{u} (Fin 1))) S (some ⟨0⟩) none))) := by
  have hdec := isIso_projectiveLineDecompositionMapAux Λ S
  rw [projectiveLineDecompositionMapAux, Adjunction.homEquiv_unit, projectiveLineHyperplaneClassAux,
    chartBoundaryClass_eq] at hdec
  refine isIso_supportedClassMap_of_isIso_biprodDesc Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
    (ProjectiveSpace.lineInfinityι S) (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)
    (ProjectiveSpace.range_lineInfinityι_eq_compl_range_toRelativeProjectiveSpace _) _
    (AffineSpace.toRelativeProjectiveSpace_over _ _)
    (leftDerivedUpperStarTateTwoIso Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))
    (leftDerivedUpperStarConstantComplexIso Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))
    (isIso_unit_tateObject_shift_affineLine_of_hasInvertibleExponent Λ S) _ ?_
  exact hdec

omit [HasKummerClass.IsNormalized Λ] in
/-- **The restricted class of the section at infinity and the Kummer boundary.** For
`x : S' ⟶ S`, the adjoint of the restriction along `ℙ¹_{S'} ⟶ ℙ¹_S` of the class with supports
of the section at infinity is an isomorphism if and only if the adjoint of the Kummer boundary of
the coordinate of `𝔸¹_{S'}` is: restricting further to the chart at infinity `𝔸¹_{S'} ⟶ ℙ¹_{S'}`,
the former becomes the latter up to an automorphism of the support. -/
theorem isIso_supportedClassMap_restrictSupportedClass_chartBoundarySupportedClass_iff
    {S S' : Scheme.{u}} [HasInvertibleExponent Λ S] [HasInvertibleExponent Λ S'] (x : S' ⟶ S)
    (gZ : ProjectiveSpace.lineInfinity S' ⟶ ProjectiveSpace.lineInfinity S)
    (hgZ : IsPullback gZ (ProjectiveSpace.lineInfinityι S')
      (ProjectiveSpace.lineInfinityι S) (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x)) :
    IsIso (supportedClassMap Λ (ProjectiveSpace.lineInfinityι S')
      (restrictSupportedClass Λ (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x)
        (ProjectiveSpace.lineInfinityι S) (ProjectiveSpace.lineInfinityι S') gZ hgZ
        (leftDerivedUpperStarConstantComplexIso Λ
          (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x)).inv (Iso.refl _)
        (chartBoundarySupportedClass Λ (ProjectiveSpace.lineInfinityOpen S)
          (ProjectiveSpace.coordRatio (Option (ULift.{u} (Fin 1))) S (some ⟨0⟩) none)))) ↔
      IsIso (supportedClassMap Λ (𝔸(ULift.{u} (Fin 1); S').zeroLocusSubschemeι
          {AffineSpace.coord S' (ULift.up 0)})
        (shiftSupportedClass Λ _ 2 (kummerBoundary Λ (AffineSpace.coord S' (ULift.up 0))))) := by
  have : HasInvertibleExponent Λ (ProjectiveSpace.lineInfinityOpen S) :=
    .of_hom (ProjectiveSpace.lineInfinityOpen S).ι
  obtain ⟨gW, hgW, hW⟩ := ProjectiveSpace.exists_isIso_isPullback_lineInfinityChart S'
  obtain ⟨m, hm, hmc⟩ := ProjectiveSpace.exists_lift_lineInfinityChart_map x
  have hs : m.appTop '' {ProjectiveSpace.lineInfinityCoord S} =
      {AffineSpace.coord S' (ULift.up 0)} := by
    rw [Set.image_singleton, hmc]
  obtain ⟨τw, hτw⟩ := exists_restrictSupportedClass_eq_restrictSupportedClass Λ
    (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x)
    (ProjectiveSpace.lineInfinityChart S') m (ProjectiveSpace.lineInfinityOpen S).ι hm
    (ProjectiveSpace.lineInfinityι S) (ProjectiveSpace.lineInfinityι S')
    (𝔸(ULift.{u} (Fin 1); S').zeroLocusSubschemeι {AffineSpace.coord S' (ULift.up 0)})
    ((ProjectiveSpace.lineInfinityOpen S).toScheme.zeroLocusSubschemeι
      {ProjectiveSpace.lineInfinityCoord S}) gZ hgZ gW hW (𝟙 _)
    (isPullback_id_comp_of_mono _ _) _ (isPullback_zeroLocusSubschemeι m _ _ hs)
    (leftDerivedUpperStarTateTwoIso Λ (ProjectiveSpace.lineInfinityOpen S).ι)
    (leftDerivedUpperStarTateTwoIso Λ m)
    (chartBoundarySupportedClass Λ (ProjectiveSpace.lineInfinityOpen S)
      (ProjectiveSpace.coordRatio (Option (ULift.{u} (Fin 1))) S (some ⟨0⟩) none))
  obtain ⟨θ, hθ, hθγ⟩ := exists_supportedClassMap_restrictSupportedClass_chartBoundarySupportedClass
    Λ (ProjectiveSpace.lineInfinityOpen S)
    (ProjectiveSpace.coordRatio (Option (ULift.{u} (Fin 1))) S (some ⟨0⟩) none)
  refine (isIso_iff_of_reflects_iso _ (L((gW)^*[ModuleCat.{u + 1} Λ]))).symm.trans ?_
  rw [← isIso_supportedClassMap_restrictSupportedClass_iff Λ
    (ProjectiveSpace.lineInfinityChart S') (ProjectiveSpace.lineInfinityι S') _ gW hW _ _ τw _
    (isIso_supportedRestriction_of_isOpenImmersion Λ _ _ _ _ hW _ _ τw), hτw,
    isIso_supportedClassMap_restrictSupportedClass_iff_of_eq Λ m _ _ _
      (isPullback_zeroLocusSubschemeι m _ _ hs) _ _ _ _ _ θ hθγ, leftDerivedUpperStarTateTwoIso,
    restrictSupportedClass_shiftSupportedClass, kummerBoundary_baseChange_of_eq Λ m _ _ hmc]

/-- **Relative purity for the zero section of the affine line** (SGA 4 XVI 3.7; Fu, *Étale
cohomology theory*, 8.4; Milne, *Étale cohomology*, VI.5): for every scheme `B` on which the
exponent of `Λ` is invertible, the adjoint `Λ_{V(t)} ⟶ Rs^!(Λ(1)[2])` of the Kummer boundary
`∂κ(t)` of the coordinate `t` of `𝔸¹_B` is an isomorphism, `s : V(t) ⟶ 𝔸¹_B` the zero section.
The normalisation `AlgebraicGeometry.Etale.HasKummerClass.IsNormalized` is the case of `B`
separated and locally of finite type over a field.

It is the restriction to the chart at infinity of the class of the section at infinity of
`ℙ¹_B`, which is a fundamental class
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_lineInfinity`).
The proof uses the homotopy invariance
`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine_of_hasInvertibleExponent`.
-/
theorem isIso_supportedClassMap_kummerBoundary_coord_of_hasInvertibleExponent (B : Scheme.{u})
    [HasInvertibleExponent Λ B] :
    IsIso (supportedClassMap Λ (𝔸(ULift.{u} (Fin 1); B).zeroLocusSubschemeι
        {AffineSpace.coord B (ULift.up 0)})
      (shiftSupportedClass Λ _ 2 (kummerBoundary Λ (AffineSpace.coord B (ULift.up 0))))) := by
  obtain ⟨gZ, hgZ⟩ := ProjectiveSpace.exists_isPullback_lineInfinityι_map (𝟙 B)
  have : IsOpenImmersion (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) (𝟙 B)) := by
    rw [ProjectiveSpace.map_id]
    infer_instance
  rw [← isIso_supportedClassMap_restrictSupportedClass_chartBoundarySupportedClass_iff Λ (𝟙 B)
    gZ hgZ, isIso_supportedClassMap_restrictSupportedClass_iff Λ _ _ _ gZ hgZ _ _ _ _
    (isIso_supportedRestriction_of_isOpenImmersion Λ _ _ _ _ hgZ _ _ _)]
  have := isIso_supportedClassMap_lineInfinity Λ B
  infer_instance

end Purity

end Etale

end AlgebraicGeometry
