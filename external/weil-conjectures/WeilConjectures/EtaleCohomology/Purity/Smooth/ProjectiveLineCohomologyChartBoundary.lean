/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomologySupports
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomologyGysin
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# The class of the zero locus of a function on an open, with supports

Let `V ⊆ X` be an open, `s` a function on `V` whose zero locus `i : Z ⟶ V` is closed in `X`, and
`i' = i ≫ (V ⊆ X)`. The class `AlgebraicGeometry.Etale.chartBoundaryClass` of `Z` is the Gysin
image of the adjoint of the Kummer boundary `∂κ(s)`, read through the excision isomorphism
`Ri^! Λ_V(1) ≅ Ri'^! Λ_X(1)`. Here it is written as a class with supports
`Λ_X ⟶ Ri'_! Ri'^! (Λ_X(1)[2])` with forgotten supports
(`AlgebraicGeometry.Etale.chartBoundaryClass_eq`), and the restriction of this class with
supports to `V` is compared with `∂κ(s)`: their adjoints differ by an automorphism of `Λ_Z`
(`exists_supportedClassMap_restrictSupportedClass_chartBoundarySupportedClass`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] HasInvertibleExponent.opens

section Shift

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` commutes with the shifts. -/
instance commShift_leftDerivedUpperStarId_hom (X : Scheme.{u}) :
    NatTrans.CommShift (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom ℤ := by
  have e : (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (𝟙 X)).hom ≫
        (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ) X)).hom ≫
        (Functor.mapDerivedCategoryIdIso _).hom := by
    simp [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
      leftDerivedUpperStarIsoMapDerivedCategory]
  rw [e]
  infer_instance

/-- The base change map `Rf^! ⋙ Lg'^* ⟶ Lg^* ⋙ Rf'^!` of the exceptional inverse image
commutes with the shifts. -/
instance commShift_rightDerivedUpperShriekBaseChangeMap {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} [HasCompactification f] [HasCompactification f']
    [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    NatTrans.CommShift (rightDerivedUpperShriekBaseChangeMap Λ sq) ℤ := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have : NatTrans.CommShift (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)) ℤ :=
    NatTrans.CommShift.of_isIso (τ := rightDerivedLowerShriekBaseChangeMap Λ sq) (A := ℤ)
  exact NatTrans.CommShift.mateEquiv (rightDerivedUpperShriekAdjunction Λ f)
    (rightDerivedUpperShriekAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)))

variable {Z V X : Scheme.{u}} (i : Z ⟶ V) (j : V ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
  [IsClosedImmersion (i ≫ j)]

/-- The excision isomorphism is `L(𝟙)^* ≅ 𝟭` followed by the base change map. -/
lemma rightDerivedUpperShriekCompOpenImmersionIso_hom
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedUpperShriekCompOpenImmersionIso Λ i j L).hom =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Z).inv.app ((R(i ≫ j)^![Λ]).obj L) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_id_comp_of_mono i j)).app L :=
  rfl

/-- The excision isomorphism `R(i ≫ j)^! L ≅ Ri^!(Lj^* L)`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekCompOpenImmersionIso`) commutes with the
shifts. -/
lemma rightDerivedUpperShriekCompOpenImmersionIso_hom_shift
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    ((R(i ≫ j)^![Λ]).commShiftIso n).hom.app L ≫
        (rightDerivedUpperShriekCompOpenImmersionIso Λ i j L).hom⟦n⟧' =
      (rightDerivedUpperShriekCompOpenImmersionIso Λ i j (L⟦n⟧)).hom ≫
        (R(i)^![Λ]).map (((L((j)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).hom.app L) ≫
          ((R(i)^![Λ]).commShiftIso n).hom.app _ := by
  have h := NatTrans.shift_app_comm ((R(i ≫ j)^![Λ]).rightUnitor.inv ≫
    Functor.whiskerLeft (R(i ≫ j)^![Λ]) (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Z).inv ≫
      rightDerivedUpperShriekBaseChangeMap Λ (isPullback_id_comp_of_mono i j)) n L
  simp only [NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Category.id_comp, Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Functor.id_obj,
    Functor.map_comp, Category.assoc] at h
  rw [rightDerivedUpperShriekCompOpenImmersionIso_hom,
    rightDerivedUpperShriekCompOpenImmersionIso_hom, Functor.map_comp, Category.assoc]
  exact h

/-- The inverse of the excision isomorphism commutes with the shifts. -/
lemma rightDerivedUpperShriekCompOpenImmersionIso_inv_shift
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ) :
    (rightDerivedUpperShriekCompOpenImmersionIso Λ i j L).inv⟦n⟧' ≫
        ((R(i ≫ j)^![Λ]).commShiftIso n).inv.app L =
      ((R(i)^![Λ]).commShiftIso n).inv.app _ ≫
        (R(i)^![Λ]).map (((L((j)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).inv.app L) ≫
          (rightDerivedUpperShriekCompOpenImmersionIso Λ i j (L⟦n⟧)).inv := by
  have h := congrArg Iso.inv (Iso.ext (α := ((R(i ≫ j)^![Λ]).commShiftIso n).app L ≪≫
      (shiftFunctor _ n).mapIso (rightDerivedUpperShriekCompOpenImmersionIso Λ i j L))
    (β := rightDerivedUpperShriekCompOpenImmersionIso Λ i j (L⟦n⟧) ≪≫
      (R(i)^![Λ]).mapIso (((L((j)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).app L) ≪≫
        ((R(i)^![Λ]).commShiftIso n).app _)
    (rightDerivedUpperShriekCompOpenImmersionIso_hom_shift Λ i j L n))
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using h

/-- Pulling back along `𝟙` a morphism into `R(i ≫ j)^! L` read through the excision
isomorphism, followed by the base change map, is the morphism itself, read through
`L(𝟙)^* ≅ 𝟭`. -/
@[reassoc]
lemma map_comp_rightDerivedUpperShriekCompOpenImmersionIso_inv_comp
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (g : K ⟶ (R(i)^![Λ]).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj L)) :
    (L((𝟙 Z)^*[ModuleCat.{u + 1} Λ])).map
        (g ≫ (rightDerivedUpperShriekCompOpenImmersionIso Λ i j L).inv) ≫
      (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_id_comp_of_mono i j)).app L =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Z).hom.app K ≫ g := by
  rw [← NatIso.naturality_2 (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Z), Functor.id_map,
    Category.assoc, Category.assoc, Category.assoc,
    ← rightDerivedUpperShriekCompOpenImmersionIso_hom, Iso.inv_hom_id, Category.comp_id]

/-- Pulling back along `𝟙` a class `K ⟶ (R(i ≫ j)^! T)[n]` obtained from
`k : K ⟶ (Ri^! T')[n]` through `Lj^* T ≅ T'` and the excision isomorphism, then applying the
base change map and `Lj^*(T[n]) ≅ T'[n]`, recovers `k`, read through `L(𝟙)^* ≅ 𝟭` and the
shift compatibility of `Ri^!`. -/
lemma map_comp_rightDerivedUpperShriekBaseChangeMap_comp_map
    (T : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {T' : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (t : (L((j)^*[ModuleCat.{u + 1} Λ])).obj T ≅ T') (n : ℤ)
    {K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (k : K ⟶ ((R(i)^![Λ]).obj T')⟦n⟧) :
    (L((𝟙 Z)^*[ModuleCat.{u + 1} Λ])).map
        ((k ≫ ((R(i)^![Λ]).map t.inv ≫
          (rightDerivedUpperShriekCompOpenImmersionIso Λ i j T).inv)⟦n⟧') ≫
          ((R(i ≫ j)^![Λ]).commShiftIso n).inv.app T) ≫
      (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_id_comp_of_mono i j)).app (T⟦n⟧) ≫
        (R(i)^![Λ]).map (((L((j)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).hom.app T ≫
          t.hom⟦n⟧') =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Z).hom.app K ≫ k ≫
        ((R(i)^![Λ]).commShiftIso n).inv.app T' := by
  have e : (k ≫ ((R(i)^![Λ]).map t.inv ≫
      (rightDerivedUpperShriekCompOpenImmersionIso Λ i j T).inv)⟦n⟧') ≫
        ((R(i ≫ j)^![Λ]).commShiftIso n).inv.app T =
      (k ≫ ((R(i)^![Λ]).map t.inv)⟦n⟧' ≫ ((R(i)^![Λ]).commShiftIso n).inv.app _ ≫
        (R(i)^![Λ]).map (((L((j)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).inv.app T)) ≫
        (rightDerivedUpperShriekCompOpenImmersionIso Λ i j (T⟦n⟧)).inv := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [rightDerivedUpperShriekCompOpenImmersionIso_inv_shift]
  rw [e, map_comp_rightDerivedUpperShriekCompOpenImmersionIso_inv_comp_assoc]
  simp only [Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc (R(i)^![Λ]), Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Functor.commShiftIso_inv_naturality, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.inv_hom_id]
  simp

/-- The adjoint of the class with supports `Λ_X ⟶ R(i ≫ j)_!((R(i ≫ j)^! T)[n])` of
`a : Λ_Z ⟶ (Ri^! T')[n]`, read through `Lj^* T ≅ T'` and the excision isomorphism,
pulled back along `𝟙` and followed by the base change map, is `a`, read through
`L(𝟙)^* ≅ 𝟭` and the shift compatibility of `Ri^!`. -/
lemma map_supportedClassMap_comp_rightDerivedUpperShriekBaseChangeMap_comp_map
    (T : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {T' : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (t : (L((j)^*[ModuleCat.{u + 1} Λ])).obj T ≅ T') (n : ℤ)
    (a : constantComplex Λ Z ⟶ ((R(i)^![Λ]).obj T')⟦n⟧) :
    (L((𝟙 Z)^*[ModuleCat.{u + 1} Λ])).map (supportedClassMap Λ (i ≫ j)
        (shiftSupportedClass Λ (i ≫ j) n (supportedRestrictionMap Λ (i ≫ j) ≫
          (R(i ≫ j)_![ModuleCat.{u + 1} Λ]).map (a ≫ ((R(i)^![Λ]).map t.inv ≫
            (rightDerivedUpperShriekCompOpenImmersionIso Λ i j T).inv)⟦n⟧') ≫
          ((R(i ≫ j)_![ModuleCat.{u + 1} Λ]).commShiftIso n).hom.app _))) ≫
      (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_id_comp_of_mono i j)).app (T⟦n⟧) ≫
        (R(i)^![Λ]).map (((L((j)^*[ModuleCat.{u + 1} Λ])).commShiftIso n).app T ≪≫
          (shiftFunctor _ n).mapIso t).hom =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Z).hom.app (constantComplex Λ Z) ≫ a ≫
        ((R(i)^![Λ]).commShiftIso n).inv.app T' := by
  rw [supportedClassMap_shiftSupportedClass_supportedRestrictionMap, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, map_comp_rightDerivedUpperShriekBaseChangeMap_comp_map]
end Shift

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]

variable {X : Scheme.{u}} [HasInvertibleExponent Λ X] (V : X.Opens) (s : Γ(X, V))
  [IsClosedImmersion (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s} ≫ V.ι)]

/-- The adjoint of the Kummer boundary `∂κ(f)` read with coefficients `Λ_U(1)` in degree `2` is
`AlgebraicGeometry.Etale.kummerBoundaryAdjoint`. -/
lemma supportedTranspose_kummerBoundary_comp {U : Scheme.{u}} [HasInvertibleExponent Λ U]
    (f : Γ(U, ⊤)) :
    supportedTranspose Λ (U.zeroLocusSubschemeι {f})
        (kummerBoundary Λ f ≫
          ((R(U.zeroLocusSubschemeι {f})_![ModuleCat.{u + 1} Λ]).commShiftIso (2 : ℤ)).inv.app
            _) =
      kummerBoundaryAdjoint Λ f := by
  unfold supportedTranspose kummerBoundaryAdjoint
  congr 1

/-- The adjoint of the Kummer boundary `∂κ(f)`, read with coefficients `Λ_U(1)[2]`, is
`AlgebraicGeometry.Etale.kummerBoundaryAdjoint` followed by the shift compatibility of
`Ri^!`. -/
lemma supportedClassMap_shiftSupportedClass_kummerBoundary {U : Scheme.{u}}
    [HasInvertibleExponent Λ U] (f : Γ(U, ⊤)) :
    supportedClassMap Λ (U.zeroLocusSubschemeι {f})
        (shiftSupportedClass Λ _ 2 (kummerBoundary Λ f)) =
      kummerBoundaryAdjoint Λ f ≫
        ((R(U.zeroLocusSubschemeι {f})^![Λ]).commShiftIso (2 : ℤ)).inv.app _ := by
  rw [supportedClassMap_eq_supportedTranspose, shiftSupportedClass, ← Category.assoc,
    supportedTranspose_comp, supportedTranspose_kummerBoundary_comp]

/-- The identification `Le^*(Λ(1)[2]) ≅ Λ(1)[2]` along `e`, through the shift compatibility of
`Le^*` and the identification of the twisting objects. -/
noncomputable def leftDerivedUpperStarTateTwoIso {U Y : Scheme.{u}} [HasInvertibleExponent Λ U]
    [HasInvertibleExponent Λ Y] (e : U ⟶ Y) :
    (L((e)^*[ModuleCat.{u + 1} Λ])).obj ((tateObject Λ Y 1)⟦(2 : ℤ)⟧) ≅
      (tateObject Λ U 1)⟦(2 : ℤ)⟧ :=
  ((L((e)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso (leftDerivedUpperStarTateObjectIso e 1)

/-- The class of the zero locus `i' : Z ⟶ X` of `s` with supports: the degree-two class with
supports `Λ_X ⟶ (Ri'_! Ri'^! Λ_X(1))[2]` adjoint to the morphism
`Λ_Z ⟶ (Ri^! Λ_V(1))[2] ≅ (Ri'^! Λ_X(1))[2]` of `AlgebraicGeometry.Etale.chartBoundaryClass`,
read with coefficients `Λ_X(1)[2]` (`AlgebraicGeometry.Etale.shiftSupportedClass`). -/
noncomputable def chartBoundarySupportedClass :
    constantComplex Λ X ⟶
      (R(V.toScheme.zeroLocusSubschemeι {V.topIso.inv s} ≫ V.ι)_![ModuleCat.{u + 1} Λ]).obj
        ((R(V.toScheme.zeroLocusSubschemeι {V.topIso.inv s} ≫ V.ι)^![Λ]).obj
          ((tateObject Λ X 1)⟦(2 : ℤ)⟧)) :=
  shiftSupportedClass Λ _ 2
    (supportedRestrictionMap Λ _ ≫
      (R(V.toScheme.zeroLocusSubschemeι {V.topIso.inv s} ≫ V.ι)_![ModuleCat.{u + 1} Λ]).map
        (kummerBoundaryAdjoint Λ (V.topIso.inv s) ≫
          ((R(V.toScheme.zeroLocusSubschemeι {V.topIso.inv s})^![Λ]).map
              (leftDerivedUpperStarTateObjectIso V.ι 1).inv ≫
            (rightDerivedUpperShriekCompOpenImmersionIso Λ _ V.ι _).inv)⟦(2 : ℤ)⟧') ≫
      (Functor.commShiftIso
        (R(V.toScheme.zeroLocusSubschemeι {V.topIso.inv s} ≫ V.ι)_![ModuleCat.{u + 1} Λ])
        (2 : ℤ)).hom.app _)

/-- The class of the zero locus of `s` is its class with supports, with supports forgotten. -/
lemma chartBoundaryClass_eq :
    chartBoundaryClass Λ V s =
      chartBoundarySupportedClass Λ V s ≫
        (rightDerivedUpperShriekAdjunction Λ
          (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s} ≫ V.ι)).counit.app
          ((tateObject Λ X 1)⟦(2 : ℤ)⟧) := by
  rw [chartBoundaryClass, gysinClass_eq]
  exact (shiftSupportedClass_comp_counit Λ _ 2 _).symm

/-- **The restriction of the class with supports to the open `V`.** The adjoint of the
restriction to `V` of the class with supports of the zero locus of `s`
(`AlgebraicGeometry.Etale.chartBoundarySupportedClass`) is, up to an automorphism of `Λ_Z`, the
adjoint of the Kummer boundary `∂κ(s)` of `s`, read with coefficients `Λ_V(1)[2]`. -/
theorem exists_supportedClassMap_restrictSupportedClass_chartBoundarySupportedClass :
    ∃ θ : constantComplex Λ (V.toScheme.zeroLocusSubscheme {V.topIso.inv s}) ⟶
        constantComplex Λ (V.toScheme.zeroLocusSubscheme {V.topIso.inv s}), IsIso θ ∧
      supportedClassMap Λ (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s})
          (restrictSupportedClass Λ V.ι _ _ (𝟙 _)
            (isPullback_id_comp_of_mono (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s}) V.ι)
            (leftDerivedUpperStarConstantComplexIso Λ V.ι).inv
            (leftDerivedUpperStarTateTwoIso Λ V.ι) (chartBoundarySupportedClass Λ V s)) =
        θ ≫ supportedClassMap Λ (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s})
          (shiftSupportedClass Λ _ 2 (kummerBoundary Λ (V.topIso.inv s))) := by
  obtain ⟨Θ, hΘ, hres⟩ := exists_isIso_supportedClassMap_restrictSupportedClass Λ V.ι
    (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s} ≫ V.ι)
    (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s}) (𝟙 _)
    (isPullback_id_comp_of_mono (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s}) V.ι)
  refine ⟨Θ ≫ (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ)
    (V.toScheme.zeroLocusSubscheme {V.topIso.inv s})).hom.app
      (constantComplex Λ (V.toScheme.zeroLocusSubscheme {V.topIso.inv s})), inferInstance, ?_⟩
  refine (hres _ _ _ _).trans (Eq.trans (congrArg (Θ ≫ ·)
    (map_supportedClassMap_comp_rightDerivedUpperShriekBaseChangeMap_comp_map Λ
      (V.toScheme.zeroLocusSubschemeι {V.topIso.inv s}) V.ι (tateObject Λ X 1)
      (leftDerivedUpperStarTateObjectIso V.ι 1) 2 (kummerBoundaryAdjoint Λ (V.topIso.inv s))))
    ?_)
  exact (Category.assoc _ _ _).symm.trans
    (congrArg _ (supportedClassMap_shiftSupportedClass_kummerBoundary Λ _).symm)

end Etale

end AlgebraicGeometry
