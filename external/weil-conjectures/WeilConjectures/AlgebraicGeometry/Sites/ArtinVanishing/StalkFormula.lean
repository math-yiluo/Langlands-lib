/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.StalkVanishing
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap

/-!
# Geometric stalks of higher direct images and the strict localization

Let `h: X ⟶ S` be quasi-compact and quasi-separated, `F` an abelian étale sheaf on `X`, and
`s̄` a geometric point of `S` which factors as `s: Spec Ω ⟶ W` followed by an étale
`ι: W ⟶ S`. If `Hᵠ(X ×_S W_(s), F|) = 0`, where `W_(s)` is the strict localization of `W` at `s`,
then the geometric stalk of `Rᵠh_* F` at `s̄` vanishes
(`AlgebraicGeometry.Etale.isZero_upperStar_rightDerived_lowerStar_of_subsingleton_H`). This is
the vanishing half of the strict-henselization stalk formula.

`X ×_S W_(s)` is the limit of the `X ×_S V`, `V` running over the affine pointed étale
neighbourhoods of `s` in `W`, so by continuity of étale cohomology
(`AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit`) every class on some `X ×_S V`
dies on a smaller `X ×_S V'`; and pointed étale neighbourhoods of `s` in `W` refine those of
`s ≫ ι` in `S`. We conclude with
`AlgebraicGeometry.Etale.isZero_upperStar_rightDerived_lowerStar_of_forall_exists`.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

section Helpers

variable {X S W : Scheme.{u}} (h : X ⟶ S)

/-- Base change along `h : X ⟶ S`, as a functor `Over S ⥤ Over X` whose value at `Y ⟶ S` is
`X ×_S Y` with structure morphism the *first* projection. -/
@[simps]
noncomputable def overPullbackFstFunctor : CategoryTheory.Over S ⥤ CategoryTheory.Over X where
  obj Y := CategoryTheory.Over.mk (pullback.fst h Y.hom)
  map {Y Z} g := CategoryTheory.Over.homMk
    (pullback.map h Y.hom h Z.hom (𝟙 X) g.left (𝟙 S) (by simp) (by simp)) (by simp)
  map_id Y := by ext; apply pullback.hom_ext <;> simp
  map_comp f g := by ext; apply pullback.hom_ext <;> simp

/-- `overPullbackFstFunctor h` is isomorphic to Mathlib's base change functor
`Over.pullback h`. -/
noncomputable def overPullbackFstFunctorIso :
    overPullbackFstFunctor h ≅ CategoryTheory.Over.pullback h :=
  NatIso.ofComponents
    (fun Y ↦ CategoryTheory.Over.isoMk (pullbackSymmetry h Y.hom) (by simp; rfl))
    (fun g ↦ by ext; apply pullback.hom_ext <;> simp)

instance : PreservesLimitsOfSize.{v, w} (overPullbackFstFunctor h) :=
  preservesLimits_of_natIso (overPullbackFstFunctorIso h).symm

variable (ι : W ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ W)

/-- A pointed étale neighbourhood of `s` in `W` is a pointed étale neighbourhood of `s ≫ ι` in
`S`, by composing with the étale morphism `ι : W ⟶ S`. -/
noncomputable def neighborhoodCompEtale [Etale ι] :
    PointedEtaleNeighborhood s ⥤ PointedEtaleNeighborhood (s ≫ ι) where
  obj x :=
    haveI : Etale x.1.hom := x.1.prop
    Functor.elementsMk _ (Scheme.Etale.mk (x.1.hom ≫ ι)) (CategoryTheory.Over.homMk x.2.left
      (by simpa using congrArg (· ≫ ι) (CategoryTheory.Over.w x.2)))
  map {x y} f := ⟨MorphismProperty.Over.homMk f.1.left (by simp),
    CategoryTheory.Over.OverMorphism.ext (congrArg (fun g ↦ g.left) f.2)⟩

end Helpers

/-- `pullbackNeighborhoodMap` is compatible with composition. -/
lemma pullbackNeighborhoodMap_comp {X S : Scheme.{u}} (h : X ⟶ S) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) {x y z : PointedEtaleNeighborhood s} (f : z ⟶ y)
    (g : y ⟶ x) :
    pullbackNeighborhoodMap h s f ≫ pullbackNeighborhoodMap h s g =
      pullbackNeighborhoodMap h s (f ≫ g) := by
  apply pullback.hom_ext <;> simp

/-- **Vanishing of geometric stalks of higher direct images.** Let `h : X ⟶ S` be
quasi-compact and quasi-separated, `F` an abelian étale sheaf on `X`, `ι : W ⟶ S` étale and
`s : Spec Ω ⟶ W` a geometric point. If `Hᵠ(X ×_S W_(s), F|) = 0` for `q > 0`, where `W_(s)` is
the strict localization of `W` at `s`, then the geometric stalk of `Rᵠh_* F` at `s ≫ ι`
vanishes. -/
theorem isZero_upperStar_rightDerived_lowerStar_of_subsingleton_H {X S W : Scheme.{u}}
    (h : X ⟶ S) [QuasiCompact h] [QuasiSeparated h] (ι : W ⟶ S) [Etale ι]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ W) (q : ℕ) (hq : 0 < q)
    (hcoh : Subsingleton (Sheaf.H
      ((pullback.fst h (strictLocalizationToBase s ≫ ι))^*[AddCommGrpCat.{u + 1}].obj F) q)) :
    IsZero ((s ≫ ι)^*[AddCommGrpCat.{u + 1}].obj
      ((((h)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj F)) := by
  let I := InitiallySmall.CofilteredInitialModel.{u} (AffinePointedEtaleNeighborhood s)
  let Φ : I ⥤ AffinePointedEtaleNeighborhood s :=
    InitiallySmall.fromCofilteredInitialModel.{u} (AffinePointedEtaleNeighborhood s)
  have := IsCofiltered.isConnected (AffinePointedEtaleNeighborhood s)
  let K := (CategoryTheory.Over.map ι).mapCone (strictLocalizationConeOver s)
  have hK : IsLimit K := isLimitOfReflects (CategoryTheory.Over.forget S)
    (isLimitOfPreserves (CategoryTheory.Over.forget W) (isLimitStrictLocalizationConeOver s))
  let D : I ⥤ CategoryTheory.Over X :=
    Φ ⋙ (affineNeighborhoodDiagramOver s ⋙ CategoryTheory.Over.map ι) ⋙
      overPullbackFstFunctor h
  let cn : Cone D := ((overPullbackFstFunctor h).mapCone K).whisker Φ
  have hc : IsLimit ((CategoryTheory.Over.forget X).mapCone cn) :=
    (Functor.Initial.isLimitWhiskerEquiv Φ _).symm
      (isLimitOfPreserves (CategoryTheory.Over.forget X)
        (isLimitOfPreserves (overPullbackFstFunctor h) hK))
  have hA (i : I) : IsAffine ((𝟭 Scheme.{u}).obj (Φ.obj i).obj.1.left) := (Φ.obj i).2
  have (i : I) : CompactSpace (D.obj i).left := by
    have := hA i
    change CompactSpace (pullback h ((Φ.obj i).obj.1.hom ≫ ι) : Scheme.{u}); infer_instance
  have (i : I) : QuasiSeparatedSpace (D.obj i).left := by
    have := hA i
    change QuasiSeparatedSpace (pullback h ((Φ.obj i).obj.1.hom ≫ ι) : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd h _)
  have : ∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g).left := fun {i j} g ↦
    MorphismProperty.pullbackMap (P := @IsAffineHom) (MorphismProperty.id_mem _ X)
      (inferInstanceAs (IsAffineHom (Φ.map g).hom.1.left)) (by simp) (by simp)
  refine isZero_upperStar_rightDerived_lowerStar_of_forall_exists h (s ≫ ι) F q hq ?_
  intro x c
  have : Etale x.1.hom := x.1.prop
  let x' : PointedEtaleNeighborhood s :=
    Functor.elementsMk _ (Scheme.Etale.mk (pullback.snd x.1.hom ι)) (CategoryTheory.Over.homMk
      (pullback.lift x.2.left s (CategoryTheory.Over.w x.2)) (pullback.lift_snd _ _ _))
  let e : (neighborhoodCompEtale ι s).obj x' ⟶ x :=
    ⟨MorphismProperty.Over.homMk (pullback.fst _ _) pullback.condition,
      CategoryTheory.Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  obtain ⟨a, ⟨fa⟩⟩ := AffinePointedEtaleNeighborhood.exists_hom s x'
  obtain ⟨⟨m, _, fm⟩⟩ : Nonempty (CostructuredArrow Φ a) := IsConnected.is_nonempty
  let f0 : (neighborhoodCompEtale ι s).obj ((AffinePointedEtaleNeighborhood.ι s).obj (Φ.obj m))
      ⟶ x :=
    (neighborhoodCompEtale ι s).map ((AffinePointedEtaleNeighborhood.ι s).map fm ≫ fa) ≫ e
  have w0 : (D.obj m).hom = pullbackNeighborhoodMap h (s ≫ ι) f0 ≫ pullback.fst h x.1.hom := by
    simp [D]; rfl
  let c0 := Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1}
    (pullbackNeighborhoodMap h (s ≫ ι) f0) (pullback.fst h x.1.hom) (D.obj m).hom w0).app F).inv
    q (cohomologyMap _ _ q c)
  obtain ⟨j, g, hg⟩ := (cohomologyMap_isColimit_of_isLimit F D cn hc q).2 m c0 (by
    have hinj := injective_sheafHMap_of_isIso ((upperStarComp AddCommGrpCat.{u + 1}
      (cn.π.app m).left (D.obj m).hom cn.pt.hom
      (CategoryTheory.Over.w (cn.π.app m)).symm).app F).inv q
    have := @Function.Injective.subsingleton _ _ _ hinj hcoh
    exact @Subsingleton.elim _ this _ _)
  refine ⟨_, (neighborhoodCompEtale ι s).map
    ((AffinePointedEtaleNeighborhood.ι s).map (Φ.map g)) ≫ f0, ?_⟩
  replace hg := (cohomologyMap_map_eq_zero_iff _ _ _ _).1 hg
  have hDg : (D.map g).left = pullbackNeighborhoodMap h (s ≫ ι)
      ((neighborhoodCompEtale ι s).map ((AffinePointedEtaleNeighborhood.ι s).map (Φ.map g))) :=
    rfl
  rw [hDg] at hg
  exact (cohomologyMap_cohomologyMap_eq_zero_iff' _
    (pullbackNeighborhoodMap h (s ≫ ι) f0) _
    (pullbackNeighborhoodMap_comp h (s ≫ ι) _ f0) _ c).1 hg

end AlgebraicGeometry.Etale
