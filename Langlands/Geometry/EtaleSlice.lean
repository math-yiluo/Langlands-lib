import Langlands.Geometry.EtaleAutomorphism
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Abelian

/-! # The slice of a small étale site -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleSlice

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleAutomorphism

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme.{u}} (V : X.Etale)

/-- An object of the slice has an étale structural map to the cover scheme. -/
def toSmallEtale : Over V ⥤ V.left.Etale where
  obj U := Scheme.Etale.mk U.hom.left
  map f := MorphismProperty.Over.homMk f.left.left
    (by exact congrArg (fun t => t.left) (Over.w f))

/-- Compose an étale map to the cover with the cover's structural map. -/
def fromSmallEtale : V.left.Etale ⥤ Over V where
  obj U := Over.mk
    (MorphismProperty.Over.homMk U.hom :
      Scheme.Etale.mk (U.hom ≫ V.hom) ⟶ V)
  map f := Over.homMk
    (MorphismProperty.Over.homMk f.left (by
      dsimp
      rw [← Category.assoc, MorphismProperty.Over.w]))
    (by
      apply MorphismProperty.Over.Hom.ext
      exact MorphismProperty.Over.w f)

/-- The iterated slice is the small étale category of the cover scheme. -/
def siteEquivalence : Over V ≌ V.left.Etale where
  functor := toSmallEtale V
  inverse := fromSmallEtale V
  unitIso := NatIso.ofComponents
    (fun U => Over.isoMk (MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 U.left.left ≫ (U.hom.left ≫ V.hom) = U.left.hom
      simpa only [Category.id_comp] using MorphismProperty.Over.w U.hom)))
  counitIso := NatIso.ofComponents
    (fun U => MorphismProperty.Over.isoMk (Iso.refl _))

/-- The slice topology is the jointly-surjective étale topology. -/
theorem mem_sliceTopology_iff {U : Over V} (S : Sieve U) :
    S ∈ (X.smallEtaleTopology.over V) U ↔
      ∀ x : U.left.left, ∃ (W : Over V) (f : W ⟶ U) (w : W.left.left),
        S f ∧ f.left.left w = x := by
  rw [GrothendieckTopology.mem_over_iff, mem_smallEtaleTopology_iff]
  refine forall_congr' fun x => ?_
  constructor
  · rintro ⟨W, f, w, hf, hw⟩
    exact ⟨Over.mk (f ≫ U.hom), Over.homMk f, w,
      (Sieve.overEquiv_iff _ _).mp hf, hw⟩
  · rintro ⟨W, f, w, hf, hw⟩
    refine ⟨W.left, f.left, w, ?_, hw⟩
    change (Sieve.functorPushforward (Over.forget V) S) f.left
    exact ⟨W, f, 𝟙 W.left, hf, by simp⟩

instance toSmallEtale_isCocontinuous :
    (toSmallEtale V).IsCocontinuous
      (X.smallEtaleTopology.over V) V.left.smallEtaleTopology where
  cover_lift {U S} hS := by
    rw [mem_smallEtaleTopology_iff] at hS
    rw [mem_sliceTopology_iff]
    intro x
    obtain ⟨W, f, w, hf, hw⟩ := hS x
    let W' : Over V := Over.mk
      (MorphismProperty.Over.homMk (f.left ≫ U.hom.left) :
        Scheme.Etale.mk ((f.left ≫ U.hom.left) ≫ V.hom) ⟶ V)
    let f' : W' ⟶ U := Over.homMk (MorphismProperty.Over.homMk f.left)
    let e : (toSmallEtale V).obj W' ⟶ W :=
      MorphismProperty.Over.homMk (𝟙 W.left) (by
        dsimp [W', toSmallEtale]
        rw [Category.id_comp]
        exact MorphismProperty.Over.w f |>.symm)
    refine ⟨W', f', w, ?_, hw⟩
    change S ((toSmallEtale V).map f')
    have he : (toSmallEtale V).map f' = e ≫ f := by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.id_comp f.left).symm
    rw [he]
    exact S.downward_closed hf e

instance fromSmallEtale_isCocontinuous :
    (fromSmallEtale V).IsCocontinuous
      V.left.smallEtaleTopology (X.smallEtaleTopology.over V) where
  cover_lift {U S} hS := by
    rw [mem_sliceTopology_iff] at hS
    rw [mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨W, f, w, hf, hw⟩ := hS x
    let W' : V.left.Etale := Scheme.Etale.mk W.hom.left
    let f' : W' ⟶ U := MorphismProperty.Over.homMk f.left.left
      (by exact congrArg (fun t => t.left) (Over.w f))
    let e : (fromSmallEtale V).obj W' ⟶ W :=
      Over.homMk (MorphismProperty.Over.homMk (𝟙 W.left.left) (by
        change 𝟙 W.left.left ≫ W.left.hom = W.hom.left ≫ V.hom
        simpa only [Category.id_comp] using (MorphismProperty.Over.w W.hom).symm))
    refine ⟨W', f', w, ?_, hw⟩
    change S ((fromSmallEtale V).map f')
    have he : (fromSmallEtale V).map f' = e ≫ f := by
      apply Over.OverMorphism.ext
      apply MorphismProperty.Over.Hom.ext
      exact (Category.id_comp f.left.left).symm
    rw [he]
    exact S.downward_closed hf e

instance siteEquivalence_inverse_isDenseSubsite :
    (siteEquivalence V).inverse.IsDenseSubsite
      V.left.smallEtaleTopology (X.smallEtaleTopology.over V) := by
  let : (siteEquivalence V).functor.IsCocontinuous
      (X.smallEtaleTopology.over V) V.left.smallEtaleTopology :=
    toSmallEtale_isCocontinuous V
  let : (siteEquivalence V).inverse.IsCocontinuous
      V.left.smallEtaleTopology (X.smallEtaleTopology.over V) :=
    fromSmallEtale_isCocontinuous V
  exact (siteEquivalence V).isDenseSubsite_inverse_of_isCocontinuous _ _

/-- Sheafification on the cover's small étale site supplies sheafification on
the actual slice, without changing the module carrier universe. -/
instance moduleHasSheafify (R : Type u) [Ring R] :
    HasSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} R) :=
  (siteEquivalence V).hasSheafify _ V.left.smallEtaleTopology _

/-- The slice-site module sheaves and the cover's module sheaves are equivalent. -/
def moduleSheafEquivalence (R : Type u) [Ring R] :
    Sheaf (X.smallEtaleTopology.over V) (ModuleCat.{u} R) ≌
      Sheaf V.left.smallEtaleTopology (ModuleCat.{u} R) :=
  (siteEquivalence V).sheafCongr _ _ _

end Langlands.Geometry.EtaleSlice
