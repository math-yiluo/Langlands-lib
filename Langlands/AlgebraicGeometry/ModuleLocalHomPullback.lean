import Langlands.AlgebraicGeometry.ModuleDual
import Langlands.AlgebraicGeometry.Modules.PullbackUnit

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

noncomputable section

namespace Langlands.Scheme.Modules

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

/-- Restriction of a pulled-back module to an inverse-image open, naturally in the module. -/
def restrictPullbackNatIso (f : X ⟶ Y) (U : Y.Opens) :
    AlgebraicGeometry.Scheme.Modules.pullback f ⋙
      AlgebraicGeometry.Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
    AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι ⋙
      AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U) :=
  isoWhiskerLeft _ (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback _) ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackComp _ _ ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp _ _).symm ≪≫
    isoWhiskerRight (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback _).symm _

/-- Pull back a local module-sheaf morphism to the inverse-image open. -/
def localHomPullback (f : X ⟶ Y) {M N : Y.Modules} (U : Y.Opens)
    (h : LocalHom M N U) :
    LocalHom ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) (f ⁻¹ᵁ U) :=
  (internalHomSectionsEquiv _ _ _).symm
    ((restrictPullbackNatIso f U).hom.app M ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U)).map
        (internalHomSectionsEquiv M N U h) ≫
      (restrictPullbackNatIso f U).inv.app N)

lemma internalHomSectionsEquiv_localHomPullback (f : X ⟶ Y)
    {M N : Y.Modules} (U : Y.Opens) (h : LocalHom M N U) :
    internalHomSectionsEquiv _ _ _ (localHomPullback f U h) =
      (restrictPullbackNatIso f U).hom.app M ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U)).map
          (internalHomSectionsEquiv M N U h) ≫
        (restrictPullbackNatIso f U).inv.app N :=
  Equiv.apply_symm_apply _ _

@[simp]
lemma localHomPullback_zero (f : X ⟶ Y) (M N : Y.Modules) (U : Y.Opens) :
    localHomPullback f U (0 : LocalHom M N U) = 0 := by
  apply (internalHomSectionsEquiv _ _ _).injective
  simp [internalHomSectionsEquiv_localHomPullback]

@[simp]
lemma localHomPullback_add (f : X ⟶ Y) {M N : Y.Modules} (U : Y.Opens)
    (h k : LocalHom M N U) :
    localHomPullback f U (h + k) = localHomPullback f U h + localHomPullback f U k := by
  apply (internalHomSectionsEquiv _ _ _).injective
  rw [internalHomSectionsEquiv_add, internalHomSectionsEquiv_localHomPullback,
    internalHomSectionsEquiv_localHomPullback, internalHomSectionsEquiv_localHomPullback,
    internalHomSectionsEquiv_add]
  simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

/-- The construction respects precomposition and postcomposition by global maps. -/
lemma localHomPullback_naturality (f : X ⟶ Y) {M M' N N' : Y.Modules}
    (a : M' ⟶ M) (b : N ⟶ N') (U : Y.Opens) (h : LocalHom M N U) :
    localHomPullback f U (a.over U ≫ h ≫ b.over U) =
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map a).over (f ⁻¹ᵁ U) ≫
        localHomPullback f U h ≫
        ((AlgebraicGeometry.Scheme.Modules.pullback f).map b).over (f ⁻¹ᵁ U) := by
  apply (internalHomSectionsEquiv _ _ _).injective
  rw [internalHomSectionsEquiv_localHomPullback]
  change _ = internalHomSectionsEquiv _ _ _
    ((internalHomMap ((AlgebraicGeometry.Scheme.Modules.pullback f).map a)
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map b)).app _
      (localHomPullback f U h))
  rw [internalHomSectionsEquiv_naturality, internalHomSectionsEquiv_localHomPullback]
  change (restrictPullbackNatIso f U).hom.app M' ≫
      (AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U)).map
        (internalHomSectionsEquiv M' N' U ((internalHomMap a b).app U h)) ≫ _ = _
  rw [internalHomSectionsEquiv_naturality]
  simp only [Functor.map_comp, Category.assoc]
  have ha := (restrictPullbackNatIso f U).hom.naturality a
  have hb := (restrictPullbackNatIso f U).inv.naturality b
  dsimp at ha hb
  rw [← Category.assoc, ← ha]
  simp only [Category.assoc]
  rw [hb]

/-- Pull a local functional back and identify the pulled-back structure module. -/
def localDualPullback (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (h : Γ(dual M, U)) :
    Γ(dual ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M), f ⁻¹ᵁ U) :=
  localHomPullback f U h ≫ (pullbackUnitIso f).hom.over (f ⁻¹ᵁ U)

end Langlands.Scheme.Modules
