import Langlands.Sheaf.Equivariant.AnalyticEtaleProperRestriction

/-! # The laws of analytic étale restriction of compact sections -/

noncomputable section

universe u v uL w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Sheaf.Equivariant.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y Z : LocalizedCategory.{u, v, v} (K := K)}
  {f : X ⟶ Y} {g : Y ⟶ Z} (hf : etale f) (hg : etale g)
  (R : Type (max u (v + 1) uL)) [CommRing R]

private abbrev coefficientModules (R : Type w) [CommRing R] := ModuleCat.{w} R

local notation "modules" => coefficientModules R

private abbrev identityEtale (X : LocalizedCategory.{u, v, v} (K := K)) : etale (𝟙 X) :=
  etale_of_isIso (𝟙 X)

local instance : (etale (K := K) : MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).IsMultiplicative where
  id_mem := identityEtale
  comp_mem _ _ := etale_comp

/-- Identity restriction is identified with the identity functor by postcomposition on
étale tests. -/
def etaleRestrictionId (X : LocalizedCategory.{u, v, v} (K := K)) :
    etaleRestriction.{u, v, uL} (identityEtale X) R ≅ 𝟭 (Sheaf (etaleTopology X) modules) :=
  Functor.sheafPushforwardContinuousId' (MorphismProperty.Over.mapId (P := etale) ⊤ X)
    modules (etaleTopology X)

/-- Successive restrictions identify with restriction along the composite analytic map. -/
def etaleRestrictionComp :
    etaleRestriction.{u, v, uL} hg R ⋙ etaleRestriction.{u, v, uL} hf R ≅
      etaleRestriction.{u, v, uL} (etale_comp hf hg) R :=
  Functor.sheafPushforwardContinuousComp' (MorphismProperty.Over.mapComp ⊤ hf hg).symm
    modules (etaleTopology X) (etaleTopology Y) (etaleTopology Z)

/-- Usual restriction of global sections along the identity is the identity under
the identity comparison of sheaf functors. -/
theorem etaleSectionsRestriction_id (F : Sheaf (etaleTopology X) modules) :
    (etaleSectionsRestriction.{u, v, uL} (identityEtale X) R).app F ≫
        (etaleSections.{u, v, uL} X R).map
          (X := (etaleRestriction.{u, v, uL} (identityEtale X) R).obj F)
          ((etaleRestrictionId.{u, v, uL} R X).hom.app F) = 𝟙 _ := by
  let terminalX : IsTerminal (etaleSelf X) := etaleSelfIsTerminal
  let a := terminalX.from ((EtaleSite.postcomposeEtale (identityEtale X)).obj (etaleSelf X))
  let b := (MorphismProperty.Over.mapId (P := etale) ⊤ X).inv.app (etaleSelf X)
  dsimp [etaleSectionsRestriction, etaleRestrictionId, etaleSections,
    Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousId,
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans]
  simp only [Category.comp_id]
  change F.obj.map a.op ≫ F.obj.map b.op = 𝟙 _
  rw [← F.obj.map_comp, ← F.obj.map_id (op (etaleSelf X))]
  exact congrArg F.obj.map (Quiver.Hom.unop_inj (terminalX.hom_ext _ _))

/-- Restriction of global sections is coherent with the composition of analytic maps. -/
theorem etaleSectionsRestriction_comp (F : Sheaf (etaleTopology Z) modules) :
    (etaleSectionsRestriction.{u, v, uL} hg R).app F ≫
        (etaleSectionsRestriction.{u, v, uL} hf R).app ((etaleRestriction.{u, v, uL} hg R).obj F) ≫
        (etaleSections.{u, v, uL} X R).map ((etaleRestrictionComp.{u, v, uL} hf hg R).hom.app F) =
      (etaleSectionsRestriction.{u, v, uL} (etale_comp hf hg) R).app F := by
  let terminalY : IsTerminal (etaleSelf Y) := etaleSelfIsTerminal
  let terminalZ : IsTerminal (etaleSelf Z) := etaleSelfIsTerminal
  let a := terminalZ.from ((EtaleSite.postcomposeEtale hg).obj (etaleSelf Y))
  let b := (EtaleSite.postcomposeEtale hg).map
    (terminalY.from ((EtaleSite.postcomposeEtale hf).obj (etaleSelf X)))
  let c := (MorphismProperty.Over.mapComp ⊤ hf hg).hom.app (etaleSelf X)
  let d := terminalZ.from ((EtaleSite.postcomposeEtale (etale_comp hf hg)).obj (etaleSelf X))
  dsimp [etaleSectionsRestriction, etaleRestrictionComp, etaleSections,
    Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
    Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans]
  simp only [Category.id_comp]
  change F.obj.map a.op ≫ F.obj.map b.op ≫ F.obj.map c.op = F.obj.map d.op
  simp only [← F.obj.map_comp]
  exact congrArg F.obj.map (Quiver.Hom.unop_inj (terminalZ.hom_ext _ _))

variable (Lₓ : Type uL) [NormedField Lₓ] [NormedAlgebra K Lₓ]
  [T2Space (localizedSpaceFunctor.obj X)]
  (hX : ∀ x : (localizedFieldPointFunctor Lₓ).obj X, EtaleSite.PointAxioms Lₓ x)
  (surjX : Function.Surjective (pointProjection Lₓ X))

/-- Proper pullback along the identity acts identically on compactly supported sections
after the sheaf identity comparison. -/
theorem etaleCompactSectionsRestriction_id
    (hp : IsProperMap (localizedSpaceFunctor.map (𝟙 X)))
    (F : Sheaf (etaleTopology X) modules) :
    (etaleCompactSectionsRestriction.{u, v, uL} (identityEtale X) R Lₓ Lₓ
      hX hX surjX surjX hp).app F ≫
        (etaleCompactSections Lₓ hX R).map ((etaleRestrictionId.{u, v, uL} R X).hom.app F) =
      𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (etaleSectionsRestriction_id.{u, v, uL} R F) s.val

variable (Lᵧ L𝓏 : Type uL) [NormedField Lᵧ] [NormedAlgebra K Lᵧ]
  [NormedField L𝓏] [NormedAlgebra K L𝓏]
  [T2Space (localizedSpaceFunctor.obj Y)] [T2Space (localizedSpaceFunctor.obj Z)]
  (hY : ∀ y : (localizedFieldPointFunctor Lᵧ).obj Y, EtaleSite.PointAxioms Lᵧ y)
  (hZ : ∀ z : (localizedFieldPointFunctor L𝓏).obj Z, EtaleSite.PointAxioms L𝓏 z)
  (surjY : Function.Surjective (pointProjection Lᵧ Y))
  (surjZ : Function.Surjective (pointProjection L𝓏 Z))

/-- Successive proper restrictions on compact sections agree with the composite
restriction after the sheaf composition comparison. -/
theorem etaleCompactSectionsRestriction_comp
    (hp : IsProperMap (localizedSpaceFunctor.map f))
    (hq : IsProperMap (localizedSpaceFunctor.map g))
    (hcomp : IsProperMap (localizedSpaceFunctor.map (f ≫ g)))
    (F : Sheaf (etaleTopology Z) modules) :
    (etaleCompactSectionsRestriction.{u, v, uL} hg R Lᵧ L𝓏 hY hZ surjY surjZ hq).app F ≫
        (etaleCompactSectionsRestriction.{u, v, uL} hf R Lₓ Lᵧ hX hY surjX surjY hp).app
          ((etaleRestriction.{u, v, uL} hg R).obj F) ≫
        (etaleCompactSections Lₓ hX R).map ((etaleRestrictionComp.{u, v, uL} hf hg R).hom.app F) =
      (etaleCompactSectionsRestriction.{u, v, uL} (etale_comp hf hg) R Lₓ L𝓏
        hX hZ surjX surjZ hcomp).app F := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (etaleSectionsRestriction_comp.{u, v, uL} hf hg R F) s.val

end Langlands.Sheaf.Equivariant.Analytic
