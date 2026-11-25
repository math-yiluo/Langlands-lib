/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex

/-! # Derived pullback/direct image adjunction for schemes

Source: literature/stacks-project/cohomology.tex, Tag 079W, Cohomology Lemma
cohomology-lemma-adjoint (blueprint: lem-pc-ringed-spaces-derived-adjoint).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- For a morphism of schemes, derived pullback is left adjoint to derived direct image.

Proof:
1. The tensor pullback/direct image adjunction of Stacks Tag 0096 induces an
   adjunction on homotopy categories. The object and map clauses of
   `derivedPullback_spec` identify its underived functor with tensor pullback.
2. The recorded sheaf tensor structure and functorial flat resolutions give the
   K-flat left derivability structure. Its categorical K-flat objects satisfy the
   sheaf definition: tensoring an acyclic complex remains acyclic, as checked after
   the homotopy quotient. Thus the chosen pullback counit is invertible on this
   structure. The direct image unit is invertible on K-injectives. Whiskering these
   comparisons gives the two derived-composite universal properties.
3. Apply Mathlib's `Adjunction.derived` to the homotopy adjunction and these
   universal properties. It constructs the adjunction of the chosen functors,
   including the natural Hom equivalences and the triangle identities.
Source: literature/stacks-project/cohomology.tex, Tag 079W, Cohomology Lemma
cohomology-lemma-adjoint (blueprint: lem-pc-ringed-spaces-derived-adjoint). -/
theorem nonempty_derivedPullbackAdjunction (f : X ⟶ Y) :
    Nonempty (derivedPullback f ⊣ schemeDerivedDirectImage f) := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let : MonoidalCategory A := SheafOfModules.monoidalCategory Y.sheaf
  let : SymmetricCategory A := SheafOfModules.symmetricCategory Y.sheaf
  have : MonoidalPreadditive A := Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1
  let : MonoidalClosed A := Classical.choice (SheafOfModules.tensorClosed Y.sheaf).2.1
  have : CategoryTheory.Limits.HasColimitsOfSize.{0, 0} A :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} A
  have : Abelian.HasFunctorialFlatResolution A := schemeModule_hasFunctorialFlatResolution Y
  have : IsGrothendieckAbelian.{u} A :=
    SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have (M : A) : CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor A).flip.obj M) :=
    CategoryTheory.Limits.preservesColimitsOfShape_of_natIso
      (F := MonoidalCategory.tensorLeft M)
      (NatIso.ofComponents (fun N ↦ BraidedCategory.braiding M N)
        (by intros; simp [MonoidalCategory.curriedTensor]))
  have : CategoryTheory.HasExactColimitsOfShape ℤ A := inferInstance
  have (M : A) : CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor A).obj M) := inferInstance
  have : LocalizerMorphism.IsLeftDerivabilityStructure
      (HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat := by
    set_option synthInstance.maxSize 512 in infer_instance
  let G : A ⥤ B := Scheme.Modules.tensorPullback f
  obtain ⟨_, _, _, _, _, _, _, E, hE, hEmap, hEadd, ε, hε, _, hK⟩ :=
      derivedPullback_spec f
  have h : E = G := CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  have : G.Additive := hEadd
  have toIsKFlat (P : CochainComplex A ℤ)
      (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P) :
      CochainComplex.IsKFlatTensor (R := Y.sheaf) P := by
    intro F hF
    have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
      ((HomotopyCategory.quotient A (.up ℤ)).obj P)).mp
        ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
      (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).mpr hF)).2
  have : Abelian.HasKInjectiveResolutions B :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have : (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso A (.up ℤ)) := hε
  have hleft := (HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat
    |>.isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure ε
      (by
        rintro ⟨P, hP⟩
        obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
        exact hK K (toIsKFlat K ((HomotopyCategory.kFlat_quotient_obj_iff K).mp hP)))
      (schemeDerivedDirectImage f)
  have : (derivedPullback f ⋙ schemeDerivedDirectImage f).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε (schemeDerivedDirectImage f))
      (HomotopyCategory.quasiIso A (.up ℤ)) := hleft
  let β := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit
  have hright := (HomotopyCategory.KInjectives.localizerMorphism B)
    |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure β
      (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives _)
        |>.isIso_of_isRightDerivedFunctor β I) (derivedPullback f)
  have : (schemeDerivedDirectImage f ⋙ derivedPullback f).IsRightDerivedFunctor
      (Functor.whiskerRight β (derivedPullback f) ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso B (.up ℤ)) := hright
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)
  let homotopyAdj := adj.mapHomotopyCategory (.up ℤ)
  let d := homotopyAdj.derived (G' := derivedPullback f) (F' := schemeDerivedDirectImage f)
    (HomotopyCategory.quasiIso A (.up ℤ))
    (HomotopyCategory.quasiIso B (.up ℤ)) ε β
  exact ⟨d⟩

end AlgebraicGeometry
