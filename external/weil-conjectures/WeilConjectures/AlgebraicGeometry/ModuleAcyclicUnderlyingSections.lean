/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import Mathlib.CategoryTheory.Sites.Adjunction

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale

/-- The module-to-group forgetful functor is also a left adjoint: restriction to integers
is left adjoint to coextension, and integer modules are equivalent to abelian groups. -/
private lemma forget_leftAdjoint (R : Type (u + 1)) [CommRing R] :
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).IsLeftAdjoint := by
  let V := ModuleCat.restrictScalars.{u + 1} (algebraMap ℤ R) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let e : V ≅ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)
  have : (ModuleCat.restrictScalars.{u + 1} (algebraMap ℤ R)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (algebraMap ℤ R)).isLeftAdjoint
  exact Functor.isLeftAdjoint_of_iso e

/-- Compare inverse image before and after forgetting coefficients, using the canonical
Kan-extension and sheafification comparisons. -/
private noncomputable def pullbackForgetIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    (R : Type (u + 1)) [CommRing R]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (i)^*[AddCommGrpCat.{u + 1}].obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj M) ≅
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj
      ((i)^*[ModuleCat.{u + 1} R].obj M) := by
  let U := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let := forget_leftAdjoint R
  let G := (MorphismProperty.Over.pullback @Etale ⊤ i).op
  exact (presheafToSheaf _ AddCommGrpCat.{u + 1}).mapIso
    (Functor.leftKanExtensionCompIsoOfPreserves U M.obj G).symm ≪≫
    (sheafComposeNatIso Y.smallEtaleTopology U
      (sheafificationAdjunction _ (ModuleCat.{u + 1} R))
      (sheafificationAdjunction _ AddCommGrpCat.{u + 1})).app (G.lan.obj M.obj)

/-- The comparison respects the unit: sheafification naturality moves the Kan comparison
past its unit, then the two canonical comparison factorization identities apply. -/
private lemma pullbackForgetIso_unit {X Y : Scheme.{u}} (i : Y ⟶ X) (R : Type (u + 1)) [CommRing R]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj M) ≫
      (i)_*[AddCommGrpCat.{u + 1}].map (pullbackForgetIso i R M).hom =
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app M) := by
  apply (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_injective
  change (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app _) ≫
      Functor.whiskerLeft (MorphismProperty.Over.pullback @Etale ⊤ i).op
        ((sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (pullbackForgetIso i R M).hom) =
    Functor.whiskerRight ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app M))
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
  simp only [upperStarLowerStarAdjunction,
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app]
  dsimp
  simp only [Category.comp_id]
  let U := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let G := (MorphismProperty.Over.pullback @Etale ⊤ i).op
  let J := Y.smallEtaleTopology
  let := forget_leftAdjoint R
  change (G.leftKanExtensionUnit (M.obj ⋙ U) ≫
      Functor.whiskerLeft G (toSheafify J (G.lan.obj (M.obj ⋙ U)))) ≫
      Functor.whiskerLeft G (sheafifyMap J (U.leftKanExtensionCompIsoOfPreserves M.obj G).inv ≫
        (sheafifyComposeIso J U (G.lan.obj M.obj)).hom) =
    Functor.whiskerRight (G.leftKanExtensionUnit M.obj ≫
      Functor.whiskerLeft G (toSheafify J (G.lan.obj M.obj))) U
  rw [Functor.whiskerLeft_comp, Category.assoc,
    ← Category.assoc (Functor.whiskerLeft G _),
    ← Functor.whiskerLeft_comp]
  erw [← toSheafify_naturality]
  erw [← Functor.whiskerLeft_comp, Category.assoc, sheafComposeIso_hom_fac,
    Functor.whiskerLeft_comp, ← Category.assoc, Functor.leftKanExtensionCompIsoOfPreserves_inv_fac]
  ext
  simp
  rfl

/-- Forgetting coefficients preserves bijectivity of restriction on global sections.
Source: Stacks Project, Tag 03FD (forgetting coefficients) and Tag 095T, paragraph 2.
(blueprint: new-module-acyclic-underlying-sections)

Proof: The forgetful functor from modules to abelian groups preserves limits and
colimits. It therefore commutes with the sheafification construction of inverse
image. This gives the canonical natural isomorphism U(i^* M) ≅ i^* U(M).
Evaluation at the terminal site object and the global-sections/terminal-sections
isomorphisms identify the underlying group of Γ(M) with Γ(U(M)), and similarly on Y.
Naturality of the inverse-image adjunction unit identifies the restriction maps
under these comparisons. The given module isomorphism has a two-sided inverse;
forget its scalar structure and conjugate by the comparison isomorphisms to obtain
an inverse of the displayed abelian restriction. This also applies to the zero sheaf. -/
theorem Etale.bijective_underlying_globalSectionsUpperStarMap
    {X Y : Scheme.{u}} (i : Y ⟶ X) (r : ℕ)
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    (h : IsIso (globalSectionsUpperStarMap
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) i M)) :
    Function.Bijective (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).obj M)) := by
  let R := ULift.{u + 1} (ZMod r)
  let U := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let UM := (sheafCompose X.smallEtaleTopology U).obj M
  let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app M
  let θ := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app UM
  have hη : IsIso (η.hom.app (Opposite.op (⊤_ X.Etale))) := by
    change IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} R) i M) at h
    unfold globalSectionsUpperStarMap at h
    have h' := (show IsIso (((sheafSections X.smallEtaleTopology
      (ModuleCat.{u + 1} R)).obj (Opposite.op (⊤_ X.Etale))).map η) by
        simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using h)
    exact h'
  have hw := congrArg (fun f ↦ f.hom.app (Opposite.op (⊤_ X.Etale)))
    (pullbackForgetIso_unit i R M)
  change θ.hom.app (Opposite.op (⊤_ X.Etale)) ≫
    ((i)_*[AddCommGrpCat.{u + 1}].map (pullbackForgetIso i R M).hom).hom.app
      (Opposite.op (⊤_ X.Etale)) = U.map (η.hom.app (Opposite.op (⊤_ X.Etale))) at hw
  have : IsIso (θ.hom.app (Opposite.op (⊤_ X.Etale))) :=
    IsIso.of_isIso_fac_right hw
  have : IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i UM) := by
    have : IsIso (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (Opposite.op (⊤_ X.Etale))).map θ) := ‹IsIso (θ.hom.app (Opposite.op (⊤_ X.Etale)))›
    unfold globalSectionsUpperStarMap
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry
