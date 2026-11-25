/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsLocalSurjectivity
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsCokernelExact

/-! # Right exactness of sheafified tensor sections

Source: blueprint `lem-sc-additive-ideal-image-tensor-comparison`, Proof, Step 2;
Stacks Project, Descent, Tag 070S, Lemma 35.8.5(2), and Tag 03FH(1).
(blueprint: lem-sc-etale-tensor-sections-right-exact)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj

/-- The tensor-section construction on morphisms, before imposing descent. -/
def etaleTensorSectionsMap {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) :
    etaleTensorSectionsPresheaf F ⟶ etaleTensorSectionsPresheaf G where
  app U := ((tensorPullback U.unop.hom).map φ).app ⊤
  naturality {_ _} g := by exact etaleTensorSectionsMap_naturality φ g.unop

/-- Tensor sections are functorial in the module as well as in the étale object. -/
def etaleTensorSectionsPresheafFunctor (X : Scheme.{u}) :
    X.Modules ⥤ (X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) where
  obj := etaleTensorSectionsPresheaf
  map := etaleTensorSectionsMap
  map_id F := by
    apply NatTrans.ext
    funext U
    change ((tensorPullback U.unop.hom).map (𝟙 F)).app ⊤ = 𝟙 _
    exact congrArg (fun ψ ↦ ψ.app ⊤) ((tensorPullback U.unop.hom).map_id F)
  map_comp φ ψ := by
    apply NatTrans.ext
    funext U
    change ((tensorPullback U.unop.hom).map (φ ≫ ψ)).app ⊤ = _
    exact congrArg (fun θ ↦ θ.app ⊤) ((tensorPullback U.unop.hom).map_comp φ ψ)

instance etaleTensorSectionsPresheafFunctor_additive (X : Scheme.{u}) :
    (etaleTensorSectionsPresheafFunctor X).Additive where
  map_add {F G} φ ψ := by
    apply NatTrans.ext
    funext U
    have : (tensorPullback U.unop.hom).Additive :=
      (Classical.choose (exists_tensorPullbackAdjunction U.unop.hom)).left_adjoint_additive
    exact congrArg (fun θ ↦ θ.app ⊤) ((tensorPullback U.unop.hom).map_add (f := φ) (g := ψ))

/-- Lift the tensor sections and sheafify. This is defined for every module;
for quasi-coherent modules the sheafification does not change tensor sections. -/
def etaleTensorSectionsFunctor (X : Scheme.{u}) :
    X.Modules ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  etaleTensorSectionsPresheafFunctor X ⋙
    (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
    presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}

instance etaleTensorSectionsFunctor_preservesZeroMorphisms (X : Scheme.{u}) :
    (etaleTensorSectionsFunctor X).PreservesZeroMorphisms := by
  have : ((CategoryTheory.Functor.whiskeringRight X.Etaleᵒᵖ
      AddCommGrpCat.{u} AddCommGrpCat.{u + 1}).obj
      AddCommGrpCat.uliftFunctor.{u + 1, u}).PreservesZeroMorphisms := inferInstance
  have : (presheafToSheaf X.smallEtaleTopology
      AddCommGrpCat.{u + 1}).PreservesZeroMorphisms := inferInstance
  unfold etaleTensorSectionsFunctor
  infer_instance

/-- On a quasi-coherent module the sheafified construction is the specified tensor sheaf. -/
def etaleTensorSectionsFunctorObjIso {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] :
    (etaleTensorSectionsFunctor X).obj F ≅
      (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (etaleTensorSectionsSheaf F) :=
  (sheafificationIso ((sheafCompose X.smallEtaleTopology
    AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (etaleTensorSectionsSheaf F))).symm

/-- Sheafified tensor sections preserve cokernels of module morphisms.
Source: blueprint `lem-sc-additive-ideal-image-tensor-comparison`, Step 2;
Stacks Project, Descent, Tag 070S, Lemma 35.8.5(2), and Tag 03FH(1).
(blueprint: lem-sc-etale-tensor-sections-right-exact)

Proof: For a module morphism F to G with cokernel Q, tensor pullback is a left
adjoint and takes Q to the cokernel of the pulled-back morphism. A section of that
cokernel locally lifts to G: the module cokernel is the sheafification of the
sectionwise quotient, so this assertion holds on a Zariski cover of each etale
object. A section of G mapping to zero locally comes from F, by the same
sectionwise quotient description. These Zariski covers are etale covers.
Consequently the sheafified tensor-section sequence is right exact. Equivalently,
any morphism of abelian sheaves from the sections of G killing the sections of F
factors uniquely through the sections of Q: lift a section locally, apply the
morphism, and glue; local exactness gives independence of lifts and uniqueness.
Coequalizers are cokernels of differences in these additive categories,
and the constructed functor is additive, so it preserves all parallel-pair
colimits. The additive universe lift preserves this construction. The argument uses no
quasi-coherence, affine hypothesis, nonemptiness, or flatness: tensor pullback is
right exact for every scheme morphism. -/
theorem preservesCokernels_etaleTensorSectionsFunctor (X : Scheme.{u}) :
    PreservesColimitsOfShape WalkingParallelPair (etaleTensorSectionsFunctor X) := by
  let T := etaleTensorSectionsFunctor X
  have : T.Additive := by
    dsimp [T, etaleTensorSectionsFunctor]
    infer_instance
  have hpres : ∀ {F G : X.Modules} (φ : F ⟶ G),
      PreservesColimit (parallelPair φ 0) T := by
    intro F G φ
    let S := ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)
    have hlocal := etaleTensorSections_locallySurjective (cokernel.π φ)
      (etaleTensorSectionsMap (cokernel.π φ)) (fun _ ↦ rfl)
    have hsheaf : Sheaf.IsLocallySurjective (T.map (cokernel.π φ)) :=
      (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
        X.smallEtaleTopology _).2 hlocal
    have : Epi (S.map T).g := by
      change Epi (T.map (cokernel.π φ))
      exact Sheaf.epi_of_isLocallySurjective _
    have hexact : (S.map T).Exact :=
      etaleTensorSections_cokernel_exact φ (etaleTensorSectionsMap φ)
        (etaleTensorSectionsMap (cokernel.π φ)) (fun _ ↦ rfl) (fun _ ↦ rfl)
        (S.map T).zero
    refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel φ) ?_
    exact (CokernelCofork.isColimitMapCoconeEquiv _ T).2 hexact.gIsCokernel
  let : ∀ {F G : X.Modules} (φ : F ⟶ G),
      PreservesColimit (parallelPair φ 0) T := @hpres
  exact Functor.preservesCoequalizers_of_preservesCokernels T

end
end AlgebraicGeometry.Scheme.Modules
