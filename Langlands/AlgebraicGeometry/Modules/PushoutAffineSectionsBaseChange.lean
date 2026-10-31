import Langlands.AlgebraicGeometry.Modules.AffineSectionsBaseChange
import Mathlib.RingTheory.IsTensorProduct

/-! # Canonical affine sections comparison over a pushout of base rings -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace Langlands.Scheme.Modules

variable (R S A B : CommRingCat.{u})
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]

/-- Convert the algebra tensor product to categorical scalar extension, retaining
the scalar action of the second base ring. -/
def pushoutTensorToExtendScalarsEquiv (M : ModuleCat.{u} A) :
    B ⊗[A] M ≃ₗ[S]
      (ModuleCat.restrictScalars (algebraMap S B)).obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
  AddEquiv.toLinearEquiv (extendScalarsAlgebraEquiv A B M).symm.toAddEquiv <| by
    intro s x
    change (extendScalarsAlgebraEquiv A B M).symm (s • x) =
      algebraMap S B s • (extendScalarsAlgebraEquiv A B M).symm x
    rw [← IsScalarTower.algebraMap_smul B s x, map_smul]

/-- The pushout cancellation comparison, in the actual scalar extension and
restriction functors of `ModuleCat`. -/
def pushoutScalarTensorIso (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap R S)).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj M) ≅
      (ModuleCat.restrictScalars (algebraMap S B)).obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) := by
  let MR := (ModuleCat.restrictScalars (algebraMap R A)).obj M
  letI : IsScalarTower R A MR := IsScalarTower.of_compHom R A M
  exact extendScalarsAlgebraIso R S MR ≪≫
    (Algebra.IsPushout.cancelBaseChange R S A B MR).symm.toModuleIso ≪≫
    (pushoutTensorToExtendScalarsEquiv S A B M).toModuleIso

lemma pushoutScalarTensorIso_hom_tmul (M : ModuleCat.{u} A) (s : S)
    (m : (ModuleCat.restrictScalars (algebraMap R A)).obj M) :
    (pushoutScalarTensorIso R S A B M).hom (s ⊗ₜ[R,algebraMap R S] m) =
      algebraMap S B s ⊗ₜ[A,algebraMap A B] m := by
  let : IsScalarTower R A ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
    IsScalarTower.of_compHom R A M
  change (pushoutTensorToExtendScalarsEquiv S A B M)
      ((Algebra.IsPushout.cancelBaseChange R S A B
        ((ModuleCat.restrictScalars (algebraMap R A)).obj M)).symm (s ⊗ₜ[R] m)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
  rfl

@[reassoc]
lemma pushoutScalarTensorIso_naturality {M N : ModuleCat.{u} A} (a : M ⟶ N) :
    (ModuleCat.extendScalars (algebraMap R S)).map
        ((ModuleCat.restrictScalars (algebraMap R A)).map a) ≫
        (pushoutScalarTensorIso R S A B N).hom =
      (pushoutScalarTensorIso R S A B M).hom ≫
        (ModuleCat.restrictScalars (algebraMap S B)).map
          ((ModuleCat.extendScalars (algebraMap A B)).map a) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (pushoutScalarTensorIso R S A B N).hom
      ((1 : S) ⊗ₜ[R,algebraMap R S]
        ((ModuleCat.restrictScalars (algebraMap R A)).map a m)) =
    (ModuleCat.restrictScalars (algebraMap S B)).map
      ((ModuleCat.extendScalars (algebraMap A B)).map a)
      ((pushoutScalarTensorIso R S A B M).hom ((1 : S) ⊗ₜ[R,algebraMap R S] m))
  rw [pushoutScalarTensorIso_hom_tmul, pushoutScalarTensorIso_hom_tmul]
  rfl

/-- The two restrictions of scalars around the commutative algebra square. -/
def pushoutRestrictScalarsIso (N : ModuleCat.{u} B) :
    (ModuleCat.restrictScalars (algebraMap R A)).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj N) ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.restrictScalars (algebraMap S B)).obj N) :=
  (ModuleCat.restrictScalarsComp'App (algebraMap R A) (algebraMap A B)
    (algebraMap R B) (IsScalarTower.algebraMap_eq R A B) N).symm ≪≫
  ModuleCat.restrictScalarsComp'App (algebraMap R S) (algebraMap S B)
    (algebraMap R B) (IsScalarTower.algebraMap_eq R S B) N

/-- The semilinear sections map induced by the actual pullback unit on `Spec A`,
viewed over the base-ring square using the canonical pushforward sections isomorphisms. -/
def pushoutAffineSectionsPullbackMap (M : (Spec A).Modules) :
    (moduleSpecΓFunctor (R := R)).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj M) ⟶
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((moduleSpecΓFunctor (R := S)).obj
          ((AlgebraicGeometry.Scheme.Modules.pushforward
            (Spec.map (CommRingCat.ofHom (algebraMap S B)))).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M))) :=
  (pushforwardΓIso (CommRingCat.ofHom (algebraMap R A))).hom.app M ≫
    (ModuleCat.restrictScalars (algebraMap R A)).map
      (affineSectionsPullbackMap (CommRingCat.ofHom (algebraMap A B)) M) ≫
    (pushoutRestrictScalarsIso R S A B _).hom ≫
    (ModuleCat.restrictScalars (algebraMap R S)).map
      ((pushforwardΓIso (CommRingCat.ofHom (algebraMap S B))).inv.app _)

omit [Algebra.IsPushout R S A B] in
lemma pushoutAffineSectionsPullbackMap_apply (M : (Spec A).Modules)
    (m : (moduleSpecΓFunctor (R := R)).obj
      ((AlgebraicGeometry.Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj M)) :
    pushoutAffineSectionsPullbackMap R S A B M m =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).unit.app M).app ⊤ m :=
  rfl

omit [Algebra.IsPushout R S A B] in
@[reassoc]
lemma pushoutAffineSectionsPullbackMap_naturality {M N : (Spec A).Modules}
    (a : M ⟶ N) :
    (moduleSpecΓFunctor (R := R)).map
        ((AlgebraicGeometry.Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map a) ≫
        pushoutAffineSectionsPullbackMap R S A B N =
      pushoutAffineSectionsPullbackMap R S A B M ≫
        (ModuleCat.restrictScalars (algebraMap R S)).map
          ((moduleSpecΓFunctor (R := S)).map
            ((AlgebraicGeometry.Scheme.Modules.pushforward
              (Spec.map (CommRingCat.ofHom (algebraMap S B)))).map
              ((AlgebraicGeometry.Scheme.Modules.pullback
                (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map a))) := by
  ext m
  have h := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))).unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at h
  exact congrArg (fun k => k.app ⊤ (show Γ(M, ⊤) from m)) h

/-- The scalar-linear adjunct of the pullback-induced sections map over an affine
pushout square. -/
def pushoutAffineScalarSectionsMap (M : (Spec A).Modules) :
    (ModuleCat.extendScalars (algebraMap R S)).obj
        ((moduleSpecΓFunctor (R := R)).obj
          ((AlgebraicGeometry.Scheme.Modules.pushforward
            (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj M)) ⟶
      (moduleSpecΓFunctor (R := S)).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (algebraMap S B)))).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M)) :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv _ _).symm
    (pushoutAffineSectionsPullbackMap R S A B M)

omit [Algebra.IsPushout R S A B] in
@[simp]
lemma pushoutAffineScalarSectionsMap_homEquiv (M : (Spec A).Modules) :
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv _ _
        (pushoutAffineScalarSectionsMap R S A B M) =
      pushoutAffineSectionsPullbackMap R S A B M := by
  simp [pushoutAffineScalarSectionsMap]

omit [Algebra.IsPushout R S A B] in
@[reassoc]
lemma pushoutAffineScalarSectionsMap_unit (M : (Spec A).Modules) :
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app
        ((moduleSpecΓFunctor (R := R)).obj
          ((AlgebraicGeometry.Scheme.Modules.pushforward
            (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj M)) ≫
        (ModuleCat.restrictScalars (algebraMap R S)).map
          (pushoutAffineScalarSectionsMap R S A B M) =
      pushoutAffineSectionsPullbackMap R S A B M := by
  simpa only [Adjunction.homEquiv_unit] using
    pushoutAffineScalarSectionsMap_homEquiv R S A B M

omit [Algebra.IsPushout R S A B] in
lemma pushoutAffineScalarSectionsMap_one_tmul (M : (Spec A).Modules)
    (m : (moduleSpecΓFunctor (R := R)).obj
      ((AlgebraicGeometry.Scheme.Modules.pushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj M)) :
    pushoutAffineScalarSectionsMap R S A B M ((1 : S) ⊗ₜ[R,algebraMap R S] m) =
      pushoutAffineSectionsPullbackMap R S A B M m := by
  have h := congrArg (fun k => k m) (pushoutAffineScalarSectionsMap_homEquiv R S A B M)
  simpa only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] using h

omit [Algebra.IsPushout R S A B] in
@[reassoc]
lemma pushoutAffineScalarSectionsMap_naturality {M N : (Spec A).Modules}
    (a : M ⟶ N) :
    (ModuleCat.extendScalars (algebraMap R S)).map
        ((moduleSpecΓFunctor (R := R)).map
          ((AlgebraicGeometry.Scheme.Modules.pushforward
            (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map a)) ≫
        pushoutAffineScalarSectionsMap R S A B N =
      pushoutAffineScalarSectionsMap R S A B M ≫
        (moduleSpecΓFunctor (R := S)).map
          ((AlgebraicGeometry.Scheme.Modules.pushforward
            (Spec.map (CommRingCat.ofHom (algebraMap S B)))).map
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map a)) := by
  apply ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pushoutAffineScalarSectionsMap_homEquiv, pushoutAffineScalarSectionsMap_homEquiv]
  exact pushoutAffineSectionsPullbackMap_naturality R S A B a

/-- Factorization of the canonical map into tensor cancellation, the affine sections
comparison, and the standard pushforward identifications. -/
lemma pushoutAffineScalarSectionsMap_eq (M : (Spec A).Modules) :
    pushoutAffineScalarSectionsMap R S A B M =
      (ModuleCat.extendScalars (algebraMap R S)).map
          ((pushforwardΓIso (CommRingCat.ofHom (algebraMap R A))).hom.app M) ≫
        (pushoutScalarTensorIso R S A B ((moduleSpecΓFunctor (R := A)).obj M)).hom ≫
        (ModuleCat.restrictScalars (algebraMap S B)).map
          (affineScalarSectionsMap (CommRingCat.ofHom (algebraMap A B)) M) ≫
        (pushforwardΓIso (CommRingCat.ofHom (algebraMap S B))).inv.app _ := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have h := pushoutAffineScalarSectionsMap_one_tmul R S A B M m
  refine h.trans ?_
  change affineSectionsPullbackMap (CommRingCat.ofHom (algebraMap A B)) M m =
    affineScalarSectionsMap (CommRingCat.ofHom (algebraMap A B)) M
      ((pushoutScalarTensorIso R S A B ((moduleSpecΓFunctor (R := A)).obj M)).hom
        ((1 : S) ⊗ₜ[R,algebraMap R S]
          ((pushforwardΓIso (CommRingCat.ofHom (algebraMap R A))).hom.app M m)))
  rw [pushoutScalarTensorIso_hom_tmul, map_one]
  exact (affineScalarSectionsMap_one_tmul _ M _).symm

instance isIso_pushoutAffineScalarSectionsMap (M : (Spec A).Modules)
    [M.IsQuasicoherent] : IsIso (pushoutAffineScalarSectionsMap R S A B M) := by
  rw [pushoutAffineScalarSectionsMap_eq]
  infer_instance

/-- Canonical scalar extension of affine sections commutes with base change along
the specified pushout of algebras. -/
def pushoutAffineScalarSectionsIso (M : (Spec A).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars (algebraMap R S)).obj
        ((moduleSpecΓFunctor (R := R)).obj
          ((AlgebraicGeometry.Scheme.Modules.pushforward
            (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj M)) ≅
      (moduleSpecΓFunctor (R := S)).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (algebraMap S B)))).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M)) :=
  asIso (pushoutAffineScalarSectionsMap R S A B M)

end Langlands.Scheme.Modules
