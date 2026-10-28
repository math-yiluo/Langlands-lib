import Langlands.AlgebraicGeometry.Modules.PullbackTensor

/-! # Canonical tensor comparisons for presheaf-module pullback

The pushforward comparison is restriction of scalars on sectionwise tensors.
Its adjoint is the canonical pullback tensor comparison. These are internal
presheaf constructions; this module does not assert their invertibility.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry

namespace Langlands.Scheme.Modules

local instance presheafPullbackTensorMonoidalCategory (X : AlgebraicGeometry.Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- Mathlib's pushforward on presheaves of modules along the structure morphism of `f`. -/
abbrev presheafPushforward : X.PresheafOfModules ⥤ Y.PresheafOfModules :=
  PresheafOfModules.pushforward.{u} (F := TopologicalSpace.Opens.map f.base)
    (R := X.ringCatSheaf.obj) (S := Y.ringCatSheaf.obj)
    (CategoryTheory.Functor.whiskerRight f.c (forget₂ CommRingCat.{u} RingCat.{u}))

/-- Mathlib's left adjoint to `presheafPushforward f`. -/
abbrev presheafPullback : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.pullback.{u} (F := TopologicalSpace.Opens.map f.base)
    (R := X.ringCatSheaf.obj) (S := Y.ringCatSheaf.obj)
    (CategoryTheory.Functor.whiskerRight f.c (forget₂ CommRingCat.{u} RingCat.{u}))

/-- Mathlib's presheaf pullback-pushforward adjunction for `f`. -/
abbrev presheafPullbackPushforwardAdjunction :
    presheafPullback f ⊣ presheafPushforward f :=
  PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (F := TopologicalSpace.Opens.map f.base)
    (R := X.ringCatSheaf.obj) (S := Y.ringCatSheaf.obj)
    (CategoryTheory.Functor.whiskerRight f.c (forget₂ CommRingCat.{u} RingCat.{u}))

/-- The sectionwise map `U(P) ⊗ U(Q) → U(P ⊗ Q)` sending `p ⊗ q` to `p ⊗ q`. -/
def presheafPushforwardTensorApp (P Q : X.PresheafOfModules) :
    (presheafPushforward f).obj P ⊗ (presheafPushforward f).obj Q ⟶
      (presheafPushforward f).obj (P ⊗ Q) where
  app V :=
    restrictScalarsTensorLift (f.c.app V).hom
      (M := P.obj ((TopologicalSpace.Opens.map f.base).op.obj V))
      (N := Q.obj ((TopologicalSpace.Opens.map f.base).op.obj V)) (𝟙 _)
  naturality := by
    intro V W i
    exact ModuleCat.MonoidalCategory.tensor_ext (fun p q => rfl)

/-- Pure tensors are unchanged, with their tensor product now over `𝒪_X(f⁻¹V)`. -/
@[simp]
lemma presheafPushforwardTensorApp_app_tmul (P Q : X.PresheafOfModules) (V : Y.Opensᵒᵖ)
    (p : ((presheafPushforward f).obj P).obj V)
    (q : ((presheafPushforward f).obj Q).obj V) :
    ((presheafPushforwardTensorApp f P Q).app V).hom (p ⊗ₜ q) =
      TensorProduct.tmul
        (R := X.presheaf.obj ((TopologicalSpace.Opens.map f.base).op.obj V))
        (M := P.obj ((TopologicalSpace.Opens.map f.base).op.obj V))
        (N := Q.obj ((TopologicalSpace.Opens.map f.base).op.obj V)) p q :=
  rfl

/-- Naturality of the presheaf pushforward tensor comparison in both factors. -/
lemma presheafPushforwardTensorApp_naturality {P P' Q Q' : X.PresheafOfModules}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    ((presheafPushforward f).map a ⊗ₘ (presheafPushforward f).map b) ≫
        presheafPushforwardTensorApp f P' Q' =
      presheafPushforwardTensorApp f P Q ≫ (presheafPushforward f).map (a ⊗ₘ b) := by
  exact PresheafOfModules.hom_ext
    (fun V => ModuleCat.MonoidalCategory.tensor_ext (fun p q => rfl))

/-- The natural presheaf pushforward tensor comparison. -/
def presheafPushforwardTensor :
    (presheafPushforward f).prod (presheafPushforward f) ⋙
        CategoryTheory.MonoidalCategory.tensor Y.PresheafOfModules ⟶
      CategoryTheory.MonoidalCategory.tensor X.PresheafOfModules ⋙ presheafPushforward f where
  app PQ := presheafPushforwardTensorApp f PQ.1 PQ.2
  naturality _ _ ab := presheafPushforwardTensorApp_naturality f ab.1 ab.2

@[simp]
lemma presheafPushforwardTensor_app (P Q : X.PresheafOfModules) :
    (presheafPushforwardTensor f).app (P, Q) = presheafPushforwardTensorApp f P Q :=
  rfl

/-- The adjoint comparison `L(M ⊗ N) → L(M) ⊗ L(N)`, defined using the tensor of units. -/
def presheafPullbackTensorComparisonApp (M N : Y.PresheafOfModules) :
    (presheafPullback f).obj (M ⊗ N) ⟶
      (presheafPullback f).obj M ⊗ (presheafPullback f).obj N :=
  ((presheafPullbackPushforwardAdjunction f).homEquiv _ _).symm
    (((presheafPullbackPushforwardAdjunction f).unit.app M ⊗ₘ
        (presheafPullbackPushforwardAdjunction f).unit.app N) ≫
      presheafPushforwardTensorApp f ((presheafPullback f).obj M) ((presheafPullback f).obj N))

/-- The pullback comparison is characterized by its image under the adjunction. -/
lemma homEquiv_presheafPullbackTensorComparisonApp (M N : Y.PresheafOfModules) :
    (presheafPullbackPushforwardAdjunction f).homEquiv _ _
        (presheafPullbackTensorComparisonApp f M N) =
      ((presheafPullbackPushforwardAdjunction f).unit.app M ⊗ₘ
          (presheafPullbackPushforwardAdjunction f).unit.app N) ≫
        presheafPushforwardTensorApp f ((presheafPullback f).obj M)
          ((presheafPullback f).obj N) :=
  Equiv.apply_symm_apply _ _

/-- On pure tensors, the adjunction image sends `m ⊗ n` to `η_M(m) ⊗ η_N(n)`. -/
lemma homEquiv_presheafPullbackTensorComparisonApp_app_tmul
    (M N : Y.PresheafOfModules) (V : Y.Opensᵒᵖ) (m : M.obj V) (n : N.obj V) :
    (((presheafPullbackPushforwardAdjunction f).homEquiv _ _
        (presheafPullbackTensorComparisonApp f M N)).app V).hom (m ⊗ₜ n) =
      TensorProduct.tmul
        (R := X.presheaf.obj ((TopologicalSpace.Opens.map f.base).op.obj V))
        (M := ((presheafPullback f).obj M).obj ((TopologicalSpace.Opens.map f.base).op.obj V))
        (N := ((presheafPullback f).obj N).obj ((TopologicalSpace.Opens.map f.base).op.obj V))
        (((presheafPullbackPushforwardAdjunction f).unit.app M).app V m)
        (((presheafPullbackPushforwardAdjunction f).unit.app N).app V n) := by
  rw [homEquiv_presheafPullbackTensorComparisonApp]
  rfl

/-- Equivalently, pull back the defining composite and then apply the counit. -/
lemma presheafPullbackTensorComparisonApp_eq (M N : Y.PresheafOfModules) :
    presheafPullbackTensorComparisonApp f M N =
      (presheafPullback f).map
          (((presheafPullbackPushforwardAdjunction f).unit.app M ⊗ₘ
              (presheafPullbackPushforwardAdjunction f).unit.app N) ≫
            presheafPushforwardTensorApp f ((presheafPullback f).obj M)
              ((presheafPullback f).obj N)) ≫
        (presheafPullbackPushforwardAdjunction f).counit.app _ :=
  Adjunction.homEquiv_counit _ _ _ _

/-- Naturality of the presheaf pullback tensor comparison in both factors. -/
lemma presheafPullbackTensorComparisonApp_naturality {M M' N N' : Y.PresheafOfModules}
    (a : M ⟶ M') (b : N ⟶ N') :
    (presheafPullback f).map (a ⊗ₘ b) ≫ presheafPullbackTensorComparisonApp f M' N' =
      presheafPullbackTensorComparisonApp f M N ≫
        ((presheafPullback f).map a ⊗ₘ (presheafPullback f).map b) := by
  apply ((presheafPullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_presheafPullbackTensorComparisonApp, homEquiv_presheafPullbackTensorComparisonApp,
    Category.assoc, ← presheafPushforwardTensorApp_naturality,
    ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom, (presheafPullbackPushforwardAdjunction f).unit_naturality a,
    (presheafPullbackPushforwardAdjunction f).unit_naturality b]

/-- The natural presheaf pullback tensor comparison. -/
def presheafPullbackTensorComparison :
    CategoryTheory.MonoidalCategory.tensor Y.PresheafOfModules ⋙ presheafPullback f ⟶
      (presheafPullback f).prod (presheafPullback f) ⋙
        CategoryTheory.MonoidalCategory.tensor X.PresheafOfModules where
  app MN := presheafPullbackTensorComparisonApp f MN.1 MN.2
  naturality _ _ ab := presheafPullbackTensorComparisonApp_naturality f ab.1 ab.2

@[simp]
lemma presheafPullbackTensorComparison_app (M N : Y.PresheafOfModules) :
    (presheafPullbackTensorComparison f).app (M, N) = presheafPullbackTensorComparisonApp f M N :=
  rfl

end Langlands.Scheme.Modules
