import Langlands.AlgebraicGeometry.Modules.Tensor

/-! # The canonical tensor comparison for pullback of module sheaves

For `f : X ⟶ Y`, `pushforwardTensor f` is the canonical map `f_*P ⊗ f_*Q → f_*(P ⊗ Q)` and
`pullbackTensorComparison f` is its adjoint comparison `f^*(M ⊗ N) → f^*M ⊗ f^*N`
(Stacks 01CD). Invertibility is not proved here. -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry

namespace Langlands.Scheme.Modules

local instance (X : AlgebraicGeometry.Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- The sheafification unit `P ⊗ Q → tensorObj P Q` on the sectionwise tensor presheaf. -/
abbrev tensorSheafifyUnit (P Q : X.Modules) : P.val ⊗ Q.val ⟶ (tensorObj P Q).val :=
  (sheafifyAdjunction X).unit.app (P.val ⊗ Q.val)

/-- Precomposition with `tensorMap a b` corresponds to precomposition with `a ⊗ b` on presheaves. -/
lemma tensorHomEquiv_tensorMap_comp {P P' Q Q' T : X.Modules} (a : P ⟶ P') (b : Q ⟶ Q')
    (g : tensorObj P' Q' ⟶ T) :
    tensorHomEquiv P Q T (tensorMap a b ≫ g) = (a.val ⊗ₘ b.val) ≫ tensorHomEquiv P' Q' T g :=
  (sheafifyAdjunction X).homEquiv_naturality_left _ _

/-- Postcomposition with a sheaf map corresponds to postcomposition with its underlying map. -/
lemma tensorHomEquiv_comp {P Q T T' : X.Modules} (g : tensorObj P Q ⟶ T) (h : T ⟶ T') :
    tensorHomEquiv P Q T' (g ≫ h) = tensorHomEquiv P Q T g ≫ h.val :=
  (sheafifyAdjunction X).homEquiv_naturality_right _ _

/-- Naturality of the sheafification unit with respect to `tensorMap`. -/
lemma tensorSheafifyUnit_naturality {P P' Q Q' : X.Modules} (a : P ⟶ P') (b : Q ⟶ Q') :
    (a.val ⊗ₘ b.val) ≫ tensorSheafifyUnit P' Q' = tensorSheafifyUnit P Q ≫ (tensorMap a b).val :=
  (sheafifyAdjunction X).unit.naturality (a.val ⊗ₘ b.val)

/-- Functoriality of `tensorMap` under composition. -/
lemma tensorMap_comp {P P' P'' Q Q' Q'' : X.Modules} (a : P ⟶ P') (a' : P' ⟶ P'')
    (b : Q ⟶ Q') (b' : Q' ⟶ Q'') :
    tensorMap a b ≫ tensorMap a' b' = tensorMap (a ≫ a') (b ≫ b') :=
  ((tensorFunctor X).map_comp (X := (P, Q)) (Y := (P', Q')) (Z := (P'', Q'')) (a, b) (a', b')).symm

/-- Restriction of scalars along `φ : R →+* S` turns an `S`-linear map `g : M ⊗_S N → T` into the
`R`-linear map `M ⊗_R N → T` sending `m ⊗ n` to `g (m ⊗ n)`. -/
def restrictScalarsTensorLift {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {M N T : ModuleCat.{u} S} (g : M ⊗ N ⟶ T) :
    (ModuleCat.restrictScalars φ).obj M ⊗ (ModuleCat.restrictScalars φ).obj N ⟶
      (ModuleCat.restrictScalars φ).obj T :=
  ModuleCat.MonoidalCategory.tensorLift (fun m n => g.hom ((m : M) ⊗ₜ[S] (n : N)))
    (fun m₁ m₂ n => (congrArg g.hom (TensorProduct.add_tmul (R := S) (M := M) (N := N) m₁ m₂ n)).trans
      (map_add g.hom _ _))
    (fun a m n => (congrArg g.hom
      (TensorProduct.smul_tmul' (R := S) (M := M) (N := N) (φ a) m n).symm).trans
      (map_smul g.hom (φ a) _))
    (fun m n₁ n₂ => (congrArg g.hom (TensorProduct.tmul_add (R := S) (M := M) (N := N) m n₁ n₂)).trans
      (map_add g.hom _ _))
    (fun a m n => (congrArg g.hom
      (TensorProduct.tmul_smul (R := S) (M := M) (N := N) (φ a) m n)).trans
      (map_smul g.hom (φ a) _))

@[simp]
lemma restrictScalarsTensorLift_tmul {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {M N T : ModuleCat.{u} S} (g : M ⊗ N ⟶ T) (m : M) (n : N) :
    (restrictScalarsTensorLift φ g).hom (m ⊗ₜ n) = g.hom (m ⊗ₜ n) :=
  rfl

/-- The presheaf map `f_*P ⊗ f_*Q → f_*(P ⊗ Q)` sending `p ⊗ q` to the sheafified `p ⊗ q`. -/
def pushforwardTensorPresheafHom (P Q : X.Modules) :
    ((Scheme.Modules.pushforward f).obj P).val ⊗ ((Scheme.Modules.pushforward f).obj Q).val ⟶
      ((Scheme.Modules.pushforward f).obj (tensorObj P Q)).val where
  app U :=
    restrictScalarsTensorLift (f.c.app U).hom
      (M := P.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U))
      (N := Q.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U))
      (T := (tensorObj P Q).val.obj ((TopologicalSpace.Opens.map f.base).op.obj U))
      ((tensorSheafifyUnit P Q).app ((TopologicalSpace.Opens.map f.base).op.obj U))
  naturality := by
    intro U V i
    refine ModuleCat.MonoidalCategory.tensor_ext (fun p q => ?_)
    have h := PresheafOfModules.naturality_apply (tensorSheafifyUnit P Q)
      ((TopologicalSpace.Opens.map f.base).op.map i)
      ((p : P.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U)) ⊗ₜ
        (q : Q.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U)))
    change (tensorSheafifyUnit P Q).app ((TopologicalSpace.Opens.map f.base).op.obj V)
        ((P.val.map ((TopologicalSpace.Opens.map f.base).op.map i) p :
            P.val.obj ((TopologicalSpace.Opens.map f.base).op.obj V)) ⊗ₜ
          (Q.val.map ((TopologicalSpace.Opens.map f.base).op.map i) q :
            Q.val.obj ((TopologicalSpace.Opens.map f.base).op.obj V))) =
      (tensorObj P Q).val.map ((TopologicalSpace.Opens.map f.base).op.map i)
        ((tensorSheafifyUnit P Q).app ((TopologicalSpace.Opens.map f.base).op.obj U)
          ((p : P.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U)) ⊗ₜ
            (q : Q.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U))))
    exact h

/-- On an open `U` of `Y`, `pushforwardTensorPresheafHom` sends `p ⊗ q` to the image of `p ⊗ q`
under the sheafification unit on `f⁻¹U`. -/
lemma pushforwardTensorPresheafHom_app_tmul (P Q : X.Modules) (U : Y.Opensᵒᵖ)
    (p : ((Scheme.Modules.pushforward f).obj P).val.obj U)
    (q : ((Scheme.Modules.pushforward f).obj Q).val.obj U) :
    ((pushforwardTensorPresheafHom f P Q).app U).hom (p ⊗ₜ q) =
      (tensorSheafifyUnit P Q).app ((TopologicalSpace.Opens.map f.base).op.obj U)
        ((p : P.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U)) ⊗ₜ
          (q : Q.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U))) :=
  rfl

/-- The canonical map `tensorObj (f_*P) (f_*Q) → f_*(tensorObj P Q)`: the sheaf map adjoint
to `pushforwardTensorPresheafHom` under the sheafification adjunction on `Y`. -/
def pushforwardTensorApp (P Q : X.Modules) :
    tensorObj ((Scheme.Modules.pushforward f).obj P) ((Scheme.Modules.pushforward f).obj Q) ⟶
      (Scheme.Modules.pushforward f).obj (tensorObj P Q) :=
  (tensorHomEquiv _ _ _).symm (pushforwardTensorPresheafHom f P Q)

/-- `pushforwardTensorApp` corresponds to `pushforwardTensorPresheafHom` under `tensorHomEquiv`. -/
lemma tensorHomEquiv_pushforwardTensorApp (P Q : X.Modules) :
    tensorHomEquiv _ _ _ (pushforwardTensorApp f P Q) = pushforwardTensorPresheafHom f P Q :=
  (tensorHomEquiv _ _ _).apply_symm_apply _

/-- Naturality of `pushforwardTensorApp` in both factors. -/
lemma pushforwardTensorApp_naturality {P P' Q Q' : X.Modules} (a : P ⟶ P') (b : Q ⟶ Q') :
    tensorMap ((Scheme.Modules.pushforward f).map a) ((Scheme.Modules.pushforward f).map b) ≫
        pushforwardTensorApp f P' Q' =
      pushforwardTensorApp f P Q ≫ (Scheme.Modules.pushforward f).map (tensorMap a b) := by
  apply (tensorHomEquiv _ _ _).injective
  rw [tensorHomEquiv_tensorMap_comp, tensorHomEquiv_comp, tensorHomEquiv_pushforwardTensorApp,
    tensorHomEquiv_pushforwardTensorApp]
  refine PresheafOfModules.hom_ext (fun U => ModuleCat.MonoidalCategory.tensor_ext (fun p q => ?_))
  have h := congrArg (fun φ => (φ.app ((TopologicalSpace.Opens.map f.base).op.obj U)).hom
      ((p : P.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U)) ⊗ₜ
        (q : Q.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U))))
    (tensorSheafifyUnit_naturality a b)
  exact h

/-- The canonical pushforward tensor map `f_*P ⊗ f_*Q → f_*(P ⊗ Q)`, natural in `P` and `Q`. -/
def pushforwardTensor :
    (Scheme.Modules.pushforward f).prod (Scheme.Modules.pushforward f) ⋙ tensorFunctor Y ⟶
      tensorFunctor X ⋙ Scheme.Modules.pushforward f where
  app PQ := pushforwardTensorApp f PQ.1 PQ.2
  naturality _ _ ab := pushforwardTensorApp_naturality f ab.1 ab.2

@[simp]
lemma pushforwardTensor_app (P Q : X.Modules) :
    (pushforwardTensor f).app (P, Q) = pushforwardTensorApp f P Q :=
  rfl

/-- The canonical map `f^*(M ⊗ N) → f^*M ⊗ f^*N`: the adjoint, under the pullback-pushforward
adjunction, of `M ⊗ N → f_*f^*M ⊗ f_*f^*N → f_*(f^*M ⊗ f^*N)`. -/
def pullbackTensorComparisonApp (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (tensorObj M N) ⟶
      tensorObj ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (tensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      pushforwardTensorApp f ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N))

/-- The comparison corresponds, under the pullback-pushforward adjunction, to the composite
`M ⊗ N → f_*f^*M ⊗ f_*f^*N → f_*(f^*M ⊗ f^*N)`. -/
lemma homEquiv_pullbackTensorComparisonApp (M N : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (pullbackTensorComparisonApp f M N) =
      tensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
        pushforwardTensorApp f ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N) :=
  Equiv.apply_symm_apply _ _

/-- Explicit form of the comparison: pull back the composite and apply the adjunction counit. -/
lemma pullbackTensorComparisonApp_eq (M N : Y.Modules) :
    pullbackTensorComparisonApp f M N =
      (Scheme.Modules.pullback f).map
          (tensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
              ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
            pushforwardTensorApp f ((Scheme.Modules.pullback f).obj M)
              ((Scheme.Modules.pullback f).obj N)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app _ :=
  Adjunction.homEquiv_counit _ _ _ _

/-- Naturality of `pullbackTensorComparisonApp` in both factors. -/
lemma pullbackTensorComparisonApp_naturality {M M' N N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (tensorMap a b) ≫ pullbackTensorComparisonApp f M' N' =
      pullbackTensorComparisonApp f M N ≫
        tensorMap ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_pullbackTensorComparisonApp, homEquiv_pullbackTensorComparisonApp, Category.assoc,
    ← pushforwardTensorApp_naturality, ← Category.assoc, ← Category.assoc, tensorMap_comp,
    tensorMap_comp, (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality a,
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality b]

/-- The canonical tensor comparison `f^*(M ⊗ N) → f^*M ⊗ f^*N`, natural in `M` and `N`
(Stacks 01CD); its invertibility is not proved here. -/
def pullbackTensorComparison :
    tensorFunctor Y ⋙ Scheme.Modules.pullback f ⟶
      (Scheme.Modules.pullback f).prod (Scheme.Modules.pullback f) ⋙ tensorFunctor X where
  app MN := pullbackTensorComparisonApp f MN.1 MN.2
  naturality _ _ ab := pullbackTensorComparisonApp_naturality f ab.1 ab.2

@[simp]
lemma pullbackTensorComparison_app (M N : Y.Modules) :
    (pullbackTensorComparison f).app (M, N) = pullbackTensorComparisonApp f M N :=
  rfl

end Langlands.Scheme.Modules
