import Langlands.AlgebraicGeometry.RelativeDifferentialsUniversal
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Algebraic-to-sheaf differential comparison on spectra -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme

variable (R A : CommRingCat.{u}) [Algebra R A]

local notation "φ" => (CommRingCat.ofHom (algebraMap R A))

local instance (M : (Spec A).Modules) : Module R Γ(M, ⊤) :=
  Module.compHom Γ(M, ⊤) (algebraMap R A)

local instance (M : (Spec A).Modules) :
    IsScalarTower R A Γ(M, ⊤) :=
  IsScalarTower.of_compHom R A Γ(M, ⊤)

namespace RelativeDerivation

/-- The algebraic derivation obtained by taking global sections on a spectrum. -/
def specToAlgebra {M : (Spec A).Modules} (d : RelativeDerivation (Spec.map φ) M) :
    Derivation R A Γ(M, ⊤) where
  toFun a := d.app ⊤ ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv a)
  map_add' a b := by simp only [map_add]
  map_smul' r a := by
    have hz : d.app ⊤ ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ((algebraMap R A) r)) = 0 := by
      change d.app ⊤ ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv (φ r)) = 0
      rw [← CommRingCat.comp_apply, AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply]
      exact d.app_base_restrict ⊤ ⊤ (by simp) _
    rw [Algebra.smul_def]
    rw [map_mul, app_mul, hz, smul_zero, add_zero]
    rfl
  map_one_eq_zero' := by
    change d.app ⊤ ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv 1) = 0
    rw [map_one]
    exact d.d_one _
  leibniz' a b := by
    change d.app ⊤ ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv (a * b)) =
      a • d.app ⊤ ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv b) +
      b • d.app ⊤ ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv a)
    rw [map_mul, app_mul]
    rfl

@[simp]
lemma specToAlgebra_apply {M : (Spec A).Modules}
    (d : RelativeDerivation (Spec.map φ) M) (a : A) :
    specToAlgebra R A d a = d.app ⊤ ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv a) := rfl

end RelativeDerivation

/-- The global linear comparison induced by the actual universal derivation. -/
def relativeDifferentialsSpecLinearMap :
    ModuleCat.of A (KaehlerDifferential R A) ⟶
      moduleSpecΓFunctor.obj (relativeDifferentials (Spec.map φ)) :=
  ModuleCat.ofHom (Y := moduleSpecΓFunctor.obj (relativeDifferentials (Spec.map φ)))
    (RelativeDerivation.specToAlgebra R A (relativeDifferentialsDerivation (Spec.map φ))).liftKaehlerDifferential

/-- The canonical comparison from algebraic differentials to the actual differential sheaf. -/
def relativeDifferentialsSpecMap :
    tilde (ModuleCat.of A (KaehlerDifferential R A)) ⟶ relativeDifferentials (Spec.map φ) :=
  (tilde.adjunction.homEquiv _ _).symm (relativeDifferentialsSpecLinearMap R A)

@[simp]
lemma relativeDifferentialsSpecMap_adjoint :
    tilde.adjunction.homEquiv _ _ (relativeDifferentialsSpecMap R A) =
      relativeDifferentialsSpecLinearMap R A :=
  Equiv.apply_symm_apply _ _

/-- Compatibility with the algebraic and sheaf universal derivations under tilde adjunction. -/
@[simp]
lemma relativeDifferentialsSpecMap_adjoint_D (a : A) :
    (tilde.adjunction.homEquiv _ _ (relativeDifferentialsSpecMap R A))
      (KaehlerDifferential.D R A a) =
    (relativeDifferentialsDerivation (Spec.map φ)).app ⊤
      ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv a) := by
  rw [relativeDifferentialsSpecMap_adjoint]
  exact (RelativeDerivation.specToAlgebra R A
    (relativeDifferentialsDerivation (Spec.map φ))).liftKaehlerDifferential_comp_D a

/-- Local sections of the comparison send each algebraic differential to the sheaf differential. -/
lemma relativeDifferentialsSpecMap_app_toOpen_D (W : (Spec A).Opens) (a : A) :
    (relativeDifferentialsSpecMap R A).app W
      (tilde.toOpen (ModuleCat.of A (KaehlerDifferential R A)) W
        (KaehlerDifferential.D R A a)) =
    (relativeDifferentialsDerivation (Spec.map φ)).app W
      ((Spec A).presheaf.map W.leTop.op ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv a)) := by
  have h : tilde.toOpen (ModuleCat.of A (KaehlerDifferential R A)) W ≫
      (modulesSpecToSheaf.map (relativeDifferentialsSpecMap R A)).hom.app (.op W) =
    relativeDifferentialsSpecLinearMap R A ≫
      (modulesSpecToSheaf.obj (relativeDifferentials (Spec.map φ))).presheaf.map W.leTop.op := by
    change tilde.toOpen _ W ≫
      (modulesSpecToSheaf.map (tilde.map (relativeDifferentialsSpecLinearMap R A) ≫
        (relativeDifferentials (Spec.map φ)).fromTildeΓ)).hom.app (.op W) = _
    rw [Functor.map_comp]
    change tilde.toOpen _ W ≫
      ((modulesSpecToSheaf.map (tilde.map (relativeDifferentialsSpecLinearMap R A))).hom.app (.op W) ≫
        (modulesSpecToSheaf.map
          (relativeDifferentials (Spec.map φ)).fromTildeΓ).hom.app (.op W)) = _
    rw [← Category.assoc, tilde.toOpen_map_app, Category.assoc]
    exact congrArg (fun k => relativeDifferentialsSpecLinearMap R A ≫ k)
      ((relativeDifferentials (Spec.map φ)).toOpen_fromTildeΓ_app W)
  have ha := congrArg (fun k => k (KaehlerDifferential.D R A a)) h
  change (relativeDifferentialsSpecMap R A).app W
      (tilde.toOpen (ModuleCat.of A (KaehlerDifferential R A)) W
        (KaehlerDifferential.D R A a)) =
    (relativeDifferentials (Spec.map φ)).presheaf.map W.leTop.op
      (relativeDifferentialsSpecLinearMap R A (KaehlerDifferential.D R A a)) at ha
  rw [← relativeDifferentialsSpecMap_adjoint, relativeDifferentialsSpecMap_adjoint_D] at ha
  exact ha.trans ((relativeDifferentialsDerivation (Spec.map φ)).app_restrict W.leTop _).symm

/-- The adjoint's values on algebraic differentials uniquely determine the comparison. -/
lemma relativeDifferentialsSpecMap_unique
    (α : tilde (ModuleCat.of A (KaehlerDifferential R A)) ⟶ relativeDifferentials (Spec.map φ))
    (h : ∀ a : A, (tilde.adjunction.homEquiv _ _ α) (KaehlerDifferential.D R A a) =
      (relativeDifferentialsDerivation (Spec.map φ)).app ⊤
        ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv a)) :
    α = relativeDifferentialsSpecMap R A := by
  apply (tilde.adjunction.homEquiv _ _).injective
  apply ModuleCat.hom_ext
  let : Module R (moduleSpecΓFunctor.obj (relativeDifferentials (Spec.map φ))) :=
    Module.compHom _ (algebraMap R A)
  let : IsScalarTower R A
      (moduleSpecΓFunctor.obj (relativeDifferentials (Spec.map φ))) :=
    IsScalarTower.of_compHom R A _
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  exact (h a).trans (relativeDifferentialsSpecMap_adjoint_D R A a).symm

end Langlands.Scheme
