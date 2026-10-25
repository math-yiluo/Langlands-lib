import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Pullback of an associated sheaf along a morphism of spectra -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite

open scoped ChangeOfRings TensorProduct

namespace Langlands.Scheme.Modules

variable {R A : CommRingCat.{u}} (φ : R ⟶ A)

/-- Global sections over `Spec R` of a pushforward along `Spec.map φ` are the restriction of
scalars along `φ` of the global sections over `Spec A`. -/
def pushforwardΓIso :
    AlgebraicGeometry.Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := A) ⋙ ModuleCat.restrictScalars φ.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤))

lemma pushforwardΓIso_hom_app_apply (N : (Spec A).Modules)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((AlgebraicGeometry.Scheme.Modules.pushforward (Spec.map φ)).obj N)) :
    ((pushforwardΓIso φ).hom.app N) x = x :=
  rfl

lemma pushforwardΓIso_inv_app_apply (N : (Spec A).Modules)
    (x : (ModuleCat.restrictScalars φ.hom).obj ((moduleSpecΓFunctor (R := A)).obj N)) :
    ((pushforwardΓIso φ).inv.app N) x = x :=
  rfl

/-- The composite adjunction `tilde ⋙ pullback ⊣ pushforward ⋙ Γ`. -/
def tildePullbackAdjunction :
    tilde.functor R ⋙ AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ) ⊣
      AlgebraicGeometry.Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) :=
  tilde.adjunction.comp (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction _)

/-- The composite adjunction `extendScalars ⋙ tilde ⊣ Γ ⋙ restrictScalars`, transported to the
right adjoint `pushforward ⋙ Γ` along `pushforwardΓIso`. -/
def extendScalarsTildeAdjunction :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor A ⊣
      AlgebraicGeometry.Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).ofNatIsoRight
    (pushforwardΓIso φ).symm

/-- The canonical natural isomorphism `p^* (M^~) ≅ (A ⊗[R] M)^~` for `p = Spec.map φ`, obtained by
uniqueness of left adjoints. -/
def tildePullbackNatIso :
    tilde.functor R ⋙ AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor A :=
  (tildePullbackAdjunction φ).leftAdjointUniq (extendScalarsTildeAdjunction φ)

/-- The canonical isomorphism `p^* (M^~) ≅ (A ⊗[R] M)^~` for `p = Spec.map φ`. -/
def tildePullbackIso (M : ModuleCat.{u} R) :
    (AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj M) :=
  (tildePullbackNatIso φ).app M

lemma tildePullbackNatIso_app (M : ModuleCat.{u} R) :
    (tildePullbackNatIso φ).app M = tildePullbackIso φ M :=
  rfl

/-- Naturality of `tildePullbackIso` in the module. -/
@[reassoc]
lemma tildePullbackIso_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).map (tilde.map f) ≫
        (tildePullbackIso φ N).hom =
      (tildePullbackIso φ M).hom ≫ tilde.map ((ModuleCat.extendScalars φ.hom).map f) :=
  (tildePullbackNatIso φ).hom.naturality f

/-- Naturality of the inverse of `tildePullbackIso` in the module. -/
@[reassoc]
lemma tildePullbackIso_inv_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    tilde.map ((ModuleCat.extendScalars φ.hom).map f) ≫ (tildePullbackIso φ N).inv =
      (tildePullbackIso φ M).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).map (tilde.map f) :=
  (tildePullbackNatIso φ).inv.naturality f

/-- The adjoint `M^~ ⟶ p_* N` of a morphism `p^* (M^~) ⟶ N`. -/
abbrev tildePullbackAdjoint {M : ModuleCat.{u} R} {N : (Spec A).Modules}
    (g : (AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ⟶ N) :
    tilde M ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward (Spec.map φ)).obj N :=
  (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _ g

/-- Morphisms out of `p^* (M^~)` are determined by the images of the global generators
`tilde.toOpen M ⊤ m` under their adjoints. -/
lemma tildePullback_hom_ext {M : ModuleCat.{u} R} {N : (Spec A).Modules}
    {g₁ g₂ : (AlgebraicGeometry.Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ⟶ N}
    (h : ∀ m : M, (tildePullbackAdjoint φ g₁).app ⊤ (tilde.toOpen M ⊤ m) =
      (tildePullbackAdjoint φ g₂).app ⊤ (tilde.toOpen M ⊤ m)) :
    g₁ = g₂ := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (Spec.map φ)).homEquiv _ _).injective
  apply (tilde.adjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext m
  exact h m

/-- The global generator formula: the adjoint of `tildePullbackIso` sends `m ∈ M = Γ(M^~)` to
`1 ⊗ₜ m ∈ A ⊗[R] M = Γ((A ⊗[R] M)^~)`. -/
lemma tildePullbackIso_adjoint_toOpen_top (M : ModuleCat.{u} R) (m : M) :
    (tildePullbackAdjoint φ (tildePullbackIso φ M).hom).app ⊤ (tilde.toOpen M ⊤ m) =
      tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤ ((1 : A) ⊗ₜ[R, φ.hom] m) := by
  have h := (tildePullbackAdjunction φ).homEquiv_leftAdjointUniq_hom_app
    (extendScalarsTildeAdjunction φ) M
  exact ConcreteCategory.congr_hom h m

/-- The generator formula on every open: the adjoint of `tildePullbackIso` sends the section
`tilde.toOpen M U m` over `U` to the section `tilde.toOpen (A ⊗[R] M) (p ⁻¹ᵁ U) (1 ⊗ₜ m)`. -/
lemma tildePullbackIso_adjoint_toOpen (M : ModuleCat.{u} R) (U : (Spec R).Opens) (m : M) :
    (tildePullbackAdjoint φ (tildePullbackIso φ M).hom).app U (tilde.toOpen M U m) =
      tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) (Spec.map φ ⁻¹ᵁ U)
        ((1 : A) ⊗ₜ[R, φ.hom] m) := by
  set β := tildePullbackAdjoint φ (tildePullbackIso φ M).hom
  have hnat := ConcreteCategory.congr_hom
    (β.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op) (tilde.toOpen M ⊤ m)
  have htop := tildePullbackIso_adjoint_toOpen_top φ M m
  change β.app U ((tilde M).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (tilde.toOpen M ⊤ m)) =
    (tilde ((ModuleCat.extendScalars φ.hom).obj M)).presheaf.map
      (homOfLE (le_top : Spec.map φ ⁻¹ᵁ U ≤ ⊤)).op
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤ ((1 : A) ⊗ₜ[R, φ.hom] m))
  rw [← htop]
  exact hnat

section Algebra

variable (A B : CommRingCat.{u}) [Algebra A B]

/-- The additive map `B ⊗[A, algebraMap A B] M → B ⊗[A] M`, `b ⊗ₜ m ↦ b ⊗ₜ m`. -/
def extendScalarsToAlgebraTensor (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj M →+ B ⊗[A] M :=
  TensorProduct.liftAddHom (R := A)
    (M := (ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj
      (ModuleCat.of B B)) (N := M)
    (AddMonoidHom.mk' (fun b => (TensorProduct.mk A B M b).toAddMonoidHom)
      (fun b c => by ext m; exact TensorProduct.add_tmul (R := A) (M := B) b c m))
    (fun a b m => by
      change (algebraMap A B a * (show B from b)) ⊗ₜ[A] m = (show B from b) ⊗ₜ[A] (a • m)
      rw [← Algebra.smul_def, TensorProduct.smul_tmul])

/-- The additive map `B ⊗[A] M → B ⊗[A, algebraMap A B] M`, `b ⊗ₜ m ↦ b ⊗ₜ m`. -/
def algebraTensorToExtendScalars (M : ModuleCat.{u} A) :
    B ⊗[A] M →+ (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj M :=
  TensorProduct.liftAddHom (R := A) (M := B) (N := M)
    (AddMonoidHom.mk'
      (fun b => (TensorProduct.mk A
        ((ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj
          (ModuleCat.of B B)) M b).toAddMonoidHom)
      (fun b c => by
        ext m
        exact TensorProduct.add_tmul (R := A)
          (M := (ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj
            (ModuleCat.of B B)) b c m))
    (fun a b m => by
      rw [Algebra.smul_def]
      exact TensorProduct.smul_tmul (R := A)
        (M := (ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj
          (ModuleCat.of B B)) (N := M) a b m)

/-- For an `A`-algebra `B`, scalar extension along `algebraMap A B` is the algebra tensor product
`B ⊗[A] M`. The two `A`-module structures on `B` (through `algebraMap A B`, and the algebra
structure) agree only propositionally, so this is a `B`-linear equivalence rather than an
equality of modules. -/
def extendScalarsAlgebraEquiv (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj M ≃ₗ[B] B ⊗[A] M where
  toFun := extendScalarsToAlgebraTensor A B M
  invFun := algebraTensorToExtendScalars A B M
  map_add' := map_add _
  map_smul' b' x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  left_inv x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  right_inv x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The `B`-linear isomorphism `B ⊗[A, algebraMap A B] M ≅ B ⊗[A] M` in `ModuleCat B`. -/
def extendScalarsAlgebraIso (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (CommRingCat.ofHom (algebraMap A B)).hom).obj M ≅
      ModuleCat.of B (B ⊗[A] M) :=
  (extendScalarsAlgebraEquiv A B M).toModuleIso

lemma extendScalarsAlgebraIso_hom_tmul (M : ModuleCat.{u} A) (b : B) (m : M) :
    (extendScalarsAlgebraIso A B M).hom (b ⊗ₜ[A, (CommRingCat.ofHom (algebraMap A B)).hom] m) =
      b ⊗ₜ[A] m :=
  rfl

/-- The algebra form of `tildePullbackIso`: for an `A`-algebra `B` and
`p = Spec.map (CommRingCat.ofHom (algebraMap A B))`, the canonical isomorphism
`p^* (M^~) ≅ (B ⊗[A] M)^~` with the algebra tensor product. -/
def tildePullbackAlgebraIso (M : ModuleCat.{u} A) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj (tilde M) ≅
      tilde (ModuleCat.of B (B ⊗[A] M)) :=
  tildePullbackIso (CommRingCat.ofHom (algebraMap A B)) M ≪≫
    (tilde.functor B).mapIso (extendScalarsAlgebraIso A B M)

/-- The generator formula for `tildePullbackAlgebraIso` on every open, with the algebra tensor
product: `tilde.toOpen M U m ↦ tilde.toOpen (B ⊗[A] M) (p ⁻¹ᵁ U) (1 ⊗ₜ m)`. -/
lemma tildePullbackAlgebraIso_adjoint_toOpen (M : ModuleCat.{u} A) (U : (Spec A).Opens)
    (m : M) :
    (tildePullbackAdjoint (CommRingCat.ofHom (algebraMap A B))
        (tildePullbackAlgebraIso A B M).hom).app U (tilde.toOpen M U m) =
      tilde.toOpen (ModuleCat.of B (B ⊗[A] M))
        (Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ U) ((1 : B) ⊗ₜ[A] m) := by
  have h := tildePullbackIso_adjoint_toOpen (CommRingCat.ofHom (algebraMap A B)) M U m
  rw [tildePullbackAdjoint, tildePullbackAlgebraIso, Iso.trans_hom,
    Adjunction.homEquiv_naturality_right]
  change ((tilde.functor B).map (extendScalarsAlgebraIso A B M).hom).app
      (Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ U)
      ((tildePullbackAdjoint (CommRingCat.ofHom (algebraMap A B))
        (tildePullbackIso (CommRingCat.ofHom (algebraMap A B)) M).hom).app U
        (tilde.toOpen M U m)) = _
  rw [h]
  exact congrArg (fun k => k ((1 : B) ⊗ₜ[A, (CommRingCat.ofHom (algebraMap A B)).hom] m))
    (tilde.toOpen_map_app (extendScalarsAlgebraIso A B M).hom
      (Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ U))

end Algebra

end Langlands.Scheme.Modules
