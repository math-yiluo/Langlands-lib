/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import WeilConjectures.Topology.RingedModuleSkyscraper

/-!
# Pullback along flat coverings reflects isomorphisms of modules

Let `f i : Y i ⟶ X` be a jointly surjective family of flat morphisms of schemes. We show that a
morphism `φ` of (not necessarily quasi-coherent) `𝒪_X`-modules is an isomorphism as soon as all
its pullbacks `(f i)^* φ` are (`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_pullback_map`).

The proof avoids any explicit description of the pullback functor, which is only defined as a
left adjoint of the pushforward. Instead, we use skyscraper modules:

- for `x : X` and an `𝒪_{X,x}`-module `I`, the skyscraper module
  `AlgebraicGeometry.Scheme.Modules.skyscraper x I` has sections `I` over the opens containing `x`
  and `0` over the other opens;
- morphisms `P ⟶ skyscraper x I` correspond to `𝒪_{X,x}`-linear maps `P_x → I`
  (`AlgebraicGeometry.Scheme.Modules.skyscraperHomEquiv`);
- the pushforward of a skyscraper module along `f : Y ⟶ X` is a skyscraper module
  (`AlgebraicGeometry.Scheme.Modules.pushforwardSkyscraperIso`).

Hence if `(f i)^* φ` is an isomorphism and `x = f i y`, precomposition with the stalk map
`φ_x : P_x → Q_x` is bijective on linear maps to every `𝒪_{Y i,y}`-module, which forces `φ_x`
to be bijective since `𝒪_{X,x} → 𝒪_{Y i,y}` is faithfully flat
(`LinearMap.bijective_of_bijective_comp`). A morphism of modules which is bijective on all stalks
is an isomorphism.
-/

@[expose] public section

universe u u₁ u₂ u₃

open CategoryTheory Opposite TopologicalSpace TensorProduct

/-- Let `A → B` be faithfully flat. A linear map `u : M → N` of `A`-modules is bijective as soon as
precomposition with `u` is a bijection `(N →ₗ[A] I) → (M →ₗ[A] I)` for every `B`-module `I`
(viewed as an `A`-module). Indeed, by the base change adjunction this says that `B ⊗[A] u` is an
isomorphism, and `B` is faithfully flat over `A`. -/
theorem LinearMap.bijective_of_bijective_comp {A : Type u₁} {B : Type u₂} {M N : Type u₃}
    [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N] (u : M →ₗ[A] N)
    (h : ∀ (I : Type (max u₂ u₃)) [AddCommGroup I] [Module A I] [Module B I]
      [IsScalarTower A B I], Function.Bijective fun g : N →ₗ[A] I ↦ g ∘ₗ u) :
    Function.Bijective u := by
  let v : B ⊗[A] M →ₗ[B] B ⊗[A] N := u.baseChange B
  have key (I : Type (max u₂ u₃)) [AddCommGroup I] [Module A I] [Module B I]
      [IsScalarTower A B I] : Function.Bijective fun g : B ⊗[A] N →ₗ[B] I ↦ g ∘ₗ v := by
    have e (g : N →ₗ[A] I) : LinearMap.liftBaseChangeEquiv B (g ∘ₗ u) =
        LinearMap.liftBaseChangeEquiv B g ∘ₗ v := by
      ext m
      simp [v]
    have : (fun g : B ⊗[A] N →ₗ[B] I ↦ g ∘ₗ v) = (LinearMap.liftBaseChangeEquiv B) ∘
        (fun g : N →ₗ[A] I ↦ g ∘ₗ u) ∘ (LinearMap.liftBaseChangeEquiv B).symm := by
      ext g : 1
      simp [e]
    rw [this]
    exact (LinearMap.liftBaseChangeEquiv B).bijective.comp
      ((h I).comp (LinearMap.liftBaseChangeEquiv B).symm.bijective)
  obtain ⟨w, hw⟩ := (key (B ⊗[A] M)).2 LinearMap.id
  have hvw : v ∘ₗ w = LinearMap.id := (key (B ⊗[A] N)).1 (by
    simp only [LinearMap.comp_assoc, hw]
    rfl)
  have hv : Function.Bijective v :=
    ⟨Function.LeftInverse.injective (g := w) fun t ↦ congr($hw t),
      Function.RightInverse.surjective (g := w) fun t ↦ congr($hvw t)⟩
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B]
  rwa [← LinearMap.baseChange_eq_lTensor]

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (x : X) (I : Type u) [AddCommGroup I] [Module (X.presheaf.stalk x) I]

/-- The sections over `V` of the skyscraper module at `x` with value `I`: a copy of `I` if
`x ∈ V`, and zero otherwise. This is `SheafOfModules.ringedSkyscraperSectionsType` for the
underlying ringed space. -/
def SkyscraperSections (V : X.Opens) : Type u :=
  SheafOfModules.ringedSkyscraperSectionsType X.toRingedSpace x I V

namespace SkyscraperSections

variable {x I} {V : X.Opens}

instance : AddCommGroup (SkyscraperSections x I V) :=
  inferInstanceAs (AddCommGroup (PLift (x ∈ V) → I))

omit [AddCommGroup I] [Module (X.presheaf.stalk x) I] in
@[ext]
lemma ext {s t : SkyscraperSections x I V} (h : ∀ hx : x ∈ V, s ⟨hx⟩ = t ⟨hx⟩) : s = t :=
  funext fun hx ↦ h hx.down

omit [Module (X.presheaf.stalk x) I] in
@[simp] lemma add_apply (s t : SkyscraperSections x I V) (hx : x ∈ V) :
    (s + t) ⟨hx⟩ = s ⟨hx⟩ + t ⟨hx⟩ := rfl

omit [Module (X.presheaf.stalk x) I] in
@[simp] lemma zero_apply (hx : x ∈ V) : (0 : SkyscraperSections x I V) ⟨hx⟩ = 0 := rfl

instance : SMul Γ(X, V) (SkyscraperSections x I V) where
  smul a s hx := X.presheaf.germ V x hx.down a • s hx

@[simp] lemma smul_apply (a : Γ(X, V)) (s : SkyscraperSections x I V) (hx : x ∈ V) :
    (a • s) ⟨hx⟩ = X.presheaf.germ V x hx a • s ⟨hx⟩ := rfl

instance : Module Γ(X, V) (SkyscraperSections x I V) where
  one_smul s := by ext; simp
  mul_smul a b s := by ext; simp [mul_smul]
  smul_zero a := by ext; simp
  smul_add a s t := by ext; simp
  add_smul a b s := by ext; simp [add_smul]
  zero_smul s := by ext; simp

end SkyscraperSections

/-- The presheaf of abelian groups underlying the skyscraper module at `x` with value `I`.
It is the abelian skyscraper presheaf `SheafOfModules.ringedSkyscraperPresheafAbOfType` of the
underlying ringed space. -/
def skyscraperPresheafAb : X.Opensᵒᵖ ⥤ Ab.{u} :=
  SheafOfModules.ringedSkyscraperPresheafAbOfType X.toRingedSpace x I

instance (V : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj V) ((skyscraperPresheafAb x I).obj V) :=
  inferInstanceAs (Module Γ(X, V.unop) (SkyscraperSections x I V.unop))

omit [Module (X.presheaf.stalk x) I] in
lemma skyscraperPresheafAb_map_apply {V V' : X.Opensᵒᵖ} (i : V ⟶ V')
    (s : SkyscraperSections x I V.unop) (hx : x ∈ V'.unop) :
    (skyscraperPresheafAb x I).map i s ⟨hx⟩ = s ⟨i.unop.le hx⟩ :=
  rfl


lemma skyscraperPresheafAb_map_smul {V V' : X.Opensᵒᵖ} (i : V ⟶ V')
    (a : X.ringCatSheaf.obj.obj V) (s : (skyscraperPresheafAb x I).obj V) :
    (skyscraperPresheafAb x I).map i (a • s) =
      X.ringCatSheaf.obj.map i a • (skyscraperPresheafAb x I).map i s := by
  refine SkyscraperSections.ext fun hx ↦ ?_
  exact congrArg (· • (s ⟨i.unop.le hx⟩ : I))
    (TopCat.Presheaf.germ_res_apply X.presheaf i.unop x hx a).symm

omit [Module (X.presheaf.stalk x) I] in
lemma isSheaf_skyscraperPresheafAb :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (skyscraperPresheafAb x I) :=
  SheafOfModules.ringedSkyscraperPresheafAbOfType_isSheaf X.toRingedSpace x I

/-- The skyscraper `𝒪_X`-module at `x` with value an `𝒪_{X,x}`-module `I`: its sections over `V`
are `I` if `x ∈ V`, and `0` otherwise, with `Γ(X, V)` acting through the germ map. -/
def skyscraper : X.Modules where
  val := PresheafOfModules.ofPresheaf (skyscraperPresheafAb x I)
    fun _ _ i a s ↦ skyscraperPresheafAb_map_smul x I i a s
  isSheaf := isSheaf_skyscraperPresheafAb x I

section Stalk

variable {X : Scheme.{u}}

/-- The stalk at `x` of an `𝒪_X`-module is a module over the local ring `𝒪_{X,x}`. -/
instance (M : X.Modules) (x : X) : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  inferInstanceAs (Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X)
    (M.val : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ _ _)).presheaf x))

lemma germ_smul (M : X.Modules) {U : X.Opens} (x : X) (hx : x ∈ U) (r : Γ(X, U))
    (m : Γ(M, U)) :
    M.presheaf.germ U x hx (r • m) = X.presheaf.germ U x hx r • M.presheaf.germ U x hx m :=
  PresheafOfModules.germ_smul (R := X.presheaf) M.val x U hx r m

/-- An additive map out of the stalk of an `𝒪_X`-module which is compatible with the scalar
multiplication on germs is `𝒪_{X,x}`-linear. -/
def stalkLinearMapMk {M : X.Modules} {x : X} {N : Type*} [AddCommGroup N]
    [Module (X.presheaf.stalk x) N] (ℓ : M.presheaf.stalk x →+ N)
    (h : ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) (m : Γ(M, U)),
      ℓ (M.presheaf.germ U x hx (r • m)) =
        X.presheaf.germ U x hx r • ℓ (M.presheaf.germ U x hx m)) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N where
  __ := ℓ
  map_smul' r m := by
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hxV, m, rfl⟩ := M.presheaf.exists_germ_eq m
    have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
      ← M.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m, ← germ_smul]
    exact h _ hx _ _

@[simp]
lemma stalkLinearMapMk_apply {M : X.Modules} {x : X} {N : Type*} [AddCommGroup N]
    [Module (X.presheaf.stalk x) N] (ℓ : M.presheaf.stalk x →+ N) (h) (m : M.presheaf.stalk x) :
    stalkLinearMapMk ℓ h m = ℓ m :=
  rfl

/-- The map induced on stalks at `x` by a morphism of `𝒪_X`-modules, as an `𝒪_{X,x}`-linear
map. -/
def Hom.stalkLinearMap {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x :=
  stalkLinearMapMk
    (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf))
    fun U hx r m ↦ by
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply]
      rw [mapPresheaf_app, Hom.app_smul, germ_smul]

lemma Hom.stalkLinearMap_apply {M N : X.Modules} (φ : M ⟶ N) (x : X) (m : M.presheaf.stalk x) :
    φ.stalkLinearMap x m = (TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf m :=
  rfl

@[simp]
lemma Hom.stalkLinearMap_germ {M N : X.Modules} (φ : M ⟶ N) {U : X.Opens} (x : X) (hx : x ∈ U)
    (m : Γ(M, U)) :
    φ.stalkLinearMap x (M.presheaf.germ U x hx m) = N.presheaf.germ U x hx (φ.app U m) := by
  rw [Hom.stalkLinearMap_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply, mapPresheaf_app]

end Stalk

section SkyscraperHom

variable {X : Scheme.{u}} (x : X) (I : Type u) [AddCommGroup I] [Module (X.presheaf.stalk x) I]

/-- Evaluation at `x` on the stalk at `x` of the skyscraper module, as an additive map. -/
def skyscraperStalkEvalAddHom : (skyscraper x I).presheaf.stalk x →+ I :=
  ConcreteCategory.hom (Limits.colimit.desc _
    { pt := AddCommGrpCat.of I
      ι :=
        { app U := AddCommGrpCat.ofHom
            { toFun s := (show SkyscraperSections x I U.unop.1 from s) ⟨U.unop.2⟩
              map_zero' := rfl
              map_add' _ _ := rfl }
          naturality _ _ _ := rfl } })

lemma skyscraperStalkEvalAddHom_germ {U : X.Opens} (hx : x ∈ U) (s : Γ(skyscraper x I, U)) :
    skyscraperStalkEvalAddHom x I ((skyscraper x I).presheaf.germ U x hx s) =
      s ⟨hx⟩ := by
  rw [skyscraperStalkEvalAddHom, TopCat.Presheaf.germ]
  erw [Limits.colimit.ι_desc_apply]
  rfl

/-- Evaluation at `x` on the stalk at `x` of the skyscraper module. -/
def skyscraperStalkEval : (skyscraper x I).presheaf.stalk x →ₗ[X.presheaf.stalk x] I :=
  stalkLinearMapMk (skyscraperStalkEvalAddHom x I) fun U hx r s ↦ by
    rw [skyscraperStalkEvalAddHom_germ, skyscraperStalkEvalAddHom_germ]
    rfl

@[simp]
lemma skyscraperStalkEval_germ {U : X.Opens} (hx : x ∈ U) (s : Γ(skyscraper x I, U)) :
    skyscraperStalkEval x I ((skyscraper x I).presheaf.germ U x hx s) =
      s ⟨hx⟩ :=
  skyscraperStalkEvalAddHom_germ x I hx s

variable {x I}

/-- The morphism to the skyscraper module at `x` induced by an `𝒪_{X,x}`-linear map out of the
stalk at `x`. -/
def toSkyscraper {P : X.Modules} (ℓ : P.presheaf.stalk x →ₗ[X.presheaf.stalk x] I) :
    P ⟶ skyscraper x I :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun p := show SkyscraperSections x I V.unop from
            fun hx ↦ ℓ (P.presheaf.germ V.unop x hx.down p)
          map_zero' := SkyscraperSections.ext fun _ ↦ (congrArg ℓ (map_zero _)).trans (map_zero ℓ)
          map_add' _ _ := SkyscraperSections.ext fun _ ↦
            (congrArg ℓ (map_add _ _ _)).trans (map_add ℓ _ _) }
      naturality V V' i := by
        ext p
        refine SkyscraperSections.ext fun hx ↦ ?_
        exact congrArg ℓ (P.presheaf.germ_res_apply i.unop x hx p) }
    fun V r p ↦ by
      refine SkyscraperSections.ext fun hx ↦ ?_
      exact (congrArg ℓ (germ_smul P x hx r p)).trans (ℓ.map_smul _ _)⟩

lemma toSkyscraper_app_apply {P : X.Modules} (ℓ : P.presheaf.stalk x →ₗ[X.presheaf.stalk x] I)
    {V : X.Opens} (p : Γ(P, V)) (hx : x ∈ V) :
    (toSkyscraper ℓ).app V p ⟨hx⟩ =
      ℓ (P.presheaf.germ V x hx p) :=
  rfl

lemma comp_toSkyscraper {P Q : X.Modules} (φ : P ⟶ Q)
    (ℓ : Q.presheaf.stalk x →ₗ[X.presheaf.stalk x] I) :
    φ ≫ toSkyscraper ℓ = toSkyscraper (ℓ ∘ₗ φ.stalkLinearMap x) := by
  refine hom_ext _ _ fun V ↦ ?_
  ext p
  refine SkyscraperSections.ext fun hx ↦ ?_
  rw [Hom.comp_app, ConcreteCategory.comp_apply, toSkyscraper_app_apply, toSkyscraper_app_apply,
    LinearMap.comp_apply, Hom.stalkLinearMap_germ]

variable (x I) in
/-- **The stalk–skyscraper adjunction** for modules: morphisms `P ⟶ skyscraper x I` correspond
to `𝒪_{X,x}`-linear maps from the stalk of `P` at `x` to `I`. -/
def skyscraperHomEquiv (P : X.Modules) :
    (P.presheaf.stalk x →ₗ[X.presheaf.stalk x] I) ≃ (P ⟶ skyscraper x I) where
  toFun := toSkyscraper
  invFun g := skyscraperStalkEval x I ∘ₗ g.stalkLinearMap x
  left_inv ℓ := by
    ext t
    obtain ⟨U, hx, p, rfl⟩ := P.presheaf.exists_germ_eq t
    rw [LinearMap.comp_apply, Hom.stalkLinearMap_germ, skyscraperStalkEval_germ,
      toSkyscraper_app_apply]
  right_inv g := by
    refine hom_ext _ _ fun V ↦ ?_
    ext p
    refine SkyscraperSections.ext fun hx ↦ ?_
    rw [toSkyscraper_app_apply, LinearMap.comp_apply, Hom.stalkLinearMap_germ,
      skyscraperStalkEval_germ]

end SkyscraperHom

section Pushforward

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) (I : Type u) [AddCommGroup I]
  [Module (Y.presheaf.stalk y) I] [Module (X.presheaf.stalk (f y)) I]
  [Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)]
  [IsScalarTower (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) I]

include f in
lemma germ_smul_eq_germ_app_smul
    (h : algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) = (f.stalkMap y).hom)
    {V : X.Opens} (hy : f y ∈ V) (r : Γ(X, V)) (i : I) :
    X.presheaf.germ V (f y) hy r • i = Y.presheaf.germ (f ⁻¹ᵁ V) y hy (f.app V r) • i := by
  rw [← Scheme.Hom.germ_stalkMap_apply, ← algebraMap_smul (Y.presheaf.stalk y), h]

/-- The pushforward along `f : Y ⟶ X` of the skyscraper module at `y` with value `I` is the
skyscraper module at `f y` with value `I`, viewed as an `𝒪_{X,f y}`-module. -/
def pushforwardSkyscraperIso
    (h : algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) = (f.stalkMap y).hom) :
    (pushforward f).obj (skyscraper y I) ≅ skyscraper (f y) I where
  hom := ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun s := show SkyscraperSections (f y) I V.unop from
            fun hx ↦ s ⟨hx.down⟩
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality _ _ _ := rfl }
    fun _ r _ ↦ SkyscraperSections.ext fun hx ↦
      (germ_smul_eq_germ_app_smul f y I h hx r _).symm⟩
  inv := ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun s := show SkyscraperSections y I (f ⁻¹ᵁ V.unop) from
            fun hx ↦ s ⟨hx.down⟩
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality _ _ _ := rfl }
    fun _ r _ ↦ SkyscraperSections.ext fun hx ↦
      germ_smul_eq_germ_app_smul f y I h hx r _⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

end Pushforward

/-- A morphism of `𝒪_X`-modules which is bijective on all stalks is an isomorphism. -/
lemma isIso_of_bijective_stalkLinearMap {X : Scheme.{u}} {P Q : X.Modules} (φ : P ⟶ Q)
    (h : ∀ x, Function.Bijective (φ.stalkLinearMap x)) : IsIso φ := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
    (F := ⟨P.presheaf, P.isSheaf⟩) (G := ⟨Q.presheaf, Q.isSheaf⟩) ⟨φ.mapPresheaf⟩ U
    fun x _ ↦ h x

/-- Pullback along a jointly surjective family of flat morphisms reflects isomorphisms of
arbitrary (not necessarily quasi-coherent) sheaves of modules. -/
theorem isIso_of_isIso_pullback_map {X : Scheme.{u}} {ι : Type*} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, Flat (f i)] (hf : ∀ x : X, ∃ i y, f i y = x)
    {P Q : X.Modules} (φ : P ⟶ Q) (h : ∀ i, IsIso ((pullback (f i)).map φ)) : IsIso φ := by
  refine isIso_of_bijective_stalkLinearMap φ fun x ↦ ?_
  obtain ⟨i, y, rfl⟩ := hf x
  algebraize [((f i).stalkMap y).hom]
  have : Module.FaithfullyFlat (X.presheaf.stalk (f i y)) ((Y i).presheaf.stalk y) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap (f i) y) ((f i).toLRSHom.prop y)
  refine LinearMap.bijective_of_bijective_comp (B := (Y i).presheaf.stalk y) _ fun I _ _ _ _ ↦ ?_
  let S := (pushforward (f i)).obj (skyscraper y I)
  let e := pushforwardSkyscraperIso (f i) y I rfl
  let adj := pullbackPushforwardAdjunction (f i)
  -- precomposition with `(f i)^* φ` is bijective, since it is an isomorphism
  have h₁ : Function.Bijective fun g : (pullback (f i)).obj Q ⟶ skyscraper y I ↦
      (pullback (f i)).map φ ≫ g :=
    ⟨fun g₁ g₂ hg ↦ by simpa using congr(inv ((pullback (f i)).map φ) ≫ $hg),
      fun g ↦ ⟨inv ((pullback (f i)).map φ) ≫ g, by simp⟩⟩
  -- hence so is precomposition with `φ` on morphisms to `(f i)_* (skyscraper y I)`
  have h₂ : Function.Bijective fun g : Q ⟶ S ↦ φ ≫ g := by
    have : (fun g : Q ⟶ S ↦ φ ≫ g) = adj.homEquiv P (skyscraper y I) ∘
        (fun g ↦ (pullback (f i)).map φ ≫ g) ∘ (adj.homEquiv Q (skyscraper y I)).symm := by
      ext g : 1
      simp [adj.homEquiv_naturality_left]
    rw [this]
    exact (Equiv.bijective _).comp (h₁.comp (Equiv.bijective _))
  -- hence so is precomposition with `φ` on morphisms to `skyscraper (f i y) I`
  have h₃ : Function.Bijective fun g : Q ⟶ skyscraper (f i y) I ↦ φ ≫ g := by
    have : (fun g : Q ⟶ skyscraper (f i y) I ↦ φ ≫ g) = (e.homToEquiv) ∘
        (fun g : Q ⟶ S ↦ φ ≫ g) ∘ (e.homToEquiv).symm := by
      ext g : 1
      simp
    rw [this]
    exact (Equiv.bijective _).comp (h₂.comp (Equiv.bijective _))
  have : (fun g ↦ g ∘ₗ φ.stalkLinearMap (f i y)) = (skyscraperHomEquiv (f i y) I P).symm ∘
      (fun g : Q ⟶ skyscraper (f i y) I ↦ φ ≫ g) ∘ skyscraperHomEquiv (f i y) I Q := by
    ext g : 1
    exact ((congrArg (skyscraperHomEquiv (f i y) I P).symm (comp_toSkyscraper φ g)).trans
      ((skyscraperHomEquiv (f i y) I P).symm_apply_apply _)).symm
  rw [this]
  exact (Equiv.bijective _).comp (h₃.comp (Equiv.bijective _))

end AlgebraicGeometry.Scheme.Modules

end
