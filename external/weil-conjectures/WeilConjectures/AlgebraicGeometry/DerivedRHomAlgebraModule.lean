/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategoryQCoherentAlgebra
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.HomComplexSingleNatural
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# Derived internal Hom with its algebra module structure

Source: Stacks Project, Duality for Schemes, Section 48.11, Tags 0BUZ, 0BV0, 0BV1
(blueprint: def-pc-derived-rhom-algebra-module).

The natural algebra action is precomposition with multiplication. The derived functor
is the localization of termwise Hom after a functorial, degreewise injective K-injective
resolution. Its underlying object is the shared derived internal Hom.
-/

@[expose] public section

universe u w wB

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem compose_comparisons
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    (H : A ⥤ D) [H.Additive] (T : D ⥤ A) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (O : A ⥤ A) [O.Additive] (I : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (S : DerivedCategory A ⥤ DerivedCategory D) (R : DerivedCategory A ⥤ DerivedCategory A)
    (s : Nonempty (DerivedCategory.Q ⋙ S ≅
      I ⋙ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q))
    (e : H ⋙ T ≅ O)
    (t : Nonempty (DerivedCategory.Q ⋙ R ≅
      I ⋙ O.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)) :
    Nonempty (S ⋙ T.mapDerivedCategory ≅ R) := by
  obtain ⟨s⟩ := s
  obtain ⟨t⟩ := t
  let s' : DerivedCategory.Q ⋙ S ⋙ T.mapDerivedCategory ≅
      I ⋙ H.mapHomologicalComplex (.up ℤ) ⋙ T.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    Functor.isoWhiskerRight s T.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (I ⋙ H.mapHomologicalComplex (.up ℤ))
        T.mapDerivedCategoryFactors
  let ec := Functor.mapHomologicalComplexCompIso e (.up ℤ)
  let s'' := s' ≪≫ Functor.isoWhiskerLeft I (Functor.isoWhiskerRight ec DerivedCategory.Q)
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _).preimageIso (s'' ≪≫ t.symm)⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem fixed_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (I : C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C) (R : Dᵒᵖ × D ⥤ E)
    (P : C) (O : C ⥤ C) (V : C ⥤ E)
    (c : Nonempty (Q.op.prod Q ⋙ R ≅ (𝟭 _).prod I ⋙ Functor.uncurry.obj H ⋙ V))
    (e : Nonempty (H.obj (op P) ≅ O)) :
    Nonempty (Q ⋙ ((Functor.const D).obj (op (Q.obj P))).prod' (𝟭 D) ⋙ R ≅
      I ⋙ O ⋙ V) := by
  obtain ⟨c⟩ := c
  obtain ⟨e⟩ := e
  let c' := (Functor.curry.mapIso c).app (op P)
  let a := (Functor.curryObjProdComp Q.op Q R).app (op P)
  let b : (Functor.curry.obj
      ((𝟭 _).prod I ⋙ Functor.uncurry.obj H ⋙ V)).obj (op P) ≅
      I ⋙ H.obj (op P) ⋙ V :=
    NatIso.ofComponents (fun K ↦ Iso.refl _) (by intro K K' f; simp)
  exact ⟨a.symm ≪≫ c' ≪≫ b ≪≫
    Functor.isoWhiskerLeft I (Functor.isoWhiskerRight e V)⟩


private theorem restrictScalars_finite_limits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (α : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} α) := by
  let T := SheafOfModules.restrictScalars.{u} α
  have he : T ⋙ SheafOfModules.toSheaf.{u} R ≅ SheafOfModules.toSheaf.{u} S := Iso.refl _
  have : PreservesFiniteLimits (T ⋙ SheafOfModules.toSheaf.{u} R) :=
    preservesFiniteLimits_of_natIso he.symm
  exact preservesFiniteLimits_of_reflects_of_preserves T (SheafOfModules.toSheaf.{u} R)

private theorem restrictScalars_finite_colimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (α : R ⟶ S) :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} α) := by
  let T := SheafOfModules.restrictScalars.{u} α
  have he : T ⋙ SheafOfModules.toSheaf.{u} R ≅ SheafOfModules.toSheaf.{u} S := Iso.refl _
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u} R) :=
    { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have : PreservesFiniteColimits (T ⋙ SheafOfModules.toSheaf.{u} R) :=
    preservesFiniteColimits_of_natIso he.symm
  exact preservesFiniteColimits_of_reflects_of_preserves T (SheafOfModules.toSheaf.{u} R)

attribute [local instance] restrictScalars_finite_limits restrictScalars_finite_colimits

private theorem additive_resolution_inverts
    {A : Type*} [Category A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (F : A ⥤ D) [F.Additive] :
    (HomologicalComplex.quasiIso A (.up ℤ)).IsInvertedBy
      (CochainComplex.kInjectiveResolutionFunctor.{u} A ⋙
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  intro M N f hf
  have : QuasiIso f := hf
  have : QuasiIso (η.app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2
  have : QuasiIso (η.app N) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A N).2
  have hη : QuasiIso (η.app M ≫ I.map f) := by
    rw [← η.naturality f]
    dsimp
    infer_instance
  have : QuasiIso (I.map f) := (quasiIso_iff_comp_left _ _).mp hη
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff (I.map f)).mp
    (inferInstance : QuasiIso (I.map f))
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
  change QuasiIso ((F.mapHomologicalComplex _).map (I.map f))
  rw [← he]
  exact homotopyEquivalences_le_quasiIso _ _ _ ⟨F.mapHomotopyEquiv e, rfl⟩

variable (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf)

/-- The section carrier of the shared internal Hom, on an open U.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable abbrev sheafAlgebraHomSections (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) (U : (Opens Y)ᵒᵖ) :=
  (PresheafOfModules.homObj.{u, u, u, u} B.toModule.val F.val).obj U

/-- Multiplication by a restricted algebra section is additive and O-linear.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Distribute multiplication over addition. The O action is multiplication by the structure
map; commutativity and associativity move it past b. -/
theorem sheafAlgebraMul_linear (U : Opens Y) (b : B.right.obj.obj (op U))
    (W : (Over U)ᵒᵖ) :
    (∀ x y : B.toModule.val.obj (op W.unop.left),
      B.right.obj.map W.unop.hom.op b *
        (@id (B.right.obj.obj (op W.unop.left)) (x + y)) =
        B.right.obj.map W.unop.hom.op b *
          (@id (B.right.obj.obj (op W.unop.left)) x) + B.right.obj.map W.unop.hom.op b *
          (@id (B.right.obj.obj (op W.unop.left)) y)) ∧
    (∀ (r : Y.sheaf.obj.obj (op W.unop.left))
      (x : B.toModule.val.obj (op W.unop.left)),
      B.right.obj.map W.unop.hom.op b *
        (@id (B.right.obj.obj (op W.unop.left)) (r • x)) =
        r • (@id (B.toModule.val.obj (op W.unop.left))
          (B.right.obj.map W.unop.hom.op b *
            (@id (B.right.obj.obj (op W.unop.left)) x)))) := by
  dsimp [Scheme.CommAlgebraSheaf.toModule, SheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalars, PresheafOfModules.restrictScalarsObj,
    SheafOfModules.unit, PresheafOfModules.unit, ModuleCat.restrictScalars,
    ModuleCat.RestrictScalars.obj']
  constructor
  · intro x y
    change _ * (x + y : B.right.obj.obj (op W.unop.left)) = _
    exact mul_add _ _ _
  · intro r x
    let r' : B.right.obj.obj (op W.unop.left) := (B.hom.hom.app _).hom r
    let x' : B.right.obj.obj (op W.unop.left) := x
    let b' : B.right.obj.obj (op W.unop.left) := B.right.obj.map W.unop.hom.op b
    change b' * (r' * x') = r' * (b' * x')
    exact mul_left_comm _ _ _

/-- The component of multiplication by b on B restricted to U.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraMulApp (U : Opens Y) (b : B.right.obj.obj (op U))
    (W : (Over U)ᵒᵖ) :
    ((PresheafOfModules.restrictOver Y.sheaf.obj U).obj B.toModule.val).obj W ⟶
      ((PresheafOfModules.restrictOver Y.sheaf.obj U).obj B.toModule.val).obj W :=
  ModuleCat.ofHom
    { toFun := fun x ↦ B.right.obj.map W.unop.hom.op b *
          (@id (B.right.obj.obj (op W.unop.left)) x)
      map_add' := (sheafAlgebraMul_linear Y B U b W).1
      map_smul' := (sheafAlgebraMul_linear Y B U b W).2 }

/-- Multiplication components commute with restrictions.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Restriction is a ring map, so preserves products; functoriality identifies the two
restrictions of b. -/
theorem sheafAlgebraMul_naturality (U : Opens Y) (b : B.right.obj.obj (op U))
    {W V : (Over U)ᵒᵖ} (f : W ⟶ V) :
    ((PresheafOfModules.restrictOver Y.sheaf.obj U).obj B.toModule.val).map f ≫
      (ModuleCat.restrictScalars
        (((Over.forget U).op ⋙ Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map f).hom).map
        (sheafAlgebraMulApp Y B U b V) =
      sheafAlgebraMulApp Y B U b W ≫
        ((PresheafOfModules.restrictOver Y.sheaf.obj U).obj B.toModule.val).map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change B.right.obj.map V.unop.hom.op b *
    B.right.obj.map f.unop.left.op (@id (B.right.obj.obj (op W.unop.left)) x) =
    B.right.obj.map f.unop.left.op
      (B.right.obj.map W.unop.hom.op b * (@id (B.right.obj.obj (op W.unop.left)) x))
  rw [map_mul]
  have hb : B.right.obj.map f.unop.left.op (B.right.obj.map W.unop.hom.op b) =
      B.right.obj.map V.unop.hom.op b := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, Over.w]
  rw [hb]

/-- Multiplication by b on the first argument, on every open over U.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraMul (U : Opens Y) (b : B.right.obj.obj (op U)) :
    (PresheafOfModules.restrictOver Y.sheaf.obj U).obj B.toModule.val ⟶
      (PresheafOfModules.restrictOver Y.sheaf.obj U).obj B.toModule.val where
  app := sheafAlgebraMulApp Y B U b
  naturality := sheafAlgebraMul_naturality Y B U b

/-- The B(U) action on Hom is precomposition with multiplication by b.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable instance sheafAlgebraHomSMul (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) (U : (Opens Y)ᵒᵖ) :
    SMul (B.right.obj.obj U) (sheafAlgebraHomSections Y B F U) where
  smul b φ := sheafAlgebraMul Y B U.unop b ≫ φ

/-- On every open over U the B-action is precomposition with multiplication.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Expand sheafAlgebraHomSMul, the composition of presheaf morphisms, and
sheafAlgebraMulApp. The composite evaluates φ at the product of the restriction of b
with x, exactly as asserted. -/
theorem sheafAlgebraHom_smul (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) (U : (Opens Y)ᵒᵖ)
    (b : B.right.obj.obj U) (φ : sheafAlgebraHomSections Y B F U)
    (W : (Over U.unop)ᵒᵖ) (x : B.toModule.val.obj (op W.unop.left)) :
    (b • φ).app W x = φ.app W
      (B.right.obj.map W.unop.hom.op b * (@id (B.right.obj.obj (op W.unop.left)) x)) := by
  rfl

/-- The explicit action satisfies the module axioms.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Evaluate at every W and x. The unit and product axioms follow from commutative
multiplication in B; the four distributive and zero axioms follow from distributivity in B and
additivity of φ. -/
theorem sheafAlgebraHom_module_axioms (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) (U : (Opens Y)ᵒᵖ) :
    (∀ φ : sheafAlgebraHomSections Y B F U, (1 : B.right.obj.obj U) • φ = φ) ∧
    (∀ (b c : B.right.obj.obj U) (φ : sheafAlgebraHomSections Y B F U),
      (b * c) • φ = b • c • φ) ∧
    (∀ (b : B.right.obj.obj U) (φ ψ : sheafAlgebraHomSections Y B F U),
      b • (φ + ψ) = b • φ + b • ψ) ∧
    (∀ b : B.right.obj.obj U, b • (0 : sheafAlgebraHomSections Y B F U) = 0) ∧
    (∀ (b c : B.right.obj.obj U) (φ : sheafAlgebraHomSections Y B F U),
      (b + c) • φ = b • φ + c • φ) ∧
    (∀ φ : sheafAlgebraHomSections Y B F U, (0 : B.right.obj.obj U) • φ = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [sheafAlgebraHom_smul, map_one, one_mul]
    rfl
  · intro b c φ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [sheafAlgebraHom_smul, map_mul, mul_assoc, id_eq]
    exact congrArg (fun z : B.right.obj.obj (op W.unop.left) ↦ φ.app W z)
      (mul_left_comm _ _ _)
  · intro b φ ψ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · intro b
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · intro b c φ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [sheafAlgebraHom_smul, map_add, add_mul, map_add]
    rfl
  · intro φ
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [sheafAlgebraHom_smul, map_zero, zero_mul]
    rfl

/-- The B(U)-module structure with the explicitly defined scalar action.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable instance sheafAlgebraHomModule (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) (U : (Opens Y)ᵒᵖ) :
    Module (B.right.obj.obj U) (sheafAlgebraHomSections Y B F U) where
  smul := (sheafAlgebraHomSMul Y B F U).smul
  one_smul := (sheafAlgebraHom_module_axioms Y B F U).1
  mul_smul := (sheafAlgebraHom_module_axioms Y B F U).2.1
  smul_add := (sheafAlgebraHom_module_axioms Y B F U).2.2.1
  smul_zero := (sheafAlgebraHom_module_axioms Y B F U).2.2.2.1
  add_smul := (sheafAlgebraHom_module_axioms Y B F U).2.2.2.2.1
  zero_smul := (sheafAlgebraHom_module_axioms Y B F U).2.2.2.2.2

/-- The existing Hom restrictions are semilinear for the B action.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The restriction of a morphism over U is its pullback to opens over V. The multiplier is the
restriction of b; functoriality of B restrictions identifies these actions. -/
theorem sheafAlgebraHom_restrict_smul (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))
    {U V : (Opens Y)ᵒᵖ} (f : U ⟶ V) (b : B.right.obj.obj U)
    (φ : sheafAlgebraHomSections Y B F U) :
    (PresheafOfModules.homObj.{u, u, u, u} B.toModule.val F.val).presheaf.map f (b • φ) =
      @SMul.smul _ (sheafAlgebraHomSections Y B F V)
        (sheafAlgebraHomSMul Y B F V) (B.right.obj.map f b)
        ((PresheafOfModules.homObj.{u, u, u, u} B.toModule.val F.val).presheaf.map f φ) := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let φ' := PresheafOfModules.restrictOverMap f.unop φ
  let b' : B.right.obj.obj (op W.unop.left) :=
    B.right.obj.map ((Over.map f.unop).obj W.unop).hom.op b
  let c' : B.right.obj.obj (op W.unop.left) :=
    B.right.obj.map W.unop.hom.op (B.right.obj.map f b)
  let x' : B.right.obj.obj (op W.unop.left) := x
  change φ'.app W (b' * x') = φ'.app W (c' * x')
  have hb : b' = c' := PresheafOfModules.overSections_coe_map_obj f.unop b W
  rw [hb]

/-- The Hom sheaf with B-module sections and the existing Hom restriction maps.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraHomObj (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj B.right) where
  val :=
    letI (U : (Opens Y)ᵒᵖ) :
        Module ((B.right.obj ⋙ forget₂ CommRingCat RingCat).obj U)
          ((PresheafOfModules.homObj.{u, u, u, u} B.toModule.val F.val).presheaf.obj U) :=
      sheafAlgebraHomModule Y B F U
    PresheafOfModules.ofPresheaf
    (R := B.right.obj ⋙ forget₂ CommRingCat RingCat)
    (PresheafOfModules.homObj.{u, u, u, u} B.toModule.val F.val).presheaf
    (fun {U V} f b φ ↦ sheafAlgebraHom_restrict_smul Y B F (U := U) (V := V) f b φ)
  isSheaf := (SheafOfModules.homObj.{u, u, u, u} (R := Y.sheaf) B.toModule F).isSheaf

/-- Postcomposition commutes with the B action.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Evaluate at W and x; both sides are g applied to φ evaluated at the product of the
restriction of b with x. -/
theorem sheafAlgebraHom_map_smul {F G : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)} (g : F ⟶ G)
    (U : (Opens Y)ᵒᵖ) (b : B.right.obj.obj U)
    (φ : sheafAlgebraHomSections Y B F U) :
    (PresheafOfModules.homObjMap (𝟙 B.toModule.val) g.val).app U (b • φ) =
      @SMul.smul _ (sheafAlgebraHomSections Y B G U)
        (sheafAlgebraHomSMul Y B G U) b
        ((PresheafOfModules.homObjMap (𝟙 B.toModule.val) g.val).app U φ) := by
  simp only [PresheafOfModules.homObjMap_app_apply]
  exact (Category.assoc _ _ _).symm

/-- The functor map is the existing postcomposition map with its B-linearity proof.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraHomMap {F G : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)} (g : F ⟶ G) :
    sheafAlgebraHomObj Y B F ⟶ sheafAlgebraHomObj Y B G where
  val := PresheafOfModules.homMk
    ((PresheafOfModules.toPresheaf
      (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).map
      (PresheafOfModules.homObjMap (𝟙 B.toModule.val) g.val))
    (sheafAlgebraHom_map_smul Y B g)

/-- Postcomposition preserves identity and composition.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The underlying maps are homObjMap; its identity and composition laws imply the equalities
by extensionality of module morphisms. -/
theorem sheafAlgebraHom_functor_axioms :
    (∀ F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf),
      sheafAlgebraHomMap Y B (𝟙 F) = 𝟙 (sheafAlgebraHomObj Y B F)) ∧
    (∀ (F G H : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) (f : F ⟶ G) (g : G ⟶ H),
      sheafAlgebraHomMap Y B (f ≫ g) =
        sheafAlgebraHomMap Y B f ≫ sheafAlgebraHomMap Y B g) := by
  constructor
  · intro F
    ext U φ
    change (PresheafOfModules.homObjMap (𝟙 B.toModule.val) (𝟙 F.val)).app U φ = φ
    rw [PresheafOfModules.homObjMap_id]
    rfl
  · intro F G H f g
    ext U φ
    change (PresheafOfModules.homObjMap (𝟙 B.toModule.val) (f.val ≫ g.val)).app U φ =
      (PresheafOfModules.homObjMap (𝟙 B.toModule.val) g.val).app U
        ((PresheafOfModules.homObjMap (𝟙 B.toModule.val) f.val).app U φ)
    simp only [PresheafOfModules.homObjMap_app_apply]
    simp

/-- The explicit algebra-valued Hom functor: sections are Hom and maps postcompose.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraHom : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf) ⥤ SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj B.right) where
  obj := sheafAlgebraHomObj Y B
  map := sheafAlgebraHomMap Y B
  map_id := (sheafAlgebraHom_functor_axioms Y B).1
  map_comp := fun f g ↦ (sheafAlgebraHom_functor_axioms Y B).2 _ _ _ f g

/-- The explicit Hom functor is additive.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: On every section postcomposition by f + g is the sum of postcomposition by f and g.
Extensionality gives additivity. -/
theorem sheafAlgebraHom_additive : (sheafAlgebraHom Y B).Additive := by
  constructor
  intro F G f g
  ext U φ
  change (PresheafOfModules.homObjMap (𝟙 B.toModule.val) (f.val + g.val)).app U φ =
    (PresheafOfModules.homObjMap (𝟙 B.toModule.val) f.val).app U φ +
      (PresheafOfModules.homObjMap (𝟙 B.toModule.val) g.val).app U φ
  simp only [PresheafOfModules.homObjMap_app_apply]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

attribute [instance] sheafAlgebraHom_additive

/-- The identity on Hom sections is O-linear after restriction of scalars.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The structure map sends r to its multiplication action on B. O-linearity of φ moves that
multiplier to the output, giving the existing Hom scalar action. -/
theorem sheafAlgebraHom_underlying_linear (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))
    (U : (Opens Y)ᵒᵖ) (r : Y.sheaf.obj.obj U)
    (φ : sheafAlgebraHomSections Y B F U) :
    (B.hom.hom.app U).hom r • φ =
      r • (φ : (PresheafOfModules.homObj.{u, u, u, u} B.toModule.val F.val).obj U) := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [sheafAlgebraHom_smul]
  change φ.app W (B.right.obj.map W.unop.hom.op ((B.hom.hom.app U).hom r) *
      (@id (B.right.obj.obj (op W.unop.left)) x)) =
    (Y.sheaf.obj.map W.unop.hom.op r) • φ.app W x
  have hr := congrArg (fun k ↦ k r) (congrArg CommRingCat.Hom.hom
    (B.hom.hom.naturality W.unop.hom.op))
  dsimp at hr
  rw [← hr]
  exact (φ.app W).hom.map_smul (Y.sheaf.obj.map W.unop.hom.op r) x

private theorem forget_restrictScalars {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat} (α : R ⟶ S) :
    SheafOfModules.restrictScalars α ⋙ SheafOfModules.forget R ⋙
      PresheafOfModules.toPresheaf R.obj =
      SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj := rfl

private theorem sheaf_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : SheafOfModules R} (h : M.val = N.val) : M = N := by
  cases M
  cases N
  cases h
  rfl

private theorem functor_eq_of_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (F G : C ⥤ D) (H : D ⥤ E) [H.Faithful]
    (ho : ∀ X, F.obj X = G.obj X) (hc : F ⋙ H = G ⋙ H) : F = G := by
  refine CategoryTheory.Functor.ext ho ?_
  intro X Y f
  apply H.map_injective
  simpa only [H.map_comp, eqToHom_map, Functor.comp_obj, Functor.comp_map] using
    CategoryTheory.Functor.congr_hom hc f


private theorem restrict_ofPresheaf_eq
    {C : Type*} [Category C] (R S : Cᵒᵖ ⥤ RingCat) (α : R ⟶ S)
    (P : Cᵒᵖ ⥤ AddCommGrpCat) (m₁ : ∀ U, Module (S.obj U) (P.obj U))
    (m₂ : ∀ U, Module (R.obj U) (P.obj U))
    (h : (fun U ↦ letI := m₁ U; Module.compHom (P.obj U) (α.app U).hom) = m₂)
    (h₁ : ∀ ⦃U V⦄ (f : U ⟶ V) (r : S.obj U) (x : P.obj U),
      P.map f (@SMul.smul _ _ (m₁ U).toSMul r x) =
        @SMul.smul _ _ (m₁ V).toSMul (S.map f r) (P.map f x))
    (h₂ : ∀ ⦃U V⦄ (f : U ⟶ V) (r : R.obj U) (x : P.obj U),
      P.map f (@SMul.smul _ _ (m₂ U).toSMul r x) =
        @SMul.smul _ _ (m₂ V).toSMul (R.map f r) (P.map f x)) :
    (PresheafOfModules.restrictScalars α).obj
      (@PresheafOfModules.ofPresheaf _ _ S P m₁ h₁) =
        @PresheafOfModules.ofPresheaf _ _ R P m₂ h₂ := by
  subst m₂
  rfl

private theorem presheaf_ofPresheaf_eq
    {C : Type*} [Category C] (R : Cᵒᵖ ⥤ RingCat) (M : PresheafOfModules R) :
    @PresheafOfModules.ofPresheaf _ _ R M.presheaf
      (fun U ↦ (M.obj U).isModule) (fun _ _ f r x ↦ M.map_smul f r x) = M := by
  rfl

private theorem sheafAlgebraHomUnderlying_obj_val_eq
    (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
    (forget₂ CommRingCat RingCat)).obj Y.sheaf)) :
    ((sheafAlgebraHom Y B ⋙ SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)).obj F).val =
      (SheafOfModules.homObj (R := Y.sheaf) B.toModule F).val := by
  let P := (PresheafOfModules.homObj B.toModule.val F.val).presheaf
  let R := Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat
  let m₁ : ∀ U, Module (R.obj U) (P.obj U) := fun U ↦
    Module.compHom (sheafAlgebraHomSections Y B F U) (B.hom.hom.app U).hom
  let m₂ : ∀ U, Module (R.obj U) (P.obj U) := fun U ↦
    (PresheafOfModules.homObj B.toModule.val F.val).obj U |>.isModule
  have hm : m₁ = m₂ := by
    funext U
    exact Module.ext' _ _ (sheafAlgebraHom_underlying_linear Y B F U)
  let S := B.right.obj ⋙ forget₂ CommRingCat RingCat
  let α : R ⟶ S := (Functor.whiskerRight B.hom.hom (forget₂ CommRingCat RingCat))
  have h := restrict_ofPresheaf_eq R S α P (sheafAlgebraHomModule Y B F) m₂ hm
    (fun _ _ f b φ ↦ sheafAlgebraHom_restrict_smul Y B F f b φ)
    (fun _ _ f r x ↦ (PresheafOfModules.homObj B.toModule.val F.val).map_smul f r x)
  exact h.trans (presheaf_ofPresheaf_eq R (PresheafOfModules.homObj B.toModule.val F.val))

private theorem sheafAlgebraHomUnderlying_obj_eq (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) :
    (sheafAlgebraHom Y B ⋙ SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)).obj F =
      ((SheafOfModules.homFunctor Y.sheaf).obj (op B.toModule)).obj F :=
  sheaf_eq (sheafAlgebraHomUnderlying_obj_val_eq Y B F)

/-- Restricting the explicitly constructed Hom functor gives the existing O-module Hom.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The carriers, additive groups, restriction functions and postcomposition functions
are the same by construction. The O scalar action is also the same: O-linearity of each
Hom section identifies precomposition by multiplication by r with multiplication of its
output by r, as in sheafAlgebraHom_underlying_linear. Extensionality of Module structures,
module morphisms and functors, and proof irrelevance of their axioms, give equality. -/
theorem sheafAlgebraHomUnderlying_eq :
    sheafAlgebraHom Y B ⋙ SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom) =
      (SheafOfModules.homFunctor Y.sheaf).obj (op B.toModule) := by
  let R := ((sheafCompose (Opens.grothendieckTopology Y)
    (forget₂ CommRingCat RingCat)).obj Y.sheaf)
  apply functor_eq_of_comp _ _
    (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj)
    (sheafAlgebraHomUnderlying_obj_eq Y B)
  rw [CategoryTheory.Functor.assoc, forget_restrictScalars]
  refine CategoryTheory.Functor.ext (fun F ↦ rfl) ?_
  intro F G f
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  rfl


/-- The identity comparison, transported along equality of the constructed underlying
functor with the shared Hom functor. No Hom object, map or isomorphism is chosen.
Source: Stacks Project, Section 48.11, Tag 0BUZ
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraHomUnderlyingIso :
    sheafAlgebraHom Y B ⋙ SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom) ≅
      (SheafOfModules.homFunctor Y.sheaf).obj (op B.toModule) :=
  eqToIso (sheafAlgebraHomUnderlying_eq Y B)

/-- The functorial K-injective resolution in the Grothendieck abelian category of
O_Y-modules, using the canonical factorization construction.
Source: Stacks Project, Cohomology on Sites, Section 07A5, Theorem 079P
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def sheafAlgebraHomResolution :
    CochainComplex (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) ℤ :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) :=
    SheafOfModules.isGrothendieckAbelian _
  CochainComplex.kInjectiveResolutionFunctor.{u}
    (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))

/-- The canonical natural resolution map into the preceding functor.
Source: Stacks Project, Cohomology on Sites, Section 07A5, Theorem 079P
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def toSheafAlgebraHomResolution :
    𝟭 (CochainComplex (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) ℤ) ⟶
      sheafAlgebraHomResolution Y :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)) :=
    SheafOfModules.isGrothendieckAbelian _
  CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))

section

variable (hB : B.toModule.IsQuasicoherent)
  [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))]
  [HasDerivedCategory.{wB} (SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj B.right))]

set_option linter.unusedSectionVars false in
/-- The resolution followed by termwise algebra-valued Hom inverts quasi-isomorphisms
after localization in D(B).
Source: Stacks Project, Section 48.11, Tag 0BV0; Cohomology on Sites, Lemma 0A95
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Naturality of M → I(M) and two-out-of-three make I(s) a quasi-isomorphism between
K-injective complexes for each quasi-isomorphism s. Apply quasiIso_homComplex_map with
both first complexes B[0] and the identity between them. The underlying termwise Hom
complex is Hom^•(B[0], I(M)); thus its map is a quasi-isomorphism. Quasi-isomorphisms of
B-modules are detected on underlying abelian sheaves, so Q_B inverts this map. -/
theorem sheafAlgebraHomResolution_inverts :
    (HomologicalComplex.quasiIso (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))
      (ComplexShape.up ℤ)).IsInvertedBy
      (sheafAlgebraHomResolution Y ⋙
        (sheafAlgebraHom Y B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) := by
  let A := SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
    (forget₂ CommRingCat RingCat)).obj Y.sheaf)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  exact additive_resolution_inverts (sheafAlgebraHom Y B)

end

/-- Derived internal Hom with the natural B-module structure: localize termwise
Hom(B, I(M)), where I is the fixed degreewise injective K-injective resolution.
Source: Stacks Project, Section 48.11, Tags 0BV0 and 0BV1
(blueprint: def-pc-derived-rhom-algebra-module). -/
noncomputable def derivedRHomAlgebraModule
    (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf) (hB : B.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))]
    [HasDerivedCategory.{wB} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right))] :
    DerivedCategory (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj Y.sheaf)) ⥤
      sheafAlgebraDerivedCategory Y B hB :=
  Localization.lift
    (sheafAlgebraHomResolution Y ⋙
      (sheafAlgebraHom Y B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (sheafAlgebraHomResolution_inverts Y B) DerivedCategory.Q

variable (hB : B.toModule.IsQuasicoherent)
  [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))]
  [HasDerivedCategory.{wB} (SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj B.right))]

/-- Computation on a representative, naturally in the entire complex M.
Source: Stacks Project, Section 48.11, Tag 0BV0
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The localization factorization isomorphism Localization.fac identifies Q followed
by the lifted functor with its defining functor M ↦ Q_B Hom(B, I(M)). -/
theorem derivedRHomAlgebraModule_comparison :
    Nonempty (DerivedCategory.Q ⋙ derivedRHomAlgebraModule Y B hB ≅
      sheafAlgebraHomResolution Y ⋙
        (sheafAlgebraHom Y B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) := by
  exact ⟨Localization.fac _ (sheafAlgebraHomResolution_inverts Y B) DerivedCategory.Q⟩

set_option linter.unusedSectionVars false in
/-- Restriction of algebra scalars preserves finite limits.
Source: Stacks Project, Section 48.11, Tag 0BV1
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The underlying abelian sheaf is unchanged. Finite limits carry the induced B action;
forgetting it gives the same universal cone in O-modules. -/
theorem sheafAlgebraRestrictScalars_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)) := by
  exact restrictScalars_finite_limits _

attribute [instance] sheafAlgebraRestrictScalars_preservesFiniteLimits

set_option linter.unusedSectionVars false in
/-- Restriction of algebra scalars preserves finite colimits.
Source: Stacks Project, Section 48.11, Tag 0BV1
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: The underlying abelian sheaf is unchanged. Finite colimits carry the induced B action;
forgetting it gives the same universal cone in O-modules. -/
theorem sheafAlgebraRestrictScalars_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)) := by
  exact restrictScalars_finite_colimits _

attribute [instance] sheafAlgebraRestrictScalars_preservesFiniteColimits

-- The single-complex and scalar-restriction encodings need additional elaboration fuel.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Forgetting the algebra action recovers the recorded derived internal Hom, naturally
in K. The derived restriction of scalars is the exact functor mapDerivedCategory; the Hom
computation uses the same I as the definition above.
Source: Stacks Project, Section 48.11, Tag 0BV1
(blueprint: def-pc-derived-rhom-algebra-module).
Proof: Restriction of scalars is exact on sheaves of modules since kernels, images and
cokernels have the same underlying abelian sheaves. Its termwise functor therefore
induces mapDerivedCategory with its canonical factorization isomorphism.
Forgetting Hom(B, I(M)) gives
Hom^•(B[0], I(M)). Apply derivedInternalHom_comparison with this same resolution and
specialize its first variable to B[0]. Both resulting functors descend through Q;
full faithfulness of precomposition by a localization descends the natural isomorphism. -/
theorem derivedRHomAlgebraModule_underlying :
    Nonempty (derivedRHomAlgebraModule Y B hB ⋙
      (SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)).mapDerivedCategory ≅
        ((Functor.const (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf)))).obj
          (op (DerivedCategory.Q.obj
            ((HomologicalComplex.single (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj Y.sheaf))
              (ComplexShape.up ℤ) 0).obj B.toModule)))).prod' (𝟭 _) ⋙
          derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
      let A := SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat)).obj Y.sheaf)
      let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
      let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
      let η := CochainComplex.toKInjectiveResolution.{u} A
      let L := (CochainComplex.singleFunctor A 0).obj B.toModule
      let T := SheafOfModules.restrictScalars.{u}
        ((sheafCompose (Opens.grothendieckTopology Y)
          (forget₂ CommRingCat RingCat)).map B.hom)
      have eL := homComplex_single_natural_iso Y B.toModule
      have c := derivedInternalHom_comparison.{u, w}
        (Opens.grothendieckTopology Y) Y.sheaf I η
        (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
          CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩)
      have t := fixed_comparison DerivedCategory.Q I
        (homComplexFunctor (R := Y.sheaf))
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf) L
        (((SheafOfModules.homFunctor Y.sheaf).obj (op B.toModule)).mapHomologicalComplex
          (.up ℤ)) DerivedCategory.Q c eL
      have s := derivedRHomAlgebraModule_comparison Y B hB
      exact compose_comparisons (sheafAlgebraHom Y B) T
        ((SheafOfModules.homFunctor Y.sheaf).obj (op B.toModule)) I
        (derivedRHomAlgebraModule Y B hB) _ s (sheafAlgebraHomUnderlyingIso Y B) t

end AlgebraicGeometry
