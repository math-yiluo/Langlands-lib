/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.ConstructibleSheaf.RestrictScalars
import WeilConjectures.ConstructibleSheaf.InternalHom
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.Algebra.Prime.Lemmas
import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkTensorScalar

/-! # Lisse adic sheaves

## Main definitions

* `LisseIntegralSheaf`: finite locally constant compatible coefficient systems.
* `LisseRationalSheaf`: integral models with rationalized morphisms.
* `lisseIntegralScalarExtension` and `lisseRationalScalarExtension`: coefficient extension.
* `LisseAlgebraicSheaf`: the coefficient-category 2-colimit.
* The `lisseIntegral`, `lisseRational` and `lisseAlgebraic` fibre, tensor and unit constructions.

## References

* Deligne, Weil II, (0.1), (1.1.1) b)-d), pp. 144, 146-147
* SGA 5 VI (1.2.5)
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings

noncomputable section

namespace AlgebraicGeometry.Scheme

-- Use the category's direct quiver, avoiding conversion through a reflexive quiver.
attribute [-instance] CategoryTheory.catToReflQuiver

/-- Share the existing algebra module on a finite coefficient field. -/
local instance (priority := 100000) lisseCoefficientFieldModule
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] :
    Module ℚ_[l] E := Algebra.toModule

/-- Share the subring's existing coefficient-integer ring structure. -/
local instance (priority := 100000) lisseCoefficientIntegersCommRing
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    CommRing (Padic.coefficientExtensionIntegers l E) := inferInstance

/-- Share the existing subring algebra in its coefficient field. -/
local instance (priority := 100000) lisseCoefficientIntegersAlgebra
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Algebra (Padic.coefficientExtensionIntegers l E) E := inferInstance

/-- Share the existing coefficient-integer module in its field. -/
local instance (priority := 100000) lisseCoefficientIntegersModule
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Module (Padic.coefficientExtensionIntegers l E) E := Algebra.toModule

/-- Share the quotient ring structure without unfolding coefficient data. -/
local instance (priority := 100000) lisseCoefficientQuotientCommRing
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    CommRing (Padic.coefficientExtensionRing l E n) :=
  inferInstanceAs (CommRing
    (Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n))

/-- Share the quotient algebra structure without unfolding coefficient data. -/
local instance (priority := 100000) lisseCoefficientQuotientAlgebra
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Algebra (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionRing l E n) :=
  inferInstanceAs (Algebra (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n))

-- Keep the named structures available for the automorphism generator API.
-- Here the inherited ring instances avoid repeated conversion between equivalent copies.
attribute [-instance] lisseCoefficientIntegersCommRing lisseCoefficientIntegersAlgebra
  lisseCoefficientIntegersModule lisseCoefficientQuotientCommRing lisseCoefficientQuotientAlgebra

attribute [local irreducible] GrothendieckTopology.Point.sheafFiber

private theorem tensorComposition_candidate_exists {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (C : Type*) [Category C] [Preadditive C] [Linear R C] :
    ∃ c : ∀ F G H : C, TensorProduct R A (F ⟶ G) →ₗ[A]
        TensorProduct R A (G ⟶ H) →ₗ[A] TensorProduct R A (F ⟶ H),
      ∀ (F G H : C) (a b : A) (f : F ⟶ G) (g : G ⟶ H),
        c F G H (TensorProduct.tmul R a f) (TensorProduct.tmul R b g) =
          TensorProduct.tmul R (a * b) (f ≫ g) := by
  let c (F G H : C) :
      TensorProduct R A (F ⟶ G) →ₗ[A]
        TensorProduct R A (G ⟶ H) →ₗ[A] TensorProduct R A (F ⟶ H) :=
    TensorProduct.AlgebraTensorModule.lift
      (LinearMap.mk₂' A R
        (fun a f ↦ a • ((LinearMap.baseChangeHom R A _ _).comp
          (Linear.comp F G H)) f)
        (by intros; exact add_smul _ _ _)
        (by intro a b f; exact mul_smul a b _)
        (by intros; rw [map_add, smul_add])
        (by intros; rw [map_smul]; exact smul_comm _ _ _))
  have ct (F G H : C) (a b : A)
      (f : F ⟶ G) (g : G ⟶ H) :
      c F G H (TensorProduct.tmul R a f) (TensorProduct.tmul R b g) =
        TensorProduct.tmul R (a * b) (f ≫ g) := by
    change a • (TensorProduct.tmul R b (f ≫ g)) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  exact ⟨c, ct⟩

private theorem tensorComposition_exists {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (C : Type*) [Category C] [Preadditive C] [Linear R C] :
    ∃ c : ∀ F G H : C, TensorProduct R A (F ⟶ G) →ₗ[A]
        TensorProduct R A (G ⟶ H) →ₗ[A] TensorProduct R A (F ⟶ H),
      (∀ (F G H : C) (a b : A) (f : F ⟶ G) (g : G ⟶ H),
        c F G H (TensorProduct.tmul R a f) (TensorProduct.tmul R b g) =
          TensorProduct.tmul R (a * b) (f ≫ g)) ∧
      (∀ (F G : C) (f : TensorProduct R A (F ⟶ G)),
        c F F G (TensorProduct.tmul R 1 (𝟙 F)) f = f) ∧
      (∀ (F G : C) (f : TensorProduct R A (F ⟶ G)),
        c F G G f (TensorProduct.tmul R 1 (𝟙 G)) = f) ∧
      (∀ (F G H K : C) (f : TensorProduct R A (F ⟶ G))
        (g : TensorProduct R A (G ⟶ H)) (h : TensorProduct R A (H ⟶ K)),
        c F H K (c F G H f g) h = c F G K f (c G H K g h)) := by
  obtain ⟨c, ct⟩ := tensorComposition_candidate_exists (R := R) (A := A) C
  refine ⟨c, ct, ?_, ?_, ?_⟩
  · intro F G f
    induction f using TensorProduct.inductionOn with
    | tmul a f => rw [ct, one_mul, Category.id_comp]
    | add f g hf hg => rw [map_add, hf, hg]
  · intro F G f
    induction f using TensorProduct.inductionOn with
    | tmul a f => rw [ct, mul_one, Category.comp_id]
    | add f g hf hg => rw [map_add, LinearMap.add_apply, hf, hg]
  · intro F G H K f g h
    induction f using TensorProduct.inductionOn with
    | tmul a f =>
      induction g using TensorProduct.inductionOn with
      | tmul b g =>
        induction h using TensorProduct.inductionOn with
        | tmul d h => rw [ct, ct, ct, ct, mul_assoc, Category.assoc]
        | add h k hh hk => simp only [map_add, hh, hk]
      | add g h hg hh =>
        simp only [map_add, LinearMap.add_apply, hg, hh]
    | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]

private theorem tensor_transition_kernel {R : Type*} [CommRing R]
    {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup M'] [AddCommGroup N'] [Module R M] [Module R N]
    [Module R M'] [Module R N'] (I : Ideal R) (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hkf : LinearMap.ker f = I • ⊤) (hkg : LinearMap.ker g = I • ⊤) :
    Function.Surjective (TensorProduct.map f g) ∧
      LinearMap.ker (TensorProduct.map f g) = I • ⊤ := by
  constructor
  · exact TensorProduct.map_surjective hf hg
  · rw [TensorProduct.map_ker f.exact_subtype_ker_map hf g.exact_subtype_ker_map hg]
    apply le_antisymm
    · apply sup_le
      · rintro _ ⟨z, rfl⟩
        induction z using TensorProduct.inductionOn with
        | tmul x y =>
          change TensorProduct.tmul R x y.val ∈ I • ⊤
          have hy : y.val ∈ I • (⊤ : Submodule R N) := by
            rw [← hkg]; exact y.property
          refine Submodule.smul_induction_on hy ?_ ?_
          · intro a ha y _
            rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul']
            exact Submodule.smul_mem_smul ha Submodule.mem_top
          · intro y z hy hz
            rw [TensorProduct.tmul_add]
            exact Submodule.add_mem _ hy hz
        | add x y hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy
      · rintro _ ⟨z, rfl⟩
        induction z using TensorProduct.inductionOn with
        | tmul x y =>
          change TensorProduct.tmul R x.val y ∈ I • ⊤
          have hx : x.val ∈ I • (⊤ : Submodule R M) := by
            rw [← hkf]; exact x.property
          refine Submodule.smul_induction_on hx ?_ ?_
          · intro a ha x _
            rw [← TensorProduct.smul_tmul']
            exact Submodule.smul_mem_smul ha Submodule.mem_top
          · intro x z hx hz
            rw [TensorProduct.add_tmul]
            exact Submodule.add_mem _ hx hz
        | add x y hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy
    · apply Submodule.smul_le.mpr
      intro a ha z hz
      clear hz
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
        refine (le_sup_right : (LinearMap.rTensor N f.ker.subtype).range ≤ _) ?_
        refine ⟨TensorProduct.tmul R ⟨a • x, ?_⟩ y, ?_⟩
        · rw [hkf]
          exact Submodule.smul_mem_smul ha Submodule.mem_top
        · exact (TensorProduct.smul_tmul' a x y).symm
      | add x y hx hy =>
        rw [smul_add]
        exact Submodule.add_mem _ hx hy

private theorem quotientFactor_id {R : Type*} [CommRing R] (I : Ideal R) :
    (Ideal.Quotient.factorₐ R (le_refl I)).toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

private theorem quotientFactor_comp {R : Type*} [CommRing R]
    (I J K : Ideal R) (h : I ≤ J) (k : J ≤ K) :
    (Ideal.Quotient.factorₐ R (h.trans k)).toLinearMap =
      (Ideal.Quotient.factorₐ R k).toLinearMap.comp
        (Ideal.Quotient.factorₐ R h).toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

private theorem quotientFactor_kernel {R : Type*} [CommRing R]
    (I J : Ideal R) (h : J ≤ I) :
    LinearMap.ker (Ideal.Quotient.factorₐ R h).toLinearMap =
      I • (⊤ : Submodule R (R ⧸ J)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : r ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
    apply Submodule.map_le_smul_top I (Ideal.Quotient.mkₐ R J).toLinearMap
    exact ⟨r, hr, rfl⟩
  · apply Submodule.smul_le.mpr
    intro a ha x _
    change (Ideal.Quotient.factorₐ R h).toLinearMap (a • x) = 0
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right r ha)

/-- Sheafification for module coefficients on the small étale site. -/
local instance (priority := 100000) lisseModuleSheafify
    (Y : Scheme.{u}) (R : Type (u + 1)) [Ring R] :
    HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  (GrothendieckTopology.hasSheafify_smallEtaleTopology
    (ModuleCat.{u + 1} R) Y).isRightAdjoint

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : Scheme.{u})

/-- The inverse diagrams of sheaves of `𝒪_E`-modules, indexed by `n + 1`. -/
abbrev AdicIntegralDiagram :=
  ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))

/-- A lisse integral system: each level is finite locally constant, killed by
`I^(n+1)` for `I = (ϖ_E)`, and on every geometric stalk the transition is surjective with
kernel `I^(n+1)` times the source. -/
def IsLisseIntegralDiagram (F : AdicIntegralDiagram l E Y) : Prop :=
  let R := Padic.coefficientExtensionIntegers l E
  let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
  (∀ n : ℕ, IsFiniteLocallyConstantSheaf (F.obj (op n))) ∧
  (∀ n : ℕ, ∀ U : Y.Etale,
    I ^ (n + 1) • (⊤ : Submodule R ((F.obj (op n)).obj.obj (op U))) = ⊥) ∧
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (n : ℕ),
    let T := (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)
    let t := (T.map (F.map (homOfLE (Nat.le_succ n)).op)).hom
    Function.Surjective t ∧
      LinearMap.ker t = I ^ (n + 1) • (⊤ : Submodule R (T.obj (F.obj (op (n + 1)))))

/-- The category of lisse `𝒪_E`-sheaves. Morphisms are natural transformations,
hence exactly the compatible families of coefficient-linear maps. -/
def LisseIntegralSheaf [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)] :=
  ObjectProperty.FullSubcategory (IsLisseIntegralDiagram l E Y)

variable [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]

/-- The integral category is the original full-subcategory category, cached by name. -/
instance lisseIntegralCategory : Category (LisseIntegralSheaf l E Y) :=
  inferInstanceAs (Category (ObjectProperty.FullSubcategory (IsLisseIntegralDiagram l E Y)))

instance (priority := 10000) lisseIntegralPreadditive :
    Preadditive (LisseIntegralSheaf l E Y) :=
  inferInstanceAs (Preadditive (ObjectProperty.FullSubcategory (IsLisseIntegralDiagram l E Y)))

instance (priority := 10000) lisseIntegralLinear :
    Linear (Padic.coefficientExtensionIntegers l E) (LisseIntegralSheaf l E Y) :=
  inferInstanceAs (Linear (Padic.coefficientExtensionIntegers l E)
    (ObjectProperty.FullSubcategory (IsLisseIntegralDiagram l E Y)))

/-- Cache the additive integral Hom structure inherited from module sheaves. -/
instance (priority := 10000) lisseIntegralHomAddCommGroup
    (F G : LisseIntegralSheaf l E Y) : AddCommGroup (F ⟶ G) := inferInstance

/-- Cache the integral Hom module structure inherited from module sheaves. -/
instance (priority := 10000) lisseIntegralHomModule
    (F G : LisseIntegralSheaf l E Y) :
    Module (Padic.coefficientExtensionIntegers l E) (F ⟶ G) := inferInstance

/-- The integral fibre is the inverse limit of the geometric stalks. -/
def lisseIntegralFiber {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (F : LisseIntegralSheaf l E Y) :
    ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) :=
  limit (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber)

/-- An `E`-sheaf is an integral lattice considered up to rational morphisms. -/
structure LisseRationalSheaf where
  /-- Its chosen integral model; different models may be isomorphic. -/
  integral : LisseIntegralSheaf l E Y

/-- Rational Hom, `E ⊗_{𝒪_E} Hom(F,G)`. -/
def lisseRationalHom (F G : LisseRationalSheaf l E Y) :=
  TensorProduct (Padic.coefficientExtensionIntegers l E) E (F.integral ⟶ G.integral)

/-- The rational Hom inherits exactly the additive tensor structure. -/
instance lisseRationalHomGroup (F G : LisseRationalSheaf l E Y) :
    AddCommGroup (lisseRationalHom l E Y F G) :=
  inferInstanceAs (AddCommGroup
    (TensorProduct (Padic.coefficientExtensionIntegers l E) E (F.integral ⟶ G.integral)))

/-- The rational Hom inherits exactly the scalar tensor structure. -/
instance lisseRationalHomScalarModule (F G : LisseRationalSheaf l E Y) :
    Module E (lisseRationalHom l E Y F G) :=
  inferInstanceAs (Module E
    (TensorProduct (Padic.coefficientExtensionIntegers l E) E (F.integral ⟶ G.integral)))

-- Avoid generating unused constructor-injectivity and size functions.
set_option genInjectivity false in
set_option genSizeOf false in
/-- The bilinear composition and its laws. All data are prescribed on pure tensors;
only verification of the laws is postponed in `lisseRationalComposition_exists`. -/
structure LisseRationalComposition where
  /-- The extension of integral composition by `E`-bilinearity. -/
  comp (F G H : LisseRationalSheaf l E Y) :
    lisseRationalHom l E Y F G →ₗ[E]
      lisseRationalHom l E Y G H →ₗ[E] lisseRationalHom l E Y F H
  /-- The defining pure-tensor formula. -/
  comp_tmul (F G H : LisseRationalSheaf l E Y) (a b : E)
      (f : F.integral ⟶ G.integral) (g : G.integral ⟶ H.integral) :
    comp F G H (TensorProduct.tmul _ a f) (TensorProduct.tmul _ b g) =
      TensorProduct.tmul _ (a * b) (f ≫ g)
  /-- Identity on the left. -/
  id_comp (F G : LisseRationalSheaf l E Y) (f : lisseRationalHom l E Y F G) :
    comp F F G (TensorProduct.tmul _ 1 (𝟙 F.integral)) f = f
  /-- Identity on the right. -/
  comp_id (F G : LisseRationalSheaf l E Y) (f : lisseRationalHom l E Y F G) :
    comp F G G f (TensorProduct.tmul _ 1 (𝟙 G.integral)) = f
  /-- Associativity. -/
  assoc (F G H K : LisseRationalSheaf l E Y)
      (f : lisseRationalHom l E Y F G) (g : lisseRationalHom l E Y G H)
      (h : lisseRationalHom l E Y H K) :
    comp F H K (comp F G H f g) h = comp F G K f (comp G H K g h)

/-- Rational composition exists and satisfies the category laws. -/
theorem lisseRationalComposition_exists : Nonempty (LisseRationalComposition l E Y) := by
  obtain ⟨c, ht, hi, hc, ha⟩ := tensorComposition_exists
    (R := Padic.coefficientExtensionIntegers l E) (A := E) (LisseIntegralSheaf l E Y)
  exact ⟨{ comp F G H := c F.integral G.integral H.integral
           comp_tmul F G H := ht F.integral G.integral H.integral
           id_comp F G := hi F.integral G.integral
           comp_id F G := hc F.integral G.integral
           assoc F G H K := ha F.integral G.integral H.integral K.integral }⟩

/-- The unique bilinear composition with the prescribed pure-tensor formula. -/
@[irreducible]
def lisseRationalComposition : LisseRationalComposition l E Y :=
  Classical.choice (lisseRationalComposition_exists l E Y)

/-- The category with the stated rational Hom and induced composition. -/
instance lisseRationalCategory : Category (LisseRationalSheaf l E Y) where
  Hom := lisseRationalHom l E Y
  id F := TensorProduct.tmul _ 1 (𝟙 F.integral)
  comp {F G H} f g := (lisseRationalComposition l E Y).comp F G H f g
  id_comp := (lisseRationalComposition l E Y).id_comp _ _
  comp_id := (lisseRationalComposition l E Y).comp_id _ _
  assoc := (lisseRationalComposition l E Y).assoc _ _ _ _

/-- Rational Hom has its tensor-product additive group. -/
instance lisseRationalHomAddCommGroup (F G : LisseRationalSheaf l E Y) :
    AddCommGroup (F ⟶ G) := inferInstanceAs (AddCommGroup (lisseRationalHom l E Y F G))

/-- The rational fibre is `E ⊗_{𝒪_E} F_y`. -/
def lisseRationalFiber {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (F : LisseRationalSheaf l E Y) : ModuleCat.{u + 1} E :=
  ModuleCat.of E (TensorProduct (Padic.coefficientExtensionIntegers l E) E
    (lisseIntegralFiber l E Y y F.integral))

-- Cache the sheaf Hom actions before the tensor proof, rather than repeatedly
-- unfolding the full-subcategory and presheaf linear-category instances.
local instance (priority := 10000) lisseSheafHomAddCommGroup
    {R : Type (u + 1)} [Ring R]
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    AddCommGroup (F ⟶ G) := inferInstance

local instance (priority := 10000) lisseSheafHomModule
    {R : Type (u + 1)} [CommRing R]
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    Module R (F ⟶ G) := inferInstance

section TensorConstruction

attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
attribute [local instance] CategoryTheory.Sheaf.braidedCategory

private def IsLisseDiagramOver (R : Type (u + 1)) [CommRing R] (I : Ideal R)
    (F : ℕᵒᵖ ⥤ Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) : Prop :=
  (∀ n : ℕ, IsFiniteLocallyConstantSheaf (F.obj (op n))) ∧
  (∀ n : ℕ, ∀ U : Y.Etale,
    I ^ (n + 1) • (⊤ : Submodule R ((F.obj (op n)).obj.obj (op U))) = ⊥) ∧
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (n : ℕ),
    let T := (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)
    let t := (T.map (F.map (homOfLE (Nat.le_succ n)).op)).hom
    Function.Surjective t ∧
      LinearMap.ker t = I ^ (n + 1) • (⊤ : Submodule R (T.obj (F.obj (op (n + 1)))))

omit [IsNoetherian Y] [Y.IsSeparated] in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorDiagram_isLisse {R : Type (u + 1)} [CommRing R] (I : Ideal R)
    (F G : ObjectProperty.FullSubcategory (IsLisseDiagramOver Y R I)) :
    IsLisseDiagramOver Y R I (F.obj ⊗ G.obj) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [CategoryTheory.Monoidal.tensorObj_obj]
    exact (F.property.1 n).tensorObj (G.property.1 n)
  · intro n U
    apply bot_unique
    apply Submodule.smul_le.mpr
    intro a ha x _
    change (F.obj.obj (op n) ⊗ G.obj.obj (op n)).obj.obj (op U) at x
    have hz : a • (𝟙 (F.obj.obj (op n))) = 0 := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (Submodule.mem_bot R).mp ((F.property.2.1 n V.unop) ▸
        Submodule.smul_mem_smul ha (Submodule.mem_top : z ∈ ⊤))
    have hz' : a • (𝟙 (F.obj.obj (op n) ⊗ G.obj.obj (op n))) = 0 := by
      rw [← MonoidalCategory.id_whiskerRight, ← MonoidalLinear.smul_whiskerRight,
        hz, MonoidalPreadditive.zero_whiskerRight]
    exact congrArg (fun f ↦ f.hom.app (op U) x) hz'
  · intro Ω _ _ y n
    let T := (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)
    let f := F.obj.map (homOfLE (Nat.le_succ n)).op
    let g := G.obj.map (homOfLE (Nat.le_succ n)).op
    let e₁ := (Functor.Monoidal.μIso T (F.obj.obj (op (n + 1)))
      (G.obj.obj (op (n + 1)))).toLinearEquiv
    let e₂ := (Functor.Monoidal.μIso T (F.obj.obj (op n))
      (G.obj.obj (op n))).toLinearEquiv
    let t := (T.map ((F.obj ⊗ G.obj).map (homOfLE (Nat.le_succ n)).op)).hom
    let q := TensorProduct.map (T.map f).hom (T.map g).hom
    have hF := F.property.2.2 Ω y n
    have hG := G.property.2.2 Ω y n
    obtain ⟨hq, hk⟩ := tensor_transition_kernel (I ^ (n + 1))
      (T.map f).hom (T.map g).hom hF.1 hG.1 hF.2 hG.2
    have hn (x) : t (e₁ x) = e₂ (q x) := by
      dsimp only [t]
      rw [CategoryTheory.Monoidal.tensorObj_map]
      exact congrArg (fun f ↦ f x) (congrArg ModuleCat.Hom.hom
        (Functor.LaxMonoidal.μ_natural T f g)).symm
    constructor
    · intro x
      obtain ⟨z, hz⟩ := hq (e₂.symm x)
      refine ⟨e₁ z, ?_⟩
      rw [hn, hz, e₂.apply_symm_apply]
    · have he : (I ^ (n + 1) • (⊤ : Submodule R _)).comap
          e₁.symm.toLinearMap = I ^ (n + 1) • ⊤ := by
        rw [Submodule.comap_smul_top_of_surjective _ _ e₁.symm.surjective,
          LinearMap.ker_eq_bot.mpr e₁.symm.injective, sup_bot_eq]
      rw [← he, ← hk]
      ext x
      change t x = 0 ↔ q (e₁.symm x) = 0
      rw [← e₂.injective.eq_iff, map_zero, ← hn, e₁.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Tensor of integral systems is lisse. -/
theorem lisseIntegralTensor_isLisse (F G : LisseIntegralSheaf l E Y) :
    IsLisseIntegralDiagram l E Y (F.obj ⊗ G.obj) := by
  exact tensorDiagram_isLisse Y (R := Padic.coefficientExtensionIntegers l E)
    (Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)))
    ⟨F.obj, F.property⟩ ⟨G.obj, G.property⟩

/-- Levelwise tensor, with the tensor of transition maps. -/
def lisseIntegralTensor (F G : LisseIntegralSheaf l E Y) : LisseIntegralSheaf l E Y :=
  ⟨F.obj ⊗ G.obj, lisseIntegralTensor_isLisse l E Y F G⟩

/-- Tensor of rational objects uses the tensor of their integral models. -/
def lisseRationalTensor (F G : LisseRationalSheaf l E Y) : LisseRationalSheaf l E Y :=
  ⟨lisseIntegralTensor l E Y F.integral G.integral⟩

end TensorConstruction

/-- The quotient transition viewed as an `𝒪_E`-linear map, for any two levels. -/
def lisseUnitModuleMap (i j : ℕᵒᵖ) (f : i ⟶ j) :
    ModuleCat.of (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionRing l E (i.unop + 1)) ⟶
    ModuleCat.of (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionRing l E (j.unop + 1)) :=
  ModuleCat.ofHom (Ideal.Quotient.factorₐ (Padic.coefficientExtensionIntegers l E)
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))).toLinearMap

/-- The quotient maps preserve identities. -/
theorem lisseUnitModuleMap_id (i : ℕᵒᵖ) :
    lisseUnitModuleMap l E i i (𝟙 i) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  exact quotientFactor_id _

/-- The quotient maps preserve composition. -/
theorem lisseUnitModuleMap_comp (i j k : ℕᵒᵖ) (f : i ⟶ j) (g : j ⟶ k) :
    lisseUnitModuleMap l E i k (f ≫ g) =
      lisseUnitModuleMap l E i j f ≫ lisseUnitModuleMap l E j k g := by
  apply ModuleCat.hom_ext
  exact quotientFactor_comp _ _ _
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom g.unop) 1))

/-- The inverse diagram of constant coefficient sheaves. -/
def lisseIntegralUnitDiagram : AdicIntegralDiagram l E Y :=
  (show ℕᵒᵖ ⥤ ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) from
    { obj i := ModuleCat.of _ (Padic.coefficientExtensionRing l E (i.unop + 1))
      map {i j} f := lisseUnitModuleMap l E i j f
      map_id := lisseUnitModuleMap_id l E
      map_comp := lisseUnitModuleMap_comp l E _ _ _ }) ⋙
        constantSheaf Y.smallEtaleTopology _

-- Keep the existing standing hypotheses of this public interface.
set_option linter.unusedSectionVars false in
/-- The constant coefficient system is lisse. -/
theorem lisseIntegralUnit_isLisse :
    IsLisseIntegralDiagram l E Y (lisseIntegralUnitDiagram l E Y) := by
  let R := Padic.coefficientExtensionIntegers l E
  let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
  let Q (n : ℕ) := ModuleCat.of R (Padic.coefficientExtensionRing l E (n + 1))
  let C := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hc : Sheaf.IsConstant Y.smallEtaleTopology (C.obj (Q n)) :=
      Sheaf.isConstant_of_iso _ (X := Q n) (Iso.refl _)
    have hf := isFiniteSheaf_constantSheaf (X := Y) (Q n)
    exact { toIsLocallyConstantSheaf := hc.isLocallyConstantSheaf
            toIsFiniteSheaf := hf }
  · intro n U
    apply bot_unique
    apply Submodule.smul_le.mpr
    intro a ha x _
    have hz : a • (𝟙 (Q n)) = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change R ⧸ I ^ (n + 1) at z
      change (Ideal.Quotient.mk (I ^ (n + 1)) a) * z = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
    have hz' : a • (𝟙 (C.obj (Q n))) = 0 := by
      rw [← C.map_id, ← Functor.map_smul, hz, C.map_zero]
    exact congrArg (fun f ↦ f.hom.app (op U) x) hz'
  · intro Ω _ _ y n
    let p := (pointSmallEtale y).ulift.{u + 1}
    let e₁ := (p.sheafFiberConstantSheafIso (Q (n + 1))).toLinearEquiv
    let e₂ := (p.sheafFiberConstantSheafIso (Q n)).toLinearEquiv
    let t := (p.sheafFiber.map
      ((lisseIntegralUnitDiagram l E Y).map (homOfLE (Nat.le_succ n)).op)).hom
    let q := (lisseUnitModuleMap l E (op (n + 1)) (op n)
      (homOfLE (Nat.le_succ n)).op).hom
    have hn (x) : e₂ (t x) = q (e₁ x) := by
      exact congrArg (fun f ↦ f x)
        (congrArg ModuleCat.Hom.hom (p.sheafFiberConstantSheafIso_hom_naturality
          (lisseUnitModuleMap l E (op (n + 1)) (op n)
            (homOfLE (Nat.le_succ n)).op)))
    constructor
    · intro x
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e₂ x)
      refine ⟨e₁.symm (Ideal.Quotient.mk (I ^ (n + 2)) r), e₂.injective ?_⟩
      rw [hn, e₁.apply_symm_apply]
      exact hr
    · have hq : LinearMap.ker q = I ^ (n + 1) • (⊤ : Submodule R (Q (n + 1))) :=
        quotientFactor_kernel (I ^ (n + 1)) (I ^ (n + 2))
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      have he : (I ^ (n + 1) • (⊤ : Submodule R (Q (n + 1)))).comap
          e₁.toLinearMap = I ^ (n + 1) • ⊤ := by
        rw [Submodule.comap_smul_top_of_surjective _ _ e₁.surjective,
          LinearMap.ker_eq_bot.mpr e₁.injective, sup_bot_eq]
      rw [← he, ← hq]
      ext x
      change t x = 0 ↔ q (e₁ x) = 0
      rw [← e₂.injective.eq_iff, map_zero, hn]

/-- The tensor unit, the constant coefficient system. -/
def lisseIntegralUnit : LisseIntegralSheaf l E Y :=
  ⟨lisseIntegralUnitDiagram l E Y, lisseIntegralUnit_isLisse l E Y⟩

/-- The rational tensor unit is the rationalization of the constant coefficient system. -/
def lisseRationalUnit : LisseRationalSheaf l E Y := ⟨lisseIntegralUnit l E Y⟩

section ScalarExtension

attribute [local irreducible] ModuleCat.ringExtendScalars

variable (L : Type (u + 1)) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

/-- A field inclusion induces the inclusion of rings of integers. -/
theorem lisseIntegerInclusion_exists :
    ∃ f : Padic.coefficientExtensionIntegers l E →+*
      Padic.coefficientExtensionIntegers l L, ∀ x, (f x : L) = ι (x : E) := by
  have hE := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec.1
  have hL := (Padic.coefficientExtensionIntegers_dvr l L).choose_spec.1
  have hmap (a : E) : spectralNorm ℚ_[l] L (ι a) = spectralNorm ℚ_[l] E a := by
    unfold spectralNorm
    rw [minpoly.algHom_eq ι ι.injective]
  let f : Padic.coefficientExtensionIntegers l E →+*
      Padic.coefficientExtensionIntegers l L :=
    { toFun := fun x ↦ ⟨ι (x : E), by
        apply (hL _).mpr
        change spectralNorm ℚ_[l] L (ι (x : E)) ≤ 1
        rw [hmap]
        exact (hE _).mp x.property⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' x y := Subtype.ext (map_mul ι (x : E) (y : E))
      map_zero' := Subtype.ext (map_zero ι)
      map_add' x y := Subtype.ext (map_add ι (x : E) (y : E)) }
  exact ⟨f, fun _ ↦ rfl⟩

/-- Restriction of the given field inclusion to the rings of integers. -/
def lisseIntegerInclusion : Padic.coefficientExtensionIntegers l E →+*
    Padic.coefficientExtensionIntegers l L :=
  (lisseIntegerInclusion_exists l E L ι).choose

/-- The positive ramification index is characterized by the image of the maximal ideal. -/
theorem lisseRamificationIndex_exists :
    ∃ e : ℕ, 0 < e ∧
      Ideal.map (lisseIntegerInclusion l E L ι) (Padic.coefficientExtensionMaximalIdeal l E) =
        Padic.coefficientExtensionMaximalIdeal l L ^ e := by
  have hE := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hL := (Padic.coefficientExtensionIntegers_dvr l L).choose_spec
  rcases hE with ⟨_, hmE, _, _, _, _, _, _, _, hneE, _⟩
  rcases hL with ⟨_, hmL, _, _, hmaxL, _, _, hdvrL, _⟩
  have : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l L) := hdvrL
  have hi (x : Padic.coefficientExtensionIntegers l E) :
      (lisseIntegerInclusion l E L ι x : L) = ι (x : E) :=
    (lisseIntegerInclusion_exists l E L ι).choose_spec x
  have hinj : Function.Injective (lisseIntegerInclusion l E L ι) := by
    intro x y h
    apply Subtype.ext
    apply ι.injective
    have hc := congrArg
      (fun z : Padic.coefficientExtensionIntegers l L ↦ (z : L)) h
    exact (hi x).symm.trans (hc.trans (hi y))
  have hne : Ideal.map (lisseIntegerInclusion l E L ι)
      (Padic.coefficientExtensionMaximalIdeal l E) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr hneE
  have hle : Ideal.map (lisseIntegerInclusion l E L ι)
      (Padic.coefficientExtensionMaximalIdeal l E) ≤
        Padic.coefficientExtensionMaximalIdeal l L := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    apply (hmL _).mpr
    change spectralNorm ℚ_[l] L _ < 1
    rw [hi]
    have heq : spectralNorm ℚ_[l] L (ι (x : E)) = spectralNorm ℚ_[l] E (x : E) := by
      unfold spectralNorm
      rw [minpoly.algHom_eq ι ι.injective]
    rw [heq]
    exact (hmE _).mp hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (Padic.coefficientExtensionIntegers l L)
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hπ
  have hmax : Padic.coefficientExtensionMaximalIdeal l L =
      Ideal.span ({π} : Set (Padic.coefficientExtensionIntegers l L)) :=
    (IsLocalRing.eq_maximalIdeal hmaxL).trans hπ.maximalIdeal_eq
  refine ⟨e, ?_, ?_⟩
  · by_contra h
    have hz : e = 0 := by omega
    rw [he, hz, pow_zero, Ideal.span_singleton_one] at hle
    exact hmaxL.ne_top (top_le_iff.mp hle)
  · rw [hmax, Ideal.span_singleton_pow]
    exact he

/-- The ramification index of the coefficient inclusion. -/
def lisseRamificationIndex : ℕ := (lisseRamificationIndex_exists l E L ι).choose

/-- The source index, zero-based, corresponding to `ceil((m+1)/e)`. -/
def lisseScalarSourceIndex (m : ℕ) : ℕ :=
  (m + 1 + lisseRamificationIndex l E L ι - 1) / lisseRamificationIndex l E L ι - 1

/-- The ceiling source index is nondecreasing. -/
theorem lisseScalarSourceIndex_le (m : ℕ) :
    lisseScalarSourceIndex l E L ι m ≤ lisseScalarSourceIndex l E L ι (m + 1) := by
  unfold lisseScalarSourceIndex
  apply Nat.sub_le_sub_right
  apply Nat.div_le_div_right
  omega

/-- The scalar map to the target finite quotient. -/
def lisseScalarCoefficientMap (m : ℕ) : Padic.coefficientExtensionIntegers l E →+*
    Padic.coefficientExtensionRing l L (m + 1) :=
  (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1))).comp
    (lisseIntegerInclusion l E L ι)

/-- The level `F_n ⊗_{A_E,n} A_L,m`, as a sheaf of `𝒪_L`-modules.
Here `n = ceil(m/e)`; extending directly from `𝒪_E` gives the same balanced tensor
because `F_n` is killed by `ϖ_E^n` and `ϖ_E^n` maps to zero in `A_L,m`. -/
def lisseIntegralScalarLevel (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) :=
  (sheafCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1}
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1))))).obj
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology
      (lisseScalarCoefficientMap l E L ι m)).obj
        (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))))

/-- The local pure tensor generator in the scalar-extended finite level. -/
def lisseIntegralScalarGenerator (F : LisseIntegralSheaf l E Y) (m : ℕ) (U : Y.Etale)
    (a : Padic.coefficientExtensionRing l L (m + 1))
    (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)) :
    (lisseIntegralScalarLevel l E Y L ι F m).obj.obj (op U) :=
  ((toSheafification Y.smallEtaleTopology
    (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l L (m + 1)))).app
      ((F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj ⋙
        ModuleCat.ringExtendScalars.{u + 1, u + 1}
          (lisseScalarCoefficientMap l E L ι m))).app (op U)
          (ModuleCat.ringExtensionTmul.{u + 1, u + 1}
            (lisseScalarCoefficientMap l E L ι m) _ a s)

-- Keep record generation from expanding the sheafified scalar-level formula.
attribute [local irreducible] lisseIntegralScalarLevel lisseIntegralScalarGenerator
-- Avoid generating unused constructor-injectivity and size functions.
set_option genInjectivity false in
set_option genSizeOf false in
/-- Scalar extension with its prescribed levels, transitions and action on morphisms.
The level identifications are module-sheaf isomorphisms, and all transition and morphism
maps are fixed by their action on the sheafification of pure tensors. -/
structure LisseIntegralScalarExtensionData where
  /-- The functor on integral systems. -/
  functor : LisseIntegralSheaf l E Y ⥤ LisseIntegralSheaf l L Y
  /-- The displayed finite-level formula. -/
  levelIso (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    (functor.obj F).obj.obj (op m) ≅ lisseIntegralScalarLevel l E Y L ι F m
  /-- Transition maps are induced by the coefficient and source transition maps. -/
  transition (F : LisseIntegralSheaf l E Y) (m : ℕ) (U : Y.Etale)
      (a : Padic.coefficientExtensionRing l L (m + 2))
      (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι (m + 1)))).obj.obj (op U)) :
    (levelIso F m).hom.hom.app (op U)
      (((functor.obj F).obj.map (homOfLE (Nat.le_succ m)).op).hom.app (op U)
        ((levelIso F (m + 1)).inv.hom.app (op U)
          (lisseIntegralScalarGenerator l E Y L ι F (m + 1) U a s))) =
      lisseIntegralScalarGenerator l E Y L ι F m U
        (Padic.coefficientExtensionTransition l L (m + 1) a)
        ((F.obj.map (homOfLE (lisseScalarSourceIndex_le l E L ι m)).op).hom.app (op U) s)
  /-- The map of a morphism is the scalar extension of each of its levels. -/
  map (F G : LisseIntegralSheaf l E Y) (f : F ⟶ G) (m : ℕ) (U : Y.Etale)
      (a : Padic.coefficientExtensionRing l L (m + 1))
      (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)) :
    (levelIso G m).hom.hom.app (op U)
      (((functor.map f).hom.app (op m)).hom.app (op U)
        ((levelIso F m).inv.hom.app (op U)
          (lisseIntegralScalarGenerator l E Y L ι F m U a s))) =
      lisseIntegralScalarGenerator l E Y L ι G m U a
        ((f.hom.app (op (lisseScalarSourceIndex l E L ι m))).hom.app (op U) s)

attribute [local semireducible] lisseIntegralScalarLevel lisseIntegralScalarGenerator

set_option maxRecDepth 100 in
/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_quotientRestrictedHom {S A : Type (u + 1)} [Ring S] [Ring A]
    (q : S →+* A) (hq : Function.Surjective q) (M N : ModuleCat.{u + 1} A)
    (f : (ModuleCat.restrictScalars.{u + 1} q).obj M ⟶
      (ModuleCat.restrictScalars.{u + 1} q).obj N) :
    M ⟶ N :=
  ModuleCat.ofHom (X := M) (Y := N)
    { toFun := f
      map_add' := f.hom.map_add
      map_smul' := by
        intro a x
        obtain ⟨b, rfl⟩ := hq a
        exact f.hom.map_smul b x }

set_option maxRecDepth 100 in
/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_quotientRestrictedSheafHom {S A : Type (u + 1)} [Ring S] [Ring A]
    (q : S →+* A) (hq : Function.Surjective q)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj M ⟶
      (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj N) : M ⟶ N :=
  ⟨{ app U := lisseCoherence_quotientRestrictedHom q hq _ _ (f.hom.app U)
     naturality U V v := by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro x
       exact congrArg (fun h ↦ h x) (congrArg ModuleCat.Hom.hom (f.hom.naturality v)) }⟩

private theorem quotientTensor_kernel {R S M N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (I J : Ideal S) (hJI : J ≤ I) (K : Ideal R) (v : M →ₗ[R] N)
    (hv : Function.Surjective v) (hk : LinearMap.ker v = K • ⊤)
    (hKI : K.map (algebraMap R S) ≤ I) :
    let q := (Ideal.Quotient.factorₐ S hJI).toLinearMap
    let t := TensorProduct.AlgebraTensorModule.map q v
    Function.Surjective t ∧ LinearMap.ker t = I • ⊤ := by
  dsimp only
  let q := (Ideal.Quotient.factorₐ S hJI).toLinearMap
  let qR := q.restrictScalars R
  let t := TensorProduct.AlgebraTensorModule.map q v
  have hq : Function.Surjective qR := Ideal.Quotient.factor_surjective hJI
  constructor
  · exact TensorProduct.map_surjective hq hv
  · apply le_antisymm
    · intro z hz
      have hz' : z ∈ LinearMap.ker (TensorProduct.map qR v) := hz
      rw [TensorProduct.map_ker qR.exact_subtype_ker_map hq
        v.exact_subtype_ker_map hv] at hz'
      have hleft : (LinearMap.lTensor (S ⧸ J) v.ker.subtype).range ≤
          (I • (⊤ : Submodule S ((S ⧸ J) ⊗[R] M))).restrictScalars R := by
        rintro _ ⟨x, rfl⟩
        induction x using TensorProduct.inductionOn with
        | tmul x y =>
          change x ⊗ₜ[R] y.val ∈ I • (⊤ : Submodule S ((S ⧸ J) ⊗[R] M))
          have hy : y.val ∈ K • (⊤ : Submodule R M) := by rw [← hk]; exact y.property
          refine Submodule.smul_induction_on hy ?_ ?_
          · intro a ha y _
            rw [← TensorProduct.smul_tmul,
              ← IsScalarTower.algebraMap_smul S a x, ← TensorProduct.smul_tmul']
            exact Submodule.smul_mem_smul
              (hKI (Ideal.mem_map_of_mem _ ha)) Submodule.mem_top
          · intro y z hy hz
            rw [TensorProduct.tmul_add]
            exact Submodule.add_mem _ hy hz
        | add x y hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy
      have hright : (LinearMap.rTensor M qR.ker.subtype).range ≤
          (I • (⊤ : Submodule S ((S ⧸ J) ⊗[R] M))).restrictScalars R := by
        rintro _ ⟨x, rfl⟩
        induction x using TensorProduct.inductionOn with
        | tmul x y =>
          change x.val ⊗ₜ[R] y ∈ I • (⊤ : Submodule S ((S ⧸ J) ⊗[R] M))
          have hx : x.val ∈ I • (⊤ : Submodule S (S ⧸ J)) := by
            rw [← quotientFactor_kernel I J hJI]
            exact x.property
          refine Submodule.smul_induction_on hx ?_ ?_
          · intro a ha x _
            rw [← TensorProduct.smul_tmul']
            exact Submodule.smul_mem_smul ha Submodule.mem_top
          · intro x z hx hz
            rw [TensorProduct.add_tmul]
            exact Submodule.add_mem _ hx hz
        | add x y hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy
      exact (sup_le hleft hright) hz'
    · apply Submodule.smul_le.mpr
      intro a ha z _
      change t (a • z) = 0
      rw [map_smul]
      have hzero : ∀ w : (S ⧸ I) ⊗[R] N, a • w = 0 := by
        intro w
        induction w using TensorProduct.inductionOn with
        | tmul x y =>
          rw [TensorProduct.smul_tmul']
          have hx : a • x = 0 := by
            change Ideal.Quotient.mk I a * x = 0
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
          rw [hx, TensorProduct.zero_tmul]
        | add x y hx hy => rw [smul_add, hx, hy, add_zero]
      exact hzero _

section ScalarLissity

attribute [local semireducible] GrothendieckTopology.Point.sheafFiber

variable {Y}

variable {R S : Type (u + 1)} [Ring R] [Ring S]

private def scalarOverIso (f : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (U : Y.Etale) :
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F).over U ≅
      (Sheaf.ringExtendScalars.{u + 1, u + 1} (Y.smallEtaleTopology.over U) f).obj
        (F.over U) :=
  (((Over.forget U).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} S) (Y.smallEtaleTopology.over U) Y.smallEtaleTopology).app
      (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).symm

private def scalarConstantIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{u + 1} R)]
    [HasWeakSheafify J (ModuleCat.{u + 1} S)] (f : R →+* S)
    (M : ModuleCat.{u + 1} R) :
    (Sheaf.ringExtendScalars.{u + 1, u + 1} J f).obj ((constantSheaf J _).obj M) ≅
      (constantSheaf J _).obj ((ModuleCat.ringExtendScalars.{u + 1, u + 1} f).obj M) := by
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  exact (presheafToSheafCompComposeAndSheafifyIso J E).app
      ((Functor.const Cᵒᵖ).obj M) ≪≫
    (presheafToSheaf J _).mapIso (NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (by intros; simp))

private theorem scalarFinite (f : R →+* S) (M : ModuleCat.{u + 1} R)
    (hM : ConcreteCategory.IsFinitelyGenerated M) :
    ConcreteCategory.IsFinitelyGenerated
      ((ModuleCat.ringExtendScalars.{u + 1, u + 1} f).obj M) := by
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f
  let η := adj.unit.app M
  obtain ⟨s, hs, h⟩ := hM
  refine ⟨η '' s, hs.image _, ?_⟩
  intro N m hm hsm
  let mR := (ModuleCat.restrictScalars f).map m
  have : Mono mR := inferInstance
  have hi : IsIso (pullback.snd mR η) := h _ inferInstance fun x hx ↦ by
    obtain ⟨n, hn⟩ := hsm ⟨x, hx, rfl⟩
    exact ⟨Concrete.pullbackMk mR η n x hn, Concrete.pullbackMk_snd mR η n x hn⟩
  let ℓ := inv (pullback.snd mR η) ≫ pullback.fst mR η
  have hℓ : ℓ ≫ mR = η := by
    dsimp only [ℓ]
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  let k := (adj.homEquiv M N).symm ℓ
  have hk : k ≫ m = 𝟙 (E.obj M) := by
    apply (adj.homEquiv M (E.obj M)).injective
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    simpa [Adjunction.homEquiv_unit] using! hℓ
  have : IsSplitEpi m := ⟨⟨⟨k, hk⟩⟩⟩
  exact isIso_of_mono_of_epi m

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem scalarLisse (f : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsFiniteLocallyConstantSheaf F) :
    IsFiniteLocallyConstantSheaf
      ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F) := by
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} f
  let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  refine { toIsLocallyConstantSheaf := ?_, toIsFiniteSheaf := ?_ }
  · obtain ⟨⟨𝒰, h𝒰⟩⟩ := hF.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
    refine ⟨⟨⟨𝒰, fun i ↦ ?_⟩⟩⟩
    have := h𝒰 i
    obtain ⟨M, ⟨e⟩⟩ := (F.over (𝒰.etalePrecoverageToEtale i)).mem_essImage_of_isConstant
    exact Sheaf.isConstant_of_iso _
      (scalarOverIso f F _ ≪≫
        (Sheaf.ringExtendScalars.{u + 1, u + 1} _ f).mapIso e.symm ≪≫
        scalarConstantIso _ f M)
  · constructor
    intro Ω _ _ y
    let p := (pointSmallEtale y).ulift.{u + 1}
    have hM := (hF.isFinitelyGenerated_sheafFiber Ω y).of_iso
      (((pointSmallEtale y).uliftSheafFiberIso.{u + 1}
        (ModuleCat.{u + 1} R)).app F).symm
    exact (scalarFinite f _ hM).of_iso
      ((p.presheafFiberCompIso E).symm.app F.obj ≪≫
        (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)).symm.app (F.obj ⋙ E) ≪≫
        ((pointSmallEtale y).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} S)).app _)

end ScalarLissity

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarSheafAdj {R A : Type (u + 1)} [Ring R] [Ring A]
    (f : R →+* A) :
    Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f ⊣
      sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} f) :=
  Sheaf.adjunction _ (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f)

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarSheafUnit {R A : Type (u + 1)} [Ring R] [Ring A]
    (f : R →+* A) (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  (lisseCoherence_scalarSheafAdj Y f).unit.app M

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarSheafUnit_apply {R A : Type (u + 1)} [Ring R] [Ring A]
    (f : R →+* A) (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (x : M.obj.obj (op U)) :
    (lisseCoherence_scalarSheafUnit Y f M).hom.app (op U) x =
      ((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} A)).app
        (M.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).app (op U)
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ 1 x) := by
  simp only [lisseCoherence_scalarSheafUnit, lisseCoherence_scalarSheafAdj,
    Sheaf.adjunction_unit_app_hom, NatTrans.comp_app, ModuleCat.comp_apply,
    ModuleCat.ringExtensionTmul, one_smul]
  rfl

private def scalarChangeUnit {R A B : Type (u + 1)}
    [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) (q : A →+* B) (hq : q.comp f = g)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (v : M ⟶ N) :
    M ⟶ (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} f)).obj
      ((sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology g).obj N)) :=
  ⟨{ app U := ModuleCat.ofHom (X := M.obj.obj U)
      (Y := (ModuleCat.restrictScalars.{u + 1} f).obj
        ((ModuleCat.restrictScalars.{u + 1} q).obj
          (((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology g).obj N).obj.obj U)))
      { toFun := fun x ↦ (lisseCoherence_scalarSheafUnit Y g N).hom.app U (v.hom.app U x)
        map_add' := by intros; simp only [map_add]
        map_smul' := by
          intro r x
          change (lisseCoherence_scalarSheafUnit Y g N).hom.app U (v.hom.app U (r • x)) =
            q (f r) • (show
              ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology g).obj N).obj.obj U
              from (lisseCoherence_scalarSheafUnit Y g N).hom.app U (v.hom.app U x))
          rw [(v.hom.app U).hom.map_smul]
          have hr : q (f r) = g r := congrArg (fun k : R →+* B ↦ k r) hq
          rw [hr]
          exact ((lisseCoherence_scalarSheafUnit Y g N).hom.app U).hom.map_smul r _ }
     naturality U V k := by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro x
       have hv := congrArg (fun h ↦ h x)
         (congrArg ModuleCat.Hom.hom (v.hom.naturality k))
       have hu := congrArg (fun h ↦ h (v.hom.app U x))
         (congrArg ModuleCat.Hom.hom ((lisseCoherence_scalarSheafUnit Y g N).hom.naturality k))
       simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hv hu
       exact (congrArg (fun z ↦ (lisseCoherence_scalarSheafUnit Y g N).hom.app V z) hv).trans hu }⟩

private def scalarChangeMap {R A B : Type (u + 1)}
    [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) (q : A →+* B) (hq : q.comp f = g)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (v : M ⟶ N) :
    (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj M ⟶
      (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology g).obj N) :=
  ((lisseCoherence_scalarSheafAdj Y f).homEquiv _ _).symm (scalarChangeUnit Y f g q hq M N v)

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem scalarChangeMap_unit {R A B : Type (u + 1)}
    [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) (q : A →+* B) (hq : q.comp f = g)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (v : M ⟶ N)
    (U : Y.Etale) (x : M.obj.obj (op U)) :
    (scalarChangeMap Y f g q hq M N v).hom.app (op U)
      ((lisseCoherence_scalarSheafUnit Y f M).hom.app (op U) x) =
        (lisseCoherence_scalarSheafUnit Y g N).hom.app (op U) (v.hom.app (op U) x) := by
  have h := ((lisseCoherence_scalarSheafAdj Y f).homEquiv _ _).apply_symm_apply
    (scalarChangeUnit Y f g q hq M N v)
  rw [Adjunction.homEquiv_apply] at h
  exact congrArg (fun k ↦ k.hom.app (op U) x) h

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem scalarChangeMap_tmul {R A B : Type (u + 1)}
    [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B) (q : A →+* B) (hq : q.comp f = g)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (v : M ⟶ N)
    (U : Y.Etale) (a : A) (x : M.obj.obj (op U)) :
    (scalarChangeMap Y f g q hq M N v).hom.app (op U)
      (((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} A)).app
        (M.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).app (op U)
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} f _ a x)) =
      ((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} B)).app
        (N.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} g)).app (op U)
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} g _ (q a) (v.hom.app (op U) x)) := by
  have h := scalarChangeMap_unit Y f g q hq M N v U x
  rw [lisseCoherence_scalarSheafUnit_apply, lisseCoherence_scalarSheafUnit_apply] at h
  simp only [ModuleCat.ringExtensionTmul, map_smul, one_smul] at h ⊢
  let T := ((Sheaf.ringExtendScalars.{u + 1, u + 1}
    Y.smallEtaleTopology g).obj N).obj.obj (op U)
  change q a • (show T from _) = q a • (show T from _)
  exact congrArg (fun z : T ↦ q a • z) h

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_quotientScalarLevel {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal S)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  (sheafCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk I))).obj
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology
      ((Ideal.Quotient.mk I).comp f)).obj M)

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_quotientScalarGenerator {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal S)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (a : S ⧸ I) (x : M.obj.obj (op U)) :
    (lisseCoherence_quotientScalarLevel Y f I M).obj.obj (op U) :=
  ((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} (S ⧸ I))).app
    (M.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1}
      ((Ideal.Quotient.mk I).comp f))).app (op U)
      (ModuleCat.ringExtensionTmul.{u + 1, u + 1} _ _ a x)

private def quotientScalarMap {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) (I J : Ideal S) (h : J ≤ I)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (v : M ⟶ N) :
    lisseCoherence_quotientScalarLevel Y f J M ⟶ lisseCoherence_quotientScalarLevel Y f I N := by
  let q := Ideal.Quotient.factor h
  have hq : q.comp ((Ideal.Quotient.mk J).comp f) =
      (Ideal.Quotient.mk I).comp f := by ext; rfl
  let k := scalarChangeMap Y _ _ q hq M N v
  exact ⟨{
    app U := ModuleCat.ofHom (X := (lisseCoherence_quotientScalarLevel Y f J M).obj.obj U)
      (Y := (lisseCoherence_quotientScalarLevel Y f I N).obj.obj U)
      { toFun := k.hom.app U
        map_add' := (k.hom.app U).hom.map_add
        map_smul' := fun s x ↦ (k.hom.app U).hom.map_smul (Ideal.Quotient.mk J s) x }
    naturality U V w := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact congrArg (fun k ↦ k x) (congrArg ModuleCat.Hom.hom (k.hom.naturality w)) }⟩

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientScalarMap_apply {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (f : R →+* S) (I J : Ideal S) (h : J ≤ I)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (v : M ⟶ N)
    (U : Y.Etale) (x : (lisseCoherence_quotientScalarLevel Y f J M).obj.obj (op U)) :
    (quotientScalarMap Y f I J h M N v).hom.app (op U) x =
      (scalarChangeMap Y ((Ideal.Quotient.mk J).comp f)
        ((Ideal.Quotient.mk I).comp f) (Ideal.Quotient.factor h)
        (by ext; rfl) M N v).hom.app (op U) x := rfl

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientScalarMap_generator {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (f : R →+* S) (I J : Ideal S) (h : J ≤ I)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (v : M ⟶ N)
    (U : Y.Etale) (a : S ⧸ J) (x : M.obj.obj (op U)) :
    (quotientScalarMap Y f I J h M N v).hom.app (op U)
      (lisseCoherence_quotientScalarGenerator Y f J M U a x) =
        lisseCoherence_quotientScalarGenerator Y f I N U (Ideal.Quotient.factor h a)
          (v.hom.app (op U) x) := by
  rw [quotientScalarMap_apply]
  exact scalarChangeMap_tmul Y ((Ideal.Quotient.mk J).comp f)
    ((Ideal.Quotient.mk I).comp f) (Ideal.Quotient.factor h) (by ext; rfl) M N v U a x

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientScalar_hom_ext {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (f : R →+* S) (I J : Ideal S) (hJI : J ≤ I)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (v w : lisseCoherence_quotientScalarLevel Y f J M ⟶ lisseCoherence_quotientScalarLevel Y f I N)
    (h : ∀ (U : Y.Etale) (x : M.obj.obj (op U)),
      v.hom.app (op U) (lisseCoherence_quotientScalarGenerator Y f J M U 1 x) =
        w.hom.app (op U) (lisseCoherence_quotientScalarGenerator Y f J M U 1 x)) : v = w := by
  let P := (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology
    ((Ideal.Quotient.mk J).comp f)).obj M
  let Q := (sheafCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.factor hJI))).obj
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology
      ((Ideal.Quotient.mk I).comp f)).obj N)
  let v' := lisseCoherence_quotientRestrictedSheafHom Y (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective P Q v
  let w' := lisseCoherence_quotientRestrictedSheafHom Y (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective P Q w
  have he : v' = w' := by
    apply ((lisseCoherence_scalarSheafAdj Y ((Ideal.Quotient.mk J).comp f)).homEquiv M Q).injective
    simp only [Adjunction.homEquiv_apply]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change v.hom.app U ((lisseCoherence_scalarSheafUnit Y _ M).hom.app U x) =
      w.hom.app U ((lisseCoherence_scalarSheafUnit Y _ M).hom.app U x)
    rw [lisseCoherence_scalarSheafUnit_apply]
    exact h U.unop x
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun k ↦ k.hom.app U x) he

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientScalarGenerator_add {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal S)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (a : S ⧸ I) (x y : M.obj.obj (op U)) :
    lisseCoherence_quotientScalarGenerator Y f I M U a (x + y) =
      lisseCoherence_quotientScalarGenerator Y f I M U a x +
        lisseCoherence_quotientScalarGenerator Y f I M U a y := by
  simp only [lisseCoherence_quotientScalarGenerator, ModuleCat.ringExtensionTmul, map_add, smul_add]

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientScalarGenerator_smul {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal S)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (a : S ⧸ I) (r : R) (x : M.obj.obj (op U)) :
    lisseCoherence_quotientScalarGenerator Y f I M U a (r • x) =
      f r • lisseCoherence_quotientScalarGenerator Y f I M U a x := by
  let k := (Ideal.Quotient.mk I).comp f
  let M₀ := M.obj.obj (op U)
  let η := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} k).unit.app M₀
  let t := ((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} (S ⧸ I))).app
    (M.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} k)).app (op U)
  change t (a • (show (ModuleCat.ringExtendScalars.{u + 1, u + 1} k).obj M₀ from
      η (r • x))) = k r • t (a • (show
        (ModuleCat.ringExtendScalars.{u + 1, u + 1} k).obj M₀ from η x))
  have h : (show (ModuleCat.ringExtendScalars.{u + 1, u + 1} k).obj M₀ from
      η (r • x)) = k r • (show
        (ModuleCat.ringExtendScalars.{u + 1, u + 1} k).obj M₀ from η x) :=
    η.hom.map_smul r x
  rw [h, smul_comm a (k r), map_smul]

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientScalarMap_id {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal S)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    quotientScalarMap Y f I I le_rfl M M (𝟙 M) = 𝟙 _ := by
  apply quotientScalar_hom_ext Y f I I le_rfl M M
  intro U x
  rw [quotientScalarMap_generator, map_one]
  rfl

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientScalarMap_comp {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (f : R →+* S) (I J K : Ideal S) (hJI : J ≤ I) (hKJ : K ≤ J)
    (M N P : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (v : M ⟶ N) (w : N ⟶ P) :
    quotientScalarMap Y f J K hKJ M N v ≫ quotientScalarMap Y f I J hJI N P w =
      quotientScalarMap Y f I K (hKJ.trans hJI) M P (v ≫ w) := by
  apply quotientScalar_hom_ext Y f I K (hKJ.trans hJI) M P
  intro U x
  change (quotientScalarMap Y f I J hJI N P w).hom.app (op U)
    ((quotientScalarMap Y f J K hKJ M N v).hom.app (op U)
      (lisseCoherence_quotientScalarGenerator Y f K M U 1 x)) = _
  rw [quotientScalarMap_generator, map_one,
    quotientScalarMap_generator, quotientScalarMap_generator, map_one, map_one]
  rfl

private def integralScalarRaw (F : LisseIntegralSheaf l E Y) :
    AdicIntegralDiagram l L Y :=
  Functor.ofOpSequence (X := fun m ↦ lisseIntegralScalarLevel l E Y L ι F m)
    (fun m ↦ quotientScalarMap Y (lisseIntegerInclusion l E L ι)
    (Padic.coefficientExtensionIdeal l L (m + 1))
    (Padic.coefficientExtensionIdeal l L (m + 2))
    (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))
    (F.obj.obj (op (lisseScalarSourceIndex l E L ι (m + 1))))
    (F.obj.obj (op (lisseScalarSourceIndex l E L ι m)))
    (F.obj.map (homOfLE (lisseScalarSourceIndex_le l E L ι m)).op))

private def integralScalarRawMap {F G : LisseIntegralSheaf l E Y} (v : F ⟶ G) :
    integralScalarRaw l E Y L ι F ⟶ integralScalarRaw l E Y L ι G :=
  NatTrans.ofOpSequence (fun m ↦ quotientScalarMap Y (lisseIntegerInclusion l E L ι)
    (Padic.coefficientExtensionIdeal l L (m + 1))
    (Padic.coefficientExtensionIdeal l L (m + 1)) le_rfl _ _
    (v.hom.app (op (lisseScalarSourceIndex l E L ι m)))) (by
      intro m
      simp only [integralScalarRaw, Functor.ofOpSequence_map_homOfLE_succ]
      rw [quotientScalarMap_comp, quotientScalarMap_comp]
      congr 1
      exact v.hom.naturality _)

private def integralScalarRawFunctor :
    LisseIntegralSheaf l E Y ⥤ AdicIntegralDiagram l L Y where
  obj := integralScalarRaw l E Y L ι
  map := integralScalarRawMap l E Y L ι
  map_id F := by
    apply NatTrans.ext
    funext m
    exact quotientScalarMap_id Y _ _ _
  map_comp v w := by
    apply NatTrans.ext
    funext m
    exact (quotientScalarMap_comp Y _ _ _ _ le_rfl le_rfl _ _ _ _ _).symm

private theorem integralScalarRaw_lisse (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    IsFiniteLocallyConstantSheaf ((integralScalarRaw l E Y L ι F).obj (op m)) := by
  have h := scalarLisse (Y := Y) (lisseScalarCoefficientMap l E L ι m)
    (F.obj.obj (op (lisseScalarSourceIndex l E L ι m)))
    (F.property.1 (lisseScalarSourceIndex l E L ι m))
  exact IsFiniteLocallyConstantSheaf.restrictScalars _ _

private theorem integralScalarRaw_annihilated (F : LisseIntegralSheaf l E Y)
    (m : ℕ) (U : Y.Etale) :
    Padic.coefficientExtensionIdeal l L (m + 1) •
      (⊤ : Submodule (Padic.coefficientExtensionIntegers l L)
        (((integralScalarRaw l E Y L ι F).obj (op m)).obj.obj (op U))) = ⊥ := by
  apply bot_unique
  apply Submodule.smul_le.mpr
  intro a ha x _
  change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (m + 1)) a •
    (show ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology
      (lisseScalarCoefficientMap l E L ι m)).obj
        (F.obj.obj (op (lisseScalarSourceIndex l E L ι m)))).obj.obj (op U) from x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_smul]

/-- The coefficient index and ideal identities used by tensor comparison. -/
lemma lisseCoherence_uniformizerIdeal_eq (B : Type (u + 1)) [Field B]
    [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B] :
    Ideal.span ({Padic.coefficientExtensionUniformizer l B} :
      Set (Padic.coefficientExtensionIntegers l B)) =
        Padic.coefficientExtensionMaximalIdeal l B :=
  (Padic.coefficientExtensionIntegers_dvr l B).choose_spec
      |>.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec

/-- The coefficient index and ideal identities used by tensor comparison. -/
lemma lisseCoherence_scalarIndex_eq (n : ℕ) :
    lisseScalarSourceIndex l E L ι n = n / lisseRamificationIndex l E L ι := by
  have he : 0 < lisseRamificationIndex l E L ι :=
    (lisseRamificationIndex_exists l E L ι).choose_spec.1
  dsimp only [lisseScalarSourceIndex]
  have hn : n + 1 + lisseRamificationIndex l E L ι - 1 =
      n + lisseRamificationIndex l E L ι := by omega
  rw [hn, Nat.add_div_right _ he]
  exact Nat.add_sub_cancel _ 1

/-- The coefficient index and ideal identities used by tensor comparison. -/
lemma lisseCoherence_scalarIndex_ideal (n : ℕ) :
    Ideal.map (lisseIntegerInclusion l E L ι)
        (Padic.coefficientExtensionIdeal l E (lisseScalarSourceIndex l E L ι n + 1)) ≤
      Padic.coefficientExtensionIdeal l L (n + 1) := by
  have he : 0 < lisseRamificationIndex l E L ι :=
    (lisseRamificationIndex_exists l E L ι).choose_spec.1
  have hr : Ideal.map (lisseIntegerInclusion l E L ι)
      (Padic.coefficientExtensionMaximalIdeal l E) =
        Padic.coefficientExtensionMaximalIdeal l L ^ lisseRamificationIndex l E L ι :=
    (lisseRamificationIndex_exists l E L ι).choose_spec.2
  dsimp only [Padic.coefficientExtensionIdeal]
  rw [Ideal.map_pow, lisseCoherence_uniformizerIdeal_eq l E, hr, ←
    lisseCoherence_uniformizerIdeal_eq l L,
    ← pow_mul]
  apply Ideal.pow_le_pow_right
  rw [lisseCoherence_scalarIndex_eq l E L ι n]
  exact Nat.lt_mul_div_succ n he

section SourceStalks

attribute [local semireducible] GrothendieckTopology.Point.sheafFiber

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)

private lemma integralStalk_annihilated (F : LisseIntegralSheaf l E Y) (n : ℕ) :
    let R := Padic.coefficientExtensionIntegers l E
    let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
    I ^ (n + 1) • (⊤ : Submodule R
      ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R) |>.obj
        (F.obj.obj (op n)))) = ⊥ := by
  let p := (pointSmallEtale y).ulift.{u + 1}
  apply le_antisymm ?_ bot_le
  apply Submodule.smul_le.mpr
  intro r hr z _
  obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective
    (P := (F.obj.obj (op n)).obj) z
  have hz : r • s = 0 := by
    have h := Submodule.smul_mem_smul hr (Submodule.mem_top (x := s))
    rw [F.property.2.1 n U] at h
    exact h
  change r • p.toPresheafFiber U x (F.obj.obj (op n)).obj s = 0
  rw [← map_smul, hz, map_zero]

private theorem integralStalk_transition (F : LisseIntegralSheaf l E Y)
    (m n : ℕ) (h : m ≤ n) :
    let R := Padic.coefficientExtensionIntegers l E
    let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
    let T := (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)
    let v := (T.map (F.obj.map (homOfLE h).op)).hom
    Function.Surjective v ∧ LinearMap.ker v =
      I ^ (m + 1) • (⊤ : Submodule R (T.obj (F.obj.obj (op n)))) := by
  let R := Padic.coefficientExtensionIntegers l E
  let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
  let T := (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)
  dsimp only
  induction n, h using Nat.le_induction with
  | base =>
    have he : (homOfLE (le_refl m)).op = 𝟙 (op m) := Subsingleton.elim _ _
    rw [he, F.obj.map_id, T.map_id]
    constructor
    · exact Function.surjective_id
    · exact LinearMap.ker_id.trans
        (integralStalk_annihilated (l := l) (E := E) (Y := Y) (y := y) F m).symm
  | succ n h ih =>
    let a := (T.map (F.obj.map (homOfLE (Nat.le_succ n)).op)).hom
    let b := (T.map (F.obj.map (homOfLE h).op)).hom
    have hab : (T.map (F.obj.map (homOfLE (h.trans (Nat.le_succ n))).op)).hom =
        b.comp a := by
      have he : (homOfLE (h.trans (Nat.le_succ n))).op =
          (homOfLE (Nat.le_succ n)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
      rw [he, F.obj.map_comp, T.map_comp]
      rfl
    rw [hab]
    have ha := F.property.2.2 Ω y n
    refine ⟨ih.1.comp ha.1, ?_⟩
    rw [LinearMap.ker_comp, ih.2,
      Submodule.comap_smul_top_of_surjective _ _ ha.1, ha.2]
    exact sup_eq_left.mpr
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.succ_le_succ h)))

end SourceStalks

section ScalarStalks

set_option backward.isDefEq.respectTransparency false

attribute [local semireducible] GrothendieckTopology.Point.sheafFiber

variable {R S : Type (u + 1)} [CommRing R] [CommRing S]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)

private def scalarStalkIso {A : Type (u + 1)} [CommRing A] (r : R →+* A)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} r).obj
        ((pointSmallEtale y).ulift.{u + 1}.sheafFiber.obj M) ≅
      (pointSmallEtale y).ulift.{u + 1}.sheafFiber.obj
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology r).obj M) :=
  let p := (pointSmallEtale y).ulift.{u + 1}
  let H := ModuleCat.ringExtendScalars.{u + 1, u + 1} r
  let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r).isLeftAdjoint
  ((p.presheafFiberCompIso H).app M.obj).symm ≪≫
    ((p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} A)).app (M.obj ⋙ H)).symm

private def quotientScalarStalkIso (f : R →+* S) (I : Ideal S)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    letI := f.toAlgebra
    (S ⧸ I) ⊗[R] ((pointSmallEtale y).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} R) |>.obj M) ≃ₗ[S]
      ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} S) |>.obj
        (lisseCoherence_quotientScalarLevel Y f I M)) := by
  let p := (pointSmallEtale y).ulift.{u + 1}
  let q := Ideal.Quotient.mk I
  let r := q.comp f
  let H := ModuleCat.ringExtendScalars.{u + 1, u + 1} r
  let A := (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology r).obj M
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r
  let adj' := ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r
  let c := ((adj.leftAdjointUniq adj').app (p.sheafFiber.obj M)).symm ≪≫
    scalarStalkIso Y y r M
  let e := (ModuleCat.restrictScalars.{u + 1} q).mapIso c ≪≫
    ((p.sheafFiberCompIso (ModuleCat.restrictScalars.{u + 1} q)).app A).symm
  exact e.toLinearEquiv

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientScalarStalkIso_unit (f : R →+* S) (I : Ideal S)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (x : (pointSmallEtale y).ulift.{u + 1}.fiber.obj U)
    (s : M.obj.obj (op U)) :
    letI := f.toAlgebra
    quotientScalarStalkIso Y y f I M
      (1 ⊗ₜ[R] (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U x M.obj s) =
        (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U x
          (lisseCoherence_quotientScalarLevel Y f I M).obj (lisseCoherence_quotientScalarGenerator
            Y f I M U 1 s) := by
  let p := (pointSmallEtale y).ulift.{u + 1}
  let q := Ideal.Quotient.mk I
  let r := q.comp f
  let H := ModuleCat.ringExtendScalars.{u + 1, u + 1} r
  let A := (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology r).obj M
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} r
  let adj' := ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} r
  let e := (adj.leftAdjointUniq adj').app (p.sheafFiber.obj M)
  let z := p.toPresheafFiber U x M.obj s
  have he : e.hom (adj.unit.app _ z) = ((1 : S ⧸ I) ⊗ₜ[R,r] z) :=
    congrArg (fun k ↦ k z) (adj.unit_leftAdjointUniq_hom_app adj' _)
  have he' : e.inv ((1 : S ⧸ I) ⊗ₜ[R,r] z) = adj.unit.app _ z := by
    rw [← he]
    exact ConcreteCategory.congr_hom e.hom_inv_id _
  have hc := congrArg (fun k ↦ k s)
    ((etale_stalk_scalar_component_unique y r H adj M).2.1 U x)
  let t := ((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} (S ⧸ I))).app
    (M.obj ⋙ H)).app (op U)
  change (scalarStalkIso Y y r M).hom (adj.unit.app _ z) =
    p.toPresheafFiber U x A.obj (t (adj.unit.app _ s)) at hc
  have hp := congrArg (fun k ↦ k (t (adj.unit.app _ s)))
    (p.toPresheafFiber_presheafFiberCompIso_hom_app
      (ModuleCat.restrictScalars.{u + 1} q) U x A.obj)
  change ((p.sheafFiberCompIso (ModuleCat.restrictScalars.{u + 1} q)).app A).hom
      (p.toPresheafFiber U x (lisseCoherence_quotientScalarLevel Y f I M).obj
        (t (adj.unit.app _ s))) = p.toPresheafFiber U x A.obj (t (adj.unit.app _ s)) at hp
  change ((p.sheafFiberCompIso (ModuleCat.restrictScalars.{u + 1} q)).app A).inv
    ((scalarStalkIso Y y r M).hom (e.inv ((1 : S ⧸ I) ⊗ₜ[R,r] z))) = _
  erw [he', hc, ← hp]
  simpa only [lisseCoherence_quotientScalarGenerator, ModuleCat.ringExtensionTmul, one_smul,
    ModuleCat.comp_apply, ModuleCat.id_apply] using!
    ConcreteCategory.congr_hom
      (((p.sheafFiberCompIso (ModuleCat.restrictScalars.{u + 1} q)).app A).hom_inv_id)
      (p.toPresheafFiber U x (lisseCoherence_quotientScalarLevel Y f I M).obj
        (t (adj.unit.app _ s)))

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientScalarStalkIso_natural (f : R →+* S)
    (I J : Ideal S) (hJI : J ≤ I)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (v : M ⟶ N) :
    letI := f.toAlgebra
    let p := (pointSmallEtale y).ulift.{u + 1}
    let vR := (p.sheafFiber.map v).hom
    let vS := (p.sheafFiber.map (quotientScalarMap Y f I J hJI M N v)).hom
    vS.comp (quotientScalarStalkIso Y y f J M).toLinearMap =
      (quotientScalarStalkIso Y y f I N).toLinearMap.comp
        (TensorProduct.AlgebraTensorModule.map
          (Ideal.Quotient.factorₐ S hJI).toLinearMap vR) := by
  let : Algebra R S := f.toAlgebra
  let p := (pointSmallEtale y).ulift.{u + 1}
  let eJ := quotientScalarStalkIso Y y f J M
  let eI := quotientScalarStalkIso Y y f I N
  let vS := p.sheafFiber.map (quotientScalarMap Y f I J hJI M N v)
  let vR := p.sheafFiber.map v
  have ht (a : S ⧸ J) (z : p.sheafFiber (A := ModuleCat.{u + 1} R) |>.obj M) :
      vS (eJ (a ⊗ₜ[R] z)) = eI ((Ideal.Quotient.factor hJI a) ⊗ₜ[R] (vR z)) := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hJ : (Ideal.Quotient.mk J b) ⊗ₜ[R] z = b • ((1 : S ⧸ J) ⊗ₜ[R] z) := by
      rw [TensorProduct.smul_tmul']
      change Ideal.Quotient.mk J b ⊗ₜ[R] z =
        (Ideal.Quotient.mk J b * 1) ⊗ₜ[R] z
      rw [mul_one]
    have hI : (Ideal.Quotient.mk I b) ⊗ₜ[R] (vR z) =
        b • ((1 : S ⧸ I) ⊗ₜ[R] (vR z)) := by
      rw [TensorProduct.smul_tmul']
      change Ideal.Quotient.mk I b ⊗ₜ[R] (vR z) =
        (Ideal.Quotient.mk I b * 1) ⊗ₜ[R] (vR z)
      rw [mul_one]
    change vS (eJ ((Ideal.Quotient.mk J b) ⊗ₜ[R] z)) =
      eI ((Ideal.Quotient.mk I b) ⊗ₜ[R] (vR z))
    rw [hJ, hI, map_smul, map_smul, map_smul]
    congr 1
    obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := M.obj) z
    have hv := congrArg (fun k ↦ k s)
      (p.toPresheafFiber_naturality v.hom U x)
    have hs := congrArg (fun k ↦ k (lisseCoherence_quotientScalarGenerator Y f J M U 1 s))
      (p.toPresheafFiber_naturality (quotientScalarMap Y f I J hJI M N v).hom U x)
    change vR (p.toPresheafFiber U x M.obj s) =
      p.toPresheafFiber U x N.obj (v.hom.app (op U) s) at hv
    change vS (p.toPresheafFiber U x (lisseCoherence_quotientScalarLevel Y f J M).obj
        (lisseCoherence_quotientScalarGenerator Y f J M U 1 s)) =
      p.toPresheafFiber U x (lisseCoherence_quotientScalarLevel Y f I N).obj
        ((quotientScalarMap Y f I J hJI M N v).hom.app (op U)
          (lisseCoherence_quotientScalarGenerator Y f J M U 1 s)) at hs
    rw [hv]
    rw [quotientScalarStalkIso_unit, quotientScalarStalkIso_unit, hs,
      quotientScalarMap_generator, map_one]
  apply LinearMap.ext
  intro z
  change vS (eJ z) = eI (TensorProduct.AlgebraTensorModule.map
    (Ideal.Quotient.factorₐ S hJI).toLinearMap vR.hom z)
  induction z using TensorProduct.inductionOn with
  | tmul a z => exact ht a z
  | add z w hz hw => simp only [map_add, hz, hw]

omit [IsNoetherian Y] [Y.IsSeparated] in
private theorem quotientScalar_stalk_kernel (f : R →+* S)
    (I J : Ideal S) (hJI : J ≤ I) (K : Ideal R)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (v : M ⟶ N)
    (hv : Function.Surjective ((pointSmallEtale y).ulift.{u + 1}.sheafFiber.map v).hom)
    (hk : LinearMap.ker ((pointSmallEtale y).ulift.{u + 1}.sheafFiber.map v).hom = K • ⊤)
    (hKI : K.map f ≤ I) :
    let p := (pointSmallEtale y).ulift.{u + 1}
    let vS := (p.sheafFiber.map (quotientScalarMap Y f I J hJI M N v)).hom
    Function.Surjective vS ∧ LinearMap.ker vS = I • ⊤ := by
  let : Algebra R S := f.toAlgebra
  let p := (pointSmallEtale y).ulift.{u + 1}
  let eJ := quotientScalarStalkIso Y y f J M
  let eI := quotientScalarStalkIso Y y f I N
  let vR := (p.sheafFiber.map v).hom
  let vS := (p.sheafFiber.map (quotientScalarMap Y f I J hJI M N v)).hom
  let t := TensorProduct.AlgebraTensorModule.map
    (Ideal.Quotient.factorₐ S hJI).toLinearMap vR
  have ht := quotientTensor_kernel I J hJI K vR hv hk hKI
  have hc (z) : vS (eJ z) = eI (t z) :=
    LinearMap.congr_fun (quotientScalarStalkIso_natural Y y f I J hJI M N v) z
  refine ⟨?_, ?_⟩
  · intro w
    obtain ⟨z, hz⟩ := ht.1 (eI.symm w)
    refine ⟨eJ z, ?_⟩
    rw [hc, hz, eI.apply_symm_apply]
  · ext w
    obtain ⟨z, rfl⟩ := eJ.surjective w
    change vS (eJ z) = 0 ↔ eJ z ∈ I • ⊤
    rw [hc, ← eI.map_zero, eI.injective.eq_iff]
    have hi : (I • (⊤ : Submodule S ((p.sheafFiber (A := ModuleCat.{u + 1} S)).obj
        (lisseCoherence_quotientScalarLevel Y f J M)))).comap eJ.toLinearMap = I • ⊤ := by
      rw [Submodule.comap_smul'' eJ.injective (by rw [eJ.range]), Submodule.comap_top]
    have ht' : t z = 0 ↔ z ∈ I • (⊤ : Submodule S
        ((S ⧸ J) ⊗[R] ((p.sheafFiber (A := ModuleCat.{u + 1} R)).obj M))) := by
      change z ∈ LinearMap.ker t ↔ _
      rw [ht.2]
    exact ht'.trans (SetLike.ext_iff.mp hi z).symm

end ScalarStalks

private theorem integralScalarRaw_isLisse (F : LisseIntegralSheaf l E Y) :
    IsLisseIntegralDiagram l L Y (integralScalarRaw l E Y L ι F) := by
  refine ⟨integralScalarRaw_lisse l E Y L ι F,
    integralScalarRaw_annihilated l E Y L ι F, ?_⟩
  intro Ω _ _ y m
  let S := Padic.coefficientExtensionIntegers l L
  let I := Padic.coefficientExtensionIdeal l L (m + 1)
  let J := Padic.coefficientExtensionIdeal l L (m + 2)
  let K := Padic.coefficientExtensionIdeal l E (lisseScalarSourceIndex l E L ι m + 1)
  let M := F.obj.obj (op (lisseScalarSourceIndex l E L ι (m + 1)))
  let N := F.obj.obj (op (lisseScalarSourceIndex l E L ι m))
  let v := F.obj.map (homOfLE (lisseScalarSourceIndex_le l E L ι m)).op
  have hv := integralStalk_transition (l := l) (E := E) (Y := Y) (y := y) F
    (lisseScalarSourceIndex l E L ι m) (lisseScalarSourceIndex l E L ι (m + 1))
    (lisseScalarSourceIndex_le l E L ι m)
  have ht := quotientScalar_stalk_kernel Y y (lisseIntegerInclusion l E L ι)
    I J (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))) K M N v hv.1 hv.2
    (lisseCoherence_scalarIndex_ideal l E L ι m)
  simpa only [integralScalarRaw, Functor.ofOpSequence_map_homOfLE_succ,
    I, J, K, M, N, v, Padic.coefficientExtensionIdeal] using! ht

/-- The prescribed scalar extension exists. -/
theorem lisseIntegralScalarExtension_exists :
    Nonempty (LisseIntegralScalarExtensionData l E Y L ι) := by
  let H := integralScalarRawFunctor l E Y L ι
  let S : LisseIntegralSheaf l E Y ⥤ LisseIntegralSheaf l L Y :=
    { obj F := ⟨H.obj F, integralScalarRaw_isLisse l E Y L ι F⟩
      map v := ⟨H.map v⟩
      map_id F := by apply ObjectProperty.hom_ext; exact H.map_id F
      map_comp v w := by apply ObjectProperty.hom_ext; exact H.map_comp v w }
  refine ⟨{ functor := S
            levelIso F m := Iso.refl _
            transition := ?_
            map := ?_ }⟩
  · intro F m U a s
    change ((integralScalarRaw l E Y L ι F).map
      (homOfLE (Nat.le_succ m)).op).hom.app (op U)
      (lisseIntegralScalarGenerator l E Y L ι F (m + 1) U a s) = _
    simp only [integralScalarRaw, Functor.ofOpSequence_map_homOfLE_succ]
    exact quotientScalarMap_generator Y _ _ _ _ _ _ _ U a s
  · intro F G v m U a s
    change (quotientScalarMap Y (lisseIntegerInclusion l E L ι)
      (Padic.coefficientExtensionIdeal l L (m + 1))
      (Padic.coefficientExtensionIdeal l L (m + 1)) le_rfl _ _
      (v.hom.app (op (lisseScalarSourceIndex l E L ι m)))).hom.app (op U)
        (lisseIntegralScalarGenerator l E Y L ι F m U a s) = _
    have h := quotientScalarMap_generator Y (lisseIntegerInclusion l E L ι)
      (Padic.coefficientExtensionIdeal l L (m + 1))
      (Padic.coefficientExtensionIdeal l L (m + 1)) le_rfl _ _
      (v.hom.app (op (lisseScalarSourceIndex l E L ι m))) U a s
    have ha : Ideal.Quotient.factor
        (le_refl (Padic.coefficientExtensionIdeal l L (m + 1))) a = a :=
      congrArg (fun k ↦ k a) (quotientFactor_id (Padic.coefficientExtensionIdeal l L (m + 1)))
    simpa only [ha, lisseCoherence_quotientScalarGenerator, lisseIntegralScalarGenerator,
      lisseScalarCoefficientMap] using! h

/-- The integral coefficient extension functor, with precisely the finite-level formula. -/
@[irreducible]
def lisseIntegralScalarExtensionData : LisseIntegralScalarExtensionData l E Y L ι :=
  Classical.choice (lisseIntegralScalarExtension_exists l E Y L ι)

/-- Scalar extension `F ↦ F ⊗_{𝒪_E} 𝒪_L`. -/
@[irreducible]
def lisseIntegralScalarExtension : LisseIntegralSheaf l E Y ⥤ LisseIntegralSheaf l L Y :=
  (lisseIntegralScalarExtensionData l E Y L ι).functor

-- The record needs the named inherited structures, not their expanded implementations.
attribute [local irreducible] lisseIntegralPreadditive lisseIntegralLinear
  lisseIntegralHomAddCommGroup lisseIntegralHomModule
-- Avoid generating unused constructor-injectivity and size functions.
set_option genInjectivity false in
set_option genSizeOf false in
/-- The rational scalar-extension maps are additive and prescribed on pure tensors. -/
structure LisseRationalScalarExtensionData where
  /-- Extend every morphism's scalar coefficient and integral map. -/
  map (F G : LisseRationalSheaf l E Y) : lisseRationalHom l E Y F G →
    lisseRationalHom l L Y
      ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
      ⟨(lisseIntegralScalarExtension l E Y L ι).obj G.integral⟩
  /-- Additivity fixes the map on sums of pure tensors. -/
  map_add (F G : LisseRationalSheaf l E Y) (f g : lisseRationalHom l E Y F G) :
    map F G (f + g) = map F G f + map F G g
  /-- The defining pure tensor formula. -/
  map_tmul (F G : LisseRationalSheaf l E Y) (a : E) (f : F.integral ⟶ G.integral) :
    map F G (TensorProduct.tmul _ a f) =
      TensorProduct.tmul _ (ι a) ((lisseIntegralScalarExtension l E Y L ι).map f)
  /-- Identity preservation. -/
  map_id (F : LisseRationalSheaf l E Y) :
    map F F (TensorProduct.tmul _ 1 (𝟙 F.integral)) =
    TensorProduct.tmul _ 1 (𝟙 ((lisseIntegralScalarExtension l E Y L ι).obj F.integral))
  /-- Composition preservation. -/
  map_comp (F G H : LisseRationalSheaf l E Y)
      (f : lisseRationalHom l E Y F G) (g : lisseRationalHom l E Y G H) :
    map F H ((lisseRationalComposition l E Y).comp F G H f g) =
      (lisseRationalComposition l L Y).comp
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj G.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj H.integral⟩
        (map F G f) (map G H g)

attribute [local semireducible] lisseIntegralPreadditive lisseIntegralLinear
  lisseIntegralHomAddCommGroup lisseIntegralHomModule

set_option maxRecDepth 100 in
private theorem scalarLevel_hom_ext (F G : LisseIntegralSheaf l E Y) (m : ℕ)
    (f g : lisseIntegralScalarLevel l E Y L ι F m ⟶
      lisseIntegralScalarLevel l E Y L ι G m)
    (h : ∀ (U : Y.Etale) (a : Padic.coefficientExtensionRing l L (m + 1))
      (s : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)),
      f.hom.app (op U) (lisseIntegralScalarGenerator l E Y L ι F m U a s) =
        g.hom.app (op U) (lisseIntegralScalarGenerator l E Y L ι F m U a s)) : f = g := by
  exact quotientScalar_hom_ext Y (lisseIntegerInclusion l E L ι)
    (Padic.coefficientExtensionIdeal l L (m + 1))
    (Padic.coefficientExtensionIdeal l L (m + 1)) le_rfl
    (F.obj.obj (op (lisseScalarSourceIndex l E L ι m)))
    (G.obj.obj (op (lisseScalarSourceIndex l E L ι m))) f g
    (fun U x ↦ h U 1 x)

private theorem scalarFunctor_add (D : LisseIntegralScalarExtensionData l E Y L ι)
    {F G : LisseIntegralSheaf l E Y} (f g : F ⟶ G) :
    D.functor.map (f + g) = D.functor.map f + D.functor.map g := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext m
  apply (cancel_mono (D.levelIso G m.unop).hom).mp
  apply (cancel_epi (D.levelIso F m.unop).inv).mp
  apply scalarLevel_hom_ext l E Y L ι F G m.unop
  intro U a s
  change (D.levelIso G m.unop).hom.hom.app (op U)
    (((D.functor.map (f + g)).hom.app m).hom.app (op U)
      ((D.levelIso F m.unop).inv.hom.app (op U)
        (lisseIntegralScalarGenerator l E Y L ι F m.unop U a s))) =
    (D.levelIso G m.unop).hom.hom.app (op U)
      ((((D.functor.map f).hom.app m).hom.app (op U)
        ((D.levelIso F m.unop).inv.hom.app (op U)
          (lisseIntegralScalarGenerator l E Y L ι F m.unop U a s))) +
      (((D.functor.map g).hom.app m).hom.app (op U)
        ((D.levelIso F m.unop).inv.hom.app (op U)
          (lisseIntegralScalarGenerator l E Y L ι F m.unop U a s))))
  rw [map_add]
  rw [D.map, D.map, D.map]
  change lisseIntegralScalarGenerator l E Y L ι G m.unop U a
    (((f.hom.app (op (lisseScalarSourceIndex l E L ι m.unop))).hom.app (op U) s) +
      ((g.hom.app (op (lisseScalarSourceIndex l E L ι m.unop))).hom.app (op U) s)) = _
  exact quotientScalarGenerator_add Y (lisseIntegerInclusion l E L ι)
    (Padic.coefficientExtensionIdeal l L (m.unop + 1))
    (G.obj.obj (op (lisseScalarSourceIndex l E L ι m.unop))) U a _ _

private theorem scalarFunctor_smul (D : LisseIntegralScalarExtensionData l E Y L ι)
    {F G : LisseIntegralSheaf l E Y} (r : Padic.coefficientExtensionIntegers l E)
    (f : F ⟶ G) : D.functor.map (r • f) =
      lisseIntegerInclusion l E L ι r • D.functor.map f := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext m
  apply (cancel_mono (D.levelIso G m.unop).hom).mp
  apply (cancel_epi (D.levelIso F m.unop).inv).mp
  apply scalarLevel_hom_ext l E Y L ι F G m.unop
  intro U a s
  let z := lisseIntegralScalarGenerator l E Y L ι F m.unop U a s
  change (D.levelIso G m.unop).hom.hom.app (op U)
    (((D.functor.map (r • f)).hom.app m).hom.app (op U)
      ((D.levelIso F m.unop).inv.hom.app (op U) z)) =
    (D.levelIso G m.unop).hom.hom.app (op U)
      (lisseIntegerInclusion l E L ι r •
        (((D.functor.map f).hom.app m).hom.app (op U)
          ((D.levelIso F m.unop).inv.hom.app (op U) z)))
  rw [map_smul]
  dsimp only [z]
  rw [D.map, D.map]
  change lisseIntegralScalarGenerator l E Y L ι G m.unop U a
    (r • ((f.hom.app (op (lisseScalarSourceIndex l E L ι m.unop))).hom.app (op U) s)) = _
  exact quotientScalarGenerator_smul Y (lisseIntegerInclusion l E L ι)
    (Padic.coefficientExtensionIdeal l L (m.unop + 1))
    (G.obj.obj (op (lisseScalarSourceIndex l E L ι m.unop))) U a r _

private theorem scalarMap_add {F G : LisseIntegralSheaf l E Y} (f g : F ⟶ G) :
    (lisseIntegralScalarExtension l E Y L ι).map (f + g) =
      (lisseIntegralScalarExtension l E Y L ι).map f +
        (lisseIntegralScalarExtension l E Y L ι).map g := by
  delta lisseIntegralScalarExtension
  exact scalarFunctor_add l E Y L ι (lisseIntegralScalarExtensionData l E Y L ι) f g

private theorem scalarMap_smul {F G : LisseIntegralSheaf l E Y}
    (r : Padic.coefficientExtensionIntegers l E) (f : F ⟶ G) :
    (lisseIntegralScalarExtension l E Y L ι).map (r • f) =
      lisseIntegerInclusion l E L ι r • (lisseIntegralScalarExtension l E Y L ι).map f := by
  delta lisseIntegralScalarExtension
  exact scalarFunctor_smul l E Y L ι (lisseIntegralScalarExtensionData l E Y L ι) r f

-- Pure tensors determine the additive map uniquely by tensor induction.
attribute [local irreducible] lisseIntegralPreadditive lisseIntegralLinear
  lisseIntegralHomAddCommGroup lisseIntegralHomModule

private theorem tensorSemilinearMap_exists
    {R S M N P Q : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module S P] [Module S Q]
    (σ : R →+* S) (f : M →ₛₗ[σ] P) (g : N →ₛₗ[σ] Q) :
    ∃ h : TensorProduct R M N →+ TensorProduct S P Q,
      ∀ m n, h (TensorProduct.tmul R m n) = TensorProduct.tmul S (f m) (g n) :=
  ⟨(TensorProduct.map f g).toAddMonoidHom, TensorProduct.map_tmul f g⟩

private def scalarCoefficientSemilinear :
    E →ₛₗ[lisseIntegerInclusion l E L ι] L where
  toFun := ι
  map_add' := ι.map_add
  map_smul' r a := by
    change ι ((r : E) * a) = (lisseIntegerInclusion l E L ι r : L) * ι a
    rw [map_mul]
    have hi : (lisseIntegerInclusion l E L ι r : L) = ι (r : E) :=
      (lisseIntegerInclusion_exists l E L ι).choose_spec r
    rw [hi]

private def scalarHomSemilinear (F G : LisseRationalSheaf l E Y) :
    (F.integral ⟶ G.integral) →ₛₗ[lisseIntegerInclusion l E L ι]
      ((lisseIntegralScalarExtension l E Y L ι).obj F.integral ⟶
        (lisseIntegralScalarExtension l E Y L ι).obj G.integral) where
  toFun := (lisseIntegralScalarExtension l E Y L ι).map
  map_add' := scalarMap_add l E Y L ι
  map_smul' := scalarMap_smul l E Y L ι

@[irreducible]
private def rationalScalarMap (F G : LisseRationalSheaf l E Y) :
    lisseRationalHom l E Y F G →+
      lisseRationalHom l L Y
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj G.integral⟩ :=
  (tensorSemilinearMap_exists (lisseIntegerInclusion l E L ι)
    (scalarCoefficientSemilinear l E L ι) (scalarHomSemilinear l E Y L ι F G)).choose

private theorem rationalScalarMap_tmul (F G : LisseRationalSheaf l E Y)
    (a : E) (f : F.integral ⟶ G.integral) :
    rationalScalarMap l E Y L ι F G (TensorProduct.tmul _ a f) =
      TensorProduct.tmul _ (ι a) ((lisseIntegralScalarExtension l E Y L ι).map f) := by
  delta rationalScalarMap
  exact (tensorSemilinearMap_exists (lisseIntegerInclusion l E L ι)
    (scalarCoefficientSemilinear l E L ι) (scalarHomSemilinear l E Y L ι F G)).choose_spec a f

private theorem tensor_bilinear_map_naturality
    {R S A B : Type*} [CommRing R] [CommRing S] [Field A] [Field B]
    [Algebra R A] [Algebra S B]
    {U V W U' V' W' : Type*}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [AddCommGroup U'] [AddCommGroup V'] [AddCommGroup W']
    [Module R U] [Module R V] [Module R W]
    [Module S U'] [Module S V'] [Module S W']
    (c : TensorProduct R A U →ₗ[A] TensorProduct R A V →ₗ[A] TensorProduct R A W)
    (d : TensorProduct S B U' →ₗ[B] TensorProduct S B V' →ₗ[B] TensorProduct S B W')
    (c₀ : U → V → W) (d₀ : U' → V' → W') (φ : A →+* B)
    (f : TensorProduct R A U →+ TensorProduct S B U')
    (g : TensorProduct R A V →+ TensorProduct S B V')
    (h : TensorProduct R A W →+ TensorProduct S B W')
    (i : U → U') (j : V → V') (k : W → W')
    (hc : ∀ a b u v, c (TensorProduct.tmul R a u) (TensorProduct.tmul R b v) =
      TensorProduct.tmul R (a * b) (c₀ u v))
    (hd : ∀ a b u v, d (TensorProduct.tmul S a u) (TensorProduct.tmul S b v) =
      TensorProduct.tmul S (a * b) (d₀ u v))
    (hf : ∀ a u, f (TensorProduct.tmul R a u) = TensorProduct.tmul S (φ a) (i u))
    (hg : ∀ a u, g (TensorProduct.tmul R a u) = TensorProduct.tmul S (φ a) (j u))
    (hh : ∀ a u, h (TensorProduct.tmul R a u) = TensorProduct.tmul S (φ a) (k u))
    (hp : ∀ u v, k (c₀ u v) = d₀ (i u) (j v))
    (u : TensorProduct R A U) (v : TensorProduct R A V) :
    h (c u v) = d (f u) (g v) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
  | tmul a u =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp only [map_add, hv, hw]
    | tmul b v => rw [hc, hh, hf, hg, hd, map_mul, hp]

set_option maxRecDepth 200 in
/-- Scalar extension of rational morphisms exists with the stated formula. -/
theorem lisseRationalScalarExtension_exists :
    Nonempty (LisseRationalScalarExtensionData l E Y L ι) := by
  refine ⟨{ map := fun F G ↦ rationalScalarMap l E Y L ι F G
            map_add := fun F G f g ↦ (rationalScalarMap l E Y L ι F G).map_add f g
            map_tmul := rationalScalarMap_tmul l E Y L ι
            map_id := ?_
            map_comp := ?_ }⟩
  · intro F
    rw [rationalScalarMap_tmul, map_one, CategoryTheory.Functor.map_id]
  · intro F G H f g
    exact tensor_bilinear_map_naturality
      ((lisseRationalComposition l E Y).comp F G H)
      ((lisseRationalComposition l L Y).comp
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj G.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj H.integral⟩)
      (fun f g ↦ f ≫ g) (fun f g ↦ f ≫ g) ι.toRingHom
      (rationalScalarMap l E Y L ι F G) (rationalScalarMap l E Y L ι G H)
      (rationalScalarMap l E Y L ι F H)
      (fun f ↦ (lisseIntegralScalarExtension l E Y L ι).map f)
      (fun f ↦ (lisseIntegralScalarExtension l E Y L ι).map f)
      (fun f ↦ (lisseIntegralScalarExtension l E Y L ι).map f)
      ((lisseRationalComposition l E Y).comp_tmul F G H)
      ((lisseRationalComposition l L Y).comp_tmul
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj G.integral⟩
        ⟨(lisseIntegralScalarExtension l E Y L ι).obj H.integral⟩)
      (rationalScalarMap_tmul l E Y L ι F G)
      (rationalScalarMap_tmul l E Y L ι G H)
      (rationalScalarMap_tmul l E Y L ι F H)
      (fun f g ↦ (lisseIntegralScalarExtension l E Y L ι).map_comp f g) f g

/-- The prescribed additive scalar-extension maps. -/
@[irreducible]
def lisseRationalScalarExtensionData : LisseRationalScalarExtensionData l E Y L ι :=
  Classical.choice (lisseRationalScalarExtension_exists l E Y L ι)

/-- Scalar extension `F ⊗ E ↦ (F ⊗_{𝒪_E} 𝒪_L) ⊗ L`. -/
def lisseRationalScalarExtension : LisseRationalSheaf l E Y ⥤ LisseRationalSheaf l L Y where
  obj F := ⟨(lisseIntegralScalarExtension l E Y L ι).obj F.integral⟩
  map {F G} f := (lisseRationalScalarExtensionData l E Y L ι).map F G f
  map_id := (lisseRationalScalarExtensionData l E Y L ι).map_id
  map_comp := (lisseRationalScalarExtensionData l E Y L ι).map_comp _ _ _

set_option backward.isDefEq.respectTransparency true
-- Share ring structures in the tensor comparison proofs only.
attribute [local instance] lisseCoefficientIntegersCommRing lisseCoefficientIntegersAlgebra
  lisseCoefficientIntegersModule lisseCoefficientQuotientCommRing lisseCoefficientQuotientAlgebra

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_integralLevel_annihilated (F : LisseIntegralSheaf l E Y)
    (m : ℕ) (U : Y.Etale) :
    Padic.coefficientExtensionIdeal l E (m + 1) •
      (⊤ : Submodule (Padic.coefficientExtensionIntegers l E)
        ((F.obj.obj (op m)).obj.obj (op U))) = ⊥ :=
  F.property.2.1 m U

attribute [local irreducible] IsLisseIntegralDiagram

attribute [local semireducible] lisseIntegralScalarExtension

section SheafScalarAssociativity

-- An equality fixes the witness completely, while the choice prevents kernel
-- reduction from repeatedly expanding a large comparison construction.
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_canonicalIso_exists {C : Type*} [Category* C] {X Z : C} (e : X ≅ Z) :
    ∃ e' : X ≅ Z, e' = e := ⟨e, rfl⟩

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_canonicalIso {C : Type*} [Category* C] {X Z : C} (e : X ≅ Z) : X ≅ Z :=
  (lisseCoherence_canonicalIso_exists e).choose

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_canonicalIso_eq {C : Type*} [Category* C] {X Z : C} (e : X ≅ Z) :
    lisseCoherence_canonicalIso e = e := (lisseCoherence_canonicalIso_exists e).choose_spec

section GenericRings

variable {R S T : Type (u + 1)} [Ring R] [Ring S] [Ring T]

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_sheafRestrictionComp (f : R →+* S) (g : S →+* T) :
    sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} (g.comp f)) ≅
      sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} g) ⋙
        sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} f) :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U ↦ (ModuleCat.restrictScalarsComp f g).app (M.obj.obj U))
    (fun v ↦ by ext x; rfl))) (fun v ↦ by ext U x; rfl)

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_sheafScalarComp (f : R →+* S) (g : S →+* T) :
    Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology (g.comp f) ≅
      Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f ⋙
        Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology g :=
  lisseCoherence_canonicalIso ((conjugateIsoEquiv
    ((lisseCoherence_scalarSheafAdj Y f).comp (lisseCoherence_scalarSheafAdj Y g))
    (lisseCoherence_scalarSheafAdj Y (g.comp f))).symm (lisseCoherence_sheafRestrictionComp Y f
      g).symm)

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_sheafScalarComp_unit (f : R →+* S) (g : S →+* T)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (x : M.obj.obj (op U)) :
    ((lisseCoherence_sheafScalarComp Y f g).hom.app M).hom.app (op U)
      ((lisseCoherence_scalarSheafUnit Y (g.comp f) M).hom.app (op U) x) =
        (lisseCoherence_scalarSheafUnit Y g _).hom.app (op U)
          ((lisseCoherence_scalarSheafUnit Y f M).hom.app (op U) x) := by
  have h : (lisseCoherence_scalarSheafAdj Y (g.comp f)).homEquiv _ _
      ((lisseCoherence_sheafScalarComp Y f g).hom.app M) =
      (lisseCoherence_scalarSheafAdj Y f).unit.app M ≫
        (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} f)).map
          ((lisseCoherence_scalarSheafAdj Y g).unit.app _) ≫
            (lisseCoherence_sheafRestrictionComp Y f g).inv.app _ := by
    rw [Adjunction.homEquiv_apply]
    simpa only [lisseCoherence_sheafScalarComp, lisseCoherence_canonicalIso_eq,
      conjugateIsoEquiv_symm_apply_hom,
      Adjunction.comp_unit_app, Category.assoc, Iso.symm_hom] using!
      (unit_conjugateEquiv_symm
        ((lisseCoherence_scalarSheafAdj Y f).comp (lisseCoherence_scalarSheafAdj Y g))
        (lisseCoherence_scalarSheafAdj Y (g.comp f)) (lisseCoherence_sheafRestrictionComp Y f
          g).inv M).symm
  have hx := congrArg (fun v ↦ v.hom.app (op U) x) h
  exact hx

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_quotientRestrictionFull (q : R →+* S) (hq : Function.Surjective q) :
    (ModuleCat.restrictScalars.{u + 1} q).Full where
  map_surjective v := ⟨lisseCoherence_quotientRestrictedHom q hq _ _ v, by ext x; rfl⟩

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_sheafScalarCancel (q : R →+* S) (hq : Function.Surjective q) (g : S →+* T) :
    sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q) ⋙
        Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology (g.comp q) ≅
      Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology g := by
  letI := lisseCoherence_quotientRestrictionFull q hq
  let Q := sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)
  let E := Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology q
  let G := Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology g
  exact Functor.isoWhiskerLeft Q (lisseCoherence_sheafScalarComp Y q g) ≪≫
    (Functor.associator Q E G).symm ≪≫
    Functor.isoWhiskerRight (asIso (lisseCoherence_scalarSheafAdj Y q).counit) G ≪≫
      Functor.leftUnitor G

set_option backward.isDefEq.respectTransparency false in
omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_sheafScalarCancel_unit (q : R →+* S) (hq : Function.Surjective q)
    (g : S →+* T) (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S))
    (U : Y.Etale) (x : N.obj.obj (op U)) :
    ((lisseCoherence_sheafScalarCancel Y q hq g).hom.app N).hom.app (op U)
      ((lisseCoherence_scalarSheafUnit Y (g.comp q) _).hom.app (op U) x) =
        (lisseCoherence_scalarSheafUnit Y g N).hom.app (op U) x := by
  let c := (lisseCoherence_scalarSheafAdj Y q).counit.app N
  change ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology g).map c).hom.app (op U)
    (((lisseCoherence_sheafScalarComp Y q g).hom.app _).hom.app (op U)
      ((lisseCoherence_scalarSheafUnit Y (g.comp q) _).hom.app (op U) x)) = _
  rw [lisseCoherence_sheafScalarComp_unit]
  have hn := congrArg (fun v ↦ v.hom.app (op U)
    ((lisseCoherence_scalarSheafUnit Y q _).hom.app (op U) x))
      ((lisseCoherence_scalarSheafAdj Y g).unit.naturality c)
  change (lisseCoherence_scalarSheafUnit Y g N).hom.app (op U)
      (c.hom.app (op U) ((lisseCoherence_scalarSheafUnit Y q _).hom.app (op U) x)) =
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology g).map c).hom.app
      (op U) ((lisseCoherence_scalarSheafUnit Y g _).hom.app (op U)
        ((lisseCoherence_scalarSheafUnit Y q _).hom.app (op U) x)) at hn
  have ht := congrArg (fun v ↦ v.hom.app (op U) x)
    ((lisseCoherence_scalarSheafAdj Y q).right_triangle_components N)
  change c.hom.app (op U) ((lisseCoherence_scalarSheafUnit Y q _).hom.app (op U) x) = x at ht
  exact hn.symm.trans (congrArg ((lisseCoherence_scalarSheafUnit Y g N).hom.app (op U)) ht)

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_sheafScalarCancel_inv_unit (q : R →+* S) (hq : Function.Surjective q)
    (g : S →+* T) (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S))
    (U : Y.Etale) (x : N.obj.obj (op U)) :
    ((lisseCoherence_sheafScalarCancel Y q hq g).inv.app N).hom.app (op U)
      ((lisseCoherence_scalarSheafUnit Y g N).hom.app (op U) x) =
        (lisseCoherence_scalarSheafUnit Y (g.comp q)
          ((sheafCompose Y.smallEtaleTopology
            (ModuleCat.restrictScalars.{u + 1} q)).obj N)).hom.app (op U) x := by
  let c := lisseCoherence_sheafScalarCancel Y q hq g
  have h := congrArg (fun z ↦ (c.inv.app N).hom.app (op U) z)
    (lisseCoherence_sheafScalarCancel_unit Y q hq g N U x)
  have h₀ := congrArg (fun v ↦ v.hom.app (op U)
    ((lisseCoherence_scalarSheafUnit Y (g.comp q)
          ((sheafCompose Y.smallEtaleTopology
            (ModuleCat.restrictScalars.{u + 1} q)).obj N)).hom.app (op U) x))
      (c.hom_inv_id_app N)
  change (c.inv.app N).hom.app (op U) ((c.hom.app N).hom.app (op U)
    ((lisseCoherence_scalarSheafUnit Y (g.comp q)
          ((sheafCompose Y.smallEtaleTopology
            (ModuleCat.restrictScalars.{u + 1} q)).obj N)).hom.app (op U) x)) = _ at h₀
  exact h.symm.trans h₀

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_sheafScalarThroughQuotient {B : Type (u + 1)} [Ring B]
    (f : R →+* S) (q : S →+* B) (hq : Function.Surjective q) (g : B →+* T) :
    Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology (g.comp (q.comp f)) ≅
      Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology (q.comp f) ⋙
        sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q) ⋙
          Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology (g.comp q) :=
  lisseCoherence_sheafScalarComp Y (q.comp f) g ≪≫
    Functor.isoWhiskerLeft _ (lisseCoherence_sheafScalarCancel Y q hq g).symm ≪≫
      (Functor.associator _ _ _).symm

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_sheafScalarThroughQuotient_unit {B : Type (u + 1)} [Ring B]
    (f : R →+* S) (q : S →+* B) (hq : Function.Surjective q) (g : B →+* T)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (x : M.obj.obj (op U)) :
    ((lisseCoherence_sheafScalarThroughQuotient Y f q hq g).hom.app M).hom.app (op U)
      ((lisseCoherence_scalarSheafUnit Y (g.comp (q.comp f)) M).hom.app (op U) x) =
        (lisseCoherence_scalarSheafUnit Y (g.comp q)
          ((sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj
            ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology
              (q.comp f)).obj M))).hom.app (op U)
          ((lisseCoherence_scalarSheafUnit Y (q.comp f) M).hom.app (op U) x) := by
  change ((lisseCoherence_sheafScalarCancel Y q hq g).inv.app _).hom.app (op U)
    (((lisseCoherence_sheafScalarComp Y (q.comp f) g).hom.app M).hom.app (op U)
      ((lisseCoherence_scalarSheafUnit Y (g.comp (q.comp f)) M).hom.app (op U) x)) = _
  rw [lisseCoherence_sheafScalarComp_unit]
  exact lisseCoherence_sheafScalarCancel_inv_unit Y q hq g
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology (q.comp f)).obj M) U
    ((lisseCoherence_scalarSheafUnit Y (q.comp f) M).hom.app (op U) x)

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_sheaf_comp_apply
    (M N P : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (v : M ⟶ N) (w : N ⟶ P) (U : Y.Etale) (x : M.obj.obj (op U)) :
    (v ≫ w).hom.app (op U) x = w.hom.app (op U) (v.hom.app (op U) x) := rfl

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_sheafRestriction_apply (q : R →+* S)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S))
    (v : M ⟶ N) (U : Y.Etale) (x : M.obj.obj (op U)) :
    ((sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).map v).hom.app
      (op U) x = v.hom.app (op U) x := rfl

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarSheafMap_unit (f : R →+* S)
    (M N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (v : M ⟶ N)
    (U : Y.Etale) (x : M.obj.obj (op U)) :
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).map v).hom.app
      (op U) ((lisseCoherence_scalarSheafUnit Y f M).hom.app (op U) x) =
        (lisseCoherence_scalarSheafUnit Y f N).hom.app (op U) (v.hom.app (op U) x) := by
  exact (congrArg (fun v ↦ v.hom.app (op U) x)
    ((lisseCoherence_scalarSheafAdj Y f).unit.naturality v)).symm

end GenericRings

section CommutativeQuotients

variable {R S : Type (u + 1)} [CommRing R] [CommRing S]

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_quotientSectionTorsion (I : Ideal R)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hM : ∀ U : Y.Etale, I • (⊤ : Submodule R (M.obj.obj (op U))) = ⊥)
    (U : Y.Etale) : Module.IsTorsionBySet R (M.obj.obj (op U)) I := by
  intro x a
  have h := Submodule.smul_mem_smul (N := (⊤ : Submodule R (M.obj.obj (op U))))
    a.property (Submodule.mem_top (x := x))
  rw [hM U] at h
  exact h

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_quotientSheafLift (I : Ideal R)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hM : ∀ U : Y.Etale, I • (⊤ : Submodule R (M.obj.obj (op U))) = ⊥) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (R ⧸ I)) := by
  let O (U : Y.Etaleᵒᵖ) : ModuleCat.{u + 1} (R ⧸ I) := by
    letI := (lisseCoherence_quotientSectionTorsion Y I M hM U.unop).module
    exact ModuleCat.of (R ⧸ I) (M.obj.obj U)
  let P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (R ⧸ I) :=
    { obj := O
      map {U V} v := lisseCoherence_quotientRestrictedHom (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective (O U) (O V) (M.obj.map v)
      map_id U := by
        ext x
        change (M.obj.map (𝟙 U)) x = x
        exact congrArg (fun f ↦ f x) (M.obj.map_id U)
      map_comp v w := by
        ext x
        change (M.obj.map (v ≫ w)) x = (M.obj.map w) ((M.obj.map v) x)
        rw [M.obj.map_comp]
        rfl }
  refine ⟨P, ?_⟩
  apply (Presheaf.isSheaf_iff_isSheaf_forget Y.smallEtaleTopology P
    (CategoryTheory.forget (ModuleCat.{u + 1} (R ⧸ I)))).mpr
  exact ((sheafCompose Y.smallEtaleTopology
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj M).property

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_quotientSheafLiftIso (I : Ideal R)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hM : ∀ U : Y.Etale, I • (⊤ : Submodule R (M.obj.obj (op U))) = ⊥) :
    M ≅ (sheafCompose Y.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk I))).obj
        (lisseCoherence_quotientSheafLift Y I M hM) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ Iso.refl _) (by intros; ext x; rfl))

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_quotientSheafUnit_isIso (I : Ideal R)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hM : ∀ U : Y.Etale, I • (⊤ : Submodule R (M.obj.obj (op U))) = ⊥) :
    IsIso (lisseCoherence_scalarSheafUnit Y (Ideal.Quotient.mk I) M) := by
  have := lisseCoherence_quotientRestrictionFull (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact (lisseCoherence_scalarSheafAdj Y (Ideal.Quotient.mk I)).isIso_unit_app_of_iso
    (lisseCoherence_quotientSheafLiftIso Y I M hM)

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_quotientScalar_hom_ext_ann (f : R →+* S) (I : Ideal S)
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S))
    (hN : ∀ U : Y.Etale, I • (⊤ : Submodule S (N.obj.obj (op U))) = ⊥)
    (v w : lisseCoherence_quotientScalarLevel Y f I M ⟶ N)
    (h : ∀ (U : Y.Etale) (x : M.obj.obj (op U)),
      v.hom.app (op U) (lisseCoherence_quotientScalarGenerator Y f I M U 1 x) =
        w.hom.app (op U) (lisseCoherence_quotientScalarGenerator Y f I M U 1 x)) : v = w := by
  let P := (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology
    ((Ideal.Quotient.mk I).comp f)).obj M
  let Q := lisseCoherence_quotientSheafLift Y I N hN
  let e := lisseCoherence_quotientSheafLiftIso Y I N hN
  let v' := lisseCoherence_quotientRestrictedSheafHom Y (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective P Q (v ≫ e.hom)
  let w' := lisseCoherence_quotientRestrictedSheafHom Y (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective P Q (w ≫ e.hom)
  have he : v' = w' := by
    apply ((lisseCoherence_scalarSheafAdj Y ((Ideal.Quotient.mk I).comp f)).homEquiv M Q).injective
    simp only [Adjunction.homEquiv_apply]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change v.hom.app U ((lisseCoherence_scalarSheafUnit Y _ M).hom.app U x) =
      w.hom.app U ((lisseCoherence_scalarSheafUnit Y _ M).hom.app U x)
    rw [lisseCoherence_scalarSheafUnit_apply]
    exact h U.unop x
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun k ↦ k.hom.app U x) he

end CommutativeQuotients

section GenericRings

variable {R S T : Type (u + 1)} [Ring R] [Ring S] [Ring T]

attribute [local irreducible] Sheaf.ringExtendScalars lisseCoherence_scalarSheafAdj
  lisseCoherence_scalarSheafUnit
  lisseCoherence_sheafScalarThroughQuotient lisseCoherence_sheafScalarCancel
    lisseCoherence_sheafScalarComp

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarTransportIso {B V : Type (u + 1)} [Ring B] [Ring V]
    (t : V →+* T) (f : R →+* S) (q : S →+* B) (hq : Function.Surjective q)
    (g : B →+* T) (k : R →+* T) (j : S →+* T)
    (hk : g.comp (q.comp f) = k) (hj : g.comp q = j)
    (r : R →+* B) (hr : r = q.comp f)
    (M₀ M₁ : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (e : M₀ ≅ M₁)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S))
    (d : N ≅ (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj
      ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology r).obj M₁)) :
    (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} t)).obj
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology k).obj M₀) ≅
      (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} t)).obj
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology j).obj N) := by
  subst r
  exact lisseCoherence_canonicalIso (
    (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} t)).mapIso
    ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology k).mapIso e ≪≫
      eqToIso (congrArg (fun f ↦
        (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj M₁) hk.symm) ≪≫
      (lisseCoherence_sheafScalarThroughQuotient Y f q hq g).app M₁ ≪≫
      eqToIso (congrArg (fun f ↦
        (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj _ ) hj) ≪≫
      (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology j).mapIso d.symm))

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarTransportIso_unit {B V : Type (u + 1)} [Ring B] [Ring V]
    (t : V →+* T) (f : R →+* S) (q : S →+* B) (hq : Function.Surjective q)
    (g : B →+* T) (k : R →+* T) (j : S →+* T)
    (hk : g.comp (q.comp f) = k) (hj : g.comp q = j)
    (r : R →+* B) (hr : r = q.comp f)
    (M₀ M₁ : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (e : M₀ ≅ M₁)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S))
    (d : N ≅ (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj
      ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology r).obj M₁))
    (U : Y.Etale) (x : M₀.obj.obj (op U)) :
    (lisseCoherence_scalarTransportIso Y t f q hq g k j hk hj r hr M₀ M₁ e N d).hom.hom.app (op U)
      ((lisseCoherence_scalarSheafUnit Y k M₀).hom.app (op U) x) =
        (lisseCoherence_scalarSheafUnit Y j N).hom.app (op U)
          (d.inv.hom.app (op U) ((lisseCoherence_scalarSheafUnit Y r M₁).hom.app (op U)
            (e.hom.hom.app (op U) x))) := by
  subst r
  subst k
  subst j
  simp only [lisseCoherence_scalarTransportIso, lisseCoherence_canonicalIso_eq,
    Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
    eqToIso_refl, Iso.refl_hom, Category.id_comp]
  erw [lisseCoherence_sheafRestriction_apply (R := V) (S := T)]
  erw [lisseCoherence_sheaf_comp_apply (R := T), lisseCoherence_sheaf_comp_apply (R := T),
    lisseCoherence_scalarSheafMap_unit Y (g.comp (q.comp f)),
    lisseCoherence_sheafScalarThroughQuotient_unit Y f q hq g, lisseCoherence_scalarSheafMap_unit
      Y (g.comp q)]

attribute [local irreducible] lisseCoherence_scalarTransportIso

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarIdentityTransportIso (q k : R →+* S) (h : k = q)
    (M₀ M₁ : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (e : M₀ ≅ M₁)
    [IsIso (lisseCoherence_scalarSheafUnit Y q M₁)] :
    (sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} q)).obj
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology k).obj M₀) ≅ M₁ :=
  lisseCoherence_canonicalIso ((sheafCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u +
    1} q)).mapIso
    (eqToIso (congrArg (fun f ↦
      (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj M₀) h) ≪≫
      (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology q).mapIso e) ≪≫
    (asIso (lisseCoherence_scalarSheafUnit Y q M₁)).symm)

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarIdentityTransportIso_unit (q k : R →+* S) (h : k = q)
    (M₀ M₁ : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (e : M₀ ≅ M₁)
    [IsIso (lisseCoherence_scalarSheafUnit Y q M₁)] (U : Y.Etale) (x : M₀.obj.obj (op U)) :
    (lisseCoherence_scalarIdentityTransportIso Y q k h M₀ M₁ e).hom.hom.app (op U)
      ((lisseCoherence_scalarSheafUnit Y k M₀).hom.app (op U) x) = e.hom.hom.app (op U) x := by
  subst k
  simp only [lisseCoherence_scalarIdentityTransportIso, lisseCoherence_canonicalIso_eq,
    Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, eqToIso_refl, Iso.refl_hom, Category.id_comp]
  erw [lisseCoherence_sheaf_comp_apply (R := R), lisseCoherence_sheafRestriction_apply (R := R) (S
    := S),
    lisseCoherence_scalarSheafMap_unit Y q]
  exact congrArg (fun v ↦ v.hom.app (op U) (e.hom.hom.app (op U) x))
    (asIso (lisseCoherence_scalarSheafUnit Y q M₁)).hom_inv_id

attribute [local irreducible] lisseCoherence_scalarIdentityTransportIso

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_sheafIso_conjugate_apply_eq {A : Type (u + 1)} [Ring A]
    {M₀ M₁ N₀ N₁ : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (e : M₀ ≅ M₁) (e₀ : M₀ ≅ N₀) (c : N₀ ≅ N₁) (e₁ : M₁ ≅ N₁)
    (he : e = e₀ ≪≫ c ≪≫ e₁.symm) (U : Y.Etale) (x : N₀.obj.obj (op U)) (y : N₁.obj.obj (op U))
    (h : c.hom.hom.app (op U) x = y) :
    e.hom.hom.app (op U) (e₀.inv.hom.app (op U) x) =
      e₁.inv.hom.app (op U) y := by
  subst e
  change e₁.inv.hom.app (op U)
    (c.hom.hom.app (op U) (e₀.hom.hom.app (op U) (e₀.inv.hom.app (op U) x))) = _
  have he : e₀.hom.hom.app (op U) (e₀.inv.hom.app (op U) x) = x :=
    congrArg (fun v ↦ v.hom.app (op U) x) e₀.inv_hom_id
  exact (congrArg (fun z ↦ e₁.inv.hom.app (op U) (c.hom.hom.app (op U) z)) he).trans
    (congrArg (fun z ↦ e₁.inv.hom.app (op U) z) h)

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_sheafIso_conjugateWithFormula_exists {A : Type (u + 1)} [Ring A]
    {M₀ M₁ N₀ N₁ : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (e₀ : M₀ ≅ N₀) (c : N₀ ≅ N₁) (e₁ : M₁ ≅ N₁) :
    ∃ e : { e : M₀ ≅ M₁ // ∀ (U : Y.Etale) (x : N₀.obj.obj (op U))
        (y : N₁.obj.obj (op U)), c.hom.hom.app (op U) x = y →
      e.hom.hom.app (op U) (e₀.inv.hom.app (op U) x) =
        e₁.inv.hom.app (op U) y }, e.val = e₀ ≪≫ c ≪≫ e₁.symm :=
  ⟨⟨e₀ ≪≫ c ≪≫ e₁.symm, fun U x y h ↦
    lisseCoherence_sheafIso_conjugate_apply_eq Y _ e₀ c e₁ rfl U x y h⟩, rfl⟩

omit [IsNoetherian Y] [Y.IsSeparated] in
/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_sheafIso_conjugateWithFormula {A : Type (u + 1)} [Ring A]
    {M₀ M₁ N₀ N₁ : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (e₀ : M₀ ≅ N₀) (c : N₀ ≅ N₁) (e₁ : M₁ ≅ N₁) :
    { e : M₀ ≅ M₁ // ∀ (U : Y.Etale) (x : N₀.obj.obj (op U))
        (y : N₁.obj.obj (op U)), c.hom.hom.app (op U) x = y →
      e.hom.hom.app (op U) (e₀.inv.hom.app (op U) x) =
        e₁.inv.hom.app (op U) y } :=
  (lisseCoherence_sheafIso_conjugateWithFormula_exists Y e₀ c e₁).choose

attribute [local irreducible] lisseCoherence_sheafIso_conjugateWithFormula

end GenericRings

end SheafScalarAssociativity

-- Keep the proved comparison APIs opaque after leaving their construction sections.
attribute [local irreducible] lisseCoherence_scalarSheafAdj lisseCoherence_scalarSheafUnit
  lisseCoherence_sheafScalarComp
  lisseCoherence_scalarTransportIso lisseCoherence_scalarIdentityTransportIso
    lisseCoherence_sheafIso_conjugateWithFormula

attribute [local irreducible] Sheaf.ringExtendScalars

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_integerInclusion_id :
    lisseIntegerInclusion l E E (AlgHom.id ℚ_[l] E) = RingHom.id _ := by
  ext x
  exact (lisseIntegerInclusion_exists l E E (AlgHom.id ℚ_[l] E)).choose_spec x

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_integerInclusion_comp
    (M : Type (u + 1)) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (κ : L →ₐ[ℚ_[l]] M) :
    lisseIntegerInclusion l E M (κ.comp ι) =
      (lisseIntegerInclusion l L M κ).comp (lisseIntegerInclusion l E L ι) := by
  ext x
  have h₁ : (lisseIntegerInclusion l E M (κ.comp ι) x : M) = κ (ι (x : E)) :=
    (lisseIntegerInclusion_exists l E M (κ.comp ι)).choose_spec x
  have h₂ : (lisseIntegerInclusion l L M κ (lisseIntegerInclusion l E L ι x) : M) =
      κ (lisseIntegerInclusion l E L ι x : L) :=
    (lisseIntegerInclusion_exists l L M κ).choose_spec _
  have h₃ : (lisseIntegerInclusion l E L ι x : L) = ι (x : E) :=
    (lisseIntegerInclusion_exists l E L ι).choose_spec x
  exact h₁.trans (h₂.trans (congrArg κ h₃)).symm

private theorem maximalIdeal_pow_injective :
    Function.Injective (fun n : ℕ ↦ Padic.coefficientExtensionMaximalIdeal l E ^ n) := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  rcases h with ⟨_, _, _, _, hm, _, _, hdvr, _, hne, _⟩
  have : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) := hdvr
  intro n m hnm
  exact (pow_inj_of_not_isUnit (mt Ideal.isUnit_iff.mp hm.ne_top) hne).mp hnm

private theorem ramification_id : lisseRamificationIndex l E E (AlgHom.id ℚ_[l] E) = 1 := by
  apply maximalIdeal_pow_injective l E
  have h := (lisseRamificationIndex_exists l E E (AlgHom.id ℚ_[l] E)).choose_spec.2
  change Ideal.map (lisseIntegerInclusion l E E (AlgHom.id ℚ_[l] E)) _ = _ at h
  simpa only [lisseCoherence_integerInclusion_id, Ideal.map_id, pow_one, lisseRamificationIndex]
    using h.symm

private theorem ramification_comp
    (M : Type (u + 1)) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (κ : L →ₐ[ℚ_[l]] M) :
    lisseRamificationIndex l E M (κ.comp ι) =
      lisseRamificationIndex l L M κ * lisseRamificationIndex l E L ι := by
  apply maximalIdeal_pow_injective l M
  have hEL : Ideal.map (lisseIntegerInclusion l E L ι)
      (Padic.coefficientExtensionMaximalIdeal l E) =
      Padic.coefficientExtensionMaximalIdeal l L ^ lisseRamificationIndex l E L ι :=
    (lisseRamificationIndex_exists l E L ι).choose_spec.2
  have hLM : Ideal.map (lisseIntegerInclusion l L M κ)
      (Padic.coefficientExtensionMaximalIdeal l L) =
      Padic.coefficientExtensionMaximalIdeal l M ^ lisseRamificationIndex l L M κ :=
    (lisseRamificationIndex_exists l L M κ).choose_spec.2
  have hEM : Ideal.map (lisseIntegerInclusion l E M (κ.comp ι))
      (Padic.coefficientExtensionMaximalIdeal l E) =
      Padic.coefficientExtensionMaximalIdeal l M ^ lisseRamificationIndex l E M (κ.comp ι) :=
    (lisseRamificationIndex_exists l E M (κ.comp ι)).choose_spec.2
  change _ ^ lisseRamificationIndex l E M (κ.comp ι) = _
  rw [← hEM, lisseCoherence_integerInclusion_comp, ← Ideal.map_map, hEL, Ideal.map_pow, hLM]
  exact (pow_mul _ _ _).symm

/-- Extending coefficients along the identity leaves the level index unchanged. -/
theorem lisseScalarSourceIndex_id (m : ℕ) :
    lisseScalarSourceIndex l E E (AlgHom.id ℚ_[l] E) m = m := by
  rw [lisseCoherence_scalarIndex_eq, ramification_id, Nat.div_one]

/-- Successive scalar extensions have the same index as their composite. -/
theorem lisseScalarSourceIndex_comp
    (M : Type (u + 1)) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (κ : L →ₐ[ℚ_[l]] M) (m : ℕ) :
    lisseScalarSourceIndex l E L ι (lisseScalarSourceIndex l L M κ m) =
      lisseScalarSourceIndex l E M (κ.comp ι) m := by
  simp only [lisseCoherence_scalarIndex_eq, ramification_comp, Nat.div_div_eq_div_mul]

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarIndex_mono {m n : ℕ} (h : m ≤ n) :
    lisseScalarSourceIndex l E L ι m ≤ lisseScalarSourceIndex l E L ι n := by
  simp only [lisseCoherence_scalarIndex_eq]
  exact Nat.div_le_div_right h

attribute [local irreducible] lisseScalarSourceIndex lisseRamificationIndex
  lisseIntegerInclusion Padic.coefficientExtensionIntegers

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_integralLevel_annihilated_le (F : LisseIntegralSheaf l E Y)
    (m n : ℕ) (h : m ≤ n) (U : Y.Etale) :
    Padic.coefficientExtensionIdeal l E (n + 1) •
      (⊤ : Submodule (Padic.coefficientExtensionIntegers l E)
        ((F.obj.obj (op m)).obj.obj (op U))) = ⊥ := by
  apply bot_unique
  exact (Submodule.smul_mono_left
    (Ideal.pow_le_pow_right (Nat.succ_le_succ h))).trans
      (le_of_eq (lisseCoherence_integralLevel_annihilated l E Y F m U))

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_sequenceCast_naturality {C : Type*} [Category C] (F : ℕᵒᵖ ⥤ C)
    {a b c d : ℕ} (ha : a = c) (hb : b = d) (hab : a ≤ b) (hcd : c ≤ d) :
    F.map (homOfLE hab).op ≫ eqToHom (congrArg (fun n ↦ F.obj (op n)) ha) =
      eqToHom (congrArg (fun n ↦ F.obj (op n)) hb) ≫ F.map (homOfLE hcd).op := by
  subst c
  subst d
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_natTrans_index_cast {C : Type*} [Category C] {F G : ℕᵒᵖ ⥤ C}
    (v : F ⟶ G) {a b : ℕ} (h : a = b) :
    v.app (op a) ≫ eqToHom (congrArg (fun n ↦ G.obj (op n)) h) =
      eqToHom (congrArg (fun n ↦ F.obj (op n)) h) ≫ v.app (op b) := by
  subst b
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarCoefficientFactor (m : ℕ) :
    Padic.coefficientExtensionRing l E (lisseScalarSourceIndex l E L ι m + 1) →+*
      Padic.coefficientExtensionRing l L (m + 1) :=
  Ideal.Quotient.lift _ (lisseScalarCoefficientMap l E L ι m) (by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (lisseCoherence_scalarIndex_ideal l E L ι m (Ideal.mem_map_of_mem _ ha)))

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarCoefficientFactor_comp (m : ℕ) :
    (lisseCoherence_scalarCoefficientFactor l E L ι m).comp
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E
          (lisseScalarSourceIndex l E L ι m + 1))) =
      lisseScalarCoefficientMap l E L ι m := by
  ext x
  rfl

/-- The level identification recorded by the chosen scalar functor. -/
def lisseScalarLevelIso (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    ((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj (op m) ≅
      lisseIntegralScalarLevel l E Y L ι F m := by
  unfold lisseIntegralScalarExtension
  exact (lisseIntegralScalarExtensionData l E Y L ι).levelIso F m

/-- A local tensor generator transported into the chosen scalar functor. -/
def lisseScalarGenerator (F : LisseIntegralSheaf l E Y) (m : ℕ) (U : Y.Etale)
    (a : Padic.coefficientExtensionRing l L (m + 1))
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)) :
    (((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj (op m)).obj.obj (op U) :=
  (lisseScalarLevelIso l E Y L ι F m).inv.hom.app (op U)
    (lisseIntegralScalarGenerator l E Y L ι F m U a x)

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_chosenScalarLevel_ext (F : LisseIntegralSheaf l E Y) (m : ℕ)
    (N : Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)))
    (hN : ∀ U : Y.Etale, Padic.coefficientExtensionIdeal l L (m + 1) •
      (⊤ : Submodule (Padic.coefficientExtensionIntegers l L) (N.obj.obj (op U))) = ⊥)
    (v w : ((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj (op m) ⟶ N)
    (h : ∀ (U : Y.Etale)
      (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)),
      v.hom.app (op U) (lisseScalarGenerator l E Y L ι F m U 1 x) =
        w.hom.app (op U) (lisseScalarGenerator l E Y L ι F m U 1 x)) : v = w := by
  apply (cancel_epi (lisseScalarLevelIso l E Y L ι F m).inv).mp
  apply lisseCoherence_quotientScalar_hom_ext_ann Y (lisseIntegerInclusion l E L ι)
    (Padic.coefficientExtensionIdeal l L (m + 1))
    (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))) N hN
  exact h

/-- Local unit tensor generators detect morphisms from a scalar extension. -/
theorem lisseScalarHom_ext (F : LisseIntegralSheaf l E Y)
    (H : LisseIntegralSheaf l L Y)
    (v w : (lisseIntegralScalarExtension l E Y L ι).obj F ⟶ H)
    (h : ∀ (m : ℕ) (U : Y.Etale)
      (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)),
      (v.hom.app (op m)).hom.app (op U) (lisseScalarGenerator l E Y L ι F m U 1 x) =
        (w.hom.app (op m)).hom.app (op U) (lisseScalarGenerator l E Y L ι F m U 1 x)) :
    v = w := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext m
  exact lisseCoherence_chosenScalarLevel_ext l E Y L ι F m.unop (H.obj.obj m)
    (lisseCoherence_integralLevel_annihilated l L Y H m.unop) _ _ (h m.unop)

/-- Transport between equal levels commutes with local unit tensor generators. -/
theorem lisseScalarGenerator_cast (F : LisseIntegralSheaf l E Y)
    (m n : ℕ) (h : m = n) (U : Y.Etale)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)) :
    (eqToHom (congrArg (fun k ↦ ((lisseIntegralScalarExtension l E Y L ι).obj F).obj.obj
      (op k)) h)).hom.app (op U) (lisseScalarGenerator l E Y L ι F m U 1 x) =
      lisseScalarGenerator l E Y L ι F n U 1
        ((eqToHom (congrArg (fun k ↦ F.obj.obj (op (lisseScalarSourceIndex l E L ι k))) h)).hom.app
          (op U) x) := by
  subst n
  rfl

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_rawGenerator_one (F : LisseIntegralSheaf l E Y) (m : ℕ)
    (U : Y.Etale)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)) :
    lisseIntegralScalarGenerator l E Y L ι F m U 1 x =
      (lisseCoherence_scalarSheafUnit Y (lisseScalarCoefficientMap l E L ι m)
        (F.obj.obj (op (lisseScalarSourceIndex l E L ι m)))).hom.app (op U) x := by
  rw [lisseCoherence_scalarSheafUnit_apply]
  rfl

attribute [local irreducible] lisseIntegralScalarGenerator

/-- Scalar extension maps a unit tensor generator by the underlying section map. -/
theorem lisseScalarGenerator_map (F G : LisseIntegralSheaf l E Y) (v : F ⟶ G)
    (m : ℕ) (U : Y.Etale) (a : Padic.coefficientExtensionRing l L (m + 1))
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι m))).obj.obj (op U)) :
    (((lisseIntegralScalarExtension l E Y L ι).map v).hom.app (op m)).hom.app (op U)
      (lisseScalarGenerator l E Y L ι F m U a x) =
        lisseScalarGenerator l E Y L ι G m U a
          ((v.hom.app (op (lisseScalarSourceIndex l E L ι m))).hom.app (op U) x) := by
  let e := lisseScalarLevelIso l E Y L ι G m
  let z := (((lisseIntegralScalarExtension l E Y L ι).map v).hom.app (op m)).hom.app
    (op U) (lisseScalarGenerator l E Y L ι F m U a x)
  have h := (lisseIntegralScalarExtensionData l E Y L ι).map F G v m U a x
  have hh := congrArg (fun t ↦ e.inv.hom.app (op U) t) h
  have he := congrArg (fun t ↦ t.hom.app (op U) z) e.hom_inv_id
  dsimp only [e, z, lisseScalarLevelIso, lisseScalarGenerator,
    lisseIntegralScalarExtension] at he ⊢
  exact he.symm.trans hh

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_extendedGenerator_transition (F : LisseIntegralSheaf l E Y)
    (m : ℕ) (U : Y.Etale) (a : Padic.coefficientExtensionRing l L (m + 2))
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι (m + 1)))).obj.obj (op U)) :
    (((lisseIntegralScalarExtension l E Y L ι).obj F).obj.map
      (homOfLE (Nat.le_succ m)).op).hom.app (op U)
        (lisseScalarGenerator l E Y L ι F (m + 1) U a x) =
      lisseScalarGenerator l E Y L ι F m U (Padic.coefficientExtensionTransition l L (m + 1) a)
        ((F.obj.map (homOfLE (lisseScalarSourceIndex_le l E L ι m)).op).hom.app (op U) x) := by
  let e := lisseScalarLevelIso l E Y L ι F m
  let z := (((lisseIntegralScalarExtension l E Y L ι).obj F).obj.map
    (homOfLE (Nat.le_succ m)).op).hom.app (op U)
      (lisseScalarGenerator l E Y L ι F (m + 1) U a x)
  have h := (lisseIntegralScalarExtensionData l E Y L ι).transition F m U a x
  have hh := congrArg (fun t ↦ e.inv.hom.app (op U) t) h
  have he := congrArg (fun t ↦ t.hom.app (op U) z) e.hom_inv_id
  dsimp only [e, z, lisseScalarLevelIso, lisseScalarGenerator,
    lisseIntegralScalarExtension] at he ⊢
  exact he.symm.trans hh

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_sequenceGenerator_naturality
    {A : ℕᵒᵖ ⥤ Type v} {B : ℕᵒᵖ ⥤ Type w}
    (gen : ∀ n, A.obj (op n) → B.obj (op n))
    (step : ∀ n x, B.map (homOfLE (Nat.le_succ n)).op (gen (n + 1) x) =
      gen n (A.map (homOfLE (Nat.le_succ n)).op x))
    (m n : ℕ) (h : m ≤ n) (x : A.obj (op n)) :
    B.map (homOfLE h).op (gen n x) = gen m (A.map (homOfLE h).op x) := by
  induction n, h using Nat.le_induction with
  | base =>
    simp only [homOfLE_refl, op_id]
    rw [A.map_id, B.map_id]
    rfl
  | succ n h ih =>
    have he : (homOfLE (h.trans (Nat.le_succ n))).op =
        (homOfLE (Nat.le_succ n)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [he, A.map_comp, B.map_comp]
    change B.map (homOfLE h).op
        (B.map (homOfLE (Nat.le_succ n)).op (gen (n + 1) x)) = _
    rw [step, ih]
    rfl

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_extendedGenerator_transition_le (F : LisseIntegralSheaf l E Y)
    (m n : ℕ) (h : m ≤ n) (U : Y.Etale)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E L ι n))).obj.obj (op U)) :
    (((lisseIntegralScalarExtension l E Y L ι).obj F).obj.map
      (homOfLE h).op).hom.app (op U) (lisseScalarGenerator l E Y L ι F n U 1 x) =
      lisseScalarGenerator l E Y L ι F m U 1
        ((F.obj.map (homOfLE (lisseCoherence_scalarIndex_mono l E L ι h)).op).hom.app (op U) x) :=
          by
  let evR : Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⥤ Type (u + 1) :=
    sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op U) ⋙ CategoryTheory.forget _
  let evS : Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l L)) ⥤ Type (u + 1) :=
    sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op U) ⋙ CategoryTheory.forget _
  have mono : Monotone (lisseScalarSourceIndex l E L ι) := by
    intro a b h
    exact lisseCoherence_scalarIndex_mono l E L ι h
  let A := mono.functor.op ⋙ F.obj ⋙ evR
  let B := ((lisseIntegralScalarExtension l E Y L ι).obj F).obj ⋙ evS
  exact lisseCoherence_sequenceGenerator_naturality (A := A) (B := B)
    (fun n x ↦ lisseScalarGenerator l E Y L ι F n U 1 x)
    (fun n x ↦ by
      dsimp only [A, B, evR, evS]
      change (((lisseIntegralScalarExtension l E Y L ι).obj F).obj.map
        (homOfLE (Nat.le_succ n)).op).hom.app (op U)
          (lisseScalarGenerator l E Y L ι F (n + 1) U 1 x) =
        lisseScalarGenerator l E Y L ι F n U 1
          ((F.obj.map (homOfLE (lisseScalarSourceIndex_le l E L ι n)).op).hom.app (op U) x)
      erw [lisseCoherence_extendedGenerator_transition, map_one])
    m n h x

attribute [local irreducible] lisseIntegralScalarExtension lisseScalarLevelIso
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionMaximalIdeal
  Padic.coefficientExtensionAbsoluteValue

section IntegralScalarComposition

variable (M : Type (u + 1)) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (κ : L →ₐ[ℚ_[l]] M)

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarCompositeIndexIso (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    F.obj.obj (op (lisseScalarSourceIndex l E M (κ.comp ι) m)) ≅
      F.obj.obj (op (lisseScalarSourceIndex l E L ι
        (lisseScalarSourceIndex l L M κ m))) :=
  eqToIso (congrArg (fun n ↦ F.obj.obj (op n)) (lisseScalarSourceIndex_comp l E L ι M κ m).symm)

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarCompositeCoefficient (m : ℕ) :
    (lisseCoherence_scalarCoefficientFactor l L M κ m).comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L
        (lisseScalarSourceIndex l L M κ m + 1))).comp (lisseIntegerInclusion l E L ι)) =
        lisseScalarCoefficientMap l E M (κ.comp ι) m := by
  rw [← RingHom.comp_assoc, lisseCoherence_scalarCoefficientFactor_comp]
  change (Ideal.Quotient.mk _).comp
    ((lisseIntegerInclusion l L M κ).comp (lisseIntegerInclusion l E L ι)) = _
  rw [← lisseCoherence_integerInclusion_comp]
  rfl

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarCompositeRawIso (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    lisseIntegralScalarLevel l E Y M (κ.comp ι) F m ≅
      lisseIntegralScalarLevel l L Y M κ
        ((lisseIntegralScalarExtension l E Y L ι).obj F) m :=
  lisseCoherence_scalarTransportIso Y (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l M (m +
    1)))
    (lisseIntegerInclusion l E L ι)
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L
      (lisseScalarSourceIndex l L M κ m + 1))) Ideal.Quotient.mk_surjective
    (lisseCoherence_scalarCoefficientFactor l L M κ m) (lisseScalarCoefficientMap l E M (κ.comp ι)
      m)
    (lisseScalarCoefficientMap l L M κ m) (lisseCoherence_scalarCompositeCoefficient l E L ι M κ m)
    (lisseCoherence_scalarCoefficientFactor_comp l L M κ m)
    (lisseScalarCoefficientMap l E L ι (lisseScalarSourceIndex l L M κ m)) rfl _ _
    (lisseCoherence_scalarCompositeIndexIso l E Y L ι M κ F m) _
    (lisseScalarLevelIso l E Y L ι F (lisseScalarSourceIndex l L M κ m))

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarCompositeRawIso_generator (F : LisseIntegralSheaf l E Y) (m : ℕ)
    (U : Y.Etale)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E M (κ.comp ι) m))).obj.obj (op U)) :
    (lisseCoherence_scalarCompositeRawIso l E Y L ι M κ F m).hom.hom.app (op U)
      (lisseIntegralScalarGenerator l E Y M (κ.comp ι) F m U 1 x) =
        lisseIntegralScalarGenerator l L Y M κ
          ((lisseIntegralScalarExtension l E Y L ι).obj F) m U 1
          (lisseScalarGenerator l E Y L ι F (lisseScalarSourceIndex l L M κ m) U 1
            ((lisseCoherence_scalarCompositeIndexIso l E Y L ι M κ F m).hom.hom.app (op U) x)) := by
  simp only [lisseScalarGenerator, lisseCoherence_rawGenerator_one]
  have h := lisseCoherence_scalarTransportIso_unit
    (R := Padic.coefficientExtensionIntegers l E)
    (S := Padic.coefficientExtensionIntegers l L)
    (T := Padic.coefficientExtensionRing l M (m + 1)) Y
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l M (m + 1)))
    (lisseIntegerInclusion l E L ι)
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L
      (lisseScalarSourceIndex l L M κ m + 1))) Ideal.Quotient.mk_surjective
    (lisseCoherence_scalarCoefficientFactor l L M κ m) (lisseScalarCoefficientMap l E M (κ.comp ι)
      m)
    (lisseScalarCoefficientMap l L M κ m) (lisseCoherence_scalarCompositeCoefficient l E L ι M κ m)
    (lisseCoherence_scalarCoefficientFactor_comp l L M κ m)
    (lisseScalarCoefficientMap l E L ι (lisseScalarSourceIndex l L M κ m)) rfl _ _
    (lisseCoherence_scalarCompositeIndexIso l E Y L ι M κ F m) _
    (lisseScalarLevelIso l E Y L ι F (lisseScalarSourceIndex l L M κ m))
  dsimp only [lisseCoherence_scalarCompositeRawIso] at h ⊢
  exact h U x

attribute [local irreducible] lisseCoherence_scalarCompositeRawIso

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarCompositeLevelIso (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    ((lisseIntegralScalarExtension l E Y M (κ.comp ι)).obj F).obj.obj (op m) ≅
      ((lisseIntegralScalarExtension l L Y M κ).obj
        ((lisseIntegralScalarExtension l E Y L ι).obj F)).obj.obj (op m) :=
  (lisseCoherence_sheafIso_conjugateWithFormula Y
    (lisseScalarLevelIso l E Y M (κ.comp ι) F m)
    (lisseCoherence_scalarCompositeRawIso l E Y L ι M κ F m)
    (lisseScalarLevelIso l L Y M κ
      ((lisseIntegralScalarExtension l E Y L ι).obj F) m)).val

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarCompositeLevelIso_generator (F : LisseIntegralSheaf l E Y)
    (m : ℕ) (U : Y.Etale)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E M (κ.comp ι) m))).obj.obj (op U)) :
    (lisseCoherence_scalarCompositeLevelIso l E Y L ι M κ F m).hom.hom.app (op U)
      (lisseScalarGenerator l E Y M (κ.comp ι) F m U 1 x) =
        lisseScalarGenerator l L Y M κ
          ((lisseIntegralScalarExtension l E Y L ι).obj F) m U 1
          (lisseScalarGenerator l E Y L ι F (lisseScalarSourceIndex l L M κ m) U 1
            ((lisseCoherence_scalarCompositeIndexIso l E Y L ι M κ F m).hom.hom.app (op U) x)) := by
  have h := (lisseCoherence_sheafIso_conjugateWithFormula Y
    (lisseScalarLevelIso l E Y M (κ.comp ι) F m)
    (lisseCoherence_scalarCompositeRawIso l E Y L ι M κ F m)
    (lisseScalarLevelIso l L Y M κ
      ((lisseIntegralScalarExtension l E Y L ι).obj F) m)).property U _ _
    (lisseCoherence_scalarCompositeRawIso_generator l E Y L ι M κ F m U x)
  delta lisseScalarGenerator
  exact h

attribute [local irreducible] lisseCoherence_scalarCompositeLevelIso

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarCompositeLevel_naturality (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    ((lisseIntegralScalarExtension l E Y M (κ.comp ι)).obj F).obj.map
        (homOfLE (Nat.le_succ m)).op ≫ (lisseCoherence_scalarCompositeLevelIso l E Y L ι M κ F
          m).hom =
      (lisseCoherence_scalarCompositeLevelIso l E Y L ι M κ F (m + 1)).hom ≫
        ((lisseIntegralScalarExtension l L Y M κ).obj
          ((lisseIntegralScalarExtension l E Y L ι).obj F)).obj.map
            (homOfLE (Nat.le_succ m)).op := by
  let H := (lisseIntegralScalarExtension l L Y M κ).obj
    ((lisseIntegralScalarExtension l E Y L ι).obj F)
  apply lisseCoherence_chosenScalarLevel_ext l E Y M (κ.comp ι) F (m + 1) (H.obj.obj (op m))
    (lisseCoherence_integralLevel_annihilated_le l M Y H m (m + 1) (Nat.le_succ m))
  intro U x
  change (lisseCoherence_scalarCompositeLevelIso l E Y L ι M κ F m).hom.hom.app (op U)
      ((((lisseIntegralScalarExtension l E Y M (κ.comp ι)).obj F).obj.map
        (homOfLE (Nat.le_succ m)).op).hom.app (op U)
          (lisseScalarGenerator l E Y M (κ.comp ι) F (m + 1) U 1 x)) =
    (H.obj.map (homOfLE (Nat.le_succ m)).op).hom.app (op U)
      ((lisseCoherence_scalarCompositeLevelIso l E Y L ι M κ F (m + 1)).hom.hom.app (op U)
        (lisseScalarGenerator l E Y M (κ.comp ι) F (m + 1) U 1 x))
  rw [lisseCoherence_extendedGenerator_transition, map_one,
    lisseCoherence_scalarCompositeLevelIso_generator,
    lisseCoherence_scalarCompositeLevelIso_generator, lisseCoherence_extendedGenerator_transition,
      map_one,
    lisseCoherence_extendedGenerator_transition_le]
  apply congrArg (lisseScalarGenerator l L Y M κ
    ((lisseIntegralScalarExtension l E Y L ι).obj F) m U 1)
  apply congrArg (lisseScalarGenerator l E Y L ι F (lisseScalarSourceIndex l L M κ m) U 1)
  exact congrArg (fun v ↦ v.hom.app (op U) x)
    (lisseCoherence_sequenceCast_naturality F.obj (lisseScalarSourceIndex_comp l E L ι M κ m).symm
      (lisseScalarSourceIndex_comp l E L ι M κ (m + 1)).symm
      (lisseScalarSourceIndex_le l E M (κ.comp ι) m)
      (lisseCoherence_scalarIndex_mono l E L ι (lisseScalarSourceIndex_le l L M κ m)))

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarCompositeObjectIso (F : LisseIntegralSheaf l E Y) :
    (lisseIntegralScalarExtension l E Y M (κ.comp ι)).obj F ≅
      (lisseIntegralScalarExtension l L Y M κ).obj
        ((lisseIntegralScalarExtension l E Y L ι).obj F) := by
  let v := NatTrans.ofOpSequence (fun m ↦ (lisseCoherence_scalarCompositeLevelIso l E Y L ι M κ F
    m).hom)
    (lisseCoherence_scalarCompositeLevel_naturality l E Y L ι M κ F)
  exact ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun m ↦ lisseCoherence_scalarCompositeLevelIso l E Y L ι M κ F m.unop) (fun f ↦ v.naturality
      f))

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarCompositeObjectIso_naturality {F G : LisseIntegralSheaf l E Y}
    (v : F ⟶ G) :
    (lisseIntegralScalarExtension l E Y M (κ.comp ι)).map v ≫
        (lisseCoherence_scalarCompositeObjectIso l E Y L ι M κ G).hom =
      (lisseCoherence_scalarCompositeObjectIso l E Y L ι M κ F).hom ≫
        (lisseIntegralScalarExtension l E Y L ι ⋙
          lisseIntegralScalarExtension l L Y M κ).map v := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext m
  let H := (lisseIntegralScalarExtension l L Y M κ).obj
    ((lisseIntegralScalarExtension l E Y L ι).obj G)
  apply lisseCoherence_chosenScalarLevel_ext l E Y M (κ.comp ι) F m.unop (H.obj.obj m)
    (lisseCoherence_integralLevel_annihilated l M Y H m.unop)
  intro U x
  change (lisseCoherence_scalarCompositeLevelIso l E Y L ι M κ G m.unop).hom.hom.app (op U)
      ((((lisseIntegralScalarExtension l E Y M (κ.comp ι)).map v).hom.app m).hom.app
        (op U) (lisseScalarGenerator l E Y M (κ.comp ι) F m.unop U 1 x)) =
    ((((lisseIntegralScalarExtension l L Y M κ).map
      ((lisseIntegralScalarExtension l E Y L ι).map v)).hom.app m).hom.app (op U))
      ((lisseCoherence_scalarCompositeLevelIso l E Y L ι M κ F m.unop).hom.hom.app (op U)
        (lisseScalarGenerator l E Y M (κ.comp ι) F m.unop U 1 x))
  rw [lisseScalarGenerator_map, lisseCoherence_scalarCompositeLevelIso_generator,
    lisseCoherence_scalarCompositeLevelIso_generator, lisseScalarGenerator_map,
      lisseScalarGenerator_map]
  apply congrArg (lisseScalarGenerator l L Y M κ
    ((lisseIntegralScalarExtension l E Y L ι).obj G) m.unop U 1)
  apply congrArg (lisseScalarGenerator l E Y L ι G
    (lisseScalarSourceIndex l L M κ m.unop) U 1)
  exact congrArg (fun v ↦ v.hom.app (op U) x)
    (lisseCoherence_natTrans_index_cast v.hom (lisseScalarSourceIndex_comp l E L ι M κ m.unop).symm)

/-- The canonical integral comparison for two successive coefficient extensions. -/
@[irreducible]
def lisseIntegralScalarCompositeIso :
    lisseIntegralScalarExtension l E Y M (κ.comp ι) ≅
      lisseIntegralScalarExtension l E Y L ι ⋙ lisseIntegralScalarExtension l L Y M κ :=
  NatIso.ofComponents (lisseCoherence_scalarCompositeObjectIso l E Y L ι M κ)
    (fun v ↦ lisseCoherence_scalarCompositeObjectIso_naturality l E Y L ι M κ v)

attribute [local semireducible] lisseIntegralScalarCompositeIso

private theorem scalarCompositeFunctorIso_generator (F : LisseIntegralSheaf l E Y)
    (m : ℕ) (U : Y.Etale)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E M (κ.comp ι) m))).obj.obj (op U)) :
    (((lisseIntegralScalarCompositeIso l E Y L ι M κ).hom.app F).hom.app (op m)).hom.app (op U)
      (lisseScalarGenerator l E Y M (κ.comp ι) F m U 1 x) =
        lisseScalarGenerator l L Y M κ
          ((lisseIntegralScalarExtension l E Y L ι).obj F) m U 1
          (lisseScalarGenerator l E Y L ι F (lisseScalarSourceIndex l L M κ m) U 1
            ((lisseCoherence_scalarCompositeIndexIso l E Y L ι M κ F m).hom.hom.app (op U) x)) :=
  lisseCoherence_scalarCompositeLevelIso_generator l E Y L ι M κ F m U x

attribute [local irreducible] lisseIntegralScalarCompositeIso

end IntegralScalarComposition

attribute [local irreducible] lisseCoherence_scalarCompositeRawIso
  lisseCoherence_scalarCompositeLevelIso

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarIdentityIndexIso (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    F.obj.obj (op (lisseScalarSourceIndex l E E (AlgHom.id ℚ_[l] E) m)) ≅
      F.obj.obj (op m) :=
  eqToIso (congrArg (fun n ↦ F.obj.obj (op n)) (lisseScalarSourceIndex_id l E m))

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarIdentityRawIso (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    lisseIntegralScalarLevel l E Y E (AlgHom.id ℚ_[l] E) F m ≅ F.obj.obj (op m) := by
  let I := Padic.coefficientExtensionIdeal l E (m + 1)
  let q := Ideal.Quotient.mk I
  have hq : lisseScalarCoefficientMap l E E (AlgHom.id ℚ_[l] E) m = q := by
    simp only [lisseScalarCoefficientMap, lisseCoherence_integerInclusion_id, RingHom.comp_id, q, I]
  have := lisseCoherence_quotientSheafUnit_isIso Y I (F.obj.obj (op m))
    (lisseCoherence_integralLevel_annihilated l E Y F m)
  exact lisseCoherence_scalarIdentityTransportIso Y q _ hq _ _
    (lisseCoherence_scalarIdentityIndexIso l E Y F m)

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarIdentityLevelIso (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    ((lisseIntegralScalarExtension l E Y E (AlgHom.id ℚ_[l] E)).obj F).obj.obj (op m) ≅
      F.obj.obj (op m) :=
  (lisseCoherence_sheafIso_conjugateWithFormula Y
    (lisseScalarLevelIso l E Y E (AlgHom.id ℚ_[l] E) F m)
    (lisseCoherence_scalarIdentityRawIso l E Y F m) (Iso.refl _)).val

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarIdentityRawIso_generator (F : LisseIntegralSheaf l E Y)
    (m : ℕ) (U : Y.Etale)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E E (AlgHom.id ℚ_[l] E) m))).obj.obj (op U)) :
    (lisseCoherence_scalarIdentityRawIso l E Y F m).hom.hom.app (op U)
      (lisseIntegralScalarGenerator l E Y E (AlgHom.id ℚ_[l] E) F m U 1 x) =
        (lisseCoherence_scalarIdentityIndexIso l E Y F m).hom.hom.app (op U) x := by
  simp only [lisseCoherence_rawGenerator_one]
  have hq : lisseScalarCoefficientMap l E E (AlgHom.id ℚ_[l] E) m =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (m + 1)) := by
    simp only [lisseScalarCoefficientMap, lisseCoherence_integerInclusion_id, RingHom.comp_id]
  have := lisseCoherence_quotientSheafUnit_isIso Y (Padic.coefficientExtensionIdeal l E (m + 1))
    (F.obj.obj (op m)) (lisseCoherence_integralLevel_annihilated l E Y F m)
  exact lisseCoherence_scalarIdentityTransportIso_unit Y
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (m + 1))) _ hq _ _
    (lisseCoherence_scalarIdentityIndexIso l E Y F m) U x

attribute [local irreducible] lisseCoherence_scalarIdentityRawIso

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarIdentityLevelIso_generator (F : LisseIntegralSheaf l E Y)
    (m : ℕ) (U : Y.Etale)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E E (AlgHom.id ℚ_[l] E) m))).obj.obj (op U)) :
    (lisseCoherence_scalarIdentityLevelIso l E Y F m).hom.hom.app (op U)
      (lisseScalarGenerator l E Y E (AlgHom.id ℚ_[l] E) F m U 1 x) =
        (lisseCoherence_scalarIdentityIndexIso l E Y F m).hom.hom.app (op U) x := by
  have h := (lisseCoherence_sheafIso_conjugateWithFormula Y
    (lisseScalarLevelIso l E Y E (AlgHom.id ℚ_[l] E) F m)
    (lisseCoherence_scalarIdentityRawIso l E Y F m) (Iso.refl _)).property U _ _
      (lisseCoherence_scalarIdentityRawIso_generator l E Y F m U x)
  delta lisseScalarGenerator
  exact h

attribute [local irreducible] lisseCoherence_scalarIdentityLevelIso

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarIdentityLevel_naturality (F : LisseIntegralSheaf l E Y) (m : ℕ) :
    ((lisseIntegralScalarExtension l E Y E (AlgHom.id ℚ_[l] E)).obj F).obj.map
        (homOfLE (Nat.le_succ m)).op ≫ (lisseCoherence_scalarIdentityLevelIso l E Y F m).hom =
      (lisseCoherence_scalarIdentityLevelIso l E Y F (m + 1)).hom ≫
        F.obj.map (homOfLE (Nat.le_succ m)).op := by
  apply lisseCoherence_chosenScalarLevel_ext l E Y E (AlgHom.id ℚ_[l] E) F (m + 1)
    (F.obj.obj (op m)) (lisseCoherence_integralLevel_annihilated_le l E Y F m (m + 1) (Nat.le_succ
      m))
  intro U x
  change (lisseCoherence_scalarIdentityLevelIso l E Y F m).hom.hom.app (op U)
      ((((lisseIntegralScalarExtension l E Y E (AlgHom.id ℚ_[l] E)).obj F).obj.map
        (homOfLE (Nat.le_succ m)).op).hom.app (op U)
          (lisseScalarGenerator l E Y E (AlgHom.id ℚ_[l] E) F (m + 1) U 1 x)) =
    (F.obj.map (homOfLE (Nat.le_succ m)).op).hom.app (op U)
      ((lisseCoherence_scalarIdentityLevelIso l E Y F (m + 1)).hom.hom.app (op U)
        (lisseScalarGenerator l E Y E (AlgHom.id ℚ_[l] E) F (m + 1) U 1 x))
  rw [lisseCoherence_extendedGenerator_transition, map_one,
    lisseCoherence_scalarIdentityLevelIso_generator,
    lisseCoherence_scalarIdentityLevelIso_generator]
  exact congrArg (fun v ↦ v.hom.app (op U) x)
    (lisseCoherence_sequenceCast_naturality F.obj (lisseScalarSourceIndex_id l E m)
      (lisseScalarSourceIndex_id l E (m + 1))
      (lisseScalarSourceIndex_le l E E (AlgHom.id ℚ_[l] E) m) (Nat.le_succ m))

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_scalarIdentityObjectIso (F : LisseIntegralSheaf l E Y) :
    (lisseIntegralScalarExtension l E Y E (AlgHom.id ℚ_[l] E)).obj F ≅ F := by
  let v := NatTrans.ofOpSequence (fun m ↦ (lisseCoherence_scalarIdentityLevelIso l E Y F m).hom)
    (lisseCoherence_scalarIdentityLevel_naturality l E Y F)
  exact ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun m ↦ lisseCoherence_scalarIdentityLevelIso l E Y F m.unop) (fun f ↦ v.naturality f))

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_scalarIdentityObjectIso_naturality {F G : LisseIntegralSheaf l E Y}
    (v : F ⟶ G) :
    (lisseIntegralScalarExtension l E Y E (AlgHom.id ℚ_[l] E)).map v ≫
        (lisseCoherence_scalarIdentityObjectIso l E Y G).hom =
      (lisseCoherence_scalarIdentityObjectIso l E Y F).hom ≫ v := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext m
  apply lisseCoherence_chosenScalarLevel_ext l E Y E (AlgHom.id ℚ_[l] E) F m.unop
    (G.obj.obj m) (lisseCoherence_integralLevel_annihilated l E Y G m.unop)
  intro U x
  change (lisseCoherence_scalarIdentityLevelIso l E Y G m.unop).hom.hom.app (op U)
      ((((lisseIntegralScalarExtension l E Y E (AlgHom.id ℚ_[l] E)).map v).hom.app m).hom.app
        (op U) (lisseScalarGenerator l E Y E (AlgHom.id ℚ_[l] E) F m.unop U 1 x)) =
    (v.hom.app m).hom.app (op U)
      ((lisseCoherence_scalarIdentityLevelIso l E Y F m.unop).hom.hom.app (op U)
        (lisseScalarGenerator l E Y E (AlgHom.id ℚ_[l] E) F m.unop U 1 x))
  rw [lisseScalarGenerator_map, lisseCoherence_scalarIdentityLevelIso_generator,
    lisseCoherence_scalarIdentityLevelIso_generator]
  exact congrArg (fun v ↦ v.hom.app (op U) x)
    (lisseCoherence_natTrans_index_cast v.hom (lisseScalarSourceIndex_id l E m.unop))

/-- The canonical integral comparison for identity coefficient extension. -/
@[irreducible]
def lisseIntegralScalarIdentityIso :
    lisseIntegralScalarExtension l E Y E (AlgHom.id ℚ_[l] E) ≅ 𝟭 _ :=
  NatIso.ofComponents (lisseCoherence_scalarIdentityObjectIso l E Y)
    (fun v ↦ lisseCoherence_scalarIdentityObjectIso_naturality l E Y v)

attribute [local semireducible] lisseIntegralScalarIdentityIso

private theorem scalarIdentityFunctorIso_generator (F : LisseIntegralSheaf l E Y)
    (m : ℕ) (U : Y.Etale)
    (x : (F.obj.obj (op (lisseScalarSourceIndex l E E (AlgHom.id ℚ_[l] E) m))).obj.obj (op U)) :
    (((lisseIntegralScalarIdentityIso l E Y).hom.app F).hom.app (op m)).hom.app (op U)
      (lisseScalarGenerator l E Y E (AlgHom.id ℚ_[l] E) F m U 1 x) =
        (lisseCoherence_scalarIdentityIndexIso l E Y F m).hom.hom.app (op U) x :=
  lisseCoherence_scalarIdentityLevelIso_generator l E Y F m U x

section IntegralScalarCoherence

variable (M : Type (u + 1)) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (κ : L →ₐ[ℚ_[l]] M)
    (N : Type (u + 1)) [Field N] [Algebra ℚ_[l] N] [FiniteDimensional ℚ_[l] N]
    (μ : M →ₐ[ℚ_[l]] N)

set_option backward.isDefEq.respectTransparency false in
private theorem scalarComposite_assoc (F : LisseIntegralSheaf l E Y) :
    (lisseIntegralScalarCompositeIso l E Y M (κ.comp ι) N μ).hom.app F ≫
        (lisseIntegralScalarExtension l M Y N μ).map
          ((lisseIntegralScalarCompositeIso l E Y L ι M κ).hom.app F) =
      (lisseIntegralScalarCompositeIso l E Y L ι N (μ.comp κ)).hom.app F ≫
        (lisseIntegralScalarCompositeIso l L Y M κ N μ).hom.app
          ((lisseIntegralScalarExtension l E Y L ι).obj F) := by
  apply lisseScalarHom_ext l E Y N ((μ.comp κ).comp ι) F
  intro m U x
  change (((lisseIntegralScalarExtension l M Y N μ).map
      ((lisseIntegralScalarCompositeIso l E Y L ι M κ).hom.app F)).hom.app (op m)).hom.app (op U)
    ((((lisseIntegralScalarCompositeIso l E Y M (κ.comp ι) N μ).hom.app F).hom.app
      (op m)).hom.app (op U) (lisseScalarGenerator l E Y N ((μ.comp κ).comp ι) F m U 1 x)) =
    (((lisseIntegralScalarCompositeIso l L Y M κ N μ).hom.app
      ((lisseIntegralScalarExtension l E Y L ι).obj F)).hom.app (op m)).hom.app (op U)
      ((((lisseIntegralScalarCompositeIso l E Y L ι N (μ.comp κ)).hom.app F).hom.app
        (op m)).hom.app (op U) (lisseScalarGenerator l E Y N ((μ.comp κ).comp ι) F m U 1 x))
  erw [scalarCompositeFunctorIso_generator, lisseScalarGenerator_map,
    scalarCompositeFunctorIso_generator, scalarCompositeFunctorIso_generator,
    scalarCompositeFunctorIso_generator]
  simp only [lisseCoherence_scalarCompositeIndexIso, eqToIso.hom]
  erw [lisseScalarGenerator_cast l E Y L ι F _ _
    (lisseScalarSourceIndex_comp l L M κ N μ m).symm]
  apply congrArg (lisseScalarGenerator l M Y N μ
    ((lisseIntegralScalarExtension l L Y M κ).obj
      ((lisseIntegralScalarExtension l E Y L ι).obj F)) m U 1)
  apply congrArg (lisseScalarGenerator l L Y M κ
    ((lisseIntegralScalarExtension l E Y L ι).obj F)
    (lisseScalarSourceIndex l M N μ m) U 1)
  apply congrArg (lisseScalarGenerator l E Y L ι F
    (lisseScalarSourceIndex l L M κ (lisseScalarSourceIndex l M N μ m)) U 1)
  rw [← lisseCoherence_sheaf_comp_apply (R := Padic.coefficientExtensionIntegers l E),
    ← lisseCoherence_sheaf_comp_apply (R := Padic.coefficientExtensionIntegers l E)]
  simp only [eqToHom_trans]
  rfl

end IntegralScalarCoherence

set_option backward.isDefEq.respectTransparency false in
private theorem scalarComposite_left_unit (F : LisseIntegralSheaf l E Y) :
    (lisseIntegralScalarCompositeIso l E Y E (AlgHom.id ℚ_[l] E) L ι).hom.app F ≫
        (lisseIntegralScalarExtension l E Y L ι).map
          ((lisseIntegralScalarIdentityIso l E Y).hom.app F) =
      𝟙 ((lisseIntegralScalarExtension l E Y L ι).obj F) := by
  apply lisseScalarHom_ext l E Y L ι F
  intro m U x
  change (((lisseIntegralScalarExtension l E Y L ι).map
      ((lisseIntegralScalarIdentityIso l E Y).hom.app F)).hom.app (op m)).hom.app (op U)
    ((((lisseIntegralScalarCompositeIso l E Y E (AlgHom.id ℚ_[l] E) L ι).hom.app F).hom.app
      (op m)).hom.app (op U) (lisseScalarGenerator l E Y L ι F m U 1 x)) =
        lisseScalarGenerator l E Y L ι F m U 1 x
  erw [scalarCompositeFunctorIso_generator, lisseScalarGenerator_map,
    scalarIdentityFunctorIso_generator]
  congr 1
  simp only [lisseCoherence_scalarCompositeIndexIso, lisseCoherence_scalarIdentityIndexIso,
    eqToIso.hom]
  rw [← lisseCoherence_sheaf_comp_apply (R := Padic.coefficientExtensionIntegers l E)]
  simp only [eqToHom_trans, eqToHom_refl, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem scalarComposite_right_unit (F : LisseIntegralSheaf l E Y) :
    (lisseIntegralScalarCompositeIso l E Y L ι L (AlgHom.id ℚ_[l] L)).hom.app F ≫
        (lisseIntegralScalarIdentityIso l L Y).hom.app
          ((lisseIntegralScalarExtension l E Y L ι).obj F) =
      𝟙 ((lisseIntegralScalarExtension l E Y L ι).obj F) := by
  apply lisseScalarHom_ext l E Y L ι F
  intro m U x
  change (((lisseIntegralScalarIdentityIso l L Y).hom.app
      ((lisseIntegralScalarExtension l E Y L ι).obj F)).hom.app (op m)).hom.app (op U)
    ((((lisseIntegralScalarCompositeIso l E Y L ι L (AlgHom.id ℚ_[l] L)).hom.app F).hom.app
      (op m)).hom.app (op U) (lisseScalarGenerator l E Y L ι F m U 1 x)) =
        lisseScalarGenerator l E Y L ι F m U 1 x
  erw [scalarCompositeFunctorIso_generator, scalarIdentityFunctorIso_generator]
  simp only [lisseCoherence_scalarIdentityIndexIso, eqToIso.hom]
  erw [lisseScalarGenerator_cast l E Y L ι F _ _ (lisseScalarSourceIndex_id l L m)]
  apply congrArg (lisseScalarGenerator l E Y L ι F m U 1)
  simp only [lisseCoherence_scalarCompositeIndexIso, eqToIso.hom]
  rw [← lisseCoherence_sheaf_comp_apply (R := Padic.coefficientExtensionIntegers l E)]
  simp only [eqToHom_trans, eqToHom_refl, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app]
  rfl

private theorem rationalHom_add_comp (F G H : LisseRationalSheaf l E Y)
    (f f' : F ⟶ G) (g : G ⟶ H) : (f + f') ≫ g = f ≫ g + f' ≫ g := by
  exact congrArg (fun t : lisseRationalHom l E Y G H →ₗ[E]
      lisseRationalHom l E Y F H ↦ t g)
    (((lisseRationalComposition l E Y).comp F G H).map_add f f')

private theorem rationalHom_comp_add (F G H : LisseRationalSheaf l E Y)
    (f : F ⟶ G) (g g' : G ⟶ H) : f ≫ (g + g') = f ≫ g + f ≫ g' := by
  exact ((lisseRationalComposition l E Y).comp F G H f).map_add g g'

@[instance_reducible]
private def rationalPreadditive : Preadditive (LisseRationalSheaf l E Y) where
  homGroup := lisseRationalHomAddCommGroup l E Y
  add_comp := rationalHom_add_comp l E Y
  comp_add := rationalHom_comp_add l E Y

attribute [local instance] rationalPreadditive

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_rational_tmul_comp (F G H : LisseRationalSheaf l E Y)
    (a b : E) (f : F.integral ⟶ G.integral) (g : G.integral ⟶ H.integral) :
    ((TensorProduct.tmul (Padic.coefficientExtensionIntegers l E) a f : F ⟶ G) ≫
      (TensorProduct.tmul (Padic.coefficientExtensionIntegers l E) b g : G ⟶ H) : F ⟶ H) =
        (TensorProduct.tmul (Padic.coefficientExtensionIntegers l E) (a * b) (f ≫ g) :
          F ⟶ H) :=
  (lisseRationalComposition l E Y).comp_tmul F G H a b f g

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_rationalizeIsoRaw (F G : LisseRationalSheaf l E Y) (e : F.integral ≅
  G.integral) :
    F ≅ G where
  hom := TensorProduct.tmul _ 1 e.hom
  inv := TensorProduct.tmul _ 1 e.inv
  hom_inv_id := by
    change (lisseRationalComposition l E Y).comp F G F
      (TensorProduct.tmul _ 1 e.hom) (TensorProduct.tmul _ 1 e.inv) = _
    rw [(lisseRationalComposition l E Y).comp_tmul, one_mul, e.hom_inv_id]
    rfl
  inv_hom_id := by
    change (lisseRationalComposition l E Y).comp G F G
      (TensorProduct.tmul _ 1 e.inv) (TensorProduct.tmul _ 1 e.hom) = _
    rw [(lisseRationalComposition l E Y).comp_tmul, one_mul, e.inv_hom_id]
    rfl

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_rationalScalar_map_tmul (F G : LisseRationalSheaf l E Y)
    (a : E) (f : F.integral ⟶ G.integral) :
    (lisseRationalScalarExtension l E Y L ι).map (TensorProduct.tmul _ a f) =
      TensorProduct.tmul _ (ι a) ((lisseIntegralScalarExtension l E Y L ι).map f) :=
  (lisseRationalScalarExtensionData l E Y L ι).map_tmul F G a f

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_rationalScalar_map_add (F G : LisseRationalSheaf l E Y)
    (f g : F ⟶ G) :
    (lisseRationalScalarExtension l E Y L ι).map (f + g) =
      (lisseRationalScalarExtension l E Y L ι).map f +
        (lisseRationalScalarExtension l E Y L ι).map g :=
  (lisseRationalScalarExtensionData l E Y L ι).map_add F G f g

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_rationalScalar_map_zero (F G : LisseRationalSheaf l E Y) :
    (lisseRationalScalarExtension l E Y L ι).map (0 : F ⟶ G) = 0 := by
  have h := lisseCoherence_rationalScalar_map_add l E Y L ι F G 0 0
  rw [zero_add] at h
  exact add_eq_left.mp h.symm

private theorem rationalComparison_square
    (X Z : LisseRationalSheaf l L Y) (F G : LisseRationalSheaf l E Y)
    (a : X.integral ⟶ (lisseIntegralScalarExtension l E Y L ι).obj F.integral)
    (b : F.integral ⟶ G.integral) (c : X.integral ⟶ Z.integral)
    (d : Z.integral ⟶ (lisseIntegralScalarExtension l E Y L ι).obj G.integral)
    (h : a ≫ (lisseIntegralScalarExtension l E Y L ι).map b = c ≫ d) :
    ((TensorProduct.tmul (Padic.coefficientExtensionIntegers l L) 1 a :
      X ⟶ (lisseRationalScalarExtension l E Y L ι).obj F) ≫
      (lisseRationalScalarExtension l E Y L ι).map
        (TensorProduct.tmul (Padic.coefficientExtensionIntegers l E) 1 b : F ⟶ G) :
      X ⟶ (lisseRationalScalarExtension l E Y L ι).obj G) =
    ((TensorProduct.tmul (Padic.coefficientExtensionIntegers l L) 1 c : X ⟶ Z) ≫
      (TensorProduct.tmul (Padic.coefficientExtensionIntegers l L) 1 d :
        Z ⟶ (lisseRationalScalarExtension l E Y L ι).obj G) :
      X ⟶ (lisseRationalScalarExtension l E Y L ι).obj G) := by
  erw [lisseCoherence_rationalScalar_map_tmul l E Y L ι F G 1 b, map_one,
    lisseCoherence_rational_tmul_comp, lisseCoherence_rational_tmul_comp, one_mul]
  exact congrArg (fun f ↦ TensorProduct.tmul (Padic.coefficientExtensionIntegers l L) (1 : L) f) h

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_tensor_intertwining_map
    {R A S B M P Q U W V : Type*}
    [CommRing R] [Field A] [Algebra R A]
    [CommRing S] [Field B] [Algebra S B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup P] [AddCommGroup Q] [AddCommGroup U]
    [AddCommGroup W] [AddCommGroup V]
    [Module S P] [Module S Q] [Module S U] [Module S W] [Module S V]
    (c : TensorProduct S B P →ₗ[B]
      TensorProduct S B U →ₗ[B] TensorProduct S B V)
    (d : TensorProduct S B W →ₗ[B]
      TensorProduct S B Q →ₗ[B] TensorProduct S B V)
    (m : M → P) (n : M → Q) (c₀ : P → U → V) (d₀ : W → Q → V)
    (ψ : A →+* B)
    (f : TensorProduct R A M →+ TensorProduct S B P)
    (g : TensorProduct R A M →+ TensorProduct S B Q)
    (hc : ∀ a b x y, c (TensorProduct.tmul S a x) (TensorProduct.tmul S b y) =
      TensorProduct.tmul S (a * b) (c₀ x y))
    (hd : ∀ a b x y, d (TensorProduct.tmul S a x) (TensorProduct.tmul S b y) =
      TensorProduct.tmul S (a * b) (d₀ x y))
    (hf : ∀ a x, f (TensorProduct.tmul R a x) = TensorProduct.tmul S (ψ a) (m x))
    (hg : ∀ a x, g (TensorProduct.tmul R a x) = TensorProduct.tmul S (ψ a) (n x))
    (u : U) (w : W) (hp : ∀ x, c₀ (m x) u = d₀ w (n x))
    (x : TensorProduct R A M) :
    c (f x) (TensorProduct.tmul S 1 u) =
      d (TensorProduct.tmul S 1 w) (g x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a x =>
    rw [hf, hg, hc, hd, mul_one, one_mul]
    exact congrArg (fun v ↦ TensorProduct.tmul S (ψ a) v) (hp x)

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_rationalScalarAddHom (F G : LisseRationalSheaf l E Y) :
    (F ⟶ G) →+ ((lisseRationalScalarExtension l E Y L ι).obj F ⟶
      (lisseRationalScalarExtension l E Y L ι).obj G) where
  toFun := (lisseRationalScalarExtension l E Y L ι).map
  map_zero' := lisseCoherence_rationalScalar_map_zero l E Y L ι F G
  map_add' := lisseCoherence_rationalScalar_map_add l E Y L ι F G

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_rationalScalarIdentityIsoRaw
    (e : lisseIntegralScalarExtension l E Y E (AlgHom.id ℚ_[l] E) ≅ 𝟭 _) :
    lisseRationalScalarExtension l E Y E (AlgHom.id ℚ_[l] E) ≅ 𝟭 _ := by
  refine NatIso.ofComponents (fun F ↦ lisseCoherence_rationalizeIsoRaw l E Y _ _
    (e.app F.integral)) ?_
  intro F G v
  let SF := (lisseRationalScalarExtension l E Y E (AlgHom.id ℚ_[l] E)).obj F
  let SG := (lisseRationalScalarExtension l E Y E (AlgHom.id ℚ_[l] E)).obj G
  exact lisseCoherence_tensor_intertwining_map
    ((lisseRationalComposition l E Y).comp SF SG G)
    ((lisseRationalComposition l E Y).comp SF F G)
    (fun f ↦ (lisseIntegralScalarExtension l E Y E (AlgHom.id ℚ_[l] E)).map f)
    (fun f ↦ f) (fun f g ↦ f ≫ g) (fun f g ↦ f ≫ g) (RingHom.id E)
    (lisseCoherence_rationalScalarAddHom l E Y E (AlgHom.id ℚ_[l] E) F G) (AddMonoidHom.id _)
    ((lisseRationalComposition l E Y).comp_tmul SF SG G)
    ((lisseRationalComposition l E Y).comp_tmul SF F G)
    (lisseCoherence_rationalScalar_map_tmul l E Y E (AlgHom.id ℚ_[l] E) F G)
    (fun _ _ ↦ rfl) (e.hom.app G.integral) (e.hom.app F.integral)
    (fun f ↦ e.hom.naturality f) v

/-- The rationalization of the canonical integral identity comparison. -/
@[irreducible]
def lisseRationalScalarIdentityIso :
    lisseRationalScalarExtension l E Y E (AlgHom.id ℚ_[l] E) ≅ 𝟭 _ :=
  lisseCoherence_rationalScalarIdentityIsoRaw l E Y (lisseIntegralScalarIdentityIso l E Y)

attribute [local semireducible] lisseRationalScalarIdentityIso

/-- Canonical tensor comparison construction or its compatibility law. -/
theorem lisseCoherence_apply_after_eq {A B : Sort*} (g : A → B) {x y : A} {z : B}
    (h : x = y) (k : g y = z) : g x = z :=
  (congrArg g h).trans k

/-- Canonical tensor comparison construction or its compatibility law. -/
def lisseCoherence_rationalScalarCompositeIsoRaw
    (M : Type (u + 1)) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (κ : L →ₐ[ℚ_[l]] M)
    (e : lisseIntegralScalarExtension l E Y M (κ.comp ι) ≅
      lisseIntegralScalarExtension l E Y L ι ⋙ lisseIntegralScalarExtension l L Y M κ) :
    lisseRationalScalarExtension l E Y M (κ.comp ι) ≅
      lisseRationalScalarExtension l E Y L ι ⋙ lisseRationalScalarExtension l L Y M κ := by
  refine NatIso.ofComponents (fun F ↦ lisseCoherence_rationalizeIsoRaw l M Y _ _
    (e.app F.integral)) ?_
  intro F G v
  let SF := (lisseRationalScalarExtension l E Y M (κ.comp ι)).obj F
  let SG := (lisseRationalScalarExtension l E Y M (κ.comp ι)).obj G
  let TF := (lisseRationalScalarExtension l L Y M κ).obj
    ((lisseRationalScalarExtension l E Y L ι).obj F)
  let TG := (lisseRationalScalarExtension l L Y M κ).obj
    ((lisseRationalScalarExtension l E Y L ι).obj G)
  exact lisseCoherence_tensor_intertwining_map
    ((lisseRationalComposition l M Y).comp SF SG TG)
    ((lisseRationalComposition l M Y).comp SF TF TG)
    (fun f ↦ (lisseIntegralScalarExtension l E Y M (κ.comp ι)).map f)
    (fun f ↦ (lisseIntegralScalarExtension l L Y M κ).map
      ((lisseIntegralScalarExtension l E Y L ι).map f))
    (fun f g ↦ f ≫ g) (fun f g ↦ f ≫ g) (κ.comp ι).toRingHom
    (lisseCoherence_rationalScalarAddHom l E Y M (κ.comp ι) F G)
    ((lisseCoherence_rationalScalarAddHom l L Y M κ
      ((lisseRationalScalarExtension l E Y L ι).obj F)
      ((lisseRationalScalarExtension l E Y L ι).obj G)).comp
        (lisseCoherence_rationalScalarAddHom l E Y L ι F G))
    ((lisseRationalComposition l M Y).comp_tmul SF SG TG)
    ((lisseRationalComposition l M Y).comp_tmul SF TF TG)
    (lisseCoherence_rationalScalar_map_tmul l E Y M (κ.comp ι) F G)
    (by
      intro a f
      change (lisseRationalScalarExtension l L Y M κ).map
        ((lisseRationalScalarExtension l E Y L ι).map
          (TensorProduct.tmul (Padic.coefficientExtensionIntegers l E) a f)) = _
      exact lisseCoherence_apply_after_eq
        (fun w : (lisseRationalScalarExtension l E Y L ι).obj F ⟶
            (lisseRationalScalarExtension l E Y L ι).obj G ↦
          (lisseRationalScalarExtension l L Y M κ).map w)
        (lisseCoherence_rationalScalar_map_tmul l E Y L ι F G a f)
        (lisseCoherence_rationalScalar_map_tmul l L Y M κ
          ((lisseRationalScalarExtension l E Y L ι).obj F)
          ((lisseRationalScalarExtension l E Y L ι).obj G) (ι a)
          ((lisseIntegralScalarExtension l E Y L ι).map f)))
    (e.hom.app G.integral) (e.hom.app F.integral) (fun f ↦ e.hom.naturality f) v

/-- The rationalization of the canonical integral composite comparison. -/
@[irreducible]
def lisseRationalScalarCompositeIso
    (M : Type (u + 1)) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (κ : L →ₐ[ℚ_[l]] M) :
    lisseRationalScalarExtension l E Y M (κ.comp ι) ≅
      lisseRationalScalarExtension l E Y L ι ⋙ lisseRationalScalarExtension l L Y M κ :=
  lisseCoherence_rationalScalarCompositeIsoRaw l E Y L ι M κ
    (lisseIntegralScalarCompositeIso l E Y L ι M κ)

attribute [local semireducible] lisseRationalScalarCompositeIso

private theorem rationalScalarComposite_assoc
    (M : Type (u + 1)) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (κ : L →ₐ[ℚ_[l]] M)
    (N : Type (u + 1)) [Field N] [Algebra ℚ_[l] N] [FiniteDimensional ℚ_[l] N]
    (μ : M →ₐ[ℚ_[l]] N) (F : LisseRationalSheaf l E Y) :
    (lisseRationalScalarCompositeIso l E Y M (κ.comp ι) N μ).hom.app F ≫
        (lisseRationalScalarExtension l M Y N μ).map
          ((lisseRationalScalarCompositeIso l E Y L ι M κ).hom.app F) =
      (lisseRationalScalarCompositeIso l E Y L ι N (μ.comp κ)).hom.app F ≫
        (lisseRationalScalarCompositeIso l L Y M κ N μ).hom.app
          ((lisseRationalScalarExtension l E Y L ι).obj F) := by
  exact rationalComparison_square l M Y N μ
    ((lisseRationalScalarExtension l E Y N (μ.comp (κ.comp ι))).obj F)
    ((lisseRationalScalarExtension l L Y N (μ.comp κ)).obj
      ((lisseRationalScalarExtension l E Y L ι).obj F))
    ((lisseRationalScalarExtension l E Y M (κ.comp ι)).obj F)
    ((lisseRationalScalarExtension l L Y M κ).obj
      ((lisseRationalScalarExtension l E Y L ι).obj F))
    _ _ _ _ (scalarComposite_assoc l E Y L ι M κ N μ F.integral)

private theorem rationalComparison_unit
    (F G : LisseRationalSheaf l E Y)
    (a : (lisseIntegralScalarExtension l E Y L ι).obj G.integral ⟶
      (lisseIntegralScalarExtension l E Y L ι).obj F.integral)
    (b : F.integral ⟶ G.integral)
    (h : a ≫ (lisseIntegralScalarExtension l E Y L ι).map b =
      𝟙 ((lisseIntegralScalarExtension l E Y L ι).obj G.integral)) :
    ((TensorProduct.tmul (Padic.coefficientExtensionIntegers l L) 1 a :
      (lisseRationalScalarExtension l E Y L ι).obj G ⟶
        (lisseRationalScalarExtension l E Y L ι).obj F) ≫
      (lisseRationalScalarExtension l E Y L ι).map
        (TensorProduct.tmul (Padic.coefficientExtensionIntegers l E) 1 b : F ⟶ G)) =
      𝟙 ((lisseRationalScalarExtension l E Y L ι).obj G) := by
  erw [lisseCoherence_rationalScalar_map_tmul l E Y L ι F G 1 b, map_one,
    lisseCoherence_rational_tmul_comp, one_mul, h]
  rfl

private theorem rationalScalarComposite_left_unit (F : LisseRationalSheaf l E Y) :
    (lisseRationalScalarCompositeIso l E Y E (AlgHom.id ℚ_[l] E) L ι).hom.app F ≫
        (lisseRationalScalarExtension l E Y L ι).map
          ((lisseRationalScalarIdentityIso l E Y).hom.app F) =
      𝟙 ((lisseRationalScalarExtension l E Y L ι).obj F) := by
  exact rationalComparison_unit l E Y L ι
    ((lisseRationalScalarExtension l E Y E (AlgHom.id ℚ_[l] E)).obj F) F
    ((lisseIntegralScalarCompositeIso l E Y E (AlgHom.id ℚ_[l] E) L ι).hom.app F.integral)
    ((lisseIntegralScalarIdentityIso l E Y).hom.app F.integral)
    (scalarComposite_left_unit l E Y L ι F.integral)

private theorem rationalScalarComposite_right_unit (F : LisseRationalSheaf l E Y) :
    (lisseRationalScalarCompositeIso l E Y L ι L (AlgHom.id ℚ_[l] L)).hom.app F ≫
        (lisseRationalScalarIdentityIso l L Y).hom.app
          ((lisseRationalScalarExtension l E Y L ι).obj F) =
      𝟙 ((lisseRationalScalarExtension l E Y L ι).obj F) := by
  erw [lisseCoherence_rational_tmul_comp, one_mul, scalarComposite_right_unit]
  rfl

/-- Canonical scalar comparison formula or tensor coherence. -/
theorem lisseRationalScalarComposite_assoc
    (M : Type (u + 1)) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (κ : L →ₐ[ℚ_[l]] M)
    (N : Type (u + 1)) [Field N] [Algebra ℚ_[l] N] [FiniteDimensional ℚ_[l] N]
    (μ : M →ₐ[ℚ_[l]] N) (F : LisseRationalSheaf l E Y) :
    (lisseRationalScalarCompositeIso l E Y M (κ.comp ι) N μ).hom.app F ≫
        (lisseRationalScalarExtension l M Y N μ).map
          ((lisseRationalScalarCompositeIso l E Y L ι M κ).hom.app F) =
      (lisseRationalScalarCompositeIso l E Y L ι N (μ.comp κ)).hom.app F ≫
        (lisseRationalScalarCompositeIso l L Y M κ N μ).hom.app
          ((lisseRationalScalarExtension l E Y L ι).obj F) := by
  exact rationalScalarComposite_assoc l E Y L ι M κ N μ F

/-- Canonical scalar comparison formula or tensor coherence. -/
theorem lisseRationalScalarComposite_left_unit (F : LisseRationalSheaf l E Y) :
    (lisseRationalScalarCompositeIso l E Y E (AlgHom.id ℚ_[l] E) L ι).hom.app F ≫
        (lisseRationalScalarExtension l E Y L ι).map
          ((lisseRationalScalarIdentityIso l E Y).hom.app F) =
      𝟙 ((lisseRationalScalarExtension l E Y L ι).obj F) := by
  exact rationalScalarComposite_left_unit l E Y L ι F

/-- Canonical scalar comparison formula or tensor coherence. -/
theorem lisseRationalScalarComposite_right_unit (F : LisseRationalSheaf l E Y) :
    (lisseRationalScalarCompositeIso l E Y L ι L (AlgHom.id ℚ_[l] L)).hom.app F ≫
        (lisseRationalScalarIdentityIso l L Y).hom.app
          ((lisseRationalScalarExtension l E Y L ι).obj F) =
      𝟙 ((lisseRationalScalarExtension l E Y L ι).obj F) := by
  exact rationalScalarComposite_right_unit l E Y L ι F

end ScalarExtension

/-- Assemble a category-valued diagram from componentwise coherence laws. -/
def lisseCoherentCategoryDiagram {B : Type u} [Preorder B]
    (C : B → Type w) [∀ b, Category.{v} (C b)]
    (map : ∀ {b c : B}, (b ⟶ c) → (C b ⥤ C c))
    (mapId : ∀ b, map (𝟙 b) ≅ 𝟭 (C b))
    (mapComp : ∀ {b c d : B} (f : b ⟶ c) (g : c ⟶ d),
      map (f ≫ g) ≅ map f ⋙ map g)
    (assoc : ∀ {b c d e : B} (f : b ⟶ c) (g : c ⟶ d) (h : d ⟶ e) (F : C b),
      (mapComp (f ≫ g) h).hom.app F ≫
        (map h).map ((mapComp f g).hom.app F) =
      (mapComp f (g ≫ h)).hom.app F ≫
        (mapComp g h).hom.app ((map f).obj F))
    (leftUnit : ∀ {b c : B} (f : b ⟶ c) (F : C b),
      (mapComp (𝟙 b) f).hom.app F ≫
        (map f).map ((mapId b).hom.app F) =
      𝟙 ((map f).obj F))
    (rightUnit : ∀ {b c : B} (f : b ⟶ c) (F : C b),
      (mapComp f (𝟙 c)).hom.app F ≫
        (mapId c).hom.app ((map f).obj F) =
      𝟙 ((map f).obj F)) :
    Pseudofunctor (LocallyDiscrete B) Cat.{v, w} := by
  refine LocallyDiscrete.mkPseudofunctor (fun b ↦ Cat.of (C b))
    (fun f ↦ (map f).toCatHom) (fun b ↦ Cat.Hom.isoMk (mapId b))
    (fun f g ↦ Cat.Hom.isoMk (mapComp f g)) ?_ ?_ ?_
  · intro b c d e f g h
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext F
    change C b at F
    change (mapComp (f ≫ g) h).hom.app F ≫
      (map h).map ((mapComp f g).hom.app F) ≫ 𝟙 _ ≫
      (mapComp g h).inv.app ((map f).obj F) ≫
      (mapComp f (g ≫ h)).inv.app F = 𝟙 _
    simp only [Category.id_comp]
    simp only [← Category.assoc]
    rw [assoc]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.id_comp, Iso.hom_inv_id_app]
    rfl
  · intro b c f
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext F
    change C b at F
    change (mapComp (𝟙 b) f).hom.app F ≫
      (map f).map ((mapId b).hom.app F) ≫ 𝟙 _ = 𝟙 ((map f).obj F)
    simpa only [Category.comp_id, Category.id_comp] using leftUnit f F
  · intro b c f
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext F
    change C b at F
    change (mapComp f (𝟙 c)).hom.app F ≫
      (mapId c).hom.app ((map f).obj F) ≫ 𝟙 _ = 𝟙 ((map f).obj F)
    simpa only [Category.comp_id, Category.id_comp] using rightUnit f F

section AlgebraicCoefficients

variable (K : Type (u + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

-- Avoid generating unused constructor-injectivity and size functions.
set_option genInjectivity false in
set_option genSizeOf false in
/-- The scalar-extension diagram, with objects and arrows specified by the integral
and rational constructions above. Its pseudofunctor coherence is tensor associativity. -/
structure LisseCoefficientDiagramData where
  /-- Coherent diagram over the directed set of finite coefficient fields. -/
  diagram : Pseudofunctor (LocallyDiscrete (Padic.FiniteCoefficientFields l K))
    Cat.{u + 1, u + 2}
  /-- Its value at E is the category of lisse E-sheaves. -/
  obj_eq (E₀ : Padic.FiniteCoefficientFields l K) :
    diagram.obj ⟨E₀⟩ = Cat.of (LisseRationalSheaf l E₀.val Y)
  /-- Its scalar-extension arrows are the prescribed rational functors. -/
  map_eq (E₀ L₀ : Padic.FiniteCoefficientFields l K) (h : E₀ ≤ L₀) :
    eqToHom (obj_eq E₀).symm ≫ diagram.map (homOfLE h).toLoc ≫ eqToHom (obj_eq L₀) =
      (lisseRationalScalarExtension l E₀.val Y L₀.val
        (IntermediateField.inclusion h)).toCatHom

/-- The coefficient diagram with canonical tensor unit and composition constraints.
The diagram is constructed explicitly; its coherence is not chosen from unspecified
pseudofunctors with the same objects and arrows. -/
@[irreducible]
def lisseCoefficientDiagramData : LisseCoefficientDiagramData l Y K := by
  refine
    { diagram := lisseCoherentCategoryDiagram
        (fun E₀ : Padic.FiniteCoefficientFields l K ↦ LisseRationalSheaf l E₀.val Y)
        (fun {E₀ L₀} f ↦ lisseRationalScalarExtension l E₀.val Y L₀.val
          (IntermediateField.inclusion (leOfHom f)))
        (fun E₀ ↦ lisseRationalScalarIdentityIso l E₀.val Y)
        (fun {E₀ L₀ M₀} f g ↦ lisseRationalScalarCompositeIso l E₀.val Y L₀.val
          (IntermediateField.inclusion (leOfHom f)) M₀.val
          (IntermediateField.inclusion (leOfHom g))) ?_ ?_ ?_
      obj_eq := fun _ ↦ rfl
      map_eq := ?_ }
  · intro E₀ L₀ M₀ N₀ f g h F
    exact lisseRationalScalarComposite_assoc l E₀.val Y L₀.val
      (IntermediateField.inclusion (leOfHom f)) M₀.val
      (IntermediateField.inclusion (leOfHom g)) N₀.val
      (IntermediateField.inclusion (leOfHom h)) F
  · intro E₀ L₀ f F
    exact lisseRationalScalarComposite_left_unit l E₀.val Y L₀.val
      (IntermediateField.inclusion (leOfHom f)) F
  · intro E₀ L₀ f F
    exact lisseRationalScalarComposite_right_unit l E₀.val Y L₀.val
      (IntermediateField.inclusion (leOfHom f)) F
  · intro E₀ L₀ h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

-- Preserve the standing hypotheses of this public interface.
set_option linter.unusedSectionVars false in
/-- The category of pairs `(E,F)`, before identifying scalar extensions. -/
abbrev LisseCoefficientPairs :=
  Pseudofunctor.Grothendieck (lisseCoefficientDiagramData l Y K).diagram

/-- Cocartesian arrows: a scalar extension followed by an isomorphism.
Inverting these gives the 2-colimit, without identifying objects as raw sets. -/
def lisseCoefficientCocartesian : MorphismProperty (LisseCoefficientPairs l Y K) :=
  fun _ _ f => IsIso f.fiber

/-- Lisse algebraic-coefficient sheaves are the 2-colimit of the lisse E-categories.
The Grothendieck construction has pairs `(E,F)` as objects; localization preserves its
objects and inverts the coefficient-extension arrows. -/
abbrev LisseAlgebraicSheaf := (lisseCoefficientCocartesian l Y K).Localization

/-- The coefficient pair underlying an algebraic-coefficient sheaf.
Localization uses type synonyms on objects, so no representative is chosen here. -/
def lisseAlgebraicPair (F : LisseAlgebraicSheaf l Y K) : LisseCoefficientPairs l Y K :=
  F.as.obj

/-- The rational model of a coefficient pair, transported along its specified category value. -/
def lisseCoefficientPairModel (F : LisseCoefficientPairs l Y K) :
    LisseRationalSheaf l F.base.val Y :=
  (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq F.base)).toFunctor.obj F.fiber

/-- The algebraic-coefficient fibre is `K ⊗_E F_y`, for the pair `(E,F)`. -/
def lisseAlgebraicFiber {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (F : LisseAlgebraicSheaf l Y K) : ModuleCat.{u + 1} K :=
  let P := lisseAlgebraicPair l Y K F
  ModuleCat.of K (TensorProduct P.base.val K
    (lisseRationalFiber l P.base.val Y y (lisseCoefficientPairModel l Y K P)))

/-- Embed a rational model as the corresponding pair in the 2-colimit. -/
def lisseAlgebraicOfModel (E₀ : Padic.FiniteCoefficientFields l K)
    (F : LisseRationalSheaf l E₀.val Y) : LisseAlgebraicSheaf l Y K :=
  (lisseCoefficientCocartesian l Y K).Q.obj
    { base := E₀
      fiber := (eqToHom ((lisseCoefficientDiagramData l Y K).obj_eq E₀).symm).toFunctor.obj F }

/-- Tensor at algebraic coefficients, formed over the compositum of the coefficient fields. -/
def lisseAlgebraicTensor (F G : LisseAlgebraicSheaf l Y K) : LisseAlgebraicSheaf l Y K :=
  let P := lisseAlgebraicPair l Y K F
  let Q := lisseAlgebraicPair l Y K G
  let L₀ := Padic.finiteCoefficientCompositum l K P.base Q.base
  let f := (lisseRationalScalarExtension l P.base.val Y L₀.val
    (IntermediateField.inclusion (show P.base.val ≤ L₀.val from le_sup_left))).obj
      (lisseCoefficientPairModel l Y K P)
  let g := (lisseRationalScalarExtension l Q.base.val Y L₀.val
    (IntermediateField.inclusion (show Q.base.val ≤ L₀.val from le_sup_right))).obj
      (lisseCoefficientPairModel l Y K Q)
  lisseAlgebraicOfModel l Y K L₀ (lisseRationalTensor l L₀.val Y f g)

/-- The algebraic-coefficient unit is the constant system over the base coefficient field. -/
def lisseAlgebraicUnit : LisseAlgebraicSheaf l Y K :=
  lisseAlgebraicOfModel l Y K (Padic.finiteCoefficientBase l K)
    (lisseRationalUnit l (Padic.finiteCoefficientBase l K).val Y)

end AlgebraicCoefficients

end AlgebraicGeometry.Scheme

-- Restore the imported instance after elaborating this file.
attribute [instance] CategoryTheory.catToReflQuiver
