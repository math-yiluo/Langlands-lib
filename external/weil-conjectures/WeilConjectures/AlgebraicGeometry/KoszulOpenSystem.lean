/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single

/-! # The truncated Koszul system on a finite principal open

Source: Stacks Project, Tags 08CX and 08DC (blueprint: def-sc-koszul-open-system).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

noncomputable section

variable (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)

/-- The negative Koszul tail differential squares to zero. Source: Stacks, Tag 08CX
(blueprint: def-sc-koszul-open-system).
Proof: compose two negatives and apply `ExteriorAlgebra.koszulBoundary_comp`. -/
theorem koszulOpenTail_square (e n : ℕ) :
    (-ModuleCat.ofHom (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (e + 1))
      (n + 2))) ≫
    (-ModuleCat.ofHom (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (e + 1))
      (n + 1))) = 0 := by
  simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using
    ExteriorAlgebra.koszulBoundary_comp A r (fun i ↦ f i ^ (e + 1)) (n + 1)

/-- The tail `I^{-n} = K_{n+1}` with negative Koszul differential, for exponent `e+1`.
Source: Stacks, Tag 08CX (blueprint: def-sc-koszul-open-system). -/
def koszulOpenTail (e : ℕ) : ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.of
    (fun n ↦ ModuleCat.of A (⋀[A]^(n + 1) (Fin r →₀ A)))
    (fun n ↦ -ModuleCat.ofHom
      (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (e + 1)) (n + 1)))
    (koszulOpenTail_square A r f e)

/-- Augmentation of the negative Koszul tail to `A`, using `K_0 ≃ A`.
Source: Stacks, Tag 08CX (blueprint: def-sc-koszul-open-system). -/
def koszulOpenAugmentationComponent (e : ℕ) :
    (koszulOpenTail A r f e).X 0 ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (e + 1)) 0) ≫
    (exteriorPower.zeroEquiv (R := A) (M := Fin r →₀ A)).toModuleIso.hom

/-- The augmentation annihilates boundaries. Source: Stacks, Tag 08CX
(blueprint: def-sc-koszul-open-system).
Proof: the Koszul differential squares to zero; compose with the degree-zero
exterior-power identification and use bilinearity to remove the negative sign. -/
theorem koszulOpenAugmentationComponent_cycle (e : ℕ) :
    (koszulOpenTail A r f e).d 1 0 ≫ koszulOpenAugmentationComponent A r f e = 0 := by
  change (-ModuleCat.ofHom
    (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (e + 1)) 1)) ≫
      (ModuleCat.ofHom
        (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (e + 1)) 0) ≫ _) = 0
  rw [Preadditive.neg_comp, ← Category.assoc,
    ExteriorAlgebra.koszulBoundary_comp, zero_comp, neg_zero]

/-- The canonical chain map `I → A[0]`. Source: Stacks, Tag 08CX
(blueprint: def-sc-koszul-open-system). -/
def koszulOpenAugmentation (e : ℕ) :
    koszulOpenTail A r f e ⟶ (ChainComplex.single₀ (ModuleCat.{u} A)).obj
      (ModuleCat.of A A) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨koszulOpenAugmentationComponent A r f e,
      koszulOpenAugmentationComponent_cycle A r f e⟩

/-- The diagonal map multiplying generator `i` by `f_i^d`.
Source: Stacks, Tag 08CX (blueprint: def-sc-koszul-open-system). -/
def koszulOpenDiagonal (d : ℕ) : (Fin r →₀ A) →ₗ[A] (Fin r →₀ A) :=
  Finsupp.linearCombination A (fun i ↦ Finsupp.single i (f i ^ d))

/-- The component of the power-comparison map on the Koszul tail.
Source: Stacks, Tag 08CX (blueprint: def-sc-koszul-open-system). -/
def koszulOpenTransitionComponent (a b n : ℕ) :
    (koszulOpenTail A r f b).X n ⟶ (koszulOpenTail A r f a).X n :=
  ModuleCat.ofHom (exteriorPower.map (n := n + 1) (koszulOpenDiagonal A r f (b - a)))

private theorem koszulOpen_exterior_coe_map (n : ℕ)
    (g : (Fin r →₀ A) →ₗ[A] (Fin r →₀ A))
    (x : ⋀[A]^n (Fin r →₀ A)) :
    (exteriorPower.map n g x : ExteriorAlgebra A (Fin r →₀ A)) =
      ExteriorAlgebra.map g (x : ExteriorAlgebra A (Fin r →₀ A)) := by
  have hh : (⋀[A]^n (Fin r →₀ A)).subtype.comp (exteriorPower.map n g) =
      (ExteriorAlgebra.map g).toLinearMap.comp (⋀[A]^n (Fin r →₀ A)).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.ιMulti_apply_coe, AlgHom.toLinearMap_apply,
      ExteriorAlgebra.map_apply_ιMulti]
  exact LinearMap.congr_fun hh x

private theorem koszulOpen_contract_natural
    (g : (Fin r →₀ A) →ₗ[A] (Fin r →₀ A))
    (φ ψ : (Fin r →₀ A) →ₗ[A] A) (h : ψ.comp g = φ)
    (x : ExteriorAlgebra A (Fin r →₀ A)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A))) ψ
        (ExteriorAlgebra.map g x) =
      ExteriorAlgebra.map g
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm A (Fin r →₀ A))) φ x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap t =>
    simp only [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    have hv : ψ (g v) = φ v := LinearMap.congr_fun h v
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      hv, hx, map_sub, map_smul]

private theorem koszulOpen_forms_comp (a b : ℕ) (h : a ≤ b) :
    (Finsupp.linearCombination A (fun i ↦ f i ^ (a + 1))).comp
        (koszulOpenDiagonal A r f (b - a)) =
      Finsupp.linearCombination A (fun i ↦ f i ^ (b + 1)) := by
  apply Finsupp.lhom_ext
  intro i x
  have hexp : b - a + (a + 1) = b + 1 := by omega
  simp only [LinearMap.comp_apply, koszulOpenDiagonal, Finsupp.linearCombination_single,
    map_smul, smul_eq_mul]
  rw [← pow_add, hexp]

/-- Power comparison commutes with the differential. Source: Stacks, Tag 08CX
(blueprint: def-sc-koszul-open-system).
Proof: on a wedge of basis vectors the comparison multiplies by the product
of their `f_i^(b-a)`. Each summand of the contraction formula commutes since
`f_i^(a+1) * f_i^(b-a) = f_i^(b+1)` when `a ≤ b`. -/
theorem koszulOpenTransitionComponent_comm (a b : ℕ) (h : a ≤ b) (n m : ℕ) :
    (koszulOpenTail A r f b).d n m ≫ koszulOpenTransitionComponent A r f a b m =
      koszulOpenTransitionComponent A r f a b n ≫ (koszulOpenTail A r f a).d n m := by
  by_cases hnm : n = m + 1
  · subst n
    dsimp only [koszulOpenTail, ChainComplex.of]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (exteriorPower.map (m + 1) (koszulOpenDiagonal A r f (b - a))
      (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (b + 1)) (m + 1) x) :
        ExteriorAlgebra A (Fin r →₀ A)) =
      (ExteriorAlgebra.koszulBoundary A r (fun i ↦ f i ^ (a + 1)) (m + 1)
        (exteriorPower.map (m + 1 + 1) (koszulOpenDiagonal A r f (b - a)) x) :
          ExteriorAlgebra A (Fin r →₀ A))
    simp only [koszulOpen_exterior_coe_map, ExteriorAlgebra.koszulBoundary,
      LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    exact (koszulOpen_contract_natural A r (koszulOpenDiagonal A r f (b - a))
      (Finsupp.linearCombination A (fun i ↦ f i ^ (b + 1)))
      (Finsupp.linearCombination A (fun i ↦ f i ^ (a + 1)))
      (koszulOpen_forms_comp A r f a b h) x).symm
  · have hn : ¬ (ComplexShape.down ℕ).Rel n m := by
      simpa only [ComplexShape.down_Rel, eq_comm] using hnm
    rw [HomologicalComplex.shape _ n m hn, HomologicalComplex.shape _ n m hn,
      zero_comp, comp_zero]

/-- The comparison `I_b → I_a` for exponents `b+1 ≥ a+1`.
Source: Stacks, Tag 08CX (blueprint: def-sc-koszul-open-system). -/
def koszulOpenTransition (a b : ℕ) (h : a ≤ b) :
    koszulOpenTail A r f b ⟶ koszulOpenTail A r f a where
  f n := koszulOpenTransitionComponent A r f a b n
  comm' n m _ := (koszulOpenTransitionComponent_comm A r f a b h n m).symm

/-- Transport Mathlib's tilde functor to the project's shared sheaf-module category.
Source: Stacks, Tag 08CX (blueprint: def-sc-koszul-open-system). -/
def koszulOpenTilde : ModuleCat.{u} A ⥤
    SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) where
  obj M := (tilde.functor (.of A)).obj M
  map g := (tilde.functor (.of A)).map g
  map_id M := (tilde.functor (.of A)).map_id M
  map_comp g h := (tilde.functor (.of A)).map_comp g h

set_option backward.isDefEq.respectTransparency false in
/-- Additivity instance for termwise tilde. Source: Stacks, Tag 08CX
(blueprint: def-sc-koszul-open-system). -/
instance koszulOpenTilde_additive : (koszulOpenTilde A).Additive := by
  constructor
  intro M N g h
  exact tilde.map_add (R := .of A) g h

/-- Termwise tilde, after extending `I^{-n}` by zero to integer cochain degrees.
Source: Stacks, Tag 08CX (blueprint: def-sc-koszul-open-system). -/
def koszulOpenSheafComplex (e : ℕ) :=
  ((koszulOpenTilde A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat)

private theorem koszulOpenDiagonal_zero :
    koszulOpenDiagonal A r f 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro i x
  simp [koszulOpenDiagonal, Finsupp.linearCombination_single]

private theorem koszulOpenDiagonal_comp (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    (koszulOpenDiagonal A r f (b - a)).comp (koszulOpenDiagonal A r f (c - b)) =
      koszulOpenDiagonal A r f (c - a) := by
  apply Finsupp.lhom_ext
  intro i x
  have hexp : c - b + (b - a) = c - a := by omega
  simp only [LinearMap.comp_apply, koszulOpenDiagonal, Finsupp.linearCombination_single,
    Finsupp.smul_single, smul_eq_mul]
  rw [mul_assoc, ← pow_add, hexp]

private theorem koszulOpenTransition_id (a : ℕ) :
    koszulOpenTransition A r f a a le_rfl = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  change ModuleCat.ofHom (exteriorPower.map (n + 1)
    (koszulOpenDiagonal A r f (a - a))) = 𝟙 _
  rw [Nat.sub_self, koszulOpenDiagonal_zero, exteriorPower.map_id]
  rfl

private theorem koszulOpenTransition_comp (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    koszulOpenTransition A r f b c hbc ≫ koszulOpenTransition A r f a b hab =
      koszulOpenTransition A r f a c (hab.trans hbc) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change (exteriorPower.map (n + 1) (koszulOpenDiagonal A r f (b - a))).comp
      (exteriorPower.map (n + 1) (koszulOpenDiagonal A r f (c - b))) = _
  rw [← exteriorPower.map_comp, koszulOpenDiagonal_comp A r f a b c hab hbc]
  rfl

variable [HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]

/-- The object `I_{e+1}` in `D(O_Spec A)`. Source: Stacks, Tag 08CX
(blueprint: def-sc-koszul-open-system). -/
def koszulOpenObject (e : ℕ) : schemeDerivedCategory (Spec (.of A)) :=
  DerivedCategory.Q.obj (koszulOpenSheafComplex A r f e)

/-- The structure module, represented by the extended single complex `A[0]`.
Source: Stacks, Tag 08CX (blueprint: def-sc-koszul-open-system). -/
def koszulOpenStructure : schemeDerivedCategory (Spec (.of A)) :=
  DerivedCategory.Q.obj (((koszulOpenTilde A).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
    (((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)).extend
      ComplexShape.embeddingDownNat))

/-- The object of the full Koszul complex in cohomological degrees `[-r,0]`.
Source: Stacks, Tag 08CX (blueprint: def-sc-koszul-open-system). -/
def koszulOpenKoszulObject (e : ℕ) : schemeDerivedCategory (Spec (.of A)) :=
  DerivedCategory.Q.obj (((koszulOpenTilde A).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
    ((ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ (e + 1))).extend
      ComplexShape.embeddingDownNat))

/-- Inclusion of `A` into degree zero of the Koszul complex.
Source: Stacks, Tag 08CX (blueprint: def-sc-koszul-open-system). -/
def koszulOpenKoszulInclusion (e : ℕ) :
    (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A) ⟶
      ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ (e + 1)) :=
  (ChainComplex.fromSingle₀Equiv _ _).symm
    (exteriorPower.zeroEquiv (R := A) (M := Fin r →₀ A)).toModuleIso.inv

/-- The canonical second arrow `O_X → K_e` of the Koszul triangle.
Source: Stacks, Tag 08CX (blueprint: def-sc-koszul-open-system). -/
def koszulOpenKoszulUnit (e : ℕ) :
    koszulOpenStructure A ⟶ koszulOpenKoszulObject A r f e :=
  DerivedCategory.Q.map (((koszulOpenTilde A).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
    (HomologicalComplex.extendMap (koszulOpenKoszulInclusion A r f e)
      ComplexShape.embeddingDownNat))

/-- The canonical augmentation in the derived category. Source: Stacks, Tag 08CX
(blueprint: def-sc-koszul-open-system). -/
def koszulOpenUnit (e : ℕ) : koszulOpenObject A r f e ⟶ koszulOpenStructure A :=
  DerivedCategory.Q.map (((koszulOpenTilde A).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
    (HomologicalComplex.extendMap (koszulOpenAugmentation A r f e)
      ComplexShape.embeddingDownNat))

/-- Derived power comparison. Source: Stacks, Tag 08CX
(blueprint: def-sc-koszul-open-system). -/
def koszulOpenMap (a b : ℕ) (h : a ≤ b) :
    koszulOpenObject A r f b ⟶ koszulOpenObject A r f a :=
  DerivedCategory.Q.map (((koszulOpenTilde A).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
    (HomologicalComplex.extendMap (koszulOpenTransition A r f a b h)
      ComplexShape.embeddingDownNat))

/-- Finite union of principal opens. Source: Stacks, Tag 08CX
(blueprint: def-sc-koszul-open-system). -/
def koszulOpen : (Spec (.of A)).Opens :=
  ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)

set_option backward.isDefEq.respectTransparency false in
/-- Power comparisons are identities at equal exponents and compose transitively.
Source: Stacks, Tag 08CX (blueprint: def-sc-koszul-open-system).
Proof: the diagonal maps multiply by `f_i^(b-a)`; for `a ≤ b ≤ c`, exponent
addition identifies their composite with `f_i^(c-a)`. Exterior powers, extension,
termwise tilde, and localization preserve identities and compositions. -/
theorem koszulOpenMap_laws :
    (∀ a : ℕ, koszulOpenMap A r f a a le_rfl = 𝟙 _) ∧
    (∀ (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
      koszulOpenMap A r f b c hbc ≫ koszulOpenMap A r f a b hab =
        koszulOpenMap A r f a c (hab.trans hbc)) := by
  constructor
  · intro a
    simp only [koszulOpenMap, koszulOpenTransition_id, HomologicalComplex.extendMap_id]
    dsimp only [koszulOpenObject, koszulOpenSheafComplex]
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  · intro a b c hab hbc
    simp only [koszulOpenMap, ← Functor.map_comp, ← HomologicalComplex.extendMap_comp,
      koszulOpenTransition_comp A r f a b c hab hbc]

/-- The directed Hom diagram respects identities and composition.
Source: Stacks, Tag 08DC (blueprint: def-sc-koszul-open-system).
Proof: precomposition reverses composition of the inverse-system maps;
apply `koszulOpenMap_laws`, then associativity of derived composition. -/
theorem koszulOpenHomDiagram_laws (E : schemeDerivedCategory (Spec (.of A))) :
    (∀ a : ℕ, (fun φ : koszulOpenObject A r f a ⟶ E ↦
      koszulOpenMap A r f a a le_rfl ≫ φ) = id) ∧
    (∀ (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
      (fun φ : koszulOpenObject A r f a ⟶ E ↦
        koszulOpenMap A r f a c (hab.trans hbc) ≫ φ) =
      (fun φ ↦ koszulOpenMap A r f b c hbc ≫ φ) ∘
        (fun φ ↦ koszulOpenMap A r f a b hab ≫ φ)) := by
  constructor
  · intro a
    funext φ
    rw [(koszulOpenMap_laws A r f).1 a, Category.id_comp]
    rfl
  · intro a b c hab hbc
    funext φ
    change koszulOpenMap A r f a c (hab.trans hbc) ≫ φ =
      koszulOpenMap A r f b c hbc ≫ (koszulOpenMap A r f a b hab ≫ φ)
    rw [← Category.assoc, (koszulOpenMap_laws A r f).2 a b c hab hbc]

/-- The directed diagram of derived Hom sets, with transition by precomposition.
Source: Stacks, Tag 08DC (blueprint: def-sc-koszul-open-system). -/
def koszulOpenHomDiagram (E : schemeDerivedCategory (Spec (.of A))) : ℕ ⥤ Type w where
  obj e := koszulOpenObject A r f e ⟶ E
  map {a b} h := TypeCat.ofHom (fun φ ↦ koszulOpenMap A r f a b (leOfHom h) ≫ φ)
  map_id a := congrArg TypeCat.ofHom ((koszulOpenHomDiagram_laws A r f E).1 a)
  map_comp {a b c} hab hbc :=
    congrArg TypeCat.ofHom
      ((koszulOpenHomDiagram_laws A r f E).2 a b c (leOfHom hab) (leOfHom hbc))

end
end AlgebraicGeometry
