/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-!

# Extension of scalars to a sequential colimit `S = colim(R --n--> R --n--> ⋯)`

Let `C` be a braided monoidal preadditive category whose tensor product preserves colimits, `R`
a commutative algebra object, `φ : R ⟶ S` a morphism of algebra objects and `n : ℕ`. Suppose
that `S` is the colimit of the sequence `R --n--> R --n--> ⋯` of multiplications by `n`
(`CategoryTheory.Mod.smulSequence`, `CategoryTheory.Mod.smulSequenceCocone`), with cocone maps
`c_k : R ⟶ S` such that `c_0 = φ` (think `c_k = n⁻ᵏ φ`, as for `𝒪_E ⟶ E = 𝒪_E[1/ℓ]`). Then
multiplication by `n` on `S` is a monomorphism (`CategoryTheory.Mod.mono_nsmul_id_of_isColimit`),
so the `c_k` are `R`-linear for the action of `R` on `S` through `φ`
(`CategoryTheory.Mod.linear_of_isColimit`).

For every `R`-module object `M`, the maps `e_k : M ⟶ S ⊗_R M`, `m ↦ c_k(1) ⊗ m`, then exhibit
`S ⊗_R M` as the colimit of the sequence `M --n--> M --n--> ⋯`
(`CategoryTheory.Mod.isColimitExtendScalarsCocone`), naturally in `M`
(`CategoryTheory.Mod.extendScalarsCoconeι_extendScalarsMap`). Consequently, when `C` is
abelian with exact sequential colimits, the extension of scalars along `φ` is exact
(`CategoryTheory.Mod.preservesFiniteLimits_extendScalars_of_isColimit`): it preserves
monomorphisms, these being preserved by sequential colimits.

Such sequential colimits are preserved by additive functors preserving the colimit
(`CategoryTheory.Mod.isColimitSmulSequenceCoconeMap`), e.g. by inverse images of sheaves.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C]

section Sequence

variable [Preadditive C]

/-- The sequence `X --n--> X --n--> ⋯` of multiplications by `n : ℕ` on an object `X` of a
preadditive category: the transition map from `i` to `j ≥ i` is the multiplication by
`n ^ (j - i)`. -/
@[simps obj map]
abbrev smulSequence (X : C) (n : ℕ) : ℕ ⥤ C where
  obj _ := X
  map {i j} _ := (n ^ (j - i)) • 𝟙 X
  map_id i := by simp
  map_comp {i j k} f g := by
    have := leOfHom f
    have := leOfHom g
    rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, ← mul_nsmul',
      ← pow_add]
    congr 2
    lia

/-- The morphism of sequences `smulSequence X n ⟶ smulSequence Y n` induced by `f : X ⟶ Y`. -/
@[simps app]
def smulSequenceMap {X Y : C} (f : X ⟶ Y) (n : ℕ) : smulSequence X n ⟶ smulSequence Y n where
  app _ := f
  naturality _ _ _ := by
    simp

instance {X Y : C} (f : X ⟶ Y) [Mono f] (n : ℕ) : Mono (smulSequenceMap f n) :=
  have (k : ℕ) : Mono ((smulSequenceMap f n).app k) := inferInstanceAs (Mono f)
  NatTrans.mono_of_mono_app _

/-- If `n • c_{k+1} = c_k` for all `k`, then `n ^ (j - i) • c_j = c_i` for `i ≤ j`. -/
lemma pow_sub_nsmul_eq {X Y : C} {n : ℕ} {c : ℕ → (X ⟶ Y)} (hc : ∀ k, n • c (k + 1) = c k)
    {i j : ℕ} (h : i ≤ j) : n ^ (j - i) • c j = c i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_sub_cancel_left, ← add_assoc, pow_succ, mul_smul, hc, ← ih (by lia),
      Nat.add_sub_cancel_left]

/-- The cocone over `X --n--> X --n--> ⋯` given by maps `c_k : X ⟶ Y` with `n • c_{k+1} = c_k`. -/
abbrev smulSequenceCocone {X Y : C} (n : ℕ) (c : ℕ → (X ⟶ Y)) (hc : ∀ k, n • c (k + 1) = c k) :
    Cocone (smulSequence X n) where
  pt := Y
  ι :=
    { app := c
      naturality i j f := by
        simp [pow_sub_nsmul_eq hc (leOfHom f)] }

/-- The multiplication by `n` on the colimit `Y` of `X --n--> X --n--> ⋯` is a split
monomorphism, with retraction the shift `c_k ↦ c_{k+1}`. -/
lemma mono_nsmul_id_of_isColimit {X Y : C} {n : ℕ} {c : ℕ → (X ⟶ Y)}
    (hc : ∀ k, n • c (k + 1) = c k) (hS : IsColimit (smulSequenceCocone n c hc)) :
    Mono (n • 𝟙 Y) := by
  let u : Y ⟶ Y := hS.desc (smulSequenceCocone n (fun k ↦ c (k + 1)) fun k ↦ hc (k + 1))
  have hu : (n • 𝟙 Y) ≫ u = 𝟙 Y := hS.hom_ext fun k ↦ by
    rw [Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul, Category.comp_id]
    exact (congrArg (n • ·) (hS.fac _ k)).trans (hc k)
  have : IsSplitMono (n • 𝟙 Y) := IsSplitMono.mk' ⟨u, hu⟩
  infer_instance

/-- The sequence `X --n--> X --n--> ⋯` mapped by an additive functor is the sequence of
multiplications by `n` on `F.obj X`. -/
def smulSequenceCompIso {D : Type*} [Category* D] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (X : C) (n : ℕ) : smulSequence X n ⋙ F ≅ smulSequence (F.obj X) n :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
    simp [F.map_nsmul]

/-- An additive functor preserving the colimit of `X --n--> X --n--> ⋯` sends a colimit cocone
`(c_k : X ⟶ Y)_k` to a colimit cocone `(F c_k : F X ⟶ F Y)_k`. -/
noncomputable def isColimitSmulSequenceCoconeMap {D : Type*} [Category* D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} {n : ℕ} {c : ℕ → (X ⟶ Y)}
    (hc : ∀ k, n • c (k + 1) = c k) (hS : IsColimit (smulSequenceCocone n c hc))
    [PreservesColimit (smulSequence X n) F] :
    IsColimit (smulSequenceCocone n (fun k ↦ F.map (c k)) fun k ↦ by
      rw [← F.map_nsmul, hc]) :=
  (IsColimit.precomposeHomEquiv (smulSequenceCompIso F X n) _).1
    (IsColimit.ofIsoColimit (isColimitOfPreserves F hS)
      (Cocone.ext (Iso.refl _) fun k ↦ by simp [smulSequenceCompIso]))

end Sequence

section Colimit

variable [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]

/-- Whiskering on the right is additive: `(n • f) ▷ Z = n • (f ▷ Z)`. -/
lemma nsmul_whiskerRight {X Y : C} (n : ℕ) (f : X ⟶ Y) (Z : C) :
    (n • f) ▷ Z = n • (f ▷ Z) :=
  (tensorRight Z).map_nsmul

variable [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ] {n : ℕ}
  (c : ℕ → (R ⟶ S))

/-- The map `e_k : M ⟶ S ⊗_R M`, `m ↦ c_k(1) ⊗ m`. -/
noncomputable def extendScalarsCoconeι (M : Mod C R) (k : ℕ) :
    M.X ⟶ (extendScalarsObj φ M).X :=
  (λ_ M.X).inv ≫ (η[R] ≫ c k) ▷ M.X ≫ extendπ φ M

omit [Preadditive C] [MonoidalPreadditive C] in
/-- The maps `e_k` are natural in the `R`-module `M`. -/
@[reassoc]
lemma extendScalarsCoconeι_extendScalarsMap {M N : Mod C R} (f : M ⟶ N) (k : ℕ) :
    extendScalarsCoconeι φ c M k ≫ (extendScalarsMap φ f).hom =
      f.hom ≫ extendScalarsCoconeι φ c N k := by
  rw [extendScalarsCoconeι, extendScalarsCoconeι, Category.assoc, Category.assoc,
    extendπ_extendScalarsMap, ← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]

variable {c}

lemma nsmul_extendScalarsCoconeι_succ (hc : ∀ k, n • c (k + 1) = c k) (M : Mod C R) (k : ℕ) :
    n • extendScalarsCoconeι φ c M (k + 1) = extendScalarsCoconeι φ c M k := by
  rw [extendScalarsCoconeι, extendScalarsCoconeι, ← hc k, Preadditive.comp_nsmul,
    nsmul_whiskerRight, Preadditive.nsmul_comp, Preadditive.comp_nsmul]

/-- The cocone `(e_k)_k : (M --n--> M --n--> ⋯) ⟶ S ⊗_R M`. -/
noncomputable abbrev extendScalarsCocone (hc : ∀ k, n • c (k + 1) = c k) (M : Mod C R) :
    Cocone (smulSequence M.X n) :=
  smulSequenceCocone n (extendScalarsCoconeι φ c M) (nsmul_extendScalarsCoconeι_succ φ hc M)

variable {φ}

omit [Preadditive C] [MonoidalPreadditive C] in
/-- `c_k(r) ⊗ m = c_k(1) ⊗ r m` in `S ⊗_R M`, by `R`-linearity of `c_k`. -/
@[reassoc]
lemma whiskerRight_extendπ (hlin : ∀ k, c k ▷ R ≫ S ◁ φ ≫ μ[S] = μ[R] ≫ c k)
    (M : Mod C R) (k : ℕ) :
    c k ▷ M.X ≫ extendπ φ M = γ[R,M.X] ≫ extendScalarsCoconeι φ c M k := by
  have h : ((λ_ R).inv ≫ (η[R] ≫ c k) ▷ R) ≫ S ◁ φ ≫ μ[S] = c k := by
    rw [comp_whiskerRight, Category.assoc, Category.assoc, hlin, MonObj.one_mul_assoc,
      Iso.inv_hom_id_assoc]
  rw [extendScalarsCoconeι, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    whiskerLeft_smul_extendπ]
  dsimp only [selfLeftAction_actionObj]
  rw [associator_inv_naturality_left_assoc, leftUnitor_tensor_inv,
    Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
    h]

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  [MonObj S] [IsCommMonObj R] in
/-- For a cocone `s` over `M --n--> M --n--> ⋯`, the cocone `(r ⊗ m ↦ s_k(r m))_k` over
`R ⊗ M --n--> R ⊗ M --n--> ⋯`. -/
noncomputable def smulCocone {M : Mod C R} (s : Cocone (smulSequence M.X n)) :
    Cocone (smulSequence R n ⋙ tensorRight M.X) where
  pt := s.pt
  ι := NatTrans.ofSequence (fun k ↦ γ[R,M.X] ≫ s.ι.app k) fun k ↦ by
    have := s.w (homOfLE (k.le_add_right 1))
    simp only [Nat.add_sub_cancel_left, pow_one, Preadditive.nsmul_comp,
      Category.id_comp] at this
    simp [← this]

variable (hc : ∀ k, n • c (k + 1) = c k) (hS : IsColimit (smulSequenceCocone n c hc))

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [BraidedCategory C] [MonObj S] [IsCommMonObj R] in
/-- The map `S ⊗ M ⟶ s` induced by a cocone `s` over `M --n--> M --n--> ⋯`, using
`S ⊗ M = colim_k (R ⊗ M)`. -/
noncomputable def descTensor {M : Mod C R} (s : Cocone (smulSequence M.X n)) :
    S ⊗ M.X ⟶ s.pt :=
  (isColimitOfPreserves (tensorRight M.X) hS).desc (smulCocone s)

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [BraidedCategory C] [MonObj S] [IsCommMonObj R] in
@[reassoc]
lemma whiskerRight_descTensor {M : Mod C R} (s : Cocone (smulSequence M.X n)) (k : ℕ) :
    c k ▷ M.X ≫ descTensor hc hS s = γ[R,M.X] ≫ s.ι.app k :=
  (isColimitOfPreserves (tensorRight M.X) hS).fac (smulCocone s) k

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [BraidedCategory C] [IsMonHom φ] in
lemma descTensor_condition (hlin : ∀ k, c k ▷ R ≫ S ◁ φ ≫ μ[S] = μ[R] ≫ c k) {M : Mod C R}
    (s : Cocone (smulSequence M.X n)) :
    (S ◁ φ ≫ μ[S]) ▷ M.X ≫ descTensor hc hS s =
      ((α_ S R M.X).hom ≫ S ◁ γ[R,M.X]) ≫ descTensor hc hS s :=
  (isColimitOfPreserves (tensorRight R ⋙ tensorRight M.X) hS).hom_ext fun k ↦ by
    dsimp
    rw [← comp_whiskerRight_assoc, hlin, comp_whiskerRight_assoc, whiskerRight_descTensor,
      ModObj.mul_smul_self_assoc, Category.assoc, associator_naturality_left_assoc,
      ← whisker_exchange_assoc, whiskerRight_descTensor]

/-- **`S ⊗_R M = colim(M --n--> M --n--> ⋯)`**: the maps `e_k : M ⟶ S ⊗_R M`,
`m ↦ c_k(1) ⊗ m`, exhibit `S ⊗_R M` as the colimit of the multiplications by `n` on `M`. -/
noncomputable def isColimitExtendScalarsCocone
    (hlin : ∀ k, c k ▷ R ≫ S ◁ φ ≫ μ[S] = μ[R] ≫ c k) (M : Mod C R) :
    IsColimit (extendScalarsCocone φ hc M) where
  desc s := extendDescHom φ (descTensor hc hS s) (descTensor_condition hc hS hlin s)
  fac s k := by
    dsimp only [extendScalarsCocone]
    rw [extendScalarsCoconeι, Category.assoc, Category.assoc,
      extendπ_extendDescHom, comp_whiskerRight_assoc, whiskerRight_descTensor,
      ModObj.one_smul_self_assoc, Iso.inv_hom_id_assoc]
  uniq s m hm := by
    rw [← cancel_epi (extendπ φ M), extendπ_extendDescHom]
    refine (isColimitOfPreserves (tensorRight M.X) hS).hom_ext fun k ↦ ?_
    dsimp
    rw [whiskerRight_extendπ_assoc hlin, whiskerRight_descTensor, ← hm k]

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  [IsCommMonObj R] in
/-- If `c_0 = φ`, the maps `c_k : R ⟶ S` are `R`-linear for the action of `R` on `S` through
`φ`: indeed `n^k c_k = φ` is, and multiplication by `n` on `S` is a monomorphism. -/
lemma linear_of_isColimit (hc : ∀ k, n • c (k + 1) = c k)
    (hS : IsColimit (smulSequenceCocone n c hc)) (h0 : c 0 = φ) (k : ℕ) :
    c k ▷ R ≫ S ◁ φ ≫ μ[S] = μ[R] ≫ c k := by
  have := mono_nsmul_id_of_isColimit hc hS
  induction k with
  | zero => rw [h0, IsMonHom.mul_hom, tensorHom_def, Category.assoc]
  | succ k ih =>
    rw [← cancel_mono (n • 𝟙 S)]
    simp only [Preadditive.comp_nsmul, Category.comp_id]
    rw [← Preadditive.nsmul_comp, ← nsmul_whiskerRight, hc, ih, ← Preadditive.comp_nsmul, hc]

end Colimit

/-! ### Exactness -/

section Exact

variable [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] {φ : R ⟶ S} [IsMonHom φ] {n : ℕ}
  {c : ℕ → (R ⟶ S)}

/-- Extension of scalars along `φ` sends a morphism of `R`-modules which is a monomorphism in
`C` to a monomorphism in `C`: it is the colimit of the morphism of sequences
`(M --n--> M --n--> ⋯) ⟶ (N --n--> N --n--> ⋯)`, and sequential colimits are exact. -/
lemma mono_extendScalarsMap_hom (hc : ∀ k, n • c (k + 1) = c k)
    (hS : IsColimit (smulSequenceCocone n c hc))
    (hlin : ∀ k, c k ▷ R ≫ S ◁ φ ≫ μ[S] = μ[R] ≫ c k) {M N : Mod C R} (f : M ⟶ N)
    [Mono f.hom] : Mono (extendScalarsMap φ f).hom := by
  let hM := isColimitExtendScalarsCocone hc hS hlin M
  let hN := isColimitExtendScalarsCocone hc hS hlin N
  have heq : (extendScalarsMap φ f).hom =
      (hM.coconePointUniqueUpToIso (colimit.isColimit _)).hom ≫
        colimMap (smulSequenceMap f.hom n) ≫
          (hN.coconePointUniqueUpToIso (colimit.isColimit _)).inv := hM.hom_ext fun k ↦ by
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc, colimit.cocone_ι, ι_colimMap_assoc,
      smulSequenceMap_app, ← colimit.cocone_ι, IsColimit.comp_coconePointUniqueUpToIso_inv]
    exact extendScalarsCoconeι_extendScalarsMap φ c f k
  have : Mono (colimMap (smulSequenceMap f.hom n)) := colim.map_mono _
  rw [heq]
  infer_instance

/-- **Flatness**: extension of scalars along `φ` preserves monomorphisms. -/
lemma preservesMonomorphisms_extendScalars (hc : ∀ k, n • c (k + 1) = c k)
    (hS : IsColimit (smulSequenceCocone n c hc))
    (hlin : ∀ k, c k ▷ R ≫ S ◁ φ ≫ μ[S] = μ[R] ≫ c k) :
    (extendScalars φ).PreservesMonomorphisms where
  preserves {M N} f _ := by
    have : (forget R).IsRightAdjoint := (freeForgetAdjunction R).isRightAdjoint
    have : Mono f.hom := (forget R).map_mono f
    have := mono_extendScalarsMap_hom hc hS hlin f
    exact (forget S).mono_of_mono_map this

/-- **Flatness**: extension of scalars along `φ` is exact, when `S` is the sequential colimit
`colim(R --n--> R --n--> ⋯)` along maps `c_k : R ⟶ S` with `c_0 = φ`. -/
lemma preservesFiniteLimits_extendScalars_of_isColimit (hc : ∀ k, n • c (k + 1) = c k)
    (hS : IsColimit (smulSequenceCocone n c hc)) (h0 : c 0 = φ) :
    PreservesFiniteLimits (extendScalars φ) := by
  have := preservesMonomorphisms_extendScalars hc hS (linear_of_isColimit hc hS h0)
  have : (extendScalars φ).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact (extendScalars φ).preservesFiniteLimits_of_preservesHomology

end Exact

end CategoryTheory.Mod
