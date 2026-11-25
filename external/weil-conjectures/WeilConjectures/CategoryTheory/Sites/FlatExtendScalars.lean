/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations

/-!
# Extension of scalars along a finite free ring map preserves flat sheaves

Let `φ : R →+* S` be a morphism of commutative rings making `S` a finite free `R`-module. If a
presheaf `P` of `R`-modules has locally trivial relations
(`CategoryTheory.Presheaf.HasLocallyTrivialRelations`), so does the presheaf `S ⊗_R P` of
`S`-modules: writing sections of `S ⊗_R P` in a basis `(b_k)` of `S`, an `S`-linear relation
between them is a finite system of `R`-linear relations between their coordinates, which is
locally trivial, and the trivialization of the coordinates gives one of the sections. By the
relation criterion for flatness, the sheafification of `S ⊗_R F` is flat for every flat sheaf
`F` of `R`-modules over a Noetherian ring `R`.

## Main results

- `CategoryTheory.Presheaf.HasLocallyTrivialRelations.comp_extendScalars`: extension of scalars
  preserves locally trivial relations.
- `CategoryTheory.Sheaf.flat_presheafToSheaf_obj_comp_extendScalars`: extension of scalars
  followed by sheafification preserves flat sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct ChangeOfRings

namespace CategoryTheory

section Coordinates

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type*} [Fintype ι]
  [DecidableEq ι] (b : Module.Basis ι R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)))
  {M : ModuleCat R}

/-- An element of `S` viewed as an `R`-module through `φ`, as an element of the ring `S`. -/
abbrev ModuleCat.restrictScalarsSelfVal
    (x : (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)) : S :=
  x

/-- An element of the ring `S`, as an element of `S` viewed as an `R`-module through `φ`. -/
abbrev ModuleCat.restrictScalarsSelfMk (x : S) :
    (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S) :=
  x

/-- An element of `S ⊗_R M` is the sum of the `b k ⊗ c_k`, where `c` are its coordinates in the
basis `b` of `S`. -/
lemma ModuleCat.ExtendScalars.sum_basis_tmul_equivFinsuppOfBasisLeft
    (y : (ModuleCat.extendScalars φ).obj M) :
    ∑ k, b k ⊗ₜ[R, φ] (TensorProduct.equivFinsuppOfBasisLeft b y k) = y := by
  conv_rhs => rw [← (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply y]
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
  intro k
  simp

/-- The coordinates of `s • y` in the basis `b` are obtained from those of `y` through the matrix
of multiplication by `s`. -/
lemma ModuleCat.ExtendScalars.equivFinsuppOfBasisLeft_smul (s : S)
    (y : (ModuleCat.extendScalars φ).obj M) (m : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (s • y) m =
      ∑ k, b.repr (s * ModuleCat.restrictScalarsSelfVal φ (b k)) m •
        TensorProduct.equivFinsuppOfBasisLeft b y k := by
  conv_lhs => rw [← sum_basis_tmul_equivFinsuppOfBasisLeft φ b y, Finset.smul_sum]
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply b _ _ m

end Coordinates

section Unit

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} [Finite ι]
  (b : Module.Basis ι R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)))

/-- For a basis `b` of `S` over `R` and an `R`-module `M`, the maps `m ↦ b i ⊗ m`, that is the
unit `m ↦ 1 ⊗ m` of extension of scalars followed by multiplication by `b i`, exhibit `S ⊗_R M`
as a sum of copies of `M`. -/
lemma ModuleCat.ExtendScalars.isIso_biproductDesc_unit_comp_map_smul (M : ModuleCat.{u} R) :
    IsIso (biproduct.desc fun i ↦
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app M ≫
        (ModuleCat.restrictScalars.{u} φ).map
          (ModuleCat.restrictScalarsSelfVal φ (b i) • 𝟙 ((ModuleCat.extendScalars φ).obj M))) := by
  classical
  have := Fintype.ofFinite ι
  -- the coordinates in the basis `b`, as `R`-linear maps
  let coord (i : ι) : (ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj M) ⟶ M :=
    ModuleCat.ofHom (X := (ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj M))
      { toFun y := TensorProduct.equivFinsuppOfBasisLeft b y i
        map_add' y y' := by simp
        map_smul' r y := by
          change TensorProduct.equivFinsuppOfBasisLeft b (φ r • y) i = _
          rw [ModuleCat.ExtendScalars.equivFinsuppOfBasisLeft_smul φ b]
          have e (k : ι) : b.repr (φ r * ModuleCat.restrictScalarsSelfVal φ (b k)) =
              r • Finsupp.single k 1 := by
            change b.repr (r • b k) = _
            rw [map_smul, Module.Basis.repr_self]
          simp only [e, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
            mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
            RingHom.id_apply] }
  refine ⟨biproduct.lift coord, ?_, ?_⟩
  · apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro k
    simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.id_comp,
      biproduct.ι_π]
    ext m
    change TensorProduct.equivFinsuppOfBasisLeft b
      ((ModuleCat.restrictScalarsSelfVal φ (b j) * 1) ⊗ₜ[R, φ] m) k = _
    rw [mul_one, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases h : j = k
    · subst h
      simp
    · simp [h]
  · rw [biproduct.lift_desc]
    ext y
    conv_rhs => rw [← ModuleCat.ExtendScalars.sum_basis_tmul_equivFinsuppOfBasisLeft φ b y]
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_id, LinearMap.id_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    change (ModuleCat.restrictScalarsSelfVal φ (b j) * 1) ⊗ₜ[R, φ] _ = _
    rw [mul_one]
    rfl

end Unit

namespace Presheaf

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} [Finite ι]
  (b : Module.Basis ι R ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)))

include b in
/-- **Extension of scalars along a finite free ring map preserves locally trivial relations.**
-/
theorem HasLocallyTrivialRelations.comp_extendScalars {P : Cᵒᵖ ⥤ ModuleCat.{u + 1} R}
    (hP : HasLocallyTrivialRelations J P) :
    HasLocallyTrivialRelations J (P ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ) := by
  classical
  have := Fintype.ofFinite ι
  intro V s q y e he
  -- the coordinates of the sections `y j` in the basis `b`
  let c : Fin s × ι → P.obj (op V) := fun jk ↦
    TensorProduct.equivFinsuppOfBasisLeft b (y jk.1) jk.2
  -- the `R`-linear relations between them
  let E : Matrix (Fin q × ι) (Fin s × ι) R := fun lm jk ↦
    b.repr (e lm.1 jk.1 * ModuleCat.restrictScalarsSelfVal φ (b jk.2)) lm.2
  have hE : ∀ lm, ∑ jk, E lm jk • c jk = 0 := by
    intro ⟨l, m⟩
    have h := congrArg (fun x ↦ TensorProduct.equivFinsuppOfBasisLeft b x m) (he l)
    simp only [map_sum, map_zero, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.coe_zero, Pi.zero_apply] at h
    rw [← h, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact (ModuleCat.ExtendScalars.equivFinsuppOfBasisLeft_smul φ b (e l j) (y j) m).symm
  obtain ⟨T, hT, hfac⟩ := hP.exists_of_fintype c E hE
  refine ⟨T, hT, fun W f hf ↦ ?_⟩
  obtain ⟨t, B, z, hEB, hz⟩ := hfac f hf
  refine ⟨t, fun j p ↦ ∑ k, φ (B (j, k) p) * ModuleCat.restrictScalarsSelfVal φ (b k),
    fun p ↦ (1 : S) ⊗ₜ[R, φ] z p, ?_, fun j ↦ ?_⟩
  · ext l p
    apply b.repr.injective
    ext m
    have h := congr_fun (congr_fun hEB (l, m)) p
    simp only [Matrix.mul_apply, Matrix.zero_apply, Fintype.sum_prod_type] at h ⊢
    rw [map_zero, Finsupp.zero_apply, ← h, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have e₁ : e l x * (φ (B (x, k) p) * ModuleCat.restrictScalarsSelfVal φ (b k)) =
        ModuleCat.restrictScalarsSelfVal φ
          (B (x, k) p • ModuleCat.restrictScalarsSelfMk φ
            (e l x * ModuleCat.restrictScalarsSelfVal φ (b k))) := by
      change _ = φ (B (x, k) p) * (e l x * _)
      ring
    rw [e₁, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  · apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext k'
    have hy := ModuleCat.ExtendScalars.sum_basis_tmul_equivFinsuppOfBasisLeft φ b (y j)
    conv_lhs => rw [← hy]
    simp only [Functor.comp_map, map_sum,
      Finsupp.coe_finsetSum, Finset.sum_apply]
    trans ∑ c, b.repr (b c) k' • P.map f.op (TensorProduct.equivFinsuppOfBasisLeft b (y j) c)
    · exact Finset.sum_congr rfl fun c _ ↦
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply b _ _ k'
    trans ∑ p, B (j, k') p • z p
    · simp only [Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact hz (j, k')
    · refine Finset.sum_congr rfl fun p _ ↦ ?_
      have h₁ := TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply b
        (ModuleCat.restrictScalarsSelfMk φ
          ((∑ k, φ (B (j, k) p) * ModuleCat.restrictScalarsSelfVal φ (b k)) * 1)) (z p) k'
      refine Eq.trans ?_ h₁.symm
      congr 1
      have h₂ : ModuleCat.restrictScalarsSelfMk φ
          ((∑ k, φ (B (j, k) p) * ModuleCat.restrictScalarsSelfVal φ (b k)) * 1) =
            ∑ k, B (j, k) p • b k := by
        rw [mul_one]
        rfl
      rw [h₂, Module.Basis.repr_sum_self]


variable [EssentiallySmall.{u + 1} C]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]
  [J.HasSheafCompose (forget (ModuleCat.{u + 1} S))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} S)]
  [IsNoetherianRing R]

include b in
/-- **Extension of scalars along a finite free ring map preserves flat sheaves.** For a flat
sheaf `F` of modules over a Noetherian ring `R` and `S` finite free over `R`, the sheafification
of `S ⊗_R F` is flat. -/
theorem _root_.CategoryTheory.Sheaf.flat_presheafToSheaf_obj_comp_extendScalars
    {F : Sheaf J (ModuleCat.{u + 1} R)} (hF : ObjectProperty.flat F) :
    ObjectProperty.flat ((presheafToSheaf J (ModuleCat.{u + 1} S)).obj
      (F.obj ⋙ ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)) :=
  flat_presheafToSheaf_obj_of_hasLocallyTrivialRelations
    ((Sheaf.hasLocallyTrivialRelations_of_flat hF).comp_extendScalars φ b)

end Presheaf

end CategoryTheory
