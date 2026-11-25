/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.OrzechProperty

/-!
# Minimal complexes of finite free modules over a local ring

Let `A` be a commutative local ring with maximal ideal `𝔪`. A cochain complex `M` of
`A`-modules is *minimal* (`CochainComplex.IsMinimal`) if all its differentials take values in
`𝔪 M`, i.e. the differentials vanish after reduction modulo `𝔪`.

## Main results

- `CochainComplex.exists_homotopyEquiv_isMinimal`: a strictly bounded complex of finite free
  `A`-modules is homotopy equivalent to a minimal one, with the same bounds and again with
  finite free terms.
- `CochainComplex.isIso_of_quasiIso_of_isMinimal`: a quasi-isomorphism between bounded above
  minimal complexes of finite free `A`-modules is an isomorphism.

These are the minimal models of perfect complexes over a local ring.

## Implementation notes

If some differential `d : Mⁱ ⟶ Mⁱ⁺¹` is nonzero modulo `𝔪`, we pick `x ∈ Mⁱ` and a linear
form `φ` on `Mⁱ⁺¹` with `φ (d x) = 1`. The map `G = φ(-) • x : Mⁱ⁺¹ ⟶ Mⁱ` satisfies
`G ≫ d ≫ G = G`, so that the null-homotopic map `P` attached to `G` is an idempotent chain
endomorphism. The kernel of `P` is a subcomplex of `M` which is homotopy equivalent to `M`
and has smaller total rank.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

/-! ### Linear algebra over a local ring -/

section LinearAlgebra

variable {A : Type u} [CommRing A]

/-- The image of an element of `I • ⊤` under a linear map lies in `I • ⊤`. -/
lemma LinearMap.map_mem_ideal_smul_top {V W : Type*} [AddCommGroup V] [Module A V]
    [AddCommGroup W] [Module A W] (f : V →ₗ[A] W) (I : Ideal A) {x : V}
    (hx : x ∈ I • (⊤ : Submodule A V)) : f x ∈ I • (⊤ : Submodule A W) := by
  have h := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

variable [IsLocalRing A]

/-- **Nakayama**: an endomorphism of a finite module over a local ring which is congruent to
the identity modulo the maximal ideal is bijective. -/
lemma LinearMap.bijective_of_sub_mem_maximalIdeal_smul_top {V : Type*} [AddCommGroup V]
    [Module A V] [Module.Finite A V] (u : V →ₗ[A] V)
    (hu : ∀ x, u x - x ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A V)) :
    Function.Bijective u := by
  refine OrzechProperty.bijective_of_surjective_endomorphism u ?_
  rw [← LinearMap.range_eq_top, ← top_le_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp inferInstance)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) fun x _ ↦ ?_
  have hx : x = u x - (u x - x) := by abel
  rw [hx]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self u x))
    (Submodule.mem_sup_right (hu x))

/-- A submodule of a finite free module over a local ring which admits a linear retraction is
again finite and free. -/
lemma Submodule.free_and_finite_of_retraction {V : Type*} [AddCommGroup V] [Module A V]
    [Module.Free A V] [Module.Finite A V] (N : Submodule A V) (r : V →ₗ[A] N)
    (hr : r ∘ₗ N.subtype = LinearMap.id) : Module.Free A N ∧ Module.Finite A N := by
  have hsurj : Function.Surjective r := fun y ↦ ⟨y, by simpa using LinearMap.congr_fun hr y⟩
  have : Module.Finite A N := Module.Finite.of_surjective r hsurj
  have : Module.Projective A N := Module.Projective.of_split N.subtype r hr
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

/-- The range of an idempotent endomorphism of a finite free module over a local ring is finite
and free. -/
lemma LinearMap.free_and_finite_range_of_isIdempotentElem {V : Type*} [AddCommGroup V]
    [Module A V] [Module.Free A V] [Module.Finite A V] {p : V →ₗ[A] V}
    (hp : IsIdempotentElem p) :
    Module.Free A (LinearMap.range p) ∧ Module.Finite A (LinearMap.range p) := by
  refine (LinearMap.range p).free_and_finite_of_retraction (p.rangeRestrict) ?_
  ext ⟨_, y, rfl⟩
  simpa using LinearMap.congr_fun hp y

/-- The kernel of an idempotent endomorphism of a finite free module over a local ring is finite
and free. -/
lemma LinearMap.free_and_finite_ker_of_isIdempotentElem {V : Type*} [AddCommGroup V]
    [Module A V] [Module.Free A V] [Module.Finite A V] {p : V →ₗ[A] V}
    (hp : IsIdempotentElem p) :
    Module.Free A (LinearMap.ker p) ∧ Module.Finite A (LinearMap.ker p) := by
  have hmem (y : V) : (LinearMap.id - p : V →ₗ[A] V) y ∈ LinearMap.ker p := by
    have := LinearMap.congr_fun hp y
    simp only [Module.End.mul_apply] at this
    simp [this]
  refine (LinearMap.ker p).free_and_finite_of_retraction
    ((LinearMap.id - p).codRestrict _ hmem) (LinearMap.ext fun ⟨y, hy⟩ ↦ Subtype.ext ?_)
  simp [LinearMap.mem_ker.mp hy]

/-- For an idempotent endomorphism `p` of a finite free module `V` over a local ring, the ranks
of the kernel and of the range of `p` add up to the rank of `V`. -/
lemma LinearMap.finrank_ker_add_finrank_range_of_isIdempotentElem {V : Type*} [AddCommGroup V]
    [Module A V] [Module.Free A V] [Module.Finite A V] {p : V →ₗ[A] V}
    (hp : IsIdempotentElem p) :
    Module.finrank A (LinearMap.ker p) + Module.finrank A (LinearMap.range p) =
      Module.finrank A V := by
  obtain ⟨_, _⟩ := LinearMap.free_and_finite_ker_of_isIdempotentElem hp
  obtain ⟨_, _⟩ := LinearMap.free_and_finite_range_of_isIdempotentElem hp
  rw [add_comm, ← Module.finrank_prod,
    (Submodule.prodEquivOfIsCompl _ _ (LinearMap.IsIdempotentElem.isCompl hp)).finrank_eq]

/-- An element of a free module over a local ring which does not lie in `𝔪 • ⊤` takes the
value `1` under some linear form. -/
lemma Module.Free.exists_linearMap_eq_one_of_notMem_smul_top {V : Type*} [AddCommGroup V]
    [Module A V] [Module.Free A V] {f : V}
    (hf : f ∉ IsLocalRing.maximalIdeal A • (⊤ : Submodule A V)) :
    ∃ φ : V →ₗ[A] A, φ f = 1 := by
  let b := Module.Free.chooseBasis A V
  by_cases h : ∀ k, b.repr f k ∈ IsLocalRing.maximalIdeal A
  · refine (hf ?_).elim
    rw [← b.linearCombination_repr f, Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem_smul (h k) Submodule.mem_top
  · push Not at h
    obtain ⟨k, hk⟩ := h
    have hu : IsUnit (b.repr f k) := by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hk
    refine ⟨(hu.unit⁻¹ : Aˣ).val • b.coord k, ?_⟩
    simp [Basis.coord_apply]

end LinearAlgebra

namespace CochainComplex

variable {A : Type u} [CommRing A]

/-! ### The subcomplex defined by the kernel of a chain endomorphism -/

section KerSubcomplex

variable {ι : Type*} {c : ComplexShape ι} {M : HomologicalComplex (ModuleCat.{v} A) c}

/-- Elementwise form of the commutation of a chain map with the differentials. -/
lemma _root_.HomologicalComplex.Hom.comm_hom_apply {M N : HomologicalComplex (ModuleCat.{v} A) c}
    (f : M ⟶ N) (k l : ι) (x : M.X k) :
    (f.f l).hom ((M.d k l).hom x) = (N.d k l).hom ((f.f k).hom x) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.comm k l)).symm x

/-- Elementwise form of the idempotence of a chain endomorphism `P`. -/
lemma _root_.HomologicalComplex.Hom.idem_hom_apply {P : M ⟶ M} (hP : P ≫ P = P) (k : ι)
    (y : M.X k) : (P.f k).hom ((P.f k).hom y) = (P.f k).hom y :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (HomologicalComplex.congr_hom hP k)) y

/-- The components of an idempotent chain endomorphism are idempotent linear maps. -/
lemma isIdempotentElem_hom_f {P : M ⟶ M} (hP : P ≫ P = P) (k : ι) :
    IsIdempotentElem (P.f k).hom :=
  LinearMap.ext (HomologicalComplex.Hom.idem_hom_apply hP k)

/-- The subcomplex of a complex of modules `M` given in each degree by the kernel of a chain
endomorphism `P` of `M`. -/
noncomputable def kerSubcomplex (P : M ⟶ M) : HomologicalComplex (ModuleCat.{v} A) c where
  X k := ModuleCat.of A (LinearMap.ker (P.f k).hom)
  d k l := ModuleCat.ofHom ((M.d k l).hom.restrict fun x hx ↦ by
    simp_all [LinearMap.mem_ker, HomologicalComplex.Hom.comm_hom_apply])
  shape k l h := by
    ext x
    simp [M.shape k l h]
  d_comp_d' k l m _ _ := by
    ext x
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (M.d_comp_d k l m)) x.1

/-- The inclusion of `kerSubcomplex P` into `M`. -/
noncomputable def kerSubcomplexι (P : M ⟶ M) : kerSubcomplex P ⟶ M where
  f k := ModuleCat.ofHom (LinearMap.ker (P.f k).hom).subtype

/-- The retraction `M ⟶ kerSubcomplex P` given by `𝟙 - P`, for an idempotent `P`. -/
noncomputable def kerSubcomplexπ (P : M ⟶ M) (hP : P ≫ P = P) : M ⟶ kerSubcomplex P where
  f k := ModuleCat.ofHom ((LinearMap.id - (P.f k).hom).codRestrict _ fun y ↦ by
    simp [HomologicalComplex.Hom.idem_hom_apply hP])
  comm' k l _ := by
    ext x
    refine Subtype.ext ?_
    simp [kerSubcomplex, HomologicalComplex.Hom.comm_hom_apply]

/-- The composition `M ⟶ kerSubcomplex P ⟶ M` is `𝟙 M - P`. -/
lemma kerSubcomplexπ_comp_kerSubcomplexι (P : M ⟶ M) (hP : P ≫ P = P) :
    kerSubcomplexπ P hP ≫ kerSubcomplexι P = 𝟙 M - P := by
  ext k x
  rfl

/-- The retraction `kerSubcomplexπ` is a left inverse of the inclusion `kerSubcomplexι`. -/
lemma kerSubcomplexι_comp_kerSubcomplexπ (P : M ⟶ M) (hP : P ≫ P = P) :
    kerSubcomplexι P ≫ kerSubcomplexπ P hP = 𝟙 _ := by
  ext k ⟨x, hx⟩
  refine Subtype.ext ?_
  exact sub_eq_self.mpr hx

/-- If `P` is an idempotent chain endomorphism of `M` which is homotopic to zero, then `M` is
homotopy equivalent to the subcomplex `kerSubcomplex P`. -/
noncomputable def homotopyEquivKerSubcomplex (P : M ⟶ M) (hP : P ≫ P = P)
    (H : Homotopy P 0) : HomotopyEquiv M (kerSubcomplex P) where
  hom := kerSubcomplexπ P hP
  inv := kerSubcomplexι P
  homotopyHomInvId := Homotopy.equivSubZero.symm
    (((Homotopy.ofEq (by rw [kerSubcomplexπ_comp_kerSubcomplexι]; abel)).trans
      (H.smul (-1 : ℤ))).trans (Homotopy.ofEq (by simp)))
  homotopyInvHomId := Homotopy.ofEq (kerSubcomplexι_comp_kerSubcomplexπ P hP)

end KerSubcomplex

/-! ### Null-homotopic maps attached to a map concentrated in one degree -/

section SingleHomotopy

variable {C : Type*} [Category* C] [Preadditive C]

/-- The family of maps `Mᵖ ⟶ M^q` which is `G` for `(p, q) = (i + 1, i)` and zero otherwise. -/
noncomputable def singleHomotopyHom (M : CochainComplex C ℤ) (i : ℤ) (G : M.X (i + 1) ⟶ M.X i)
    (p q : ℤ) : M.X p ⟶ M.X q :=
  if h : p = i + 1 ∧ q = i then (M.XIsoOfEq h.1).hom ≫ G ≫ (M.XIsoOfEq h.2).inv else 0

/-- The component of `singleHomotopyHom M i G` in bidegree `(i + 1, i)` is `G`. -/
lemma singleHomotopyHom_self (M : CochainComplex C ℤ) (i : ℤ) (G : M.X (i + 1) ⟶ M.X i) :
    singleHomotopyHom M i G (i + 1) i = G := by
  simp [singleHomotopyHom]

/-- The components of `singleHomotopyHom M i G` outside bidegree `(i + 1, i)` vanish. -/
lemma singleHomotopyHom_eq_zero (M : CochainComplex C ℤ) (i : ℤ) (G : M.X (i + 1) ⟶ M.X i)
    {p q : ℤ} (h : ¬ (p = i + 1 ∧ q = i)) : singleHomotopyHom M i G p q = 0 :=
  dite_eq_right h

/-- The null-homotopic chain endomorphism attached to `G : Mⁱ⁺¹ ⟶ Mⁱ`. -/
noncomputable def singleNullHomotopicMap (M : CochainComplex C ℤ) (i : ℤ)
    (G : M.X (i + 1) ⟶ M.X i) : M ⟶ M :=
  Homotopy.nullHomotopicMap (singleHomotopyHom M i G)

/-- The null-homotopic map `singleNullHomotopicMap M i G` is homotopic to zero. -/
noncomputable def singleNullHomotopy (M : CochainComplex C ℤ) (i : ℤ)
    (G : M.X (i + 1) ⟶ M.X i) : Homotopy (singleNullHomotopicMap M i G) 0 :=
  Homotopy.nullHomotopy _ fun p q h ↦ singleHomotopyHom_eq_zero M i G fun h' ↦ h (by
    simp only [ComplexShape.up_Rel]
    omega)

/-- In degree `i`, `singleNullHomotopicMap M i G` is `d ≫ G`. -/
lemma singleNullHomotopicMap_f_self (M : CochainComplex C ℤ) (i : ℤ)
    (G : M.X (i + 1) ⟶ M.X i) :
    (singleNullHomotopicMap M i G).f i = M.d i (i + 1) ≫ G := by
  rw [singleNullHomotopicMap, Homotopy.nullHomotopicMap_f (k₂ := i - 1) (by simp) rfl,
    singleHomotopyHom_self, singleHomotopyHom_eq_zero M i G (by omega), zero_comp, add_zero]

/-- In degree `i + 1`, `singleNullHomotopicMap M i G` is `G ≫ d`. -/
lemma singleNullHomotopicMap_f_succ (M : CochainComplex C ℤ) (i : ℤ)
    (G : M.X (i + 1) ⟶ M.X i) :
    (singleNullHomotopicMap M i G).f (i + 1) = G ≫ M.d i (i + 1) := by
  rw [singleNullHomotopicMap, Homotopy.nullHomotopicMap_f (k₂ := i) (k₀ := i + 1 + 1) rfl rfl,
    singleHomotopyHom_self, singleHomotopyHom_eq_zero M i G (by omega), comp_zero, zero_add]

/-- Outside degrees `i` and `i + 1`, `singleNullHomotopicMap M i G` vanishes. -/
lemma singleNullHomotopicMap_f_eq_zero (M : CochainComplex C ℤ) (i : ℤ)
    (G : M.X (i + 1) ⟶ M.X i) {k : ℤ} (hk₁ : k ≠ i) (hk₂ : k ≠ i + 1) :
    (singleNullHomotopicMap M i G).f k = 0 := by
  rw [singleNullHomotopicMap, Homotopy.nullHomotopicMap_f (k₂ := k - 1) (k₀ := k + 1)
    (by simp) rfl, singleHomotopyHom_eq_zero M i G (by omega),
    singleHomotopyHom_eq_zero M i G (by omega), comp_zero, zero_comp, add_zero]

/-- If `G ≫ d ≫ G = G`, the null-homotopic map attached to `G` is idempotent. -/
lemma singleNullHomotopicMap_idem (M : CochainComplex C ℤ) (i : ℤ)
    (G : M.X (i + 1) ⟶ M.X i) (hG : G ≫ M.d i (i + 1) ≫ G = G) :
    singleNullHomotopicMap M i G ≫ singleNullHomotopicMap M i G =
      singleNullHomotopicMap M i G := by
  ext k
  rw [HomologicalComplex.comp_f]
  by_cases hk₁ : k = i
  · subst hk₁
    rw [singleNullHomotopicMap_f_self, Category.assoc, hG]
  by_cases hk₂ : k = i + 1
  · subst hk₂
    rw [singleNullHomotopicMap_f_succ, Category.assoc, reassoc_of% hG]
  rw [singleNullHomotopicMap_f_eq_zero M i G hk₁ hk₂, zero_comp]

end SingleHomotopy

/-- The kernel subcomplex of a chain endomorphism of a complex which is strictly `≥ a` is
strictly `≥ a`. -/
lemma isStrictlyGE_kerSubcomplex {M : CochainComplex (ModuleCat.{v} A) ℤ} (P : M ⟶ M) (a : ℤ)
    [M.IsStrictlyGE a] : CochainComplex.IsStrictlyGE (kerSubcomplex P) a := by
  rw [isStrictlyGE_iff]
  intro k hk
  have := ModuleCat.isZero_iff_subsingleton.1 (M.isZero_of_isStrictlyGE a k hk)
  exact ModuleCat.isZero_iff_subsingleton.2
    (inferInstanceAs (Subsingleton (LinearMap.ker (P.f k).hom)))

/-- The kernel subcomplex of a chain endomorphism of a complex which is strictly `≤ b` is
strictly `≤ b`. -/
lemma isStrictlyLE_kerSubcomplex {M : CochainComplex (ModuleCat.{v} A) ℤ} (P : M ⟶ M) (b : ℤ)
    [M.IsStrictlyLE b] : CochainComplex.IsStrictlyLE (kerSubcomplex P) b := by
  rw [isStrictlyLE_iff]
  intro k hk
  have := ModuleCat.isZero_iff_subsingleton.1 (M.isZero_of_isStrictlyLE b k hk)
  exact ModuleCat.isZero_iff_subsingleton.2
    (inferInstanceAs (Subsingleton (LinearMap.ker (P.f k).hom)))

/-! ### Minimal complexes -/

variable [IsLocalRing A]

/-- A cochain complex of modules over a local ring `A` is *minimal* if all its differentials
take values in `𝔪 • ⊤`, where `𝔪` is the maximal ideal of `A`, i.e. the differentials vanish
modulo `𝔪`. -/
def IsMinimal (M : CochainComplex (ModuleCat.{v} A) ℤ) : Prop :=
  ∀ (i j : ℤ) (x : M.X i),
    (M.d i j).hom x ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A (M.X j))

/-- If `f` and `g` are homotopic maps between minimal complexes, then `f - g` takes values in
`𝔪 • ⊤` in every degree. -/
lemma IsMinimal.sub_mem_of_homotopy {M N : CochainComplex (ModuleCat.{v} A) ℤ}
    (hM : M.IsMinimal) (hN : N.IsMinimal) {f g : M ⟶ N} (H : Homotopy f g) (k : ℤ)
    (x : M.X k) :
    (f.f k).hom x - (g.f k).hom x ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A (N.X k)) := by
  rw [H.comm k, dNext_eq _ (show (ComplexShape.up ℤ).Rel k (k + 1) from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (k - 1) k by simp)]
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    add_sub_cancel_right]
  exact Submodule.add_mem _ ((H.hom (k + 1) k).hom.map_mem_ideal_smul_top _ (hM _ _ x))
    (hN _ _ _)

/-- A chain map between minimal complexes of finite modules which is a homotopy equivalence is
bijective in each degree. -/
lemma IsMinimal.bijective_of_homotopyEquiv {M N : CochainComplex (ModuleCat.{v} A) ℤ}
    (hM : M.IsMinimal) (hN : N.IsMinimal) [∀ i, Module.Finite A (M.X i)]
    [∀ i, Module.Finite A (N.X i)] (e : HomotopyEquiv M N) (k : ℤ) :
    Function.Bijective (e.hom.f k) := by
  have h₁ := LinearMap.bijective_of_sub_mem_maximalIdeal_smul_top ((e.hom ≫ e.inv).f k).hom
    fun x ↦ by simpa using hM.sub_mem_of_homotopy hM e.homotopyHomInvId k x
  have h₂ := LinearMap.bijective_of_sub_mem_maximalIdeal_smul_top ((e.inv ≫ e.hom).f k).hom
    fun x ↦ by simpa using hN.sub_mem_of_homotopy hN e.homotopyInvHomId k x
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp] at h₁ h₂
  exact ⟨h₁.1.of_comp, h₂.2.of_comp⟩

/-- A quasi-isomorphism between bounded above minimal complexes of finite free modules over a
local ring is an isomorphism of complexes. -/
theorem isIso_of_quasiIso_of_isMinimal {M M' : CochainComplex (ModuleCat.{v} A) ℤ}
    (α : M ⟶ M') [QuasiIso α] (b b' : ℤ) [M.IsStrictlyLE b] [M'.IsStrictlyLE b']
    [∀ i, Module.Free A (M.X i)] [∀ i, Module.Finite A (M.X i)]
    [∀ i, Module.Free A (M'.X i)] [∀ i, Module.Finite A (M'.X i)]
    (hM : M.IsMinimal) (hM' : M'.IsMinimal) : IsIso α := by
  have := isKProjective_of_projective M b
  have := isKProjective_of_projective M' b'
  obtain ⟨e, rfl⟩ := (IsKProjective.quasiIso_iff α).1 inferInstance
  have (k : ℤ) : IsIso (e.hom.f k) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hM.bijective_of_homotopyEquiv hM' e k
  exact HomologicalComplex.Hom.isIso_of_components _

/-- If a complex of free modules over a local ring is not minimal, then there is an idempotent
null-homotopic chain endomorphism of it which is nonzero in some degree. -/
lemma exists_idem_homotopy_of_not_isMinimal (M : CochainComplex (ModuleCat.{v} A) ℤ)
    [∀ i, Module.Free A (M.X i)] (hM : ¬ M.IsMinimal) :
    ∃ (P : M ⟶ M) (_ : Homotopy P 0) (i : ℤ), P ≫ P = P ∧ (P.f i).hom ≠ 0 := by
  simp only [IsMinimal, not_forall] at hM
  obtain ⟨i, j, x, hx⟩ := hM
  obtain rfl : j = i + 1 := by
    by_contra h
    exact hx (by simp [M.shape i j (by simp only [ComplexShape.up_Rel]; omega)])
  obtain ⟨φ, hφ⟩ := Module.Free.exists_linearMap_eq_one_of_notMem_smul_top hx
  let G : M.X (i + 1) ⟶ M.X i := ModuleCat.ofHom (φ.smulRight x)
  refine ⟨singleNullHomotopicMap M i G, singleNullHomotopy M i G, i,
    singleNullHomotopicMap_idem M i G ?_, fun h ↦ ?_⟩
  · ext y
    simp [G, hφ]
  · have h' := LinearMap.congr_fun h x
    rw [singleNullHomotopicMap_f_self] at h'
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, G, ModuleCat.hom_ofHom,
      LinearMap.smulRight_apply, hφ, one_smul, LinearMap.zero_apply] at h'
    exact hx (by simp [h'])

section KerSubcomplexRank

variable {M : CochainComplex (ModuleCat.{v} A) ℤ} [∀ i, Module.Free A (M.X i)]
  [∀ i, Module.Finite A (M.X i)]

/-- The terms of the kernel subcomplex of an idempotent chain endomorphism of a complex of
finite free modules over a local ring are finite and free. -/
lemma free_and_finite_kerSubcomplex_X {P : M ⟶ M} (hP : P ≫ P = P) (k : ℤ) :
    Module.Free A ((kerSubcomplex P).X k) ∧ Module.Finite A ((kerSubcomplex P).X k) :=
  LinearMap.free_and_finite_ker_of_isIdempotentElem (isIdempotentElem_hom_f hP k)

/-- The ranks of the kernel and of the range of an idempotent chain endomorphism `P` add up to
the rank of the terms of `M`. -/
lemma finrank_kerSubcomplex_X_add {P : M ⟶ M} (hP : P ≫ P = P) (k : ℤ) :
    Module.finrank A ((kerSubcomplex P).X k) + Module.finrank A (LinearMap.range (P.f k).hom) =
      Module.finrank A (M.X k) :=
  LinearMap.finrank_ker_add_finrank_range_of_isIdempotentElem (isIdempotentElem_hom_f hP k)

/-- In degrees where the idempotent `P` is nonzero, the rank of the kernel subcomplex is
smaller than the rank of `M`. -/
lemma finrank_kerSubcomplex_X_lt {P : M ⟶ M} (hP : P ≫ P = P) {k : ℤ}
    (hk : (P.f k).hom ≠ 0) :
    Module.finrank A ((kerSubcomplex P).X k) < Module.finrank A (M.X k) := by
  obtain ⟨_, _⟩ := LinearMap.free_and_finite_range_of_isIdempotentElem
    (isIdempotentElem_hom_f hP k)
  have : Nontrivial (LinearMap.range (P.f k).hom) := by
    rwa [Submodule.nontrivial_iff_ne_bot, Ne, LinearMap.range_eq_bot]
  have := (Module.finrank_pos_iff_of_free A (LinearMap.range (P.f k).hom)).2 this
  have := finrank_kerSubcomplex_X_add hP k
  omega

end KerSubcomplexRank

/-- A strictly bounded complex of finite free modules over a local ring is homotopy equivalent
to a minimal complex with the same bounds, whose terms are again finite free. -/
theorem exists_homotopyEquiv_isMinimal (M : CochainComplex (ModuleCat.{v} A) ℤ) (a b : ℤ)
    [M.IsStrictlyGE a] [M.IsStrictlyLE b] [∀ i, Module.Free A (M.X i)]
    [∀ i, Module.Finite A (M.X i)] :
    ∃ M' : CochainComplex (ModuleCat.{v} A) ℤ, M'.IsMinimal ∧ M'.IsStrictlyGE a ∧
      M'.IsStrictlyLE b ∧ (∀ i, Module.Free A (M'.X i)) ∧ (∀ i, Module.Finite A (M'.X i)) ∧
      Nonempty (HomotopyEquiv M M') := by
  obtain ⟨n, hn⟩ : ∃ n, ∑ k ∈ Finset.Icc a b, Module.finrank A (M.X k) = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  by_cases hM : M.IsMinimal
  · exact ⟨M, hM, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨HomotopyEquiv.refl M⟩⟩
  obtain ⟨P, H, i, hP, hi⟩ := exists_idem_homotopy_of_not_isMinimal M hM
  have := isStrictlyGE_kerSubcomplex P a
  have := isStrictlyLE_kerSubcomplex P b
  have (k : ℤ) := (free_and_finite_kerSubcomplex_X hP k).1
  have (k : ℤ) := (free_and_finite_kerSubcomplex_X hP k).2
  have hia : i ∈ Finset.Icc a b := by
    rw [Finset.mem_Icc]
    by_contra h
    refine hi (LinearMap.ext fun x ↦ ?_)
    have : Subsingleton (M.X i) := by
      rw [← ModuleCat.isZero_iff_subsingleton]
      rcases not_and_or.1 h with h | h
      · exact M.isZero_of_isStrictlyGE a i (by omega)
      · exact M.isZero_of_isStrictlyLE b i (by omega)
    exact Subsingleton.elim _ _
  have hlt : ∑ k ∈ Finset.Icc a b, Module.finrank A ((kerSubcomplex P).X k) < n := by
    rw [← hn]
    refine Finset.sum_lt_sum (fun k _ ↦ ?_) ⟨i, hia, finrank_kerSubcomplex_X_lt hP hi⟩
    have := finrank_kerSubcomplex_X_add hP k
    omega
  obtain ⟨M', h₁, h₂, h₃, h₄, h₅, ⟨e⟩⟩ := ih _ hlt (kerSubcomplex P) rfl
  exact ⟨M', h₁, h₂, h₃, h₄, h₅, ⟨(homotopyEquivKerSubcomplex P hP H).trans e⟩⟩

end CochainComplex
