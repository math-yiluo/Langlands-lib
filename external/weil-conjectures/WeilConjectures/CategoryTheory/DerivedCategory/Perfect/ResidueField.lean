/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.LocalRing

/-!
# Testing Tor amplitude at the residue field

Let `R` be an Artinian local ring with residue field `κ`, for instance the finite coefficient
ring `A_{E,n} = 𝒪_E/ϖⁿ`. An object `C` of `D(R)` has Tor amplitude in `[a, b]` as soon as
`C ⊗ᴸ κ` has cohomology in `[a, b]`; the converse is the definition of Tor amplitude. This is the
module-theoretic half of blueprint `theorem-f-shriek-finite-coefficients--1`.

## Proof

Represent `C` by a K-flat complex `P` of flat modules, so that `C ⊗ᴸ M[0]` is the complex
`P ⊗ M`. For a fixed degree `q`, the class of modules `M` for which `P ⊗ M` is exact at `q` is
closed under extensions (`LinearMap.exact_rTensor_of_exact`, a diagram chase using the flatness
of `P^{q+1}`) and under directed unions of finitely generated submodules
(`LinearMap.exact_rTensor_of_forall_finite`). Every finitely generated module over the Artinian
local ring `R` is an iterated extension of copies of `κ`, by induction on its length, so the
class contains every module as soon as it contains `κ`.

No boundedness or finiteness of `C` is needed.

## Main statements

- `LinearMap.exact_rTensor_of_exact_rTensor_residueField`: the module-theoretic core.
- `DerivedCategory.torAmplitudeIn_of_homologyConcentratedIn_tensor_residueField` and
  `DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor_residueField`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory TensorProduct Function

namespace LinearMap

variable {R : Type u} [CommRing R] {P₀ P₁ P₂ : Type*} [AddCommGroup P₀] [Module R P₀]
  [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
  (f : P₀ →ₗ[R] P₁) (g : P₁ →ₗ[R] P₂)

/-- Tensoring a pair `P₀ ⟶ P₁ ⟶ P₂` with a subsingleton module gives an exact pair. -/
lemma exact_rTensor_of_subsingleton {M : Type*} [AddCommGroup M] [Module R M] [Subsingleton M] :
    Exact (f.rTensor M) (g.rTensor M) := by
  have : Subsingleton (P₁ ⊗[R] M) := inferInstance
  intro y
  rw [Subsingleton.elim y 0]
  simpa using ⟨0, map_zero _⟩

/-- Let `P₀ ⟶ P₁ ⟶ P₂` be a complex with `P₂` flat. If tensoring it with every finitely
generated submodule of `M` gives an exact pair, so does tensoring it with `M`: every element of
`P₁ ⊗ M` comes from `P₁ ⊗ N` for a finitely generated `N ≤ M`, and `P₂ ⊗ N ⟶ P₂ ⊗ M` is
injective. -/
lemma exact_rTensor_of_forall_finite [Module.Flat R P₂] (hgf : g ∘ₗ f = 0) {M : Type*}
    [AddCommGroup M] [Module R M]
    (h : ∀ N : Submodule R M, Module.Finite R N → Exact (f.rTensor N) (g.rTensor N)) :
    Exact (f.rTensor M) (g.rTensor M) := by
  intro y
  constructor
  · intro hy
    obtain ⟨N, hN, hyN⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite {y}
      (Set.finite_singleton y)
    obtain ⟨y', rfl⟩ := hyN (Set.mem_singleton y)
    have hinj : Injective (N.subtype.lTensor P₂) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype
    have hy' : g.rTensor N y' = 0 := by
      apply hinj
      rw [map_zero, ← LinearMap.comp_apply, lTensor_comp_rTensor, ← rTensor_comp_lTensor]
      exact hy
    obtain ⟨x', rfl⟩ := ((h N hN) y').1 hy'
    refine ⟨N.subtype.lTensor P₀ x', ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, rTensor_comp_lTensor,
      lTensor_comp_rTensor]
  · rintro ⟨x, rfl⟩
    rw [← LinearMap.comp_apply, ← rTensor_comp, hgf, rTensor_zero, zero_apply]

/-- Let `P₀ ⟶ P₁ ⟶ P₂` be a complex with `P₂` flat and `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` a short exact
sequence. If tensoring the complex with `M₁` and with `M₃` gives exact pairs, so does tensoring
it with `M₂`. -/
lemma exact_rTensor_of_exact [Module.Flat R P₂] (hgf : g ∘ₗ f = 0) {M₁ M₂ M₃ : Type*}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃]
    [Module R M₃] (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃) (hi : Injective i) (hp : Surjective p)
    (hip : Exact i p) (h₁ : Exact (f.rTensor M₁) (g.rTensor M₁))
    (h₃ : Exact (f.rTensor M₃) (g.rTensor M₃)) :
    Exact (f.rTensor M₂) (g.rTensor M₂) := by
  intro y
  constructor
  · intro hy
    -- push `y` to `P₁ ⊗ M₃`, where it is a cycle, hence a boundary
    have hy₃ : g.rTensor M₃ (p.lTensor P₁ y) = 0 := by
      rw [← LinearMap.comp_apply, rTensor_comp_lTensor, ← lTensor_comp_rTensor,
        LinearMap.comp_apply, hy, map_zero]
    obtain ⟨x₃, hx₃⟩ := (h₃ _).1 hy₃
    obtain ⟨x₂, rfl⟩ := lTensor_surjective P₀ hp x₃
    -- `y - f x₂` comes from `P₁ ⊗ M₁`
    have hz : p.lTensor P₁ (y - f.rTensor M₂ x₂) = 0 := by
      rw [map_sub, ← hx₃, ← LinearMap.comp_apply (p.lTensor P₁), lTensor_comp_rTensor,
        ← rTensor_comp_lTensor, LinearMap.comp_apply, sub_self]
    obtain ⟨y₁, hy₁⟩ := (lTensor_exact P₁ hip hp _).1 hz
    -- `y₁` is a cycle, since `P₂ ⊗ M₁ ⟶ P₂ ⊗ M₂` is injective
    have hinj : Injective (i.lTensor P₂) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hi
    have hgy₁ : g.rTensor M₁ y₁ = 0 := by
      apply hinj
      rw [map_zero, ← LinearMap.comp_apply, lTensor_comp_rTensor, ← rTensor_comp_lTensor,
        LinearMap.comp_apply, hy₁, map_sub, hy, ← LinearMap.comp_apply (g.rTensor M₂),
        ← rTensor_comp, hgf, rTensor_zero, zero_apply, sub_zero]
    obtain ⟨x₁, rfl⟩ := (h₁ _).1 hgy₁
    refine ⟨x₂ + i.lTensor P₀ x₁, ?_⟩
    rw [map_add, ← LinearMap.comp_apply (f.rTensor M₂), rTensor_comp_lTensor,
      ← lTensor_comp_rTensor, LinearMap.comp_apply, hy₁, add_sub_cancel]
  · rintro ⟨x, rfl⟩
    rw [← LinearMap.comp_apply, ← rTensor_comp, hgf, rTensor_zero, zero_apply]

/-- Exactness after tensoring is invariant under linear equivalence of the module. -/
lemma exact_rTensor_of_linearEquiv [Module.Flat R P₂] (hgf : g ∘ₗ f = 0) {M M' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M')
    (h : Exact (f.rTensor M) (g.rTensor M)) : Exact (f.rTensor M') (g.rTensor M') :=
  exact_rTensor_of_exact f g hgf (e : M →ₗ[R] M') (0 : M' →ₗ[R] PUnit.{1}) e.injective
    (fun _ ↦ ⟨0, rfl⟩) (fun y ↦ by simp)
    h (exact_rTensor_of_subsingleton f g)

variable [IsLocalRing R] [IsArtinianRing R]

/-- Over an Artinian local ring, a nontrivial finitely generated module contains a submodule
isomorphic to the residue field: an atom of its lattice of submodules. -/
lemma exists_submodule_linearEquiv_residueField (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    ∃ S : Submodule R M, S ≠ ⊥ ∧ Nonempty (S ≃ₗ[R] IsLocalRing.ResidueField R) := by
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule R M)).resolve_left top_ne_bot
  have : IsSimpleModule R S := isSimpleModule_iff_isAtom.2 hS
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 this
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  exact ⟨S, hS.1, ⟨e⟩⟩

/-- Over an Artinian local ring `R` with residue field `κ`, let `P₀ ⟶ P₁ ⟶ P₂` be a complex with
`P₂` flat. If it stays exact after tensoring with `κ`, it stays exact after tensoring with every
module `M`. -/
theorem exact_rTensor_of_exact_rTensor_residueField [Module.Flat R P₂] (hgf : g ∘ₗ f = 0)
    (hκ : Exact (f.rTensor (IsLocalRing.ResidueField R)) (g.rTensor (IsLocalRing.ResidueField R)))
    (M : Type*) [AddCommGroup M] [Module R M] :
    Exact (f.rTensor M) (g.rTensor M) := by
  refine exact_rTensor_of_forall_finite f g hgf fun N _ ↦ ?_
  -- induction on the length of a finitely generated module
  suffices H : ∀ (n : ℕ) (M : Type _) [AddCommGroup M] [Module R M] [Module.Finite R M],
      Module.length R M = n → Exact (f.rTensor M) (g.rTensor M) by
    exact H _ N (ENat.natCast_toNat Module.length_ne_top).symm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ _ hn
    cases subsingleton_or_nontrivial M with
    | inl _ => exact exact_rTensor_of_subsingleton f g
    | inr _ =>
      obtain ⟨S, hS, ⟨e⟩⟩ := exists_submodule_linearEquiv_residueField (R := R) M
      have hlt := Submodule.length_quotient_lt S hS
      have hm : Module.length R (M ⧸ S) = ((Module.length R (M ⧸ S)).toNat : ℕ∞) :=
        (ENat.natCast_toNat Module.length_ne_top).symm
      have hlt' : (Module.length R (M ⧸ S)).toNat < n := by
        rw [hn, hm] at hlt
        exact_mod_cast hlt
      exact exact_rTensor_of_exact f g hgf S.subtype S.mkQ S.injective_subtype
        S.mkQ_surjective (LinearMap.exact_subtype_mkQ S)
        (exact_rTensor_of_linearEquiv f g hgf e.symm hκ) (ih _ hlt' _ hm)

end LinearMap

namespace DerivedCategory

section General

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

/-- For a K-flat complex `P` representing `K ∈ D(C)` and an object `F` of `C`, the homology of
`K ⊗ᴸ F[0]` in degree `q` vanishes exactly when the complex `P ⊗ F` is exact in degree `q`. -/
lemma isZero_homology_tensor_iff_exactAt {K : DerivedCategory C} {P : CochainComplex C ℤ}
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) (e : Q.obj P ≅ K) (F : C) (q : ℤ) :
    IsZero ((homologyFunctor C q).obj (K ⊗ (singleFunctor C 0).obj F)) ↔
      (((tensorRight F).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact Iso.isZero_iff ((homologyFunctor _ q).mapIso
    ((whiskerRightIso e.symm _) ≪≫ QObjTensorSingleFunctorObjIso P hP F) ≪≫
      (homologyFunctorFactors _ q).app _)

/-- For a K-flat complex `P` representing `K ∈ D(C)` and an object `F` of `C`, `K ⊗ᴸ F[0]` has
homology concentrated in `[a, b]` exactly when the complex `P ⊗ F` is exact outside `[a, b]`. -/
lemma homologyConcentratedIn_tensor_iff_exactAt {K : DerivedCategory C}
    {P : CochainComplex C ℤ} (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P)
    (e : Q.obj P ≅ K) (F : C) (a b : ℤ) :
    homologyConcentratedIn a b (K ⊗ (singleFunctor C 0).obj F) ↔
      ∀ q : ℤ, q < a ∨ b < q →
        (((tensorRight F).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).ExactAt q := by
  refine ⟨fun ⟨h₁, h₂⟩ q hq ↦ (isZero_homology_tensor_iff_exactAt hP e F q).1 ?_,
    fun h ↦ ⟨(isGE_iff _ a).2 fun q hq ↦ (isZero_homology_tensor_iff_exactAt hP e F q).2
      (h q (Or.inl hq)), (isLE_iff _ b).2 fun q hq ↦
        (isZero_homology_tensor_iff_exactAt hP e F q).2 (h q (Or.inr hq))⟩⟩
  rcases hq with hq | hq
  · exact (isGE_iff _ a).1 h₁ q hq
  · exact (isLE_iff _ b).1 h₂ q hq

/-- For a K-flat complex `P` representing `K ∈ D(C)`, `K` has Tor amplitude in `[a, b]` exactly
when every complex `P ⊗ F` is exact outside `[a, b]`. -/
lemma torAmplitudeIn_iff_forall_exactAt {K : DerivedCategory C} {P : CochainComplex C ℤ}
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) (e : Q.obj P ≅ K) (a b : ℤ) :
    torAmplitudeIn C a b K ↔ ∀ (F : C) (q : ℤ), q < a ∨ b < q →
      (((tensorRight F).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).ExactAt q :=
  forall_congr' fun F ↦ homologyConcentratedIn_tensor_iff_exactAt hP e F a b

/-- Every object of `D(C)` is represented by a K-flat complex of flat objects. -/
lemma exists_kFlat_flat_iso (K : DerivedCategory C) :
    ∃ (P : CochainComplex C ℤ), (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P ∧
      (∀ n, ObjectProperty.flat (P.X n)) ∧ Nonempty (Q.obj P ≅ K) := by
  obtain ⟨P, π, _, hP, hPk⟩ := CochainComplex.exists_quasiIso_flat_kFlat (Q.objPreimage K)
  have : IsIso (Q.map π) := by rwa [isIso_Q_map_iff_quasiIso]
  exact ⟨P, hPk, hP, ⟨asIso (Q.map π) ≪≫ Q.objObjPreimageIso K⟩⟩

end General

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

omit [HasDerivedCategory (ModuleCat R)] in
/-- For a complex `P` of `R`-modules and a module `M`, the complex `P ⊗ M` is exact in degree `q`
exactly when tensoring `P^{q-1} ⟶ P^q ⟶ P^{q+1}` with `M` gives an exact pair. -/
lemma exactAt_tensorRight_iff (P : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R)
    (q : ℤ) :
    (((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).ExactAt q ↔
      Function.Exact ((P.d (q - 1) q).hom.rTensor M) ((P.d q (q + 1)).hom.rTensor M) := by
  rw [HomologicalComplex.exactAt_iff' _ (q - 1) q (q + 1) (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

omit [HasDerivedCategory (ModuleCat R)] in
/-- Over an Artinian local ring `R` with residue field `κ`, let `P` be a complex of flat
modules. If `P ⊗ κ` is exact in degree `q`, so is `P ⊗ M` for every module `M`. -/
lemma exactAt_tensorRight_of_exactAt_tensorRight_residueField [IsLocalRing R]
    [IsArtinianRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ n, ObjectProperty.flat (P.X n)) (q : ℤ)
    (hκ : (((tensorRight (ModuleCat.of R (IsLocalRing.ResidueField R))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).ExactAt q) (M : ModuleCat.{u} R) :
    (((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).ExactAt q := by
  rw [exactAt_tensorRight_iff] at hκ ⊢
  have : Module.Flat R (P.X (q + 1)) := (ModuleCat.flat_iff_flat _).1 (hP _)
  refine LinearMap.exact_rTensor_of_exact_rTensor_residueField _ _ ?_ hκ M
  rw [← ModuleCat.hom_comp, P.d_comp_d, ModuleCat.hom_zero]

/-- Blueprint `theorem-f-shriek-finite-coefficients--1`: Testing finite Tor amplitude at the residue
field (over a point).

Let `R` be an Artinian local ring with residue field `κ` (for instance `A_{E,n} = 𝒪_E/ϖⁿ`), and
let `C ∈ D(R)` be such that `C ⊗ᴸ κ` has cohomology in `[a, b]`. Then `C` has Tor amplitude in
`[a, b]`. Represent `C` by a K-flat complex `P` of flat modules: the exactness of `P ⊗ κ` in a
degree `q` propagates to the exactness of `P ⊗ M` for every module `M`
(`LinearMap.exact_rTensor_of_exact_rTensor_residueField`). -/
theorem torAmplitudeIn_of_homologyConcentratedIn_tensor_residueField [IsLocalRing R]
    [IsArtinianRing R] {a b : ℤ} (C : DerivedCategory (ModuleCat.{u} R))
    (hC : homologyConcentratedIn a b (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R)))) :
    torAmplitudeIn (ModuleCat.{u} R) a b C := by
  obtain ⟨P, hPk, hP, ⟨e⟩⟩ := exists_kFlat_flat_iso C
  rw [homologyConcentratedIn_tensor_iff_exactAt hPk e] at hC
  exact (torAmplitudeIn_iff_forall_exactAt hPk e a b).2 fun M q hq ↦
    exactAt_tensorRight_of_exactAt_tensorRight_residueField P hP q (hC q hq) M

/-- Blueprint `theorem-f-shriek-finite-coefficients--1`: Testing finite Tor amplitude at the residue
field (over a point).

Over an Artinian local ring `R` with residue field `κ`, an object `C ∈ D(R)` has Tor amplitude in
`[a, b]` if and only if `C ⊗ᴸ κ` has cohomology in `[a, b]`. -/
theorem torAmplitudeIn_iff_homologyConcentratedIn_tensor_residueField [IsLocalRing R]
    [IsArtinianRing R] {a b : ℤ} (C : DerivedCategory (ModuleCat.{u} R)) :
    torAmplitudeIn (ModuleCat.{u} R) a b C ↔
      homologyConcentratedIn a b (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (IsLocalRing.ResidueField R))) :=
  ⟨fun h ↦ h _, torAmplitudeIn_of_homologyConcentratedIn_tensor_residueField C⟩

end DerivedCategory
