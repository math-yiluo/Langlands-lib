import Langlands.CommutativeAlgebra.FiniteKoszulHomotopy
import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # The finite subset Koszul complex and its generator homotopies -/

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Langlands.Cohomology.ModuleComplex

noncomputable section

namespace Langlands.CommutativeAlgebra

variable {R : Type u} [CommRing R]
variable {g : ℕ}

/-- The finite subset Koszul differential as a chain complex over the naturals. -/
def finiteKoszulChain (a : Fin g → R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (FiniteKoszulModule R (Fin g) n))
    (fun n ↦ ModuleCat.ofHom (finiteKoszulDifferential a n))
    (fun n ↦ ModuleCat.hom_ext (finiteKoszulDifferential_sq a n))

@[simp]
lemma finiteKoszulChain_d (a : Fin g → R) (n : ℕ) :
    (finiteKoszulChain a).d (n + 1) n = ModuleCat.ofHom (finiteKoszulDifferential a n) :=
  by
    change ChainComplex.of.d (fun n ↦ ModuleCat.of R (FiniteKoszulModule R (Fin g) n))
      (fun n ↦ ModuleCat.ofHom (finiteKoszulDifferential a n)) (n + 1) n = _
    exact ChainComplex.of_d _ _ n

/-- The degree-raising components of insertion, with zero components elsewhere. -/
def finiteKoszulChainInsertion (a : Fin g → R) (j : Fin g) (i k : ℕ) :
    (finiteKoszulChain a).X i ⟶ (finiteKoszulChain a).X k :=
  if h : k = i + 1 then
    ModuleCat.ofHom (finiteKoszulInsertion j i) ≫ eqToHom (by rw [h]; rfl) else 0

@[simp]
lemma finiteKoszulChainInsertion_succ (a : Fin g → R) (j : Fin g) (n : ℕ) :
    finiteKoszulChainInsertion a j n (n + 1) = ModuleCat.ofHom (finiteKoszulInsertion j n) := by
  dsimp [finiteKoszulChainInsertion, finiteKoszulChain]
  simp

/-- Multiplication by a Koszul parameter is chain null-homotopic. -/
def finiteKoszulChainGeneratorHomotopy (a : Fin g → R) (j : Fin g) :
    Homotopy (a j • 𝟙 (finiteKoszulChain a)) 0 where
  hom := finiteKoszulChainInsertion a j
  zero i k hik := by
    dsimp [finiteKoszulChainInsertion]
    split_ifs with h
    · subst k
      exact False.elim (hik (by simp [ComplexShape.down_Rel]))
    · rfl
  comm n := by
    cases n with
    | zero =>
      rw [dNext_eq_zero _ 0 (by simp [ComplexShape.down_Rel]),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 by simp)]
      apply ModuleCat.hom_ext
      change a j • LinearMap.id =
        0 + (finiteKoszulDifferential a 0).comp (finiteKoszulInsertion j 0) + 0
      simpa using (finiteKoszulInsertion_identity_zero a j).symm
    | succ n =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n by simp),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) by simp)]
      simp only [finiteKoszulChain_d, finiteKoszulChainInsertion_succ]
      apply ModuleCat.hom_ext
      change a j • LinearMap.id =
        (finiteKoszulInsertion j n).comp (finiteKoszulDifferential a n) +
          (finiteKoszulDifferential a (n + 1)).comp (finiteKoszulInsertion j (n + 1)) + 0
      simpa only [add_zero, zero_add, add_comm] using (finiteKoszulInsertion_identity a j n).symm

/-- Reindex the finite Koszul chain complex into degrees `0` through `g`. -/
def finiteKoszulCochain (a : Fin g → R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (finiteKoszulChain a).extend (ComplexShape.embeddingUpIntLE (g : ℤ))

/-- The term in degree `g-n` is the free module on the `n`-element subsets. -/
def finiteKoszulCochainXIso (a : Fin g → R) {i : ℤ} (n : ℕ)
    (hi : (g : ℤ) - n = i) :
    (finiteKoszulCochain a).X i ≅ ModuleCat.of R (FiniteKoszulModule R (Fin g) n) :=
  (finiteKoszulChain a).extendXIso (ComplexShape.embeddingUpIntLE (g : ℤ)) hi

/-- Koszul terms vanish above the number of generators. -/
lemma finiteKoszulChain_isZero (a : Fin g → R) (n : ℕ) (hn : g < n) :
    IsZero ((finiteKoszulChain a).X n) := by
  have : IsEmpty {s : Finset (Fin g) // s.card = n} := by
    refine ⟨fun s ↦ ?_⟩
    have h := s.val.card_le_univ
    simp only [Fintype.card_fin, s.property] at h
    omega
  change IsZero (ModuleCat.of R (FiniteKoszulModule R (Fin g) n))
  exact ModuleCat.isZero_of_subsingleton _

lemma finiteKoszulCochain_isStrictlyGE (a : Fin g → R) :
    (finiteKoszulCochain a).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  by_cases h : ∃ n : ℕ, (g : ℤ) - n = i
  · obtain ⟨n, hn⟩ := h
    exact IsZero.of_iso (finiteKoszulChain_isZero a n (by omega))
      (finiteKoszulCochainXIso a n hn)
  · exact (finiteKoszulChain a).isZero_extend_X _ i (by simpa using h)

lemma finiteKoszulCochain_isStrictlyLE (a : Fin g → R) :
    (finiteKoszulCochain a).IsStrictlyLE (g : ℤ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (finiteKoszulChain a).isZero_extend_X _ i (by
    intro n hn
    change (g : ℤ) - n = i at hn
    omega)

/-- The integer-indexed Koszul complex is a bounded finite free complex. -/
lemma finiteKoszulCochain_isFiniteFree (a : Fin g → R) :
    IsFiniteFree (finiteKoszulCochain a) := by
  refine ⟨⟨0, g, finiteKoszulCochain_isStrictlyGE a,
    finiteKoszulCochain_isStrictlyLE a⟩, fun i ↦ ?_⟩
  by_cases h : ∃ n : ℕ, (g : ℤ) - n = i
  · obtain ⟨n, hn⟩ := h
    let e := (finiteKoszulCochainXIso a n hn).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩
  · have hz : IsZero ((finiteKoszulCochain a).X i) :=
      (finiteKoszulChain a).isZero_extend_X
      (ComplexShape.embeddingUpIntLE (g : ℤ)) i (by simpa using h)
    have := ModuleCat.subsingleton_of_isZero hz
    exact ⟨inferInstance, inferInstance⟩

/-- Multiplication by a parameter is null-homotopic on the integer complex. -/
def finiteKoszulCochainGeneratorHomotopy (a : Fin g → R) (j : Fin g) :
    Homotopy (a j • 𝟙 (finiteKoszulCochain a)) 0 := by
  let e := ComplexShape.embeddingUpIntLE (g : ℤ)
  have hs : extendMap (a j • 𝟙 (finiteKoszulChain a)) e =
      a j • 𝟙 ((finiteKoszulChain a).extend e) := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases h : ∃ n : ℕ, e.f n = i
    · obtain ⟨n, hn⟩ := h
      rw [extendMap_f _ _ hn]
      simp only [smul_f_apply, id_f, Linear.comp_smul, Category.id_comp,
        Linear.smul_comp, Iso.hom_inv_id]
    · exact ((finiteKoszulChain a).isZero_extend_X e i (by simpa using h)).eq_of_src _ _
  change Homotopy (a j • 𝟙 ((finiteKoszulChain a).extend e)) 0
  simpa only [hs, extendMap_zero] using
    (finiteKoszulChainGeneratorHomotopy a j).extend e

/-- The ideal generated by the parameters annihilates every Koszul homology module. -/
lemma finiteKoszulCochain_span_le_annihilator (a : Fin g → R) (i : ℤ) :
    Ideal.span (Set.range a) ≤ Module.annihilator R ((finiteKoszulCochain a).homology i) := by
  rw [Ideal.span_le]
  rintro r ⟨j, rfl⟩
  apply Module.mem_annihilator.mpr
  intro z
  have h := (finiteKoszulCochainGeneratorHomotopy a j).homologyMap_eq i
  change ShortComplex.homologyMap (a j • 𝟙 ((finiteKoszulCochain a).sc i)) =
    ShortComplex.homologyMap 0 at h
  rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id,
    ShortComplex.homologyMap_zero] at h
  exact congrArg (fun f ↦ f.hom z) h

end Langlands.CommutativeAlgebra
