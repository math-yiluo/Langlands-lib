/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatBaseChangeSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexSplit
public import WeilConjectures.AlgebraicGeometry.Modules.HomSection
public import WeilConjectures.LinearAlgebra.Matrix.ComplementaryMinors

/-!
# Complexes of finite free modules near a point

Let `P` be a bounded complex of finite free `𝒪_Y`-modules, with differentials given by matrices of
global functions. This file relates the cohomology of the pullbacks of `P` to the ranks of these
matrices at the points of `Y`.

* On a scheme `X` with a point `x` whose only open neighbourhood is `X` itself, such as the
  spectrum of a local ring, epimorphisms of modules are surjective on global sections, so the
  exactness of a complex of free modules can be read off from its matrices
  (`AlgebraicGeometry.Scheme.Modules.exists_freeMatrix_mul_eq_of_isZero_homology`).
* If the cohomology of `g^* P` vanishes outside degree `i` and is finite locally free of rank `k`
  in degree `i`, then at every point `y` in the image of `g` the ranks of the matrices of the
  differentials satisfy `rank A_{q-1}(y) + rank A_q(y) + [q = i] k = rank P^q`
  (`AlgebraicGeometry.Scheme.Modules.rank_add_rank_add_eq_of_isFiniteLocallyFreeInDegree`): pull
  back further to the spectrum of the local ring at a point, where the algebra of
  `Matrix.rank_map_add_rank_map_add_eq_of_exact` applies.
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Local

variable {x : X} (hx : ∀ W : X.Opens, x ∈ W → W = ⊤)
include hx

/-- On a scheme with a point `x` whose only open neighbourhood is the whole scheme, a morphism
`𝒪_X ⟶ N` lifts along every epimorphism `M ⟶ N`. -/
lemma exists_comp_eq_of_epi_of_unit {M N : X.Modules} (p : M ⟶ N) [Epi p]
    (φ : unit X ⟶ N) : ∃ φ' : unit X ⟶ M, φ' ≫ p = φ := by
  have : Epi ((toAb X).map p) := inferInstance
  have h := (Sheaf.isLocallySurjective_iff_epi' (φ := (toAb X).map p)).2 this
  have h' : TopCat.Presheaf.IsLocallySurjective ((toPresheaf X).map p) := h
  rw [TopCat.Presheaf.isLocallySurjective_iff] at h'
  obtain ⟨V, hV, ⟨m, hm⟩, hxV⟩ := h' ⊤ (φ.app ⊤ (1 : Γ(X, ⊤))) x trivial
  obtain rfl := hx V hxV
  refine ⟨homOfGlobalSection M m, unit_hom_ext ?_⟩
  rw [Hom.comp_app, ConcreteCategory.comp_apply, homOfGlobalSection_app_one,
    presheaf_map_id_apply]
  exact hm.trans (presheaf_map_id_apply _ _)

/-- On a scheme with a point `x` whose only open neighbourhood is the whole scheme, a morphism
from a free module lifts along every epimorphism. -/
lemma exists_comp_eq_of_epi {M N : X.Modules} (p : M ⟶ N) [Epi p] {I : Type u}
    (φ : free (R := X.ringCatSheaf) I ⟶ N) : ∃ φ' : free I ⟶ M, φ' ≫ p = φ := by
  choose ψ hψ using fun i : I ↦ exists_comp_eq_of_epi_of_unit hx p (ιFree i ≫ φ)
  refine ⟨Sigma.desc ψ, Sigma.hom_ext _ _ fun i ↦ ?_⟩
  rw [Sigma.ι_comp_desc_assoc, hψ]
  rfl

/-- On a scheme with a point `x` whose only open neighbourhood is the whole scheme, a morphism
from a free module to the middle term of an exact short complex, killed by the outgoing map,
factors through the incoming map. -/
lemma exists_comp_eq_of_exact {S : ShortComplex X.Modules} (hS : S.Exact) {I : Type u}
    (κ : free (R := X.ringCatSheaf) I ⟶ S.X₂) (hκ : κ ≫ S.g = 0) :
    ∃ μ : free I ⟶ S.X₁, μ ≫ S.f = κ := by
  have := hS.epi_toCycles
  obtain ⟨μ, hμ⟩ := exists_comp_eq_of_epi hx S.toCycles (S.liftCycles κ hκ)
  refine ⟨μ, ?_⟩
  rw [← S.toCycles_i, ← Category.assoc, hμ, S.liftCycles_i]

end Local


section Matrices

variable (Q : CochainComplex X.Modules ℤ) {ι : ℤ → Type u} [∀ n, Fintype (ι n)]
  [∀ n, DecidableEq (ι n)] (e : ∀ n, Q.X n ≅ free (R := X.ringCatSheaf) (ι n))

/-- The matrix of `μ ≫ d` for a morphism `μ` from a free module to a term of a complex of free
modules. -/
lemma freeMatrix_comp_d {c : Type u} {n m : ℤ} (μ : free (R := X.ringCatSheaf) c ⟶ Q.X n) :
    freeMatrix (μ ≫ Q.d n m ≫ (e m).hom) =
      freeMatrix ((e n).inv ≫ Q.d n m ≫ (e m).hom) * freeMatrix (μ ≫ (e n).hom) := by
  rw [← freeMatrix_comp]
  simp

omit [∀ n, Fintype (ι n)] in
/-- A morphism from a free module of finite rank to a term of a complex of free modules is
determined by its matrix. -/
lemma eq_of_freeMatrix_comp_eq {c : Type u} [Finite c] {n : ℤ} [Finite (ι n)]
    {μ μ' : free (R := X.ringCatSheaf) c ⟶ Q.X n}
    (h : freeMatrix (μ ≫ (e n).hom) = freeMatrix (μ' ≫ (e n).hom)) : μ = μ' := by
  have := freeMatrix_injective h
  simpa using congrArg (· ≫ (e n).inv) this

variable {Q}

/-- The morphism `𝒪^c ⟶ Q^q` with a given matrix `K`, followed by `d`, has matrix `A_q K`. -/
lemma freeMatrix_freeHomOfMatrix_comp_d {c : Type u} [Fintype c] [DecidableEq c] {n m : ℤ}
    (K : Matrix (ι n) c Γ(X, ⊤)) :
    freeMatrix ((freeHomOfMatrix K ≫ (e n).inv) ≫ Q.d n m ≫ (e m).hom) =
      freeMatrix ((e n).inv ≫ Q.d n m ≫ (e m).hom) * K := by
  rw [freeMatrix_comp_d]
  simp

/-- If the matrix of `d` kills `K`, then `d` kills the morphism of matrix `K`. -/
lemma freeHomOfMatrix_comp_d_eq_zero {c : Type u} [Fintype c] [DecidableEq c] {n m : ℤ}
    (K : Matrix (ι n) c Γ(X, ⊤)) (hK : freeMatrix ((e n).inv ≫ Q.d n m ≫ (e m).hom) * K = 0) :
    (freeHomOfMatrix K ≫ (e n).inv) ≫ Q.d n m = 0 := by
  have h := freeMatrix_freeHomOfMatrix_comp_d e (m := m) K
  rw [hK, ← freeMatrix_zero] at h
  have := freeMatrix_injective h
  simpa using congrArg (· ≫ (e m).inv) this

variable {x : X} (hx : ∀ W : X.Opens, x ∈ W → W = ⊤)
include hx

/-- **Exactness in matrix form.** On a scheme with a point `x` whose only open neighbourhood is
the whole scheme, let `Q` be a complex of free modules of finite rank whose cohomology in degree
`q` vanishes. Then every matrix `K` killed by the matrix of `d^q` is the matrix of `d^{q-1}` times
some matrix. -/
lemma exists_freeMatrix_mul_eq_of_isZero_homology (q : ℤ) (hq : IsZero (Q.homology q))
    (c : Type u) [Finite c] (K : Matrix (ι q) c Γ(X, ⊤))
    (hK : freeMatrix ((e q).inv ≫ Q.d q (q + 1) ≫ (e (q + 1)).hom) * K = 0) :
    ∃ V : Matrix (ι (q - 1)) c Γ(X, ⊤),
      freeMatrix ((e (q - 1)).inv ≫ Q.d (q - 1) q ≫ (e q).hom) * V = K := by
  classical
  have := Fintype.ofFinite c
  have hS : (Q.sc' (q - 1) q (q + 1)).Exact := by
    rw [← HomologicalComplex.exactAt_iff' Q (q - 1) q (q + 1) (by simp) (by simp),
      HomologicalComplex.exactAt_iff_isZero_homology]
    exact hq
  obtain ⟨μ, hμ⟩ := exists_comp_eq_of_exact hx hS _ (freeHomOfMatrix_comp_d_eq_zero e K hK)
  refine ⟨freeMatrix (μ ≫ (e (q - 1)).hom), ?_⟩
  rw [← freeMatrix_comp_d]
  change freeMatrix (μ ≫ (Q.sc' (q - 1) q (q + 1)).f ≫ (e q).hom) = K
  rw [← Category.assoc, hμ, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    freeMatrix_freeHomOfMatrix]

/-- **Free cohomology in matrix form.** On a scheme with a point `x` whose only open
neighbourhood is the whole scheme, let `Q` be a complex of free modules of finite rank whose
cohomology in degree `i` is free on `κ`. Then there is a matrix `C` whose columns are cycles in
degree `i`, such that every cycle is a boundary plus a combination of the columns of `C`, uniquely
so. -/
lemma exists_freeMatrix_of_homology_iso (i : ℤ) {κ : Type u} [Fintype κ]
    (φ : Q.homology i ≅ free (R := X.ringCatSheaf) κ) :
    ∃ C : Matrix (ι i) κ Γ(X, ⊤),
      freeMatrix ((e i).inv ≫ Q.d i (i + 1) ≫ (e (i + 1)).hom) * C = 0 ∧
      (∀ K : Matrix (ι i) (ι i) Γ(X, ⊤),
        freeMatrix ((e i).inv ≫ Q.d i (i + 1) ≫ (e (i + 1)).hom) * K = 0 →
        ∃ (V : Matrix (ι (i - 1)) (ι i) Γ(X, ⊤)) (V' : Matrix κ (ι i) Γ(X, ⊤)),
          freeMatrix ((e (i - 1)).inv ≫ Q.d (i - 1) i ≫ (e i).hom) * V + C * V' = K) ∧
      (∀ (c : Type u) [Finite c] (U : Matrix (ι (i - 1)) c Γ(X, ⊤))
        (V' : Matrix κ c Γ(X, ⊤)),
        freeMatrix ((e (i - 1)).inv ≫ Q.d (i - 1) i ≫ (e i).hom) * U + C * V' = 0 → V' = 0) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_epi hx (Q.homologyπ i) φ.inv
  have hS : (ShortComplex.mk (Q.toCycles (i - 1) i) (Q.homologyπ i)
      (Q.toCycles_comp_homologyπ (i - 1) i)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (Q.homologyIsCokernel (i - 1) i (by simp))
  refine ⟨freeMatrix (ψ ≫ Q.iCycles i ≫ (e i).hom), ?_, fun K hK ↦ ?_,
    fun c _ U V' h ↦ ?_⟩
  · rw [← freeMatrix_comp]
    simp
  · set κ' := freeHomOfMatrix K ≫ (e i).inv
    have hκ' : κ' ≫ Q.d i (i + 1) = 0 := freeHomOfMatrix_comp_d_eq_zero e K hK
    set lc := Q.liftCycles κ' (i + 1) (by simp) hκ'
    set v := lc ≫ Q.homologyπ i ≫ φ.hom
    have hw : (lc - v ≫ ψ) ≫ Q.homologyπ i = 0 := by
      simp [v, hψ]
    obtain ⟨μ, hμ⟩ := exists_comp_eq_of_exact hx hS _ hw
    refine ⟨freeMatrix (μ ≫ (e (i - 1)).hom), freeMatrix v, ?_⟩
    have h₁ : κ' = μ ≫ Q.d (i - 1) i + v ≫ ψ ≫ Q.iCycles i := by
      have : lc = μ ≫ Q.toCycles (i - 1) i + v ≫ ψ := by
        rw [← sub_eq_iff_eq_add]
        exact hμ.symm
      rw [← Q.liftCycles_i κ' (i + 1) (by simp) hκ', ← Q.toCycles_i (i - 1) i]
      change lc ≫ _ = _
      rw [this, Preadditive.add_comp, Category.assoc, Category.assoc]
    rw [← freeMatrix_comp_d, ← freeMatrix_comp, ← freeMatrix_add]
    conv_rhs => rw [← freeMatrix_freeHomOfMatrix K]
    congr 1
    rw [show freeHomOfMatrix K = κ' ≫ (e i).hom by simp [κ'], h₁]
    simp
  · have := Fintype.ofFinite c
    set u := freeHomOfMatrix U
    set v' := freeHomOfMatrix V'
    have h₁ : (u ≫ (e (i - 1)).inv ≫ Q.toCycles (i - 1) i + v' ≫ ψ) ≫ Q.iCycles i = 0 := by
      refine eq_of_freeMatrix_comp_eq Q e ?_
      rw [zero_comp, freeMatrix_zero, ← h, Preadditive.add_comp, Preadditive.add_comp,
        freeMatrix_add]
      congr 1
      · have : ((u ≫ (e (i - 1)).inv ≫ Q.toCycles (i - 1) i) ≫ Q.iCycles i) ≫ (e i).hom =
            (u ≫ (e (i - 1)).inv) ≫ Q.d (i - 1) i ≫ (e i).hom := by simp
        rw [this, freeMatrix_freeHomOfMatrix_comp_d]
      · have : ((v' ≫ ψ) ≫ Q.iCycles i) ≫ (e i).hom = v' ≫ ψ ≫ Q.iCycles i ≫ (e i).hom := by
          simp
        rw [this, freeMatrix_comp, freeMatrix_freeHomOfMatrix]
    have h₂ := (cancel_mono (Q.iCycles i)).1 (h₁.trans (zero_comp).symm)
    have h₃ : v' ≫ φ.inv = 0 := by
      have := congrArg (· ≫ Q.homologyπ i) h₂
      simpa [hψ] using this
    have h₄ : v' = 0 := by simpa using congrArg (· ≫ φ.hom) h₃
    rw [← freeMatrix_freeHomOfMatrix V']
    change freeMatrix v' = 0
    rw [h₄, freeMatrix_zero]

end Matrices

end AlgebraicGeometry.Scheme.Modules
