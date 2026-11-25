/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeMatrix
public import WeilConjectures.Algebra.Homology.ShortComplex.SplitHomology
public import WeilConjectures.LinearAlgebra.Matrix.SplitFactorization
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Free cohomology of complexes of free modules with split differentials

This is the linear algebra behind Grauert's theorem.

* On a reduced scheme, a matrix of functions whose rank is at most `ρ` at every point of an open
  `N`, and exactly `ρ` at a point `y ∈ N`, has a split rank factorisation `A = L M` through `𝒪^ρ`
  on a neighbourhood of `y`
  (`AlgebraicGeometry.Scheme.Modules.exists_split_factorization`): an invertible `ρ × ρ` minor
  at `y` stays invertible nearby, and the `(ρ + 1) × (ρ + 1)` minors vanish at every point, hence
  vanish as the scheme is reduced.
* If the middle term of a complex of finite free modules is split by matrices into a free retract
  `𝒪^k`, the image of the incoming differential and a complement of the kernel of the outgoing one,
  its cohomology is `𝒪^k`
  (`AlgebraicGeometry.Scheme.Modules.nonempty_homology_iso_free_of_split`).
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

/-- The rank of a matrix of functions at a field-valued point only depends on the image point. -/
lemma rank_map_appTop_eq_of_base_eq {m n : Type*} [Finite m] [Fintype n] {R R' : CommRingCat.{u}}
    (hR : IsField Γ(Spec R, ⊤)) (hR' : IsField Γ(Spec R', ⊤)) (g : Spec R ⟶ Y)
    (g' : Spec R' ⟶ Y) (x : Spec R) (x' : Spec R') (h : g.base x = g'.base x')
    (A : Matrix m n Γ(Y, ⊤)) : (A.map g.appTop).rank = (A.map g'.appTop).rank := by
  refine le_antisymm ?_ ?_
  · obtain ⟨e₁, e₂, he⟩ := (le_rank_map_appTop_iff hR g x A _).1 le_rfl
    exact (le_rank_map_appTop_iff hR' g' x' A _).2 ⟨e₁, e₂, h ▸ he⟩
  · obtain ⟨e₁, e₂, he⟩ := (le_rank_map_appTop_iff hR' g' x' A _).1 le_rfl
    exact (le_rank_map_appTop_iff hR g x A _).2 ⟨e₁, e₂, h.symm ▸ he⟩

/-- The ring of global functions of the spectrum of a residue field is a field. -/
lemma isField_Γ_Spec_residueField (y : Y) : IsField Γ(Spec (Y.residueField y), ⊤) :=
  isField_Γ_Spec (Field.toIsField _)

/-- **Local split factorisation of a matrix of constant rank on a reduced scheme.** Let `A` be a
matrix of global functions on a reduced scheme `Y`, of rank at most `ρ` at every point of an open
`N`, and of rank at least `ρ` at a point `y ∈ N`. Then on an open neighbourhood `V ≤ N` of `y`,
`A = L * M` with `L' * L = 1` and `M * M' = 1` for matrices `L`, `M`, `L'`, `M'` through `ρ`. -/
theorem exists_split_factorization [IsReduced Y] {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n Γ(Y, ⊤)) (ρ : ℕ) (N : Y.Opens)
    (hle : ∀ y ∈ N, (A.map (Y.fromSpecResidueField y).appTop).rank ≤ ρ) {y : Y} (hy : y ∈ N)
    (hge : ρ ≤ (A.map (Y.fromSpecResidueField y).appTop).rank) :
    ∃ V : Y.Opens, V ≤ N ∧ y ∈ V ∧ ∃ (L : Matrix m (Fin ρ) Γ(V.toScheme, ⊤))
      (M : Matrix (Fin ρ) n Γ(V.toScheme, ⊤)) (L' : Matrix (Fin ρ) m Γ(V.toScheme, ⊤))
      (M' : Matrix n (Fin ρ) Γ(V.toScheme, ⊤)),
      A.map V.ι.appTop = L * M ∧ L' * L = 1 ∧ M * M' = 1 := by
  have : Nonempty (Spec (Y.residueField y)) := inferInstance
  obtain ⟨x⟩ := this
  obtain ⟨e₁, e₂, he⟩ := (le_rank_map_appTop_iff (isField_Γ_Spec_residueField y)
    (Y.fromSpecResidueField y) x A ρ).1 hge
  rw [Scheme.fromSpecResidueField_apply] at he
  refine ⟨N ⊓ Y.basicOpen (A.submatrix e₁ e₂).det, inf_le_left, ⟨hy, he⟩, ?_⟩
  set V := N ⊓ Y.basicOpen (A.submatrix e₁ e₂).det
  refine Matrix.exists_mul_eq_of_isUnit_det_submatrix _ e₁ e₂ ?_ fun f₁ f₂ ↦ ?_
  · rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine Scheme.isUnit_of_le_basicOpen (le_of_eq ?_)
    rw [← Scheme.preimage_basicOpen_top, eq_comm, ← top_le_iff]
    intro z _
    exact (inf_le_right : V ≤ _) z.2
  · rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine eq_zero_of_basicOpen_eq_bot _ ?_
    rw [← Scheme.preimage_basicOpen_top, eq_bot_iff]
    intro z hz
    have hzN : V.ι.base z ∈ N := (inf_le_left : V ≤ N) z.2
    obtain ⟨x'⟩ : Nonempty (Spec (Y.residueField (V.ι.base z))) := inferInstance
    have := (le_rank_map_appTop_iff (isField_Γ_Spec_residueField (V.ι.base z))
      (Y.fromSpecResidueField (V.ι.base z)) x' A (ρ + 1)).2 ⟨f₁, f₂, by
        rw [Scheme.fromSpecResidueField_apply]
        exact hz⟩
    have := hle _ hzN
    omega

/-- **Free cohomology of a complex of finite free modules with a split middle term.** Let `Q` be a
cochain complex of `𝒪_Y`-modules with `Q^{q-1} ≅ 𝒪^{(a)}`, `Q^q ≅ 𝒪^{(b)}`, `Q^{q+1} ≅ 𝒪^{(c)}`,
and let `A₁`, `A₂` be the matrices of the differentials into and out of degree `q`. If matrices
`I`, `P`, `σ`, `τ` satisfy `P I = 1`, `A₂ I = 0`, `P A₁ = 0` and `I P + A₁ σ + τ A₂ = 1`, then
`H^q(Q) ≅ 𝒪^{(k)}`. -/
theorem nonempty_homology_iso_free_of_split (Q : CochainComplex Y.Modules ℤ) (q : ℤ)
    {a b c k : Type u} [Fintype a] [Fintype b] [DecidableEq b] [Fintype c]
    [DecidableEq c] [Fintype k] [DecidableEq k]
    (e₀ : Q.X (q - 1) ≅ free (R := Y.ringCatSheaf) a) (e₁ : Q.X q ≅ free (R := Y.ringCatSheaf) b)
    (e₂ : Q.X (q + 1) ≅ free (R := Y.ringCatSheaf) c)
    (σ : Matrix a b Γ(Y, ⊤)) (τ : Matrix b c Γ(Y, ⊤)) (I : Matrix b k Γ(Y, ⊤))
    (P : Matrix k b Γ(Y, ⊤)) (hIP : P * I = 1)
    (hI : freeMatrix (e₁.inv ≫ Q.d q (q + 1) ≫ e₂.hom) * I = 0)
    (hP : P * freeMatrix (e₀.inv ≫ Q.d (q - 1) q ≫ e₁.hom) = 0)
    (hsum : I * P + freeMatrix (e₀.inv ≫ Q.d (q - 1) q ≫ e₁.hom) * σ +
      τ * freeMatrix (e₁.inv ≫ Q.d q (q + 1) ≫ e₂.hom) = 1) :
    Nonempty (Q.homology q ≅ free (R := Y.ringCatSheaf) k) := by
  classical
  set D₁ := e₀.inv ≫ Q.d (q - 1) q ≫ e₁.hom with hD₁
  set D₂ := e₁.inv ≫ Q.d q (q + 1) ≫ e₂.hom with hD₂
  have h₁ : Q.d (q - 1) q = e₀.hom ≫ D₁ ≫ e₁.inv := by simp [hD₁]
  have h₂ : Q.d q (q + 1) = e₁.hom ≫ D₂ ≫ e₂.inv := by simp [hD₂]
  have kIP : freeHomOfMatrix I ≫ freeHomOfMatrix P = 𝟙 _ :=
    freeMatrix_injective (by rw [freeMatrix_comp, freeMatrix_freeHomOfMatrix,
      freeMatrix_freeHomOfMatrix, freeMatrix_id, hIP])
  have kI : freeHomOfMatrix I ≫ D₂ = 0 :=
    freeMatrix_injective (by rw [freeMatrix_comp, freeMatrix_freeHomOfMatrix, hI,
      freeMatrix_zero])
  have kP : D₁ ≫ freeHomOfMatrix P = 0 :=
    freeMatrix_injective (by rw [freeMatrix_comp, freeMatrix_freeHomOfMatrix, hP,
      freeMatrix_zero])
  have ksum : freeHomOfMatrix P ≫ freeHomOfMatrix I + freeHomOfMatrix σ ≫ D₁ +
      D₂ ≫ freeHomOfMatrix τ = 𝟙 _ :=
    freeMatrix_injective (by rw [freeMatrix_add, freeMatrix_add, freeMatrix_comp,
      freeMatrix_comp, freeMatrix_comp, freeMatrix_freeHomOfMatrix, freeMatrix_freeHomOfMatrix,
      freeMatrix_freeHomOfMatrix, freeMatrix_freeHomOfMatrix, freeMatrix_id, hsum])
  let S : ShortComplex Y.Modules :=
    ShortComplex.mk (Q.d (q - 1) q) (Q.d q (q + 1)) (Q.d_comp_d _ _ _)
  have eS : Q.sc' (q - 1) q (q + 1) ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [S]) (by simp [S])
  refine ⟨Q.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso eS ≪≫ S.homologyIsoOfSplit (e₁.hom ≫ freeHomOfMatrix σ ≫ e₀.inv)
      (e₂.hom ≫ freeHomOfMatrix τ ≫ e₁.inv) (freeHomOfMatrix I ≫ e₁.inv)
      (e₁.hom ≫ freeHomOfMatrix P) ?_ ?_ ?_ ?_⟩
  · simp [kIP]
  · simp [S, h₂, reassoc_of% kI]
  · simp [S, h₁, kP]
  · simp only [S]
    rw [h₁, h₂]
    refine Eq.trans (?_ : _ = e₁.hom ≫ (freeHomOfMatrix P ≫ freeHomOfMatrix I +
      freeHomOfMatrix σ ≫ D₁ + D₂ ≫ freeHomOfMatrix τ) ≫ e₁.inv) ?_
    · simp [Preadditive.add_comp, Preadditive.comp_add]
    · rw [ksum, Category.id_comp, Iso.hom_inv_id]

lemma map_appTop_comp {m n : Type*} {X Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Matrix m n Γ(Z, ⊤)) : A.map (f ≫ g).appTop = (A.map g.appTop).map f.appTop := by
  rw [Scheme.Hom.comp_appTop, Matrix.map_map]
  rfl

/-- The rank of a matrix restricted to an open subscheme, at a point, is its rank at the image
point. -/
lemma rank_map_appTop_restrict {m n : Type*} [Finite m] [Fintype n] (V : Y.Opens) (z : V.toScheme)
    (A : Matrix m n Γ(Y, ⊤)) :
    ((A.map V.ι.appTop).map (V.toScheme.fromSpecResidueField z).appTop).rank =
      (A.map (Y.fromSpecResidueField (V.ι.base z)).appTop).rank := by
  obtain ⟨x⟩ : Nonempty (Spec (V.toScheme.residueField z)) := inferInstance
  obtain ⟨x'⟩ : Nonempty (Spec (Y.residueField (V.ι.base z))) := inferInstance
  rw [← map_appTop_comp]
  refine rank_map_appTop_eq_of_base_eq (isField_Γ_Spec_residueField z)
    (isField_Γ_Spec_residueField _) _ _ x x' ?_ A
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply,
    Scheme.fromSpecResidueField_apply]

/-- The matrices of the differentials of the pullback of a complex of free modules are the
images of the matrices of the differentials. -/
lemma freeMatrix_pullback_d {Z : Scheme.{u}} (j : Z ⟶ Y) (P : CochainComplex Y.Modules ℤ)
    {I J : Type u} [DecidableEq J] {n n' : ℤ} (eₙ : P.X n ≅ free (R := Y.ringCatSheaf) I)
    (eₙ' : P.X n' ≅ free (R := Y.ringCatSheaf) J) :
    freeMatrix ((((Modules.pullback j).mapIso eₙ ≪≫ pullbackFreeIso j I).inv ≫
        (((Modules.pullback j).mapHomologicalComplex _).obj P).d n n' ≫
        ((Modules.pullback j).mapIso eₙ' ≪≫ pullbackFreeIso j J).hom)) =
      (freeMatrix (eₙ.inv ≫ P.d n n' ≫ eₙ'.hom)).map j.appTop := by
  rw [← freeMatrix_pullback]
  congr 1
  simp

/-- Over a field point, the rank of the split idempotent of two composable matrices of ranks
`ρ₁` and `ρ₂` with split factorisations is the size minus `ρ₁ + ρ₂`. -/
lemma rank_splitIdempotent_map {R K : Type*} [CommRing R] [Field K] {a b c : Type*} [Fintype a]
    [Fintype b] [Fintype c] [DecidableEq b] {ρ₁ ρ₂ : ℕ} {A₁ : Matrix b a R} {A₂ : Matrix c b R}
    {L₁ : Matrix b (Fin ρ₁) R} {M₁ : Matrix (Fin ρ₁) a R} {L₁' : Matrix (Fin ρ₁) b R}
    {M₁' : Matrix a (Fin ρ₁) R} {L₂ : Matrix c (Fin ρ₂) R} {M₂ : Matrix (Fin ρ₂) b R}
    {L₂' : Matrix (Fin ρ₂) c R} {M₂' : Matrix b (Fin ρ₂) R} (h : A₂ * A₁ = 0)
    (h₁ : A₁ = L₁ * M₁ ∧ L₁' * L₁ = 1 ∧ M₁ * M₁' = 1)
    (h₂ : A₂ = L₂ * M₂ ∧ L₂' * L₂ = 1 ∧ M₂ * M₂' = 1) (φ : R →+* K) :
    ((Matrix.splitIdempotent L₁ L₁' M₂ M₂').map φ).rank = Fintype.card b - ρ₁ - ρ₂ := by
  have hML := Matrix.mul_eq_zero_of_split h h₁.1 h₁.2.2 h₂.1 h₂.2.1
  obtain ⟨k₁, kL₁, kM₁⟩ := Matrix.split_map φ h₁
  obtain ⟨k₂, kL₂, kM₂⟩ := Matrix.split_map φ h₂
  have kML : M₂.map φ * L₁.map φ = 0 := by
    rw [← Matrix.map_mul, hML, Matrix.map_zero _ (map_zero φ)]
  have kA : A₂.map φ * A₁.map φ = 0 := by
    rw [← Matrix.map_mul, h, Matrix.map_zero _ (map_zero φ)]
  rw [Matrix.splitIdempotent_map]
  -- the ranks of the two maps at the point
  have r₁ : (A₁.map φ).rank = ρ₁ := by
    refine le_antisymm ?_ ?_
    · rw [k₁]
      exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
    · have : L₁'.map φ * A₁.map φ * M₁'.map φ = 1 := by
        rw [k₁, Matrix.mul_assoc, Matrix.mul_assoc, kM₁, Matrix.mul_one, kL₁]
      calc ρ₁ = (1 : Matrix (Fin ρ₁) (Fin ρ₁) K).rank := by simp
        _ ≤ (A₁.map φ).rank := by
          rw [← this]
          exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have r₂ : (A₂.map φ).rank = ρ₂ := by
    refine le_antisymm ?_ ?_
    · rw [k₂]
      exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
    · have : L₂'.map φ * A₂.map φ * M₂'.map φ = 1 := by
        rw [k₂, Matrix.mul_assoc, Matrix.mul_assoc, kM₂, Matrix.mul_one, kL₂]
      calc ρ₂ = (1 : Matrix (Fin ρ₂) (Fin ρ₂) K).rank := by simp
        _ ≤ (A₂.map φ).rank := by
          rw [← this]
          exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have hle := Matrix.rank_add_rank_add_rank_le _ (A₁.map φ) (A₂.map φ)
    (Matrix.splitIdempotent_mul_self kL₁ kM₂ kML) (Matrix.splitIdempotent_mul k₁ kL₁ kML)
    (Matrix.mul_splitIdempotent k₂ kM₂ kML) kA
  have hge := Matrix.card_le_rank_add_rank_add_rank _ _ _
    (Matrix.add_splitIdempotent_add (L₁ := L₁.map φ) (L₁' := L₁'.map φ) (M₂ := M₂.map φ)
      (M₂' := M₂'.map φ))
  have p₁ : (L₁.map φ * L₁'.map φ).rank ≤ ρ₁ :=
    (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
  have p₂ : ((1 - L₁.map φ * L₁'.map φ) * (M₂'.map φ * M₂.map φ)).rank ≤ ρ₂ :=
    (Matrix.rank_mul_le_right _ _).trans
      ((Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp)))
  omega

/-- **Locally free cohomology of a complex of finite free modules with constant ranks.** Let `P`
be a cochain complex of `𝒪_Y`-modules on a reduced scheme `Y` with `P^n ≅ 𝒪^{r_n}`, and suppose
that on an open `N` the matrices of the differentials into and out of degree `q` have constant
ranks `ρ₁` and `ρ₂` at every point. Then every point `y ∈ N` lies in the image of an open
immersion `j : Z ⟶ Y` with `H^q(j^* P) ≅ 𝒪_Z^{r_q - ρ₁ - ρ₂}`. -/
theorem exists_isOpenImmersion_homology_pullback_iso_free [IsReduced Y]
    (P : CochainComplex Y.Modules ℤ) {r : ℤ → ℕ}
    (e : ∀ n, P.X n ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r n)))) (q : ℤ) {ρ₁ ρ₂ : ℕ}
    (N : Y.Opens)
    (h₁ : ∀ z ∈ N, ((freeMatrix ((e (q - 1)).inv ≫ P.d (q - 1) q ≫ (e q).hom)).map
      (Y.fromSpecResidueField z).appTop).rank = ρ₁)
    (h₂ : ∀ z ∈ N, ((freeMatrix ((e q).inv ≫ P.d q (q + 1) ≫ (e (q + 1)).hom)).map
      (Y.fromSpecResidueField z).appTop).rank = ρ₂)
    {y : Y} (hy : y ∈ N) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ Y) (_ : IsOpenImmersion j), y ∈ Set.range j.base ∧
      Nonempty ((((Modules.pullback j).mapHomologicalComplex _).obj P).homology q ≅
        free (R := Z.ringCatSheaf) (ULift.{u} (Fin (r q - ρ₁ - ρ₂)))) := by
  classical
  set A₁ := freeMatrix ((e (q - 1)).inv ≫ P.d (q - 1) q ≫ (e q).hom) with hA₁
  set A₂ := freeMatrix ((e q).inv ≫ P.d q (q + 1) ≫ (e (q + 1)).hom) with hA₂
  have hA : A₂ * A₁ = 0 := by
    rw [hA₁, hA₂, ← freeMatrix_comp]
    simp
  obtain ⟨V₁, hV₁N, hyV₁, L₁, M₁, L₁', M₁', s₁⟩ :=
    exists_split_factorization A₁ ρ₁ N (fun z hz ↦ (h₁ z hz).le) hy (h₁ y hy).ge
  obtain ⟨V₂, hV₂N, hyV₂, L₂, M₂, L₂', M₂', s₂⟩ :=
    exists_split_factorization A₂ ρ₂ N (fun z hz ↦ (h₂ z hz).le) hy (h₂ y hy).ge
  set V := V₁ ⊓ V₂ with hV
  -- the split factorisations over `V`
  have t₁ := Matrix.split_map (Y.homOfLE (inf_le_left : V ≤ V₁)).appTop.hom s₁
  have t₂ := Matrix.split_map (Y.homOfLE (inf_le_right : V ≤ V₂)).appTop.hom s₂
  rw [Matrix.map_map, ← RingHom.coe_comp, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
    Scheme.homOfLE_ι] at t₁ t₂
  set ψ₁ := (Y.homOfLE (inf_le_left : V ≤ V₁)).appTop.hom
  set ψ₂ := (Y.homOfLE (inf_le_right : V ≤ V₂)).appTop.hom
  have hB : A₂.map V.ι.appTop * A₁.map V.ι.appTop = 0 := by
    rw [← Matrix.map_mul, hA, Matrix.map_zero _ (map_zero _)]
  set ε := Matrix.splitIdempotent (L₁.map ψ₁) (L₁'.map ψ₁) (M₂.map ψ₂) (M₂'.map ψ₂) with hε
  have hrank (z : V.toScheme) :
      (ε.map (V.toScheme.fromSpecResidueField z).appTop).rank = r q - ρ₁ - ρ₂ := by
    let := (isField_Γ_Spec_residueField z).toField
    have := rank_splitIdempotent_map hB t₁ t₂ (V.toScheme.fromSpecResidueField z).appTop.hom
    simpa using this
  have hyV : y ∈ V := ⟨hyV₁, hyV₂⟩
  obtain ⟨V₃, -, hyV₃, L₃, M₃, L₃', M₃', s₃⟩ := exists_split_factorization ε (r q - ρ₁ - ρ₂) ⊤
    (fun z _ ↦ (hrank z).le) (Set.mem_univ (⟨y, hyV⟩ : V.toScheme)) (hrank _).ge
  -- everything over `Z = V₃`, via `j = V₃.ι ≫ V.ι`
  set ψ := V₃.ι.appTop.hom
  have u₁ := Matrix.split_map ψ t₁
  have u₂ := Matrix.split_map ψ t₂
  rw [← map_appTop_comp] at u₁ u₂
  have hε₃ := s₃.1
  rw [hε, Matrix.splitIdempotent_map] at hε₃
  have h₃ : M₃ * L₃ = 1 := by
    refine Matrix.mul_eq_one_of_isIdempotentElem ?_ s₃.2.1 s₃.2.2
    rw [← hε₃]
    exact Matrix.splitIdempotent_mul_self u₁.2.1 u₂.2.2
      (Matrix.mul_eq_zero_of_split (by rw [← Matrix.map_mul, hA, Matrix.map_zero _ (map_zero _)])
        u₁.1 u₁.2.2 u₂.1 u₂.2.1)
  obtain ⟨k₁, k₂, k₃⟩ := Matrix.split_homology_data
    (by rw [← Matrix.map_mul, hA, Matrix.map_zero _ (map_zero _)]) u₁.1 u₁.2.1 u₁.2.2 u₂.1 u₂.2.1
    u₂.2.2 hε₃ h₃
  obtain ⟨σ, τ, k₃⟩ : ∃ σ τ, L₃ * M₃ + A₁.map (V₃.ι ≫ V.ι).appTop * σ +
      τ * A₂.map (V₃.ι ≫ V.ι).appTop = 1 := ⟨_, _, k₃⟩
  refine ⟨V₃.toScheme, V₃.ι ≫ V.ι, inferInstance, ⟨⟨⟨y, hyV⟩, hyV₃⟩, rfl⟩, ?_⟩
  let E (n : ℤ) := (Modules.pullback (V₃.ι ≫ V.ι)).mapIso (e n) ≪≫
    pullbackFreeIso (V₃.ι ≫ V.ι) (ULift.{u} (Fin (r n)))
  refine nonempty_homology_iso_free_of_split _ q (E (q - 1)) (E q) (E (q + 1)) σ τ
    (L₃.submatrix id Equiv.ulift) (M₃.submatrix Equiv.ulift id) ?_ ?_ ?_ ?_
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, h₃, Matrix.submatrix_one_equiv]
  · rw [freeMatrix_pullback_d, ← hA₂, ← Matrix.submatrix_id_id (A₂.map _),
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, k₁, Matrix.submatrix_zero]
    rfl
  · rw [freeMatrix_pullback_d, ← hA₁, ← Matrix.submatrix_id_id (A₁.map _),
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, k₂, Matrix.submatrix_zero]
    rfl
  · rw [freeMatrix_pullback_d, freeMatrix_pullback_d, ← hA₁, ← hA₂, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id, k₃]

end AlgebraicGeometry.Scheme.Modules
