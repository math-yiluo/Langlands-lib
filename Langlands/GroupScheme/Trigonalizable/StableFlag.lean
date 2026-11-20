import Langlands.GroupScheme.MatrixRepresentation.NormalFixedRepresentation
import Langlands.GroupScheme.MatrixRepresentation.QuotientCoordinates
import Langlands.GroupScheme.MatrixRepresentation.DiagonalizableCharacterDecomposition
import Langlands.GroupScheme.MatrixRepresentation.GaloisCharacterSpaces
import Langlands.GroupScheme.FppfHomDescent
import Langlands.GroupScheme.Absolute.UnipotentPointsSolvable
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.Diagonalizable

/-! # Stable flags for extensions of diagonalizable groups by unipotent groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.TrigonalizableFlag

open MatrixRepresentation

variable {k : Type u} [Field k]
  {G U : GroupScheme (Spec (CommRingCat.of k))}
  (i : U ⟶ G) {Λ : Type u} [AddCommGroup Λ]
  (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)

/-- A representation that is trivial on the points of `U` is killed by the actual kernel of an
fppf quotient map whose kernel is the range of `U`. -/
theorem kernelι_comp_eq_zero (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    {n : Type} [Fintype n] [DecidableEq n] (σ : MatrixRepresentation G n)
    (hσ : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ U.X),
      σ.pointMatrix T (h ≫ i.hom.hom) = 1) :
    kernelι q ≫ σ = 0 := by
  apply (Grp.forget _).map_injective
  change (kernelι q).hom.hom ≫ σ.hom.hom = 1
  have hmem : (kernelι q).hom.hom ∈ (SubgroupFunctor.range (kernelι q)).carrier (kernel q).X :=
    SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  rw [hq.2.2.2] at hmem
  obtain ⟨h, hh⟩ := SubgroupFunctor.mem_range.mp hmem
  rw [← hh]
  apply (GeneralLinear.pointsEquiv n (CommRingCat.of k) (kernel q).X).injective
  rw [map_one]
  exact hσ (kernel q).X h

variable [IsAffineHom G.X.hom] [IsAffineHom U.X.hom]

/-- **Stable lines.** Let `U` be a normal unipotent subgroup of an affine `G`, with an fppf
quotient `q : G ⟶ D(Λ)` whose kernel is the range of `U`. Every representation of `G` on a
nonzero coordinate space has a nonzero vector fixed by `U` that spans a `G`-stable line. -/
theorem exists_stable_line (hU : IsUnipotent U) (hN : (SubgroupFunctor.range i).IsNormal)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    {m : ℕ} (ρ : MatrixRepresentation G (Fin (m + 1))) :
    ∃ v : Fin (m + 1) → k, v ≠ 0 ∧ (ρ.restrict i).IsFixedVector v ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        ∃ c : Γ(T.left, ⊤),
          (ρ.pointMatrix T x : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T.left, ⊤)) *ᵥ
              (fun r => scalarMap T (v r)) = c • (fun r => scalarMap T (v r)) := by
  classical
  let F := normalFixedSubrepresentation ρ i hN
  obtain ⟨v₀, hv₀, hfix₀⟩ := hU (Fin (m + 1)) (ρ.restrict i)
  have hC : F.retraction *ᵥ v₀ ≠ 0 := by
    intro h0
    apply hv₀
    rw [← F.projection v₀ hfix₀, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  have hk := kernelι_comp_eq_zero i q hq F.representation F.kills_subgroup
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  let τ : MatrixRepresentation (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp
      (Fin F.dimension) := FppfHomDescent.hom q F.representation hk
  have hτ : q ≫ τ = F.representation := FppfHomDescent.fac q F.representation hk
  have hspan := iSup_characterSpace_eq_top_diagonalizable Λ τ
  have hex : ∃ χ, τ.characterSpace χ ≠ ⊥ := by
    by_contra! hcon
    have hbot : (⨆ χ, τ.characterSpace χ) = ⊥ := iSup_eq_bot.mpr hcon
    rw [hspan] at hbot
    have hmem : F.retraction *ᵥ v₀ ∈ (⊤ : Submodule k (Fin F.dimension → k)) :=
      Submodule.mem_top
    rw [hbot, Submodule.mem_bot] at hmem
    exact hC hmem
  obtain ⟨χ, hχ⟩ := hex
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have hvT : ∀ (T : Over (Spec (CommRingCat.of k))),
      (fun r => scalarMap T ((F.inclusion *ᵥ w) r)) =
        F.inclusion.map (scalarMap T) *ᵥ fun j => scalarMap T (w j) := by
    intro T
    funext r
    rw [RingHom.map_mulVec]
    rfl
  refine ⟨F.inclusion *ᵥ w, ?_, ?_, ?_⟩
  · intro h0
    apply hw0
    have := congrArg (fun z => F.retraction *ᵥ z) h0
    simpa only [Matrix.mulVec_mulVec, F.left_inverse, Matrix.one_mulVec,
      Matrix.mulVec_zero] using this
  · intro T h
    rw [pointMatrix_restrict, hvT, Matrix.mulVec_mulVec, F.intertwines,
      F.kills_subgroup, Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]
  · intro T x
    have hrep : F.representation.pointMatrix T x = τ.pointMatrix T (x ≫ q.hom.hom) := by
      rw [← hτ]
      exact pointMatrix_restrict τ q T x
    refine ⟨(characterEval χ T (x ≫ q.hom.hom) : Γ(T.left, ⊤)), ?_⟩
    rw [hvT, Matrix.mulVec_mulVec, F.intertwines, ← Matrix.mulVec_mulVec, hrep,
      characterSpace_pointMatrix hw T (x ≫ q.hom.hom), Matrix.mulVec_smul]


section Blocks

variable {S : Type*} [CommRing S] {m : ℕ}

/-- The block-diagonal matrix with blocks `1` and `P`. -/
def ext1 (P : Matrix (Fin m) (Fin m) S) : Matrix (Fin (m + 1)) (Fin (m + 1)) S :=
  Matrix.of fun a b =>
    Fin.cases (Fin.cases 1 (fun _ => 0) b) (fun i => Fin.cases 0 (fun j => P i j) b) a

@[simp] theorem ext1_zero_zero (P : Matrix (Fin m) (Fin m) S) : ext1 P 0 0 = 1 := rfl

@[simp] theorem ext1_zero_succ (P : Matrix (Fin m) (Fin m) S) (j : Fin m) :
    ext1 P 0 j.succ = 0 := rfl

@[simp] theorem ext1_succ_zero (P : Matrix (Fin m) (Fin m) S) (i : Fin m) :
    ext1 P i.succ 0 = 0 := rfl

@[simp] theorem ext1_succ_succ (P : Matrix (Fin m) (Fin m) S) (i j : Fin m) :
    ext1 P i.succ j.succ = P i j := rfl

theorem ext1_mul (P Q : Matrix (Fin m) (Fin m) S) : ext1 P * ext1 Q = ext1 (P * Q) := by
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem ext1_one : ext1 (1 : Matrix (Fin m) (Fin m) S) = 1 := by
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem ext1_map {S' : Type*} [CommRing S'] (f : S →+* S') (P : Matrix (Fin m) (Fin m) S) :
    (ext1 P).map f = ext1 (P.map f) := by
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b <;> simp

/-- The invertible block-diagonal matrix with blocks `1` and `g`. -/
def ext1GL (g : GL (Fin m) S) : GL (Fin (m + 1)) S where
  val := ext1 g.val
  inv := ext1 (g⁻¹ : GL (Fin m) S).val
  val_inv := by rw [ext1_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, ext1_one]
  inv_val := by rw [ext1_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ext1_one]

@[simp] theorem ext1GL_val (g : GL (Fin m) S) : (ext1GL g).val = ext1 g.val := rfl

@[simp] theorem ext1GL_inv_val (g : GL (Fin m) S) :
    ((ext1GL g)⁻¹ : GL (Fin (m + 1)) S).val = ext1 (g⁻¹ : GL (Fin m) S).val := rfl

theorem ext1_mul_apply_zero (A : Matrix (Fin m) (Fin m) S)
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) S) (c : Fin (m + 1)) :
    (ext1 A * M) 0 c = M 0 c := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem ext1_mul_apply_succ (A : Matrix (Fin m) (Fin m) S)
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) S) (i : Fin m) (c : Fin (m + 1)) :
    (ext1 A * M) i.succ c = ∑ j, A i j * M j.succ c := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- Conjugating a matrix whose first column vanishes below the diagonal by block-diagonal
matrices: the first column still vanishes below the diagonal, the corner entry is kept, and the
lower-right block is conjugated. -/
theorem block_conj (A B : Matrix (Fin m) (Fin m) S) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) S)
    (hM : ∀ i : Fin m, M i.succ 0 = 0) :
    (∀ i : Fin m, (ext1 A * M * ext1 B) i.succ 0 = 0) ∧
      (ext1 A * M * ext1 B) 0 0 = M 0 0 ∧
      ∀ i j : Fin m, (ext1 A * M * ext1 B) i.succ j.succ = (A * tail M * B) i j := by
  refine ⟨fun i => ?_, ?_, fun i j => ?_⟩
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [ext1_mul_apply_succ, hM]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [ext1_mul_apply_zero]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [ext1_zero_succ, mul_zero, ext1_succ_succ, zero_add, ext1_mul_apply_succ]
    simp only [Matrix.mul_apply, tail_apply, Finset.sum_mul]

end Blocks

section QuotientCoordinates

variable {m : ℕ}

/-- Projection of `k^(m+1)` onto its last `m` coordinates. -/
def dropFirst (S : Type*) [CommRing S] (m : ℕ) : Matrix (Fin m) (Fin (m + 1)) S :=
  Matrix.of fun i b => if b = i.succ then 1 else 0

/-- Inclusion of `k^m` as the last `m` coordinates of `k^(m+1)`. -/
def insertFirst (S : Type*) [CommRing S] (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) S :=
  Matrix.of fun b j => if b = j.succ then 1 else 0

theorem dropFirst_map {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S') :
    (dropFirst S m).map f = dropFirst S' m := by
  ext i b
  simp only [dropFirst, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem insertFirst_map {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S') :
    (insertFirst S m).map f = insertFirst S' m := by
  ext b j
  simp only [insertFirst, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem dropFirst_mul_insertFirst (S : Type*) [CommRing S] :
    dropFirst S m * insertFirst S m = 1 := by
  ext i j
  simp [dropFirst, insertFirst, Matrix.mul_apply, Matrix.one_apply, Fin.succ_inj, eq_comm]

theorem dropFirst_mul_mul_insertFirst {S : Type*} [CommRing S]
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) S) :
    dropFirst S m * M * insertFirst S m = tail M := by
  ext i j
  simp [dropFirst, insertFirst, Matrix.mul_apply]

theorem dropFirst_quotient {S : Type*} [CommRing S] (M : Matrix (Fin (m + 1)) (Fin (m + 1)) S)
    (hM : ∀ i : Fin m, M i.succ 0 = 0) :
    dropFirst S m * M = (dropFirst S m * M * insertFirst S m) * dropFirst S m := by
  rw [dropFirst_mul_mul_insertFirst]
  ext i b
  refine Fin.cases ?_ (fun j => ?_) b
  · simp [dropFirst, Matrix.mul_apply, hM, (Fin.succ_ne_zero _).symm]
  · simp [dropFirst, Matrix.mul_apply, Fin.succ_inj]

end QuotientCoordinates


section Triangularization

theorem basePoint_mul {n : Type} [Fintype n] [DecidableEq n] (g h : GL n k) :
    basePoint (R := CommRingCat.of k) (g * h) = basePoint g * basePoint h := by
  simp only [basePoint, map_mul]

omit [IsAffineHom G.X.hom] [IsAffineHom U.X.hom] in
theorem conjugate_basePoint_matrix {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (g : GL n k) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ G.X) :
    ((ρ.conjugate (basePoint (R := CommRingCat.of k) g)).pointMatrix T x :
        Matrix n n Γ(T.left, ⊤)) =
      g.val.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
        (g⁻¹ : GL n k).val.map (scalarMap T) := by
  rw [conjugate_pointMatrix, pointsEquiv_constantPoint_basePoint, ← map_inv]
  rfl

theorem map_mulVec' {R S : Type*} [CommRing R] [CommRing S] {n m : Type*} [Fintype n]
    (f : R →+* S) (M : Matrix m n R) (v : n → R) :
    M.map f *ᵥ (fun r => f (v r)) = fun r => f ((M *ᵥ v) r) :=
  funext fun r => (RingHom.map_mulVec f M v r).symm

theorem mulVec_firstBasisVector {S : Type*} [CommRing S] {m : ℕ}
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) S) (r : Fin (m + 1)) :
    (M *ᵥ firstBasisVector S m) r = M r 0 := by
  simp [firstBasisVector, Matrix.mulVec_single]

/-- **Triangularization.** Every representation of `G` becomes upper triangular after a change of
basis over `k`, with all diagonal entries equal to `1` on the points of `U`. -/
theorem exists_triangular (hU : IsUnipotent U) (hN : (SubgroupFunctor.range i).IsNormal)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) (m : ℕ)
    (ρ : MatrixRepresentation G (Fin m)) :
    ∃ g : GL (Fin m) k,
      (∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) (a b : Fin m), b < a →
        ((ρ.conjugate (basePoint (R := CommRingCat.of k) g)).pointMatrix T x :
          Matrix (Fin m) (Fin m) Γ(T.left, ⊤)) a b = 0) ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ U.X) (a : Fin m),
        ((ρ.conjugate (basePoint (R := CommRingCat.of k) g)).pointMatrix T (h ≫ i.hom.hom) :
          Matrix (Fin m) (Fin m) Γ(T.left, ⊤)) a a = 1 := by
  classical
  induction m with
  | zero => exact ⟨1, fun _ _ a => a.elim0, fun _ _ a => a.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv0, hvfix, hvline⟩ := exists_stable_line i q hU hN hq ρ
    obtain ⟨g₀, hg₀⟩ := exists_mulVec_eq_firstBasisVector hv0
    set ρ' := ρ.conjugate (basePoint (R := CommRingCat.of k) g₀) with hρ'
    have hinv : (g₀⁻¹ : GL (Fin (m + 1)) k).val *ᵥ firstBasisVector k m = v := by
      rw [← hg₀, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    have he : ∀ T : Over (Spec (CommRingCat.of k)),
        (fun r => scalarMap T (firstBasisVector k m r)) = firstBasisVector Γ(T.left, ⊤) m :=
      fun T => map_firstBasisVector (scalarMap T)
    -- the first column of `ρ'` is a multiple of the first basis vector
    have hcolvec : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        ∃ c : Γ(T.left, ⊤),
          (ρ'.pointMatrix T x : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T.left, ⊤)) *ᵥ
            firstBasisVector Γ(T.left, ⊤) m = c • firstBasisVector Γ(T.left, ⊤) m := by
      intro T x
      obtain ⟨c, hc⟩ := hvline T x
      refine ⟨c, ?_⟩
      rw [hρ', conjugate_basePoint_matrix, ← he T, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, map_mulVec', hinv, hc, Matrix.mulVec_smul, map_mulVec', hg₀]
    have hcol : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) (a : Fin m),
        (ρ'.pointMatrix T x : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T.left, ⊤)) a.succ 0 = 0 := by
      intro T x a
      obtain ⟨c, hc⟩ := hcolvec T x
      have := congrFun hc a.succ
      rw [mulVec_firstBasisVector] at this
      rw [this]
      simp [firstBasisVector]
    -- on `U` the first basis vector is fixed
    have hfix' : (ρ'.restrict i).IsFixedVector (firstBasisVector k m) := by
      have := isFixedVector_conjugate hvfix g₀
      rw [hg₀, conjugate_restrict] at this
      exact this
    have hU0 : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ U.X),
        (ρ'.pointMatrix T (h ≫ i.hom.hom) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T.left, ⊤)) 0 0 = 1 := by
      intro T h
      have := congrFun (hfix' T h) 0
      rw [pointMatrix_restrict, he T, mulVec_firstBasisVector] at this
      rw [this]
      simp [firstBasisVector]
    -- the quotient representation on the last `m` coordinates
    have hquot : ρ'.IsQuotientCoordinates (dropFirst k m) (insertFirst k m) := by
      intro T x
      rw [dropFirst_map, insertFirst_map]
      exact dropFirst_quotient _ (hcol T x)
    let σ := quotientCoordinates ρ' (dropFirst k m) (insertFirst k m)
      (dropFirst_mul_insertFirst k) hquot
    have hσ : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        (σ.pointMatrix T x : Matrix (Fin m) (Fin m) Γ(T.left, ⊤)) =
          tail (ρ'.pointMatrix T x : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T.left, ⊤)) := by
      intro T x
      rw [quotientCoordinates_pointMatrix]
      change ((dropFirst k m).map (scalarMap T) : Matrix (Fin m) (Fin (m + 1)) Γ(T.left, ⊤)) *
          (ρ'.pointMatrix T x : Matrix (Fin (m + 1)) (Fin (m + 1)) Γ(T.left, ⊤)) *
          ((insertFirst k m).map (scalarMap T) : Matrix (Fin (m + 1)) (Fin m) Γ(T.left, ⊤)) = _
      rw [dropFirst_map, insertFirst_map, dropFirst_mul_mul_insertFirst]
    obtain ⟨g', htri', hdiag'⟩ := ih σ
    refine ⟨ext1GL g' * g₀, ?_, ?_⟩
    · have hρg : ρ.conjugate (basePoint (R := CommRingCat.of k) (ext1GL g' * g₀)) =
          ρ'.conjugate (basePoint (R := CommRingCat.of k) (ext1GL g')) := by
        rw [basePoint_mul, hρ', conjugate_mul]
      intro T x a b hba
      rw [hρg, conjugate_basePoint_matrix, ext1GL_val, ext1GL_inv_val, ext1_map,
        ext1_map]
      obtain ⟨h1, -, h3⟩ := block_conj (g'.val.map (scalarMap T))
        ((g'⁻¹ : GL (Fin m) k).val.map (scalarMap T)) _ (hcol T x)
      induction a using Fin.cases with
      | zero => exact absurd hba (Fin.not_lt_zero b)
      | succ a =>
        induction b using Fin.cases with
        | zero => exact h1 a
        | succ b =>
          rw [h3, ← hσ, ← conjugate_basePoint_matrix]
          exact htri' T x a b (Fin.succ_lt_succ_iff.mp hba)
    · have hρg : ρ.conjugate (basePoint (R := CommRingCat.of k) (ext1GL g' * g₀)) =
          ρ'.conjugate (basePoint (R := CommRingCat.of k) (ext1GL g')) := by
        rw [basePoint_mul, hρ', conjugate_mul]
      intro T h a
      rw [hρg, conjugate_basePoint_matrix, ext1GL_val, ext1GL_inv_val, ext1_map,
        ext1_map]
      obtain ⟨-, h2, h3⟩ := block_conj (g'.val.map (scalarMap T))
        ((g'⁻¹ : GL (Fin m) k).val.map (scalarMap T)) _ (hcol T (h ≫ i.hom.hom))
      induction a using Fin.cases with
      | zero => rw [h2, hU0]
      | succ a =>
        rw [h3, ← hσ, ← conjugate_basePoint_matrix]
        exact hdiag' T h a

end Triangularization

end Langlands.GroupScheme.TrigonalizableFlag
