import Langlands.GroupScheme.MatrixRepresentation.MinimalStableSubrepresentation
import Langlands.GroupScheme.MatrixRepresentation.QuotientCoordinates

/-! # Finite simple factors and their common unipotent matrix kernel -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section AllTests

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- For an affine group, an all-affine-tests intertwiner intertwines on every
scheme test, including nonreduced tests. -/
theorem Intertwines.pointMatrix
    {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    {C : Matrix m n k} (hC : Intertwines ρ σ C)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    C.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) =
      (σ.pointMatrix T x : Matrix m m Γ(T.left, ⊤)) * C.map (scalarMap T) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨⟨A⟩, ⟨j⟩⟩ := (essImage_algSpec (G := G.X)).mpr inferInstance
  let e : A →+* Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) :=
    (Corepresented.affineSectionsIso A).inv.hom.toRingHom
  have h₀ := congrArg (fun M : Matrix m n A => M.map e) (hC A j.hom)
  simp only [Matrix.map_mul, Matrix.map_map] at h₀
  have hC₀ : C.map (e ∘ algebraMap k A) =
      C.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) := by
    ext r s
    exact (UnipotentMatrixCriterion.scalarMap_affine A _).symm
  rw [hC₀] at h₀
  let a := x ≫ j.inv
  have h₁ := congrArg (fun M : Matrix m n
    Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) =>
      M.map a.left.appTop.hom) h₀
  simp only [Matrix.map_mul, Matrix.map_map] at h₁
  have hC₁ : C.map (a.left.appTop.hom ∘
      scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) =
      C.map (scalarMap T) := by
    ext r s
    exact scalarMap_naturality a _
  rw [hC₁] at h₁
  have hM {l : Type} [Fintype l] [DecidableEq l]
      (τ : MatrixRepresentation G l) :
      (τ.pointMatrix T x : Matrix l l Γ(T.left, ⊤)) =
        ((τ.affineMatrix A j.hom : Matrix l l A).map e).map a.left.appTop.hom := by
    have h := congrArg (fun U : GL l Γ(T.left, ⊤) =>
      (U : Matrix l l Γ(T.left, ⊤))) (τ.pointMatrix_naturality a j.hom)
    have hax : a ≫ j.hom = x := by simp [a]
    rw [hax, pointMatrix_eq_affineMatrix] at h
    exact h
  rw [hM ρ, hM σ]
  simpa only [Matrix.map_map] using h₁

end AllTests

section SplitExact

variable {k : Type u} [Field k] {A : Type v} [CommRing A]
  {n r q : Type} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r] [Fintype q] [DecidableEq q]

/-- In a split exact matrix sequence, identity action on the subspace and a
nilpotent deviation on the quotient imply nilpotent deviation on the whole. -/
theorem pow_sub_one_eq_zero_of_split_exact
    (B : Matrix n r k) (C : Matrix r n k)
    (Q : Matrix q n k) (D : Matrix n q k)
    (hCB : C * B = 1) (hQD : Q * D = 1)
    (hker : LinearMap.ker Q.mulVecLin = LinearMap.range B.mulVecLin)
    (f : k →+* A) (M : Matrix n n A) (N : Matrix q q A)
    (hMB : M * B.map f = B.map f)
    (hQM : Q.map f * M = N * Q.map f)
    (l : ℕ) (hN : (N - 1) ^ l = 0) :
    (M - 1) ^ (l + 1) = 0 := by
  let P : Matrix n n k := 1 - D * Q
  have hQP : Q * P = 0 := by
    simp only [P, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      hQD, Matrix.one_mul, sub_self]
  have hBCP : B * C * P = P := by
    apply Matrix.ext_of_mulVec_single
    intro j
    have hj : P *ᵥ Pi.single j 1 ∈ LinearMap.ker Q.mulVecLin := by
      change Q *ᵥ (P *ᵥ Pi.single j 1) = 0
      rw [Matrix.mulVec_mulVec, hQP, Matrix.zero_mulVec]
    rw [hker] at hj
    obtain ⟨v, hv⟩ := hj
    change B *ᵥ v = P *ᵥ Pi.single j 1 at hv
    rw [← Matrix.mulVec_mulVec, ← hv, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, hCB, Matrix.mul_one]
  have hAB : (M - 1) * B.map f = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hMB, sub_self]
  have hBCP' : B.map f * C.map f * P.map f = P.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hBCP]
  have hAP : (M - 1) * P.map f = 0 := by
    calc
      _ = (M - 1) * (B.map f * C.map f * P.map f) := by rw [hBCP']
      _ = 0 := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB,
          Matrix.zero_mul, Matrix.zero_mul]
  have hA : M - 1 = (M - 1) * D.map f * Q.map f := by
    have hP : P.map f = 1 - D.map f * Q.map f := by
      simp only [P, Matrix.map_sub _ (map_sub _), Matrix.map_mul,
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hP, Matrix.mul_sub, Matrix.mul_one] at hAP
    simpa only [Matrix.mul_assoc] using sub_eq_zero.mp hAP
  have hQA : Q.map f * (M - 1) = (N - 1) * Q.map f := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hQM]
  have hp (i : ℕ) : Q.map f * (M - 1) ^ i = (N - 1) ^ i * Q.map f := by
    induction i with
    | zero => simp only [pow_zero, Matrix.mul_one, Matrix.one_mul]
    | succ i hi =>
      rw [pow_succ, pow_succ, ← Matrix.mul_assoc, hi, Matrix.mul_assoc, hQA,
        ← Matrix.mul_assoc]
  have hQpow : Q.map f * (M - 1) ^ l = 0 := by
    rw [hp, hN, Matrix.zero_mul]
  calc
    _ = (M - 1) * (M - 1) ^ l := pow_succ' _ _
    _ = ((M - 1) * D.map f * Q.map f) * (M - 1) ^ l :=
      congrArg (fun Z => Z * (M - 1) ^ l) hA
    _ = 0 := by rw [Matrix.mul_assoc, hQpow, Matrix.mul_zero]

end SplitExact

section Factors

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {N M : ℕ}

/-- A finite family of simple actual subquotients whose common kernel acts
unipotently on a specified quotient representation. -/
structure SimpleFactorFamily
    (ρ : MatrixRepresentation G (Fin N)) (τ : MatrixRepresentation G (Fin M)) where
  length : ℕ
  dimension : Fin length → ℕ
  factor : ∀ i, MatrixRepresentation G (Fin (dimension i))
  simple : ∀ i, Nontrivial (Fin (dimension i) → k) ∧
    ∀ V : Submodule k (Fin (dimension i) → k),
      (factor i).IsStableSubspace V → V = ⊥ ∨ V = ⊤
  subquotient : ∀ i, (factor i).IsSubquotientOf ρ
  nilpotent : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
    (∀ i, (factor i).pointMatrix T x = 1) →
      ((τ.pointMatrix T x : Matrix (Fin M) (Fin M) Γ(T.left, ⊤)) - 1) ^ length = 0

/-- Simple factors of a quotient can be chosen as actual subquotients of the
original representation. Successive quotient dimensions strictly decrease. -/
theorem nonempty_simpleFactorFamily_of_quotient [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G (Fin N)) :
    ∀ (m : ℕ) (τ : MatrixRepresentation G (Fin m))
      (P : Matrix (Fin m) (Fin N) k),
      Intertwines ρ τ P → Function.Surjective P.mulVecLin →
        Nonempty (SimpleFactorFamily ρ τ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro τ P hP hsP
    by_cases hm : m = 0
    · subst m
      exact ⟨{
        length := 0
        dimension := Fin.elim0
        factor := fun i => Fin.elim0 i
        simple := fun i => Fin.elim0 i
        subquotient := fun i => Fin.elim0 i
        nilpotent := fun T x h => Subsingleton.elim _ _
      }⟩
    · have : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
      obtain ⟨d, σ, B, C, hCB, hB, hn, hsimple⟩ :=
        exists_simple_subrepresentation τ
      have hi : Function.Injective B.mulVecLin :=
        coordinateInclusion_injective (R := CommRingCat.of k) B C hCB
      let V := LinearMap.range B.mulVecLin
      have hV : τ.IsStableSubspace V := hB.isStableSubspace_range
      obtain ⟨q⟩ := nonempty_quotientRepresentation τ V hV
      have hdpos : 0 < d := by
        simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
          (Module.finrank_pos_iff.mpr hn : 0 < Module.finrank k (Fin d → k))
      have hdimV : Module.finrank k V = d := by
        dsimp only [V]
        rw [LinearMap.finrank_range_of_inj hi,
          Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      have hdim := q.projection.mulVecLin.finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr q.projection_surjective, q.ker_projection,
        finrank_top, hdimV] at hdim
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
      have hlt : q.dimension < m := by omega
      have hsQ : Function.Surjective (q.projection * P).mulVecLin := by
        rw [Matrix.mulVecLin_mul]
        exact q.projection_surjective.comp hsP
      obtain ⟨F⟩ := ih q.dimension hlt q.representation (q.projection * P)
        (hP.comp q.intertwines) hsQ
      refine ⟨{
        length := F.length + 1
        dimension := Fin.cases d F.dimension
        factor := Fin.cases σ F.factor
        simple := ?_
        subquotient := ?_
        nilpotent := ?_
      }⟩
      · intro i
        refine Fin.cases ?_ (fun j => F.simple j) i
        exact ⟨hn, hsimple⟩
      · intro i
        refine Fin.cases ?_ (fun j => F.subquotient j) i
        exact isSubquotientOf_of_common_quotient ρ σ τ P B hP hsP hB hi
      · intro T x hall
        have hσ : σ.pointMatrix T x = 1 := hall 0
        have hnil := F.nilpotent T x (fun i => hall i.succ)
        have hMB :
            (τ.pointMatrix T x : Matrix (Fin m) (Fin m) Γ(T.left, ⊤)) *
              B.map (scalarMap T) = B.map (scalarMap T) := by
          have h := hB.pointMatrix T x
          rw [hσ, Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one] at h
          exact h.symm
        exact pow_sub_one_eq_zero_of_split_exact B C q.projection q.sectionMap
          hCB q.right_inverse q.ker_projection (scalarMap T) _ _ hMB
          (q.intertwines.pointMatrix T x) F.length hnil

/-- Every finite-dimensional actual affine-group representation has finitely
many simple actual subquotients with unipotent action on their common kernel. -/
theorem nonempty_simpleFactorFamily [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G (Fin N)) :
    Nonempty (SimpleFactorFamily ρ ρ) := by
  apply nonempty_simpleFactorFamily_of_quotient ρ N ρ 1
  · intro A x
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
  · intro v
    exact ⟨v, Matrix.one_mulVec v⟩

/-- A chosen finite family of actual simple factors detecting unipotent action
on its common all-test kernel. -/
def simpleFactorFamily [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G (Fin N)) : SimpleFactorFamily ρ ρ :=
  Classical.choice (nonempty_simpleFactorFamily ρ)

end Factors

end Langlands.GroupScheme.MatrixRepresentation
