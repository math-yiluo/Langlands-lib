import Langlands.Representation.Archimedean.BlockEnvelopingProjection
import Langlands.Representation.Archimedean.Kostant.Matumoto
import Langlands.Group.GL.TriangularParabolic
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof

/-! # Diagonal polynomials of enveloping centres for complex matrix products -/

noncomputable section

universe u v

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.Kostant

open Langlands.Algebra Langlands.Algebra.UniversalEnveloping MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

section Diagonal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ι → ℕ)

/-- One variable for each diagonal entry in the matrix product. -/
abbrev DiagonalCoordinate := Σ i : ι, Fin (n i)

local notation "A" => DiagonalCoordinate n → ℂ
local notation "U" => UniversalEnvelopingAlgebra ℂ (GLProd ℂ n)
local notation "D" => UniversalEnvelopingAlgebra ℂ (DiagonalCoordinate n → ℂ)

/-- The diagonal entries, inserted into the actual matrix product. -/
def diagonalMatrices : A →ₐ[ℂ] GLProd ℂ n :=
  AlgHom.pi fun i => (Matrix.diagonalAlgHom ℂ (α := ℂ)).comp
    (AlgHom.pi fun a => Pi.evalAlgHom ℂ (fun _ : DiagonalCoordinate n => ℂ) ⟨i, a⟩)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem diagonalMatrices_apply (x : A) (i : ι) :
    diagonalMatrices n x i = Matrix.diagonal (fun a => x ⟨i, a⟩) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem deg_pos_iff (a : Coord n) : 0 < deg n a ↔ a.2.1 < a.2.2 := by
  change 0 < ((a.2.2 : ℕ) : ℤ) - ((a.2.1 : ℕ) : ℤ) ↔ _
  rw [sub_pos, Int.ofNat_lt, Fin.lt_def]

omit [Fintype ι] [DecidableEq ι] in
theorem deg_eq_zero_iff (a : Coord n) : deg n a = 0 ↔ a.2.1 = a.2.2 := by
  change ((a.2.2 : ℕ) : ℤ) - ((a.2.1 : ℕ) : ℤ) = 0 ↔ _
  rw [sub_eq_zero, Int.ofNat_inj, Fin.val_inj, eq_comm]

/-- Identify the zero weights with the diagonal entries. -/
def diagonalZeroCoordEquiv : DiagonalCoordinate n ≃ {a : Coord n // deg n a = 0} where
  toFun a := ⟨⟨a.1, a.2, a.2⟩, (deg_eq_zero_iff n _).2 rfl⟩
  invFun a := ⟨a.val.1, a.val.2.1⟩
  left_inv a := by cases a; rfl
  right_inv := by
    rintro ⟨⟨i, p, q⟩, h⟩
    have he : p = q := (deg_eq_zero_iff n ⟨i, p, q⟩).1 h
    subst q
    rfl

/-- The diagonal coordinate vector maps to the corresponding matrix unit. -/
theorem diagonalMatrices_basis (a : DiagonalCoordinate n) :
    diagonalMatrices n (Pi.basisFun ℂ (DiagonalCoordinate n) a) = glBasis ℂ n ⟨a.1, a.2, a.2⟩ := by
  apply (glBasis ℂ n).repr.injective
  ext c
  obtain ⟨i, p, q⟩ := c
  rw [glBasis_repr, Module.Basis.repr_self, Finsupp.single_apply, diagonalMatrices_apply,
    Matrix.diagonal_apply, Pi.basisFun_apply]
  by_cases hpq : p = q
  · subst q
    simp only [ite_true, Pi.single_apply]
    congr 1
    apply propext
    constructor
    · intro h
      exact congrArg (fun b : DiagonalCoordinate n => (⟨b.1, b.2, b.2⟩ : Coord n)) h.symm
    · intro h
      exact congrArg (fun b : Coord n => (⟨b.1, b.2.1⟩ : DiagonalCoordinate n)) h.symm
  · rw [ite_eq_right hpq, ite_eq_right]
    intro h
    exact (hpq ((deg_eq_zero_iff n ⟨i, p, q⟩).1
      (h ▸ (deg_eq_zero_iff n ⟨a.1, a.2, a.2⟩).2 rfl))).elim

private theorem lie_hdiag_basis (a : Coord n) :
    ⁅hdiag n, glBasis ℂ n a⁆ = (deg n a : ℂ) • glBasis ℂ n a := by
  rw [glBasis_apply, lie_hdiag_unit]

/-- The triangular enveloping decomposition for the full diagonal. -/
def diagonalEnvelopingDecomposition :
    RelativeEnvelopingDecomposition (LieEnvelopingEquiv.map (diagonalMatrices n).toLieHom) := by
  let P := positiveWeightLieSubalgebra (glBasis ℂ n) (deg n) (hdiag n) (lie_hdiag_basis n)
  let C := (Pi.basisFun ℂ (DiagonalCoordinate n)).reindex (diagonalZeroCoordEquiv n)
  refine relativeEnvelopingDecomposition_of_weight (glBasis ℂ n) (deg n)
    (diagonalMatrices n).toLieHom P.incl C
    (positiveWeightLieBasis _ _ _ _) ?_ (positiveWeightLieSubalgebra_incl_basis _ _ _ _)
    (hdiag n) (lie_hdiag_basis n)
  intro a
  change diagonalMatrices n ((Pi.basisFun ℂ (DiagonalCoordinate n)).reindex (diagonalZeroCoordEquiv n) a) = _
  rw [Module.Basis.reindex_apply, diagonalMatrices_basis]
  congr 1
  exact congrArg Subtype.val ((diagonalZeroCoordEquiv n).apply_symm_apply a)

theorem diagonalEnvelopingDecomposition_ideal :
    (diagonalEnvelopingDecomposition n).ideal = positiveWeightRightIdeal (glBasis ℂ n) (deg n) := rfl

private def toDiagonalPolynomial : D →ₐ[ℂ] MvPolynomial (DiagonalCoordinate n) ℂ :=
  let f := (Pi.basisFun ℂ (DiagonalCoordinate n)).constr ℂ X
  UniversalEnvelopingAlgebra.lift ℂ
    { f with
      map_lie' := fun {x y} => by
        change f ⁅x, y⁆ = ⁅f x, f y⁆
        have h : ⁅x, y⁆ = 0 := by rw [Ring.lie_def, mul_comm, sub_self]
        rw [h, map_zero, Ring.lie_def, mul_comm, sub_self] }

omit [DecidableEq ι] in
private theorem toDiagonalPolynomial_generator (a : DiagonalCoordinate n) :
    toDiagonalPolynomial n (UniversalEnvelopingAlgebra.ι ℂ (Pi.basisFun ℂ _ a)) = X a := by
  rw [toDiagonalPolynomial, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact Module.Basis.constr_basis _ _ _ _

omit [Fintype ι] [DecidableEq ι] in
private theorem diagonalGenerator_mem_center (x : A) :
    UniversalEnvelopingAlgebra.ι ℂ x ∈ Subalgebra.center ℂ D := by
  apply mem_center_of_commute
  intro y
  have h := (UniversalEnvelopingAlgebra.ι ℂ (L := A)).map_lie y x
  rw [show ⁅y, x⁆ = 0 by rw [Ring.lie_def, mul_comm, sub_self], map_zero, Ring.lie_def] at h
  exact sub_eq_zero.mp h.symm

private def fromDiagonalPolynomial : MvPolynomial (DiagonalCoordinate n) ℂ →ₐ[ℂ] D :=
  (Subalgebra.center ℂ D).val.comp (aeval fun a => (⟨UniversalEnvelopingAlgebra.ι ℂ
    (Pi.basisFun ℂ _ a), diagonalGenerator_mem_center n _⟩ : Subalgebra.center ℂ D))

omit [DecidableEq ι] in
private theorem fromDiagonalPolynomial_X (a : DiagonalCoordinate n) :
    fromDiagonalPolynomial n (X a) = UniversalEnvelopingAlgebra.ι ℂ (Pi.basisFun ℂ _ a) := by
  rw [fromDiagonalPolynomial, AlgHom.comp_apply, aeval_X]
  rfl

/-- The enveloping algebra of the diagonal is freely generated by the diagonal coordinates. -/
def diagonalEnvelopingPolynomialEquiv : D ≃ₐ[ℂ] MvPolynomial (DiagonalCoordinate n) ℂ :=
  AlgEquiv.ofAlgHom (toDiagonalPolynomial n) (fromDiagonalPolynomial n)
    (by apply MvPolynomial.algHom_ext; intro a; rw [AlgHom.comp_apply,
      fromDiagonalPolynomial_X, toDiagonalPolynomial_generator]; rfl)
    (by
      apply UniversalEnvelopingAlgebra.hom_ext
      let gen := UniversalEnvelopingAlgebra.ι ℂ (L := A)
      have h : (fromDiagonalPolynomial n).toLinearMap ∘ₗ
          ((toDiagonalPolynomial n).toLinearMap ∘ₗ gen.toLinearMap) = gen.toLinearMap := by
        refine (Pi.basisFun ℂ (DiagonalCoordinate n)).ext fun a => ?_
        change fromDiagonalPolynomial n (toDiagonalPolynomial n (gen (Pi.basisFun ℂ _ a))) =
          gen (Pi.basisFun ℂ _ a)
        rw [toDiagonalPolynomial_generator, fromDiagonalPolynomial_X]
      exact LieHom.ext fun x => LinearMap.congr_fun h x)

/-- Send a diagonal polynomial to the enveloping algebra along the diagonal inclusion. -/
def diagonalPolynomialInclusion : MvPolynomial (DiagonalCoordinate n) ℂ →ₐ[ℂ] U :=
  (LieEnvelopingEquiv.map (diagonalMatrices n).toLieHom).comp
    (diagonalEnvelopingPolynomialEquiv n).symm.toAlgHom

@[simp]
theorem diagonalPolynomialInclusion_X (a : DiagonalCoordinate n) :
    diagonalPolynomialInclusion n (X a) = UniversalEnvelopingAlgebra.ι ℂ
      (glBasis ℂ n ⟨a.1, a.2, a.2⟩) := by
  change LieEnvelopingEquiv.map (diagonalMatrices n).toLieHom (fromDiagonalPolynomial n (X a)) = _
  rw [fromDiagonalPolynomial_X, LieEnvelopingEquiv.map_generator]
  exact congrArg (UniversalEnvelopingAlgebra.ι ℂ) (diagonalMatrices_basis n a)

/-- The centre map obtained by retaining the diagonal representative and using its polynomial
coordinates. -/
def diagonalCenterPolynomial : Subalgebra.center ℂ U →ₐ[ℂ] MvPolynomial (DiagonalCoordinate n) ℂ :=
  (diagonalEnvelopingPolynomialEquiv n).toAlgHom.comp ((Subalgebra.center ℂ D).val.comp
    (diagonalEnvelopingDecomposition n).centerProjection)

theorem sub_diagonalCenterPolynomial_mem (z : Subalgebra.center ℂ U) :
    z.val - diagonalPolynomialInclusion n (diagonalCenterPolynomial n z) ∈
      positiveWeightRightIdeal (glBasis ℂ n) (deg n) := by
  rw [← diagonalEnvelopingDecomposition_ideal]
  simpa only [diagonalCenterPolynomial, diagonalPolynomialInclusion, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, Subalgebra.val_apply, AlgEquiv.symm_apply_apply] using
    (diagonalEnvelopingDecomposition n).sub_centerProjection_mem z

theorem diagonalCenterPolynomial_eq (z : Subalgebra.center ℂ U) (p : MvPolynomial (DiagonalCoordinate n) ℂ)
    (h : z.val - diagonalPolynomialInclusion n p ∈ positiveWeightRightIdeal (glBasis ℂ n) (deg n)) :
    diagonalCenterPolynomial n z = p := by
  have he := (diagonalEnvelopingDecomposition n).centerProjection_val_eq z
    ((diagonalEnvelopingPolynomialEquiv n).symm p) h
  exact (congrArg (diagonalEnvelopingPolynomialEquiv n) he).trans (AlgEquiv.apply_symm_apply _ _)

end Diagonal

section Comparison

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
  {κ : Type v} [Fintype κ] [DecidableEq κ] {m : κ → ℕ}

omit [DecidableEq ι] [DecidableEq κ] in
/-- The right ideals are compatible with a Lie map that carries each strict upper matrix unit
into a strict upper matrix unit. -/
theorem map_mem_diagonalRightIdeal (J : GLProd ℂ n →ₗ⁅ℂ⁆ GLProd ℂ m)
    (hpos : ∀ a : Coord n, 0 < deg n a → ∃ b : Coord m, 0 < deg m b ∧ J (glBasis ℂ n a) = glBasis ℂ m b)
    {x : UniversalEnvelopingAlgebra ℂ (GLProd ℂ n)} (hx : x ∈ positiveWeightRightIdeal (glBasis ℂ n) (deg n)) :
    LieEnvelopingEquiv.map J x ∈ positiveWeightRightIdeal (glBasis ℂ m) (deg m) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    obtain ⟨b, hb, hJ⟩ := hpos a ha
    rw [map_mul, LieEnvelopingEquiv.map_generator, hJ]
    exact Submodule.subset_span ⟨b, hb, _, rfl⟩
  | zero => rw [map_zero]; exact (positiveWeightRightIdeal _ _).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (positiveWeightRightIdeal _ _).add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact (positiveWeightRightIdeal _ _).smul_mem c hx

/-- A centre congruence modulo strict upper units gives the same diagonal polynomial after the
corresponding renaming of the diagonal coordinates. -/
theorem diagonalCenterPolynomial_eq_rename_of_congruence
    (J : GLProd ℂ n →ₗ⁅ℂ⁆ GLProd ℂ m) (f : DiagonalCoordinate n → DiagonalCoordinate m)
    (hdiag : ∀ a : DiagonalCoordinate n, J (glBasis ℂ n ⟨a.1, a.2, a.2⟩) =
      glBasis ℂ m ⟨(f a).1, (f a).2, (f a).2⟩)
    (hpos : ∀ a : Coord n, 0 < deg n a → ∃ b : Coord m, 0 < deg m b ∧ J (glBasis ℂ n a) = glBasis ℂ m b)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (GLProd ℂ m)))
    (w : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (GLProd ℂ n)))
    (h : z.val - LieEnvelopingEquiv.map J w.val ∈ positiveWeightRightIdeal (glBasis ℂ m) (deg m)) :
    diagonalCenterPolynomial m z = rename f (diagonalCenterPolynomial n w) := by
  have hJ : (LieEnvelopingEquiv.map J).comp (diagonalPolynomialInclusion n) =
      (diagonalPolynomialInclusion m).comp (rename f) := by
    apply MvPolynomial.algHom_ext
    intro a
    rw [AlgHom.comp_apply, diagonalPolynomialInclusion_X, LieEnvelopingEquiv.map_generator,
      hdiag, AlgHom.comp_apply, rename_X, diagonalPolynomialInclusion_X]
  apply diagonalCenterPolynomial_eq
  have h' := map_mem_diagonalRightIdeal J hpos (sub_diagonalCenterPolynomial_mem n w)
  rw [map_sub, show LieEnvelopingEquiv.map J (diagonalPolynomialInclusion n
        (diagonalCenterPolynomial n w)) = diagonalPolynomialInclusion m (rename f
        (diagonalCenterPolynomial n w)) from DFunLike.congr_fun hJ _] at h'
  convert (positiveWeightRightIdeal (glBasis ℂ m) (deg m)).add_mem h h' using 1
  abel

end Comparison

section BlockComparison

open Langlands.GeneralLinear Langlands.Geometric

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n : ℕ} (B : BlockShape n)

/-- The same diagonal positions, indexed first by their Levi block. -/
def blockDiagonalCoord (a : DiagonalCoordinate (blockRanks B ι)) :
    DiagonalCoordinate (fun _ : ι => n) :=
  ⟨a.1.1, B.index a.1.2 a.2⟩

omit [DecidableEq ι] in
private theorem blockRightIdeal_le_diagonalRightIdeal :
    positiveWeightRightIdeal (glBasis ℂ (fun _ : ι => n)) (blockAdjointWeight B ι) ≤
      positiveWeightRightIdeal (glBasis ℂ (fun _ : ι => n)) (deg (fun _ : ι => n)) := by
  apply Submodule.span_mono
  rintro _ ⟨⟨i, p, q⟩, h, v, rfl⟩
  refine ⟨⟨i, p, q⟩, (deg_pos_iff (fun _ : ι => n) ⟨i, p, q⟩).2 ?_, v, rfl⟩
  have hpq := (blockAdjointWeight_pos_iff B (⟨i, p, q⟩ : Coord (fun _ : ι => n))).1 h
  obtain ⟨⟨j, p⟩, rfl⟩ := B.indexEquiv.surjective p
  obtain ⟨⟨k, q⟩, rfl⟩ := B.indexEquiv.surjective q
  change blockIndex B (B.index j p) < blockIndex B (B.index k q) at hpq
  rw [blockIndex_index, blockIndex_index] at hpq
  exact B.index_lt_index_of_block_lt hpq p q

/-- Projection to the diagonal agrees with projection through the actual block Levi. -/
theorem diagonalCenterPolynomial_blockProjection
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (GLProd ℂ (fun _ : ι => n)))) :
    diagonalCenterPolynomial (fun _ : ι => n) z =
      rename (blockDiagonalCoord B) (diagonalCenterPolynomial (blockRanks B ι)
        ((blockEnvelopingDecomposition B).centerProjection z)) := by
  refine diagonalCenterPolynomial_eq_rename_of_congruence (blockMatrixInclusion B).toLieHom
    (blockDiagonalCoord B) ?_ ?_ z ((blockEnvelopingDecomposition B).centerProjection z) ?_
  · intro a
    exact blockMatrixInclusion_basis B ⟨a.1, a.2, a.2⟩
  · intro a ha
    refine ⟨blockCoord B a, (deg_pos_iff _ _).2 ?_, blockMatrixInclusion_basis B a⟩
    exact index_strictMono B a.1.2 ((deg_pos_iff _ a).1 ha)
  · apply blockRightIdeal_le_diagonalRightIdeal B
    exact (blockEnvelopingDecomposition B).sub_centerProjection_mem z

end BlockComparison

end Langlands.Archimedean.Kostant
