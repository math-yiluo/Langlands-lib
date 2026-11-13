import Langlands.GroupScheme.Quaternionic.DegreeSplittingDarboux
import Langlands.GroupScheme.Quaternionic.DegreeSplittingIso
import Langlands.GroupScheme.Quaternionic.AntihermitianSplitRankLower
import Langlands.GroupScheme.Quaternionic.AntihermitianSplitRankUpper
import Langlands.Algebra.CentralSimple.SeparableClosureChart
import Langlands.GroupScheme.Torus.ExponentHomomorphisms
import Langlands.GroupScheme.SymplecticMatrix.TypeC
import Langlands.GroupScheme.Rational.SplitTorusMonomorphism
import Langlands.GroupScheme.Rational.SplitRankTransport

/-!
# The Witt torus of `SU(D, h)` over a separable closure

Let `D` be a central division algebra of degree `δ` over `K`, `σ` an involution of the first
kind of `D` whose symmetric elements have dimension `δ (δ + 1) / 2`, and `H ∈ M_m(D)` an
invertible trace-valued `σ`-antihermitian Gram matrix of Witt index `r`, with `m δ = 2 N`.
This module shows (`exists_wittTorus_splitting`) that `r δ ≤ N` and that there are

* a maximal split torus `s : 𝔾ₘ^r → σ.symplecticGroup H` (the Witt torus), and
* an isomorphism `Φ` from the base change of `σ.symplecticGroup H` to the separable closure
  `K_s` of `K` onto the split symplectic group `Sp_{2N}`,

such that the base change of `s` followed by `Φ` is the explicit homomorphism
`blockTorusHom K_s δ r N : 𝔾ₘ^r → 𝔾ₘ^N` followed by the diagonal torus `t ↦ diag(t, t⁻¹)` of
`Sp_{2N}`. On points `blockTorusHom` sends `t` to `(t_{k(a)})_a`, where `k(a)` is the block
`k δ ≤ a < (k + 1) δ` containing `a`, and the coordinate is `1` when `a ≥ r δ`. Equivalently
(`characterCoordEquiv_blockTorusHom_comp_coordChar`) the coordinate character `e_a` of the
diagonal torus pulls back to the character with coordinates `blockWeight δ r a`, the indicator
of the block containing `a`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix Module
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic

namespace DegreeSplitting

attribute [local instance] restrictedSectionsAlgebra restrictedSectionsScalarTower

open FirstKindInvolution CentralSimpleUnits.MatrixDiagonalTorus FiniteAlgebraUnits.MatrixPoints
open AntihermitianSplitRank (wittGram monomial monomial_apply monomial_add monomial_zero
  weightUnits weightUnits_val weightHom symplecticTorus symplecticTorus_comp pointsEquiv_comp_weightHom
  isClosedSubgroup_symplecticTorus card_le_wittIndex exists_wittBlockBasis)

/-! ### The block exponent homomorphism -/

section BlockTorus

variable (L : Type u) [Field L] (δ r N : ℕ)

/-- The integral matrix of `blockTorusHom`: the character `e_a` of `𝔾ₘ^N` pulls back to
`blockWeight δ r a`. -/
def blockExponent : (ULift.{u} (Fin N) → ℤ) →ₗ[ℤ] (ULift.{u} (Fin r) → ℤ) :=
  (Matrix.of fun (k : ULift.{u} (Fin r)) (a : ULift.{u} (Fin N)) =>
    blockWeight δ r a.down k.down).mulVecLin

theorem blockExponent_single (a : ULift.{u} (Fin N)) :
    blockExponent δ r N (Pi.single a 1) = fun k => blockWeight δ r a.down k.down := by
  funext k
  simp [blockExponent]

/-- The homomorphism `𝔾ₘ^r → 𝔾ₘ^N`, `t ↦ (∏_k t_k^{blockWeight δ r a k})_a`. -/
def blockTorusHom :
    splitTorus.commGroupScheme (Spec (CommRingCat.of L)) (ULift.{u} (Fin r)) ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of L)) (ULift.{u} (Fin N)) :=
  splitTorus.exponentHom (Spec (CommRingCat.of L)) (ULift.{u} (Fin r)) (ULift.{u} (Fin N))
    (blockExponent δ r N)

variable {L δ r N} in
/-- On points, `blockTorusHom` is the monomial map of the block weights. -/
theorem pointsEquiv_blockTorusHom {T : Over (Spec (CommRingCat.of L))}
    (x : T ⟶ (splitTorus (Spec (CommRingCat.of L)) (ULift.{u} (Fin r))).X)
    (a : ULift.{u} (Fin N)) :
    splitTorus.pointsEquiv (ULift.{u} (Fin N)) T
        (x ≫ (CommGroupScheme.groupHom (blockTorusHom L δ r N)).hom.hom) a =
      monomial (fun k : ULift.{u} (Fin r) => blockWeight δ r a.down k.down)
        (splitTorus.pointsEquiv (ULift.{u} (Fin r)) T x) := by
  rw [← splitTorus.comp_proj, Category.assoc]
  change Gm.pointsEquiv _ T (x ≫ (CommGroupScheme.groupHom
    (blockTorusHom L δ r N ≫ splitTorus.proj _ _ a)).hom.hom) = _
  rw [blockTorusHom, splitTorus.exponentHom_comp_proj, splitTorus.pointsEquiv_exponentCharacter,
    monomial_apply, blockExponent_single]

/-- **Character identity.** The coordinate character `e_a` of the diagonal torus of `Sp_{2N}`
pulls back along `blockTorusHom` to the indicator of the block `k δ ≤ a < (k + 1) δ`. -/
theorem characterCoordEquiv_blockTorusHom_comp_coordChar (a : Fin N) :
    GeneralLinear.characterCoordEquiv (Fin r) L
        (blockTorusHom L δ r N ≫ SymplecticMatrix.coordChar (Fin N) L a) =
      fun k => if k.val * δ ≤ a.val ∧ a.val < (k.val + 1) * δ then 1 else 0 := by
  have hc : SymplecticMatrix.coordChar (Fin N) L a =
      splitTorus.exponentCharacter (Spec (CommRingCat.of L)) (ULift.{u} (Fin N))
        (Pi.single ⟨a⟩ 1) := by
    apply (GeneralLinear.characterCoordEquiv (Fin N) L).injective
    rw [SymplecticMatrix.characterCoordEquiv_coordChar]
    funext c
    rw [GeneralLinear.characterCoordEquiv_apply,
      splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm, AddEquiv.apply_symm_apply]
    simp only [Pi.single_apply, ULift.ext_iff]
  funext k
  rw [hc, blockTorusHom, splitTorus.exponentHom_comp_exponentCharacter,
    GeneralLinear.characterCoordEquiv_apply,
    splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm, AddEquiv.apply_symm_apply,
    blockExponent_single]
  rfl

end BlockTorus

/-! ### Witt weights -/

section Weights

variable {D : Type u} [DivisionRing D] {r d : ℕ}

/-- The Witt weights add up to zero where the Witt block Gram matrix is nonzero. -/
theorem wittWeight_add_eq_zero (HU : Matrix (Fin d) (Fin d) D) (s t : (Fin r ⊕ Fin r) ⊕ Fin d)
    (h : wittGram HU s t ≠ 0) : wittWeight s + wittWeight t = 0 := by
  rcases s with ((k | k) | v) <;> rcases t with ((l | l) | w) <;>
    simp [wittGram, wittWeight, Matrix.one_apply] at h ⊢
  · rw [h, add_neg_cancel]
  · rw [h, neg_add_cancel]

/-- The Witt weights add up to zero. -/
theorem sum_wittWeight : ∑ s : (Fin r ⊕ Fin r) ⊕ Fin d, wittWeight s = 0 := by
  simp [Fintype.sum_sum_type, wittWeight]

end Weights

/-! ### Diagonal matrices under the matrix chart -/

section Chart

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  {L : Type u} [Field L] [Algebra K L] {κ : Type} [Fintype κ] [DecidableEq κ]
  (e : L ⊗[K] D ≃ₐ[L] Matrix κ κ L) {n : Type} [Fintype n] [DecidableEq n]
  (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]

/-- The matrix chart of the diagonal matrix `diag(c)` is the diagonal matrix with blocks
`c_i · 1`. -/
theorem matrixChartR_diagRingHom (c : n → R) :
    matrixChartR e R (diagRingHom K D R c) = Matrix.diagonal fun p : n × κ => c p.1 := by
  have he1 : e (1 ⊗ₜ[K] (1 : D)) = 1 := by rw [← Algebra.TensorProduct.one_def, _root_.map_one]
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [matrixChartR_apply, coefficientEquiv_diagRingHom]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, chartR_tmul, he1,
      Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.smul_apply, Matrix.one_apply_ne hab, smul_zero,
        Matrix.diagonal_apply_ne _ (fun h => hab (congrArg Prod.snd h))]
  · rw [Matrix.diagonal_apply_ne _ hij, chartR_apply, _root_.map_zero, Matrix.zero_apply,
      Matrix.diagonal_apply_ne _ (fun h => hij (congrArg Prod.fst h))]

/-- A matrix which is homogeneous for weights `V` (rows) and `W` (columns) intertwines the
diagonal matrices of the monomials of the weights. -/
theorem map_mul_diagonal_monomial {α β I : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    [Fintype β] [Fintype I]
    {A : Type*} [CommRing A] (f : L →+* A) (P : Matrix α β L) (V : α → I → ℤ)
    (W : β → I → ℤ) (hP : ∀ a b, P a b ≠ 0 → V a = W b) (t : I → Aˣ) :
    P.map f * Matrix.diagonal (fun b => (monomial (W b) t : A)) =
      Matrix.diagonal (fun a => (monomial (V a) t : A)) * P.map f := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  by_cases h : P a b = 0
  · simp [h]
  · rw [hP a b h, mul_comm]

end Chart

/-! ### The Witt torus in the split symplectic group -/

section Square

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [FiniteDimensional K D] {L : Type u} [Field L] [Algebra K L] {δ : ℕ}
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin δ) (Fin δ) L) (σ : FirstKindInvolution K D)
  {m : ℕ} [NeZero m] {r d : ℕ} (ε : Fin m ≃ (Fin r ⊕ Fin r) ⊕ Fin d)
  (G : Matrix (Fin m) (Fin m) D) {N : ℕ}
  {P : Matrix (Fin N ⊕ Fin N) (Fin m × Fin δ) L} {P' : Matrix (Fin m × Fin δ) (Fin N ⊕ Fin N) L}

/-- The Witt weights of the rows, as weights of `𝔾ₘ^r` with `ULift` coordinates. -/
def liftedWittWeight (i : Fin m) : ULift.{u} (Fin r) → ℤ := fun k => wittWeight (ε i) k.down

omit [NeZero m] in
theorem liftedWittWeight_add_eq_zero (HU : Matrix (Fin d) (Fin d) D)
    (hG : ∀ i j, G i j = wittGram HU (ε i) (ε j)) (i j : Fin m) (h : G i j ≠ 0) :
    liftedWittWeight ε i + liftedWittWeight ε j = 0 := by
  funext k
  rw [hG] at h
  exact congrFun (wittWeight_add_eq_zero HU _ _ h) k.down

omit [NeZero m] in
theorem sum_liftedWittWeight : ∑ i, liftedWittWeight.{u} ε i = 0 := by
  funext k
  rw [Finset.sum_apply, Pi.zero_apply]
  simp only [liftedWittWeight]
  have h := congrFun (sum_wittWeight (r := r) (d := d)) k.down
  rw [Finset.sum_apply, Pi.zero_apply] at h
  rw [← h]
  exact Equiv.sum_comp ε (fun s => wittWeight s k.down)

omit [NeZero m] in
theorem exists_liftedWittWeight_eq_single (k : ULift.{u} (Fin r)) :
    ∃ i, liftedWittWeight ε i = Pi.single k 1 := by
  refine ⟨ε.symm (Sum.inl (Sum.inl k.down)), funext fun l => ?_⟩
  simp only [liftedWittWeight, Equiv.apply_symm_apply, wittWeight, Pi.single_apply,
    ULift.ext_iff]

variable (hPP' : P * P' = 1) (hP'P : P' * P = 1) (hPC : P * splitGram e σ G * Pᵀ = J (Fin N) L)
  (hhom : ∀ α β, P α β ≠ 0 → darbouxWeight δ r α = wittWeight (ε β.1))
  (hG : ∀ i j, G i j ≠ 0 → liftedWittWeight ε i + liftedWittWeight ε j = 0)
  (hsum : ∑ i, liftedWittWeight.{u} ε i = 0)

omit [Algebra.IsCentral K D] [FiniteDimensional K D] [NeZero m] in
include hhom hPP' in
/-- On a weighted diagonal unit, `u ↦ P Φ(u) P'` is the diagonal matrix of block weights. -/
theorem darbouxMatrix_weightUnits (R : Type u) [CommRing R] [Algebra K R] [Algebra L R]
    [IsScalarTower K L R] (t : ULift.{u} (Fin r) → Rˣ) :
    darbouxMatrix e P P' R
        (weightUnits K D (liftedWittWeight ε) R t : R ⊗[K] Matrix (Fin m) (Fin m) D) =
      Matrix.diagonal fun α =>
        (monomial (fun k : ULift.{u} (Fin r) => darbouxWeight δ r α k.down) t : R) := by
  rw [darbouxMatrix, weightUnits_val, matrixChartR_diagRingHom,
    map_mul_diagonal_monomial (algebraMap L R) P
      (fun α (k : ULift.{u} (Fin r)) => darbouxWeight δ r α k.down)
      (fun β : Fin m × Fin δ => liftedWittWeight ε β.1)
      (fun α β h => funext fun k => congrFun (hhom α β h) k.down) t,
    Matrix.mul_assoc, map_mul_map_eq_one hPP', Matrix.mul_one]

theorem monomial_neg {I : Type*} [Fintype I] {A : Type*} [CommRing A] (a : I → ℤ)
    (t : I → Aˣ) : monomial (-a) t = (monomial a t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← monomial_add, neg_add_cancel, monomial_zero]

include hhom in
/-- **The Witt torus over `L`.** After base change to `L` and the splitting isomorphism, the
weighted diagonal torus of the Witt weights is `blockTorusHom` followed by the diagonal torus of
`Sp_{2N}`. -/
theorem baseChange_symplecticTorus_comp_splittingIso :
    (splitTorus.baseChangeIso (scalarBaseMap K L) (ULift.{u} (Fin r))).inv ≫
        (GroupScheme.baseChange (scalarBaseMap K L)).map
          (symplecticTorus σ (liftedWittWeight ε) G hG hsum) ≫
        (splittingIso e σ G P P' hPP' hP'P hPC).hom =
      CommGroupScheme.groupHom (blockTorusHom L δ r N) ≫
        SymplecticMatrix.diagonalTorus (Fin N) (CommRingCat.of L) := by
  apply hom_ext_points
  intro T x
  apply (SymplecticMatrix.pointsEquiv (Fin N) (CommRingCat.of L) T).injective
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc,
    pointsEquiv_splittingIso_hom, Grp.comp_hom_hom, ← Category.assoc,
    SymplecticMatrix.pointsEquiv_diagonalTorus]
  apply Subtype.ext
  rw [splitPointsEquiv_apply, unitPoint_apply, GroupScheme.baseChangePointsEquiv_comp,
    Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, ← Category.assoc]
  have hamb : (symplecticTorus σ (liftedWittWeight ε) G hG hsum ≫ σ.symplecticGroupι G) ≫
      σ.unitaryGroupι G = weightHom (K := K) (D := D) (liftedWittWeight ε) := by
    rw [Category.assoc]
    exact symplecticTorus_comp σ _ G hG hsum
  rw [hamb, pointsEquiv_comp_weightHom]
  have ht : splitTorus.pointsEquiv (ULift.{u} (Fin r)) ((Over.map (scalarBaseMap K L)).obj T)
      (GroupScheme.baseChangePointsEquiv (scalarBaseMap K L)
        (splitTorus (Spec (CommRingCat.of K)) (ULift.{u} (Fin r))) T
        (x ≫ (splitTorus.baseChangeIso (scalarBaseMap K L) (ULift.{u} (Fin r))).inv.hom.hom)) =
      splitTorus.pointsEquiv (ULift.{u} (Fin r)) T x := by
    change splitTorus.baseChangePointsEquiv (scalarBaseMap K L) (ULift.{u} (Fin r)) T
      (x ≫ (splitTorus.baseChangeIso (scalarBaseMap K L) (ULift.{u} (Fin r))).inv.hom.hom) = _
    exact isoOfPointModels_inv _ _ _ _ _ _ T x
  rw [ht]
  refine (darbouxMatrix_weightUnits e ε hPP' hhom (restrictedSections K L T)
    (splitTorus.pointsEquiv (ULift.{u} (Fin r)) T x)).trans ?_
  rw [SymplecticMatrix.coe_leviHom, SymplecticMatrix.levi_diagonalTorusUnits]
  congr 1
  funext α
  rcases α with a | a
  · rw [SymplecticMatrix.torusWeights, Sum.elim_inl, pointsEquiv_blockTorusHom]
    rfl
  · rw [SymplecticMatrix.torusWeights, Sum.elim_inr, pointsEquiv_blockTorusHom, ← monomial_neg]
    rfl

end Square

/-! ### Maximality -/

section Maximal

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] (σ : FirstKindInvolution K D) {m : ℕ} [NeZero m]
  (H : Matrix (Fin m) (Fin m) D)

/-- A closed split torus `𝔾ₘ^I` of `σ.symplecticGroup H` with `|I|` the Witt index is a maximal
split torus. -/
theorem isMaximalSplitTorus_of_card_eq_wittIndex {I : Type u} [Fintype I] [DecidableEq I]
    (s : (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I).toGrp ⟶ σ.symplecticGroup H)
    (hs : IsClosedSubgroup s) (hu : IsUnit H) (hcard : Fintype.card I = σ.wittIndex H) :
    IsMaximalSplitTorus s := by
  refine ⟨⟨isSplitTorus_splitTorus I, hs⟩, ?_⟩
  intro M j' hj' a ha
  obtain ⟨J, hJ, ⟨e⟩⟩ := hj'.1
  have := Fintype.ofFinite J
  classical
  let f : splitTorus (Spec (CommRingCat.of K)) I ⟶ splitTorus (Spec (CommRingCat.of K)) J :=
    a ≫ e.hom
  let j'' : splitTorus (Spec (CommRingCat.of K)) J ⟶ σ.symplecticGroup H := e.inv ≫ j'
  have hj'' : IsClosedSubgroup j'' := hj'.2.iso_comp e.symm
  have hfac : f ≫ j'' = s := by
    simp only [f, j'', Category.assoc, Iso.hom_inv_id_assoc]
    exact ha
  have hle : Fintype.card J ≤ σ.wittIndex H := card_le_wittIndex σ H j'' hu hj''
  have : IsClosedImmersion s.hom.hom.left := hs
  have : Mono s.hom.hom := Over.mono_of_mono_left _
  have : Mono f.hom.hom := mono_of_mono_fac (congrArg (fun b => b.hom.hom) hfac)
  have hge : Nat.card I ≤ Nat.card J := splitTorus.card_le_card_of_mono I J f
  have : IsIso f := splitTorus.isIso_of_mono_of_card_eq I J f (le_antisymm hge (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    omega))
  exact (isIso_comp_right_iff a e.hom).mp (show IsIso (a ≫ e.hom) from inferInstance)

end Maximal

/-! ### The main theorem -/

section Main

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)

theorem isUnit_apply {A : Type*} [Ring A] [Algebra K A] (τ : FirstKindInvolution K A) {x : A}
    (hx : IsUnit x) : IsUnit (τ x) := by
  obtain ⟨v, rfl⟩ := hx
  exact ⟨⟨τ v, τ ↑v⁻¹, by rw [← FirstKindInvolution.map_mul, v.inv_mul, FirstKindInvolution.map_one],
    by rw [← FirstKindInvolution.map_mul, v.mul_inv, FirstKindInvolution.map_one]⟩, rfl⟩

theorem isClosedSubgroup_comp_iso {S : Scheme.{u}} {A B C : GroupScheme S} {i : A ⟶ B}
    (hi : IsClosedSubgroup i) (c : B ≅ C) : IsClosedSubgroup (i ≫ c.hom) := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion c.hom.hom.hom.left := IsClosedSubgroup.of_iso c
  change IsClosedImmersion (i.hom.hom.left ≫ c.hom.hom.hom.left)
  infer_instance

/-- **The Witt torus over a separable closure.** For an invertible trace-valued antihermitian
`H ∈ M_m(D)` of Witt index `r`, `D` of degree `δ` with `σ` orthogonal-type
(`dim D^σ = δ (δ + 1) / 2`) and `m δ = 2 N`: `r δ ≤ N`, and there are a maximal split torus
`s : 𝔾ₘ^r → σ.symplecticGroup H` and an isomorphism `Φ` of the base change to `K_s` with
`Sp_{2N}` such that the base change of `s` followed by `Φ` is `blockTorusHom` followed by the
diagonal torus. -/
theorem exists_wittTorus_splitting {δ m N : ℕ} [NeZero m] (hD : finrank K D = δ ^ 2)
    (hσ : finrank K σ.symmetricSubspace = δ * (δ + 1) / 2) (H : Matrix (Fin m) (Fin m) D)
    (hH : σ.IsAntihermitian H) (hu : IsUnit H) (hN : m * δ = 2 * N) :
    σ.wittIndex H * δ ≤ N ∧
      ∃ (s : (splitTorus.commGroupScheme (Spec (CommRingCat.of K))
          (ULift.{u} (Fin (σ.wittIndex H)))).toGrp ⟶ σ.symplecticGroup H)
        (Φ : σ.baseChangeSymplecticGroup H (L := SeparableClosure K) ≅
          SymplecticMatrix.groupScheme (Fin N) (CommRingCat.of (SeparableClosure K))),
        IsMaximalSplitTorus s ∧
          (splitTorus.baseChangeIso (scalarBaseMap K (SeparableClosure K))
              (ULift.{u} (Fin (σ.wittIndex H)))).inv ≫
            (GroupScheme.baseChange (scalarBaseMap K (SeparableClosure K))).map s ≫ Φ.hom =
          CommGroupScheme.groupHom
              (blockTorusHom (SeparableClosure K) δ (σ.wittIndex H) N) ≫
            SymplecticMatrix.diagonalTorus (Fin N) (CommRingCat.of (SeparableClosure K)) := by
  classical
  -- the chart over the separable closure
  obtain ⟨δ', -, hfin, ⟨e⟩⟩ := CentralSimple.exists_separableClosure_matrix_chart K D
  have hδ : δ' = δ := by
    rw [hD, sq] at hfin
    exact Nat.mul_self_inj.1 hfin.symm
  subst hδ
  -- the Witt block basis
  obtain ⟨d, ε, PW, HU, hPW, hHU, hW⟩ := exists_wittBlockBasis hH hu
  set H' := PW * H * σ.matrix (Fin m) PW with hH'
  have c := σ.symplecticGroupCongr hPW.unit H
  rw [IsUnit.unit_spec] at c
  have hu' : IsUnit H' := (hPW.mul hu).mul (isUnit_apply (σ.matrix (Fin m)) hPW)
  -- the Darboux matrix
  obtain ⟨hrN, P, P', hPP', hP'P, hPC, hhom⟩ :=
    exists_wittDarboux e σ hσ ε hHU hu' hW hN
  refine ⟨hrN, ?_⟩
  have hG := liftedWittWeight_add_eq_zero.{u} ε H' HU hW
  have hsum := sum_liftedWittWeight.{u} ε
  let sT := symplecticTorus σ (liftedWittWeight.{u} ε) H' hG hsum
  refine ⟨sT ≫ c.inv, (GroupScheme.baseChange (scalarBaseMap K (SeparableClosure K))).mapIso c ≪≫
    splittingIso e σ H' P P' hPP' hP'P hPC, ?_, ?_⟩
  · apply isMaximalSplitTorus_of_card_eq_wittIndex σ H _ _ hu (by simp)
    exact isClosedSubgroup_comp_iso
      (isClosedSubgroup_symplecticTorus σ _ H' hG hsum (exists_liftedWittWeight_eq_single ε))
      c.symm
  · simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc (GroupScheme.baseChange _) c.inv c.hom,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    exact baseChange_symplecticTorus_comp_splittingIso e σ ε H' hPP' hP'P hPC hhom hG hsum

end Main

end DegreeSplitting

end Langlands.GroupScheme.Quaternionic
