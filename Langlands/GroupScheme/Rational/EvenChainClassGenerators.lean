import Langlands.Representation.Plancherel.RationalMatrixNormComparison
import Langlands.GroupScheme.Rational.FundamentalCharacterGenerationProof
import Langlands.GroupScheme.Rational.FundamentalRepresentationsProof
import Langlands.GroupScheme.Rational.CharpolyClassFunctions
import Langlands.GroupScheme.Rational.PathFundamentalWeights
import Langlands.GroupScheme.Rational.EvenChainPatternProducts
import Langlands.GroupScheme.GeneralLinearPointTopology
import Mathlib.RingTheory.Polynomial.Vieta

/-! # Path characteristic polynomials and off-path traces detect the class quotient -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.RootDatum.Triangular

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {P : RootPairing ι ℤ X Y}
  {b : P.Base}

/-- A finite sum of elements of the simple-root cone vanishes only if every summand does. -/
theorem eq_zero_of_sum_eq_zero {σ : Type*} {s : Finset σ} {f : σ → X}
    (hf : ∀ i ∈ s, f i ∈ positiveCone P b) (h : ∑ i ∈ s, f i = 0) :
    ∀ i ∈ s, f i = 0 := by
  classical
  intro i hi
  apply eq_zero_of_mem_positiveCone_of_neg_mem (hf i hi)
  have h' : -f i = ∑ j ∈ s.erase i, f j := by
    rw [← Finset.add_sum_erase s f hi] at h
    exact neg_eq_of_add_eq_zero_right h
  rw [h']
  exact AddSubmonoid.sum_mem _ fun j hj => hf j (Finset.mem_of_mem_erase hj)

/-- The `a`-th smallest element of a set of `m` elements of `Fin N` is at least `a`. -/
theorem le_orderEmbOfFin {N m : ℕ} (t : Finset (Fin N)) (h : t.card = m) (a : Fin m) :
    (a : ℕ) ≤ (t.orderEmbOfFin h a : ℕ) := by
  obtain ⟨a, ha⟩ := a
  induction a with
  | zero => exact Nat.zero_le _
  | succ a ih =>
    have hlt : t.orderEmbOfFin h ⟨a, by omega⟩ < t.orderEmbOfFin h ⟨a + 1, ha⟩ :=
      (t.orderEmbOfFin h).strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self a))
    have := ih (by omega)
    rw [Fin.lt_def] at hlt
    simp only at this ⊢
    omega

variable {k : Type*} [CommRing k]

/-- **Elementary symmetric functions of a decreasing chain of weights.** Let `ε_0, …, ε_{N-1}`
be distinct weights, decreasing in the simple-root order. The sum of the monomials of all
`m`-element subsets of the `ε_j` has top weight `ε_0 + ⋯ + ε_{m-1}`, with coefficient one. -/
theorem isTopWeight_sum_powersetCard {N : ℕ} (ε : Fin N → X)
    (hdec : ∀ j j' : Fin N, j ≤ j' → ε j - ε j' ∈ positiveCone P b)
    (hinj : Function.Injective ε) {m : ℕ} (hm : m ≤ N) :
    IsTopWeight P b (∑ a : Fin m, ε (Fin.castLE hm a))
      (∑ t ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
        AddMonoidAlgebra.single (∑ j ∈ t, ε j) (1 : k)) := by
  classical
  have key : ∀ t ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
      (∑ a : Fin m, ε (Fin.castLE hm a)) - ∑ j ∈ t, ε j ∈ positiveCone P b ∧
        ((∑ a : Fin m, ε (Fin.castLE hm a)) = ∑ j ∈ t, ε j →
          t = Finset.univ.map (Fin.castLEEmb hm)) := by
    intro t ht
    have hcard : t.card = m := (Finset.mem_powersetCard.mp ht).2
    have hsum : ∑ j ∈ t, ε j = ∑ a : Fin m, ε (t.orderEmbOfFin hcard a) := by
      conv_lhs => rw [← Finset.image_orderEmbOfFin_univ t hcard]
      rw [Finset.sum_image fun a _ a' _ h => (t.orderEmbOfFin hcard).injective h]
    have hle : ∀ a : Fin m, Fin.castLE hm a ≤ t.orderEmbOfFin hcard a := fun a => by
      rw [Fin.le_def, Fin.val_castLE]
      exact le_orderEmbOfFin t hcard a
    have hdiff : (∑ a : Fin m, ε (Fin.castLE hm a)) - ∑ j ∈ t, ε j =
        ∑ a : Fin m, (ε (Fin.castLE hm a) - ε (t.orderEmbOfFin hcard a)) := by
      rw [hsum, Finset.sum_sub_distrib]
    refine ⟨?_, fun heq => ?_⟩
    · rw [hdiff]
      exact AddSubmonoid.sum_mem _ fun a _ => hdec _ _ (hle a)
    · have h0 : ∑ a : Fin m, (ε (Fin.castLE hm a) - ε (t.orderEmbOfFin hcard a)) = 0 := by
        rw [← hdiff, heq, sub_self]
      have hz := eq_zero_of_sum_eq_zero (fun a _ => hdec _ _ (hle a)) h0
      have hs : ∀ a, t.orderEmbOfFin hcard a = Fin.castLE hm a := fun a =>
        (hinj (sub_eq_zero.mp (hz a (Finset.mem_univ a)))).symm
      ext j
      have hj : j ∈ Finset.univ.image (t.orderEmbOfFin hcard) ↔ j ∈ t := by
        rw [Finset.image_orderEmbOfFin_univ]
      rw [← hj, Finset.mem_image, Finset.mem_map]
      simp only [Finset.mem_univ, true_and, hs]
      exact Iff.rfl
  have hS0 : Finset.univ.map (Fin.castLEEmb hm) ∈
      Finset.powersetCard m (Finset.univ : Finset (Fin N)) := by
    rw [Finset.mem_powersetCard]
    simp
  have htop : ∑ j ∈ Finset.univ.map (Fin.castLEEmb hm), ε j =
      ∑ a : Fin m, ε (Fin.castLE hm a) := by
    rw [Finset.sum_map]
    rfl
  constructor
  · rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      Finset.sum_eq_single (Finset.univ.map (Fin.castLEEmb hm))]
    · rw [AddMonoidAlgebra.coeff_single, htop, Finsupp.single_eq_same]
    · intro t ht hne
      rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right]
      intro h
      exact hne ((key t ht).2 h.symm)
    · intro h
      exact absurd hS0 h
  · intro μ hμ
    rw [AddMonoidAlgebra.coeff_sum] at hμ
    obtain ⟨t, ht, hμt⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hμ)
    rw [AddMonoidAlgebra.coeff_single] at hμt
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hμt)]
    exact (key t ht).1

end Langlands.RootDatum.Triangular

namespace Langlands.LinearAlgebra.RootDatumPathWeights

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {P : RootDatum ι M N} {b : P.Base}
  {L : ℕ} {β : Fin L → b.support} {ω : M}

/-- The sum `ε_0 + ⋯ + ε_i` of the first `i + 1` path weights is the fundamental weight of the
path vertex `i`, on the path. -/
theorem pairing_sum_pathWeight (hβ : IsPathComponent β) (hω : IsPathFundamental β ω)
    {i : ℕ} (hi : i < L) (l : Fin L) :
    P.toLinearMap (∑ j ∈ Finset.range (i + 1), pathWeight β ω j) (P.coroot (β l : ι)) =
      if (l : ℕ) = i then 1 else 0 := by
  induction i with
  | zero =>
    rw [Finset.sum_range_one, pairing_pathWeight hβ hω (by omega) l]
    split_ifs <;> omega
  | succ i ih =>
    rw [Finset.sum_range_succ, map_add, LinearMap.add_apply, ih (by omega),
      pairing_pathWeight hβ hω (by omega) l]
    split_ifs <;> omega

/-- The sum of path weights is orthogonal to the coroots of simple roots off the path. -/
theorem pairing_sum_pathWeight_of_not_mem (hβ : IsPathComponent β) (hω : IsPathFundamental β ω)
    {z : b.support} (hz : z ∉ Set.range β) (m : ℕ) :
    P.toLinearMap (∑ j ∈ Finset.range m, pathWeight β ω j) (P.coroot (z : ι)) = 0 := by
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun j _ => pairing_pathWeight_of_not_mem hβ hω hz j

/-- Path weights decrease along the path in the simple-root order. -/
theorem pathWeight_sub_mem_positiveCone (ω : M) {j j' : ℕ} (h : j ≤ j') :
    pathWeight β ω j - pathWeight β ω j' ∈ Langlands.RootDatum.Triangular.positiveCone P b := by
  rw [pathWeight_sub_pathWeight ω h]
  refine AddSubmonoid.sum_mem _ fun t _ => ?_
  unfold pathRoot
  split_ifs with ht
  · exact AddSubmonoid.subset_closure ⟨β ⟨t, ht⟩, rfl⟩
  · exact zero_mem _

end Langlands.LinearAlgebra.RootDatumPathWeights

namespace Langlands.GroupScheme.SplitPinning

open Langlands.LinearAlgebra.RootDatumPathWeights

section Charpoly

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G} {n : Type} [Fintype n] [DecidableEq n]
  {ρ : MatrixRepresentation G n} {L : ℕ} {β : Fin L → p.base.support}
  {lam : characterLattice p.torus}

/-- The torus restriction of a characteristic-polynomial coefficient is the corresponding
coefficient of the characteristic polynomial of the universal torus matrix. -/
theorem torusRestriction_charpolyCoeffClassFunction (ρ : MatrixRepresentation G n) (i : ℕ) :
    p.torusRestriction (MatrixRepresentation.charpolyCoeffClassFunction ρ i) =
      (p.torusUniversalMatrix ρ).charpoly.coeff i :=
  MatrixRepresentation.charpolyCoeffCoordinate_evaluate ρ _ i

/-- The universal torus matrix of a highest-weight representation at the fundamental weight of
the end vertex of a path has the path weights as its eigenvalues. -/
theorem charpoly_torusUniversalMatrix (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
    (hlam : IsPathFundamental β lam) :
    (p.torusUniversalMatrix ρ).charpoly =
      ∏ j : Fin (L + 1), (Polynomial.X - Polynomial.C
        (AddMonoidAlgebra.single (pathWeight β lam j) (1 : k))) := by
  classical
  let B := pathWeightBasis hρ hβ hlam
  let R := AddMonoidAlgebra k (characterLattice p.torus)
  let P : Matrix n (Fin (L + 1)) R := ((Pi.basisFun k n).toMatrix B).map (algebraMap k R)
  let Q : Matrix (Fin (L + 1)) n R := (B.toMatrix (Pi.basisFun k n)).map (algebraMap k R)
  let d : Fin (L + 1) → R := fun j => AddMonoidAlgebra.single (pathWeight β lam j) (1 : k)
  have hPQ : P * Q = 1 := by
    simp only [P, Q, ← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP : Q * P = 1 := by
    simp only [P, Q, ← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hMP : p.torusUniversalMatrix ρ * P = P * Matrix.diagonal d := by
    refine Matrix.ext fun r j => ?_
    rw [Matrix.mul_diagonal]
    have h := congrFun (p.torusUniversalMatrix_mulVec_of_mem ρ (pathWeightBasis_mem hρ hβ hlam j)) r
    simp only [Pi.smul_apply, smul_eq_mul] at h
    have hcol : (fun s => P s j) = fun s => algebraMap k R (B j s) := by
      funext s
      simp only [P, Matrix.map_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    change (p.torusUniversalMatrix ρ *ᵥ fun s => P s j) r = P r j * d j
    rw [hcol]
    simp only [P, Matrix.map_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [mul_comm]
    exact h
  have hM : p.torusUniversalMatrix ρ = P * (Matrix.diagonal d * Q) := by
    rw [← Matrix.mul_assoc, ← hMP, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  have hcard : Fintype.card n = Fintype.card (Fin (L + 1)) := by
    rw [Fintype.card_fin]
    exact card_eq_of_isHighestWeight hρ hβ hlam
  have h' := Matrix.charpoly_mul_comm' P (Matrix.diagonal d * Q)
  rw [Matrix.mul_assoc, hQP, Matrix.mul_one, hcard] at h'
  rw [hM, (Polynomial.isRegular_X_pow _).left h', Matrix.charpoly_diagonal]

/-- The signed characteristic-polynomial coefficient of index `L - i` of a path
representation restricts on the torus to the elementary symmetric function of degree `i + 1`
in the path weights. -/
theorem torusRestriction_signed_charpolyCoeff (hρ : p.IsHighestWeight ρ lam)
    (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam) {i : ℕ} (hi : i < L) :
    p.torusRestriction ((-1 : k) ^ (i + 1) •
        MatrixRepresentation.charpolyCoeffClassFunction ρ (L - i)) =
      ∑ t ∈ Finset.powersetCard (i + 1) (Finset.univ : Finset (Fin (L + 1))),
        AddMonoidAlgebra.single (∑ j ∈ t, pathWeight β lam j) (1 : k) := by
  classical
  rw [map_smul, torusRestriction_charpolyCoeffClassFunction,
    charpoly_torusUniversalMatrix hρ hβ hlam]
  have hprod : ∏ j : Fin (L + 1), (Polynomial.X - Polynomial.C
        (AddMonoidAlgebra.single (pathWeight β lam j) (1 : k))) =
      ((Finset.univ.val.map fun j : Fin (L + 1) =>
        AddMonoidAlgebra.single (pathWeight β lam j) (1 : k)).map
          fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hprod, Multiset.prod_X_sub_C_coeff _ (by simp only [Multiset.card_map,
    Finset.card_val, Finset.card_univ, Fintype.card_fin]; omega)]
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  rw [show L + 1 - (L - i) = i + 1 by omega, Finset.esymm_map_val]
  simp only [AddMonoidAlgebra.prod_single, Finset.prod_const_one]
  rw [Algebra.smul_def, ← mul_assoc, map_pow, map_neg, map_one, ← mul_pow, neg_one_mul, neg_neg,
    one_pow, one_mul]

end Charpoly

section Generation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G)

/-- Evaluation of class functions at a rational point. -/
def classEvaluation (g : rationalPoints G) : ClassFunctions.algebra G →ₐ[k] k :=
  (Lie.pointCoordinates G
    (Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv k G.X g)).comp
      (ClassFunctions.inclusion G)

theorem classEvaluation_charpolyCoeffClassFunction {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (g : rationalPoints G) (i : ℕ) :
    classEvaluation g (MatrixRepresentation.charpolyCoeffClassFunction ρ i) =
      (ρ.rationalMatrix g : Matrix n n k).charpoly.coeff i := by
  rw [Langlands.Plancherel.rationalMatrix_eq_affineMatrix]
  exact MatrixRepresentation.charpolyCoeffCoordinate_evaluate ρ _ i

theorem classEvaluation_character {a : p.base.support} (F : p.FundamentalRepresentation a)
    (g : rationalPoints G) :
    classEvaluation g F.character =
      Matrix.trace (F.representation.rationalMatrix g :
        Matrix (Fin F.dimension) (Fin F.dimension) k) := by
  rw [Langlands.Plancherel.rationalMatrix_eq_affineMatrix]
  exact F.character_evaluate _

/-- Equal values of all class functions give equal images in the canonical quotient. -/
theorem rho_eq_of_classEvaluation_eq {g g' : rationalPoints G}
    (h : ∀ f, classEvaluation g f = classEvaluation g' f) :
    g ≫ ClassFunctions.rho G = g' ≫ ClassFunctions.rho G := by
  have hρ := (ClassFunctions.rho_eq_iff G
    (Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv k G.X g)
    (Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv k G.X g')).mpr h
  have he : ∀ x : rationalPoints G,
      (Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv k G.X x :
          Lie.AffinePoints G k) ≫ ClassFunctions.rho G =
        (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom ≫ x ≫
          ClassFunctions.rho G := by
    intro x
    change ((Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom ≫ x ≫ 𝟙 _) ≫
      ClassFunctions.rho G = _
    rw [Category.comp_id, Category.assoc]
  rw [he, he] at hρ
  exact (cancel_epi _).mp hρ

variable {p}

/-- For a simple root on one of the supplied path components or off all of them,
a class function with fundamental top weight at that root whose values at two rational points
agree, provided the path characteristic polynomials and off-path fundamental traces agree. -/
theorem exists_generator [IsAlgClosed k] (hG : IsSimplyConnected G) {J : Type*}
    {L : J → ℕ} {β : ∀ c, Fin (L c) → p.base.support} (hβ : ∀ c, IsPathComponent (β c))
    {g g' : rationalPoints G}
    (hpath : ∀ c (F : p.FundamentalRepresentation (β c ⟨0, (hβ c).pos⟩)),
      Matrix.charpoly (F.representation.rationalMatrix g :
          Matrix (Fin F.dimension) (Fin F.dimension) k) =
        Matrix.charpoly (F.representation.rationalMatrix g' :
          Matrix (Fin F.dimension) (Fin F.dimension) k))
    (hoff : ∀ a : p.base.support, (∀ c i, β c i ≠ a) → ∀ F : p.FundamentalRepresentation a,
      Matrix.trace (F.representation.rationalMatrix g :
          Matrix (Fin F.dimension) (Fin F.dimension) k) =
        Matrix.trace (F.representation.rationalMatrix g' :
          Matrix (Fin F.dimension) (Fin F.dimension) k))
    (a : p.base.support) :
    ∃ (f : ClassFunctions.algebra G) (ν : characterLattice p.torus),
      p.IsFundamentalWeight a ν ∧
      Langlands.RootDatum.Triangular.IsTopWeight p.rootDatum p.base ν (p.torusRestriction f) ∧
      classEvaluation g f = classEvaluation g' f := by
  classical
  by_cases hon : ∃ c i, β c i = a
  · obtain ⟨c, i, rfl⟩ := hon
    obtain ⟨F⟩ := splitFundamentalRepresentationsExist k G p hG (β c ⟨0, (hβ c).pos⟩)
    have hlam := F.isPathFundamental (hβ c)
    have hρ := F.isHighestWeight
    refine ⟨(-1 : k) ^ ((i : ℕ) + 1) •
        MatrixRepresentation.charpolyCoeffClassFunction F.representation (L c - i),
      ∑ j ∈ Finset.range ((i : ℕ) + 1), pathWeight (β c) F.highestWeight j, ?_, ?_, ?_⟩
    · unfold IsFundamentalWeight
      intro z
      by_cases hz : z ∈ Set.range (β c)
      · obtain ⟨l, rfl⟩ := hz
        rw [pairing_sum_pathWeight (hβ c) hlam i.2 l]
        by_cases hl : l = i
        · subst hl
          simp
        · rw [ite_eq_right (fun h => hl (Fin.ext h)),
            ite_eq_right (fun h => hl ((hβ c).injective h))]
      · rw [pairing_sum_pathWeight_of_not_mem (hβ c) hlam hz, ite_eq_right]
        rintro rfl
        exact hz ⟨i, rfl⟩
    · rw [torusRestriction_signed_charpolyCoeff hρ (hβ c) hlam i.2]
      have h := Langlands.RootDatum.Triangular.isTopWeight_sum_powersetCard (k := k)
        (P := p.rootDatum) (b := p.base)
        (fun j : Fin (L c + 1) => pathWeight (β c) F.highestWeight j)
        (fun j j' hjj' => pathWeight_sub_mem_positiveCone _ hjj')
        (fun j j' h => Fin.ext (pathWeight_injOn (hβ c) hlam (by omega) (by omega) h))
        (show (i : ℕ) + 1 ≤ L c + 1 by omega)
      rw [← Fin.sum_univ_eq_sum_range (fun j => pathWeight (β c) F.highestWeight j)]
      simpa only [Fin.val_castLE] using h
    · rw [map_smul, map_smul, classEvaluation_charpolyCoeffClassFunction,
        classEvaluation_charpolyCoeffClassFunction, hpath c F]
  · push Not at hon
    obtain ⟨F⟩ := splitFundamentalRepresentationsExist k G p hG a
    refine ⟨F.character, F.highestWeight, F.isFundamentalWeight,
      ⟨p.torusRestriction_character_coeff_highestWeight F,
        fun _ hν => p.sub_mem_positiveRootMonoid_of_mem_support F hν⟩, ?_⟩
    rw [classEvaluation_character, classEvaluation_character, hoff a hon F]

/-- **Path characteristic polynomials and off-path fundamental traces detect the canonical
class quotient.** Let `G` be simply connected over an algebraically closed field, with a split
pinning, and let `β c` be path components of its Dynkin diagram. Two rational
points have the same image in the canonical quotient as soon as, for each path, the matrices of
every fundamental representation at the end vertex `β c 0` have the same characteristic
polynomial at both points, and, for each simple root off all paths, the matrices of every
fundamental representation at that root have the same trace. -/
theorem rho_eq_of_pathCharpoly_eq_of_trace_eq [IsAlgClosed k] (hG : IsSimplyConnected G)
    {J : Type*} {L : J → ℕ} {β : ∀ c, Fin (L c) → p.base.support}
    (hβ : ∀ c, IsPathComponent (β c)) {g g' : rationalPoints G}
    (hpath : ∀ c (F : p.FundamentalRepresentation (β c ⟨0, (hβ c).pos⟩)),
      Matrix.charpoly (F.representation.rationalMatrix g :
          Matrix (Fin F.dimension) (Fin F.dimension) k) =
        Matrix.charpoly (F.representation.rationalMatrix g' :
          Matrix (Fin F.dimension) (Fin F.dimension) k))
    (hoff : ∀ a : p.base.support, (∀ c i, β c i ≠ a) → ∀ F : p.FundamentalRepresentation a,
      Matrix.trace (F.representation.rationalMatrix g :
          Matrix (Fin F.dimension) (Fin F.dimension) k) =
        Matrix.trace (F.representation.rationalMatrix g' :
          Matrix (Fin F.dimension) (Fin F.dimension) k)) :
    g ≫ ClassFunctions.rho G = g' ≫ ClassFunctions.rho G := by
  classical
  let _ := Fintype.ofFinite p.rootIndex
  choose f ν hν htop hval using exists_generator hG hβ hpath hoff
  let e : Fin (Fintype.card p.base.support) ≃ p.base.support :=
    (Fintype.equivFin p.base.support).symm
  have hlam1 : ∀ j, p.rootDatum.toLinearMap (ν (e j)) (p.rootDatum.coroot (e j)) = 1 := by
    intro j
    simpa using hν (e j) (e j)
  have hlam0 : ∀ j (a : p.base.support), a ≠ e j →
      p.rootDatum.toLinearMap (ν (e j)) (p.rootDatum.coroot a) = 0 := by
    intro j a ha
    simpa [ha] using hν (e j) a
  have hcomp : p.torusRestriction.comp (MvPolynomial.aeval fun j => f (e j)) =
      MvPolynomial.aeval fun j => p.torusRestriction (f (e j)) :=
    MvPolynomial.comp_aeval _ _
  have hinv : ∀ q, Langlands.RootDatum.Triangular.IsReflectionInvariant p.rootDatum
      (MvPolynomial.aeval (R := k) (fun j => p.torusRestriction (f (e j))) q) := by
    intro q i x
    rw [← hcomp, AlgHom.comp_apply]
    exact p.torusRestriction_coeff_reflection _ i x
  apply rho_eq_of_classEvaluation_eq
  intro h
  obtain ⟨q, hq⟩ := Langlands.RootDatum.Triangular.mem_range_aeval hlam1 hlam0
    (fun j => htop (e j)) hinv
    (fun _ hx => p.eq_zero_of_forall_simple_coroot_of_isSemisimple hG.isSemisimple hx)
    (p.torusRestriction h) (fun i x => p.torusRestriction_coeff_reflection h i x)
  have hh : h = MvPolynomial.aeval (fun j => f (e j)) q := by
    apply p.torusRestriction_injective
    rw [← AlgHom.comp_apply, hcomp]
    exact hq.symm
  rw [hh, ← AlgHom.comp_apply, ← AlgHom.comp_apply, MvPolynomial.comp_aeval,
    MvPolynomial.comp_aeval]
  simp only [hval]

/-- The detection criterion for the paths of supplied even-path data: path characteristic
polynomials of the fundamental representations at the end vertices `C.path c 0` and traces of
the fundamental representations at the simple roots off all paths detect the canonical
quotient. -/
theorem EvenChainData.rho_eq_of_charpoly_eq_of_trace_eq [IsAlgClosed k]
    (hG : IsSimplyConnected G) {J : Type u} (C : p.EvenChainData J) {g g' : rationalPoints G}
    (hpath : ∀ c (F : p.FundamentalRepresentation (C.path c ⟨0, (C.isPathComponent c).pos⟩)),
      Matrix.charpoly (F.representation.rationalMatrix g :
          Matrix (Fin F.dimension) (Fin F.dimension) k) =
        Matrix.charpoly (F.representation.rationalMatrix g' :
          Matrix (Fin F.dimension) (Fin F.dimension) k))
    (hoff : ∀ a : p.base.support, (∀ c i, C.path c i ≠ a) →
      ∀ F : p.FundamentalRepresentation a,
        Matrix.trace (F.representation.rationalMatrix g :
            Matrix (Fin F.dimension) (Fin F.dimension) k) =
          Matrix.trace (F.representation.rationalMatrix g' :
            Matrix (Fin F.dimension) (Fin F.dimension) k)) :
    g ≫ ClassFunctions.rho G = g' ≫ ClassFunctions.rho G :=
  rho_eq_of_pathCharpoly_eq_of_trace_eq hG C.isPathComponent hpath hoff

end Generation

end Langlands.GroupScheme.SplitPinning
