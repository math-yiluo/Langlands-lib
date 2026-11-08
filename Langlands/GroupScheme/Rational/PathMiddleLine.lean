import Langlands.GroupScheme.Rational.SimpleRootHighestCoefficientNonvanishing
import Langlands.GroupScheme.Rational.PathLineStabilizers
import Langlands.GroupScheme.Rational.SteinbergModifiedRootProduct

/-! # The modified product `N''` fixes the middle path line -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation MatrixRepresentation.AdditiveDividedPowers
open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}
  {d : Type} [Fintype d] [DecidableEq d] (ρ : MatrixRepresentation G d)
  (D : p.SteinbergModifiedData) {q : ℕ} (e : Fin q ≃ D.Complement)
  (x : p.NormalizedSimpleRootParametrizations) (n : p.SimpleReflectionRepresentatives)

/-- The actual matrix of the modified product `N''` at an affine point is the ordered product of
the factor matrices. -/
theorem affineMatrix_steinbergModifiedProduct (A : CommAlgCat.{u} k) (c : Fin (q + 1) → A) :
    (ρ.affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := q + 1) A c ≫
          steinbergModifiedProduct D e x n) : Matrix d d A) =
      ((ρ.restrict D.xAlpha.hom).affineMatrix A
          (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => c 0)) :
            Matrix d d A) *
        (ρ.rationalMatrix D.nAlpha.point : Matrix d d k).map (algebraMap k A) *
      (List.ofFn fun j : Fin q =>
        ((ρ.restrict (x (e j).1).hom).affineMatrix A
            (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
              (fun _ => c j.succ)) : Matrix d d A) *
          ((ρ.rationalMatrix (n (e j).1).point : Matrix d d k).map (algebraMap k A))).prod := by
  let F := (Units.coeHom (Matrix d d A)).comp (ρ.affineMatrix A)
  change F _ = _
  rw [comp_steinbergModifiedProduct, map_mul, map_mul, map_list_prod, List.map_ofFn]
  have hc := VectorGroup.coordinates_affinePoint (R := CommRingCat.of k) A c
  have hconst : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      F (toUnit ((algSpec (CommRingCat.of k)).obj (op A)) ≫ g) =
        (ρ.rationalMatrix g : Matrix d d k).map (algebraMap k A) := by
    intro g
    have hn : toUnit ((algSpec (CommRingCat.of k)).obj (op A)) ≫ g =
        G.constantPoint g ((algSpec (CommRingCat.of k)).obj (op A)) := rfl
    dsimp only [F, MonoidHom.comp_apply, Units.coeHom_apply]
    rw [hn, ρ.affineMatrix_constantPoint]
    rfl
  congr 1
  · congr 1
    · dsimp only [F, MonoidHom.comp_apply, Units.coeHom_apply]
      rw [congrFun hc 0, RootParametrization.point, affineMatrix_restrict,
        ← VectorGroup.affinePoint_eq_scalarPoint]
    · exact hconst _
  · apply congrArg List.prod
    apply congrArg List.ofFn
    funext j
    dsimp only [Function.comp_def]
    rw [map_mul, hconst]
    congr 1
    dsimp only [F, MonoidHom.comp_apply, Units.coeHom_apply]
    rw [congrFun hc j.succ, NormalizedRootParametrization.point, affineMatrix_restrict,
      ← VectorGroup.affinePoint_eq_scalarPoint]

/-- The polynomial matrix of the modified product `N''`: the ordered product of the universal root
matrices, in the coordinate `X 0` for the merged root and `X (j + 1)` for the `j`-th complementary
root, and the constant representative matrices. -/
def steinbergModifiedPolynomialMatrix : Matrix d d (MvPolynomial (Fin (q + 1)) k) :=
  (univariateMatrix (ρ.restrict D.xAlpha.hom)).map (Polynomial.aeval (MvPolynomial.X 0)) *
      (ρ.rationalMatrix D.nAlpha.point : Matrix d d k).map MvPolynomial.C *
    (List.ofFn fun j : Fin q =>
      (univariateMatrix (ρ.restrict (x (e j).1).hom)).map
          (Polynomial.aeval (MvPolynomial.X j.succ)) *
        (ρ.rationalMatrix (n (e j).1).point : Matrix d d k).map MvPolynomial.C).prod

/-- Polynomial evaluation recovers the actual matrix of `N''` over every algebra. -/
theorem steinbergModifiedPolynomialMatrix_aeval (A : CommAlgCat.{u} k) (c : Fin (q + 1) → A) :
    (steinbergModifiedPolynomialMatrix ρ D e x n).map (MvPolynomial.aeval c) =
      (ρ.affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := q + 1) A c ≫
          steinbergModifiedProduct D e x n) : Matrix d d A) := by
  have hroot : ∀ (σ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) d)
      (i : Fin (q + 1)),
      ((univariateMatrix σ).map
          (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin (q + 1)) k))).map
          (MvPolynomial.aeval c) =
        (σ.affineMatrix A (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A
          (fun _ => c i)) : Matrix d d A) := by
    intro σ i
    rw [← univariateMatrix_aeval]
    ext a b
    change (MvPolynomial.aeval c)
      (Polynomial.aeval (MvPolynomial.X i) (univariateMatrix σ a b)) =
      Polynomial.aeval (c i) (univariateMatrix σ a b)
    rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
  have hconst : ∀ M : Matrix d d k,
      (M.map MvPolynomial.C).map (MvPolynomial.aeval c) = M.map (algebraMap k A) := by
    intro M
    ext a b
    exact MvPolynomial.aeval_C c _
  rw [affineMatrix_steinbergModifiedProduct, steinbergModifiedPolynomialMatrix]
  change (MvPolynomial.aeval c).mapMatrix (_ * _ * (List.ofFn _).prod) = _
  rw [map_mul, map_mul, map_list_prod, List.map_ofFn]
  congr 1
  · congr 1
    · exact hroot _ 0
    · exact hconst _
  · apply congrArg List.prod
    apply congrArg List.ofFn
    funext j
    dsimp only [Function.comp_def]
    rw [map_mul]
    congr 1
    · exact hroot _ j.succ
    · exact hconst _

/-- The polynomial matrix of `N''` is the actual matrix at the universal point. -/
theorem steinbergModifiedPolynomialMatrix_eq_affineMatrix :
    steinbergModifiedPolynomialMatrix ρ D e x n =
      (ρ.affineMatrix (VectorGroup.coordinateAlgebra (CommRingCat.of k) (q + 1))
        (steinbergModifiedProduct D e x n) :
          Matrix d d (MvPolynomial (Fin (q + 1)) k)) := by
  have h := steinbergModifiedPolynomialMatrix_aeval ρ D e x n
    (VectorGroup.coordinateAlgebra (CommRingCat.of k) (q + 1)) MvPolynomial.X
  rw [VectorGroup.affinePoint_X (R := CommRingCat.of k) (r := q + 1),
    Category.id_comp] at h
  simpa only [MvPolynomial.aeval_X_left, AlgHom.coe_id, Matrix.map_id] using h

omit [IsAffineHom G.X.hom] in
/-- An additive matrix all of whose positive divided powers kill `v` fixes the scalar extension
of `v` at every affine coordinate. -/
theorem affineMatrix_mulVec_eq_self_of_dividedPower
    (σ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) d) {v : d → k}
    (hv : ∀ m, 1 ≤ m → dividedPower σ m v = 0) (A : CommAlgCat.{u} k) (c : A) :
    (σ.affineMatrix A (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => c)) :
        Matrix d d A) *ᵥ (fun i => algebraMap k A (v i)) = fun i => algebraMap k A (v i) :=
  MatrixRepresentation.AdditiveDividedPowers.affineMatrix_mulVec_eq_self_of_dividedPower_eq_zero
    σ hv A c

/-- A determinant `det (1 - M)` vanishes when `M` fixes the scalar extension of a nonzero vector
over a field. -/
theorem det_one_sub_eq_zero_of_mulVec_eq_self {A : Type*} [CommRing A] [Algebra k A]
    (M : Matrix d d A) {v : d → k} (hv0 : v ≠ 0)
    (hv : M *ᵥ (fun i => algebraMap k A (v i)) = fun i => algebraMap k A (v i)) :
    (1 - M).det = 0 := by
  have h1 : (1 - M) *ᵥ (fun i => algebraMap k A (v i)) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_self]
  have h2 : (1 - M).det • (fun i => algebraMap k A (v i)) = 0 := by
    have h3 : ((1 - M).adjugate * (1 - M)) *ᵥ (fun i => algebraMap k A (v i)) = 0 := by
      rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
    rwa [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h3
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have h3 := congrFun h2 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h3
  have hu : IsUnit (algebraMap k A (v i)) := (IsUnit.mk0 _ hi).map (algebraMap k A)
  exact (hu.mul_left_eq_zero).mp h3

variable {ρ} {L : ℕ} {β : Fin L → p.base.support} {lam : characterLattice p.torus}

/-- **The middle line of `N''`.** Let `v` be a nonzero vector of the line of the path weight
`ε_j`. Suppose the merged root and every complementary simple root never shift `ε_j` to a path
weight, and the merged and complementary representatives fix `v`. Then the actual matrix of the
modified product `N''` at every affine point fixes `v`, and `det (1 - ρ(N''))` vanishes. -/
theorem det_one_sub_affineMatrix_steinbergModifiedProduct_eq_zero
    (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam)
    {j : ℕ} {v : d → k} (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam j))
    (hv0 : v ≠ 0)
    (hα : ∀ m, 1 ≤ m → ∀ l ≤ L,
      pathWeight β lam j + m • p.rootDatum.root D.alpha ≠ pathWeight β lam l)
    (hαn : (ρ.rationalMatrix D.nAlpha.point : Matrix d d k) *ᵥ v = v)
    (hc : ∀ (i : Fin q) (m : ℕ), 1 ≤ m → ∀ l ≤ L,
      pathWeight β lam j + m • p.rootDatum.root ((e i).1 : p.rootIndex) ≠ pathWeight β lam l)
    (hcn : ∀ i : Fin q, (ρ.rationalMatrix (n (e i).1).point : Matrix d d k) *ᵥ v = v)
    (A : CommAlgCat.{u} k) (c : Fin (q + 1) → A) :
    (1 - (ρ.affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := q + 1) A c ≫
          steinbergModifiedProduct D e x n) : Matrix d d A)).det = 0 := by
  apply det_one_sub_eq_zero_of_mulVec_eq_self _ hv0
  have hrat : ∀ g : rationalPoints G, (ρ.rationalMatrix g : Matrix d d k) *ᵥ v = v →
      ((ρ.rationalMatrix g : Matrix d d k).map (algebraMap k A)) *ᵥ
        (fun i => algebraMap k A (v i)) = fun i => algebraMap k A (v i) := by
    intro g hg
    funext i
    have := congrArg (algebraMap k A) (congrFun hg i)
    rw [← this, RingHom.map_mulVec]
    rfl
  rw [affineMatrix_steinbergModifiedProduct, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hprod : ∀ l : List (Matrix d d A),
      (∀ M ∈ l, M *ᵥ (fun i => algebraMap k A (v i)) = fun i => algebraMap k A (v i)) →
        l.prod *ᵥ (fun i => algebraMap k A (v i)) = fun i => algebraMap k A (v i) := by
    intro l hl
    induction l with
    | nil => simp
    | cons M l ih =>
      rw [List.prod_cons, ← Matrix.mulVec_mulVec, ih (fun N hN => hl N (List.mem_cons_of_mem _ hN)),
        hl M List.mem_cons_self]
  rw [hprod]
  · rw [hrat _ hαn]
    exact affineMatrix_mulVec_eq_self_of_dividedPower _
      (fun m hm => dividedPower_eq_zero_of_shift_ne hρ hβ hlam D.xAlpha.torus_equivariant
        (hα m hm) hv) A (c 0)
  · intro M hM
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hM
    rw [← Matrix.mulVec_mulVec, hrat _ (hcn i)]
    exact affineMatrix_mulVec_eq_self_of_dividedPower _
      (fun m hm => dividedPower_eq_zero_of_shift_ne hρ hβ hlam
        (x (e i).1).torus_equivariant (hc i m hm) hv) A (c i.succ)

/-- **`N''` lies in `f = 0`.** Let the two middle simple roots of the modified data be the
consecutive path vertices `β i` and `β (i + 1)`, use the canonical simple-reflection
representatives of the supplied normalized root maps, and let the merged representative lie in the
subgroup generated by the root subgroups of `± α`. Then for every nonzero vector `v` of the line of
`ε_{i+1}`, the actual matrix of `N''` at every affine point fixes `v`, and `det (1 - ρ(N''))`
vanishes. -/
theorem det_one_sub_affineMatrix_steinbergModifiedProduct_eq_zero_of_path
    (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam)
    {i : ℕ} (hi : i + 2 ≤ L) (ha : D.a = β ⟨i, by omega⟩) (hb : D.b = β ⟨i + 1, by omega⟩)
    (hnα : D.nAlpha.point ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root D.alpha)).carrier
          (Over.mk (𝟙 _)) ⊔
        (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root D.alpha)).carrier
          (Over.mk (𝟙 _)))
    {v : d → k} (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam (i + 1)))
    (hv0 : v ≠ 0) (A : CommAlgCat.{u} k) (c : Fin (q + 1) → A) :
    (1 - (ρ.affineMatrix A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := q + 1) A c ≫
          steinbergModifiedProduct D e x (canonicalSimpleReflectionRepresentatives x)) :
            Matrix d d A)).det = 0 := by
  have hroot : p.rootDatum.root D.alpha = pathWeight β lam i - pathWeight β lam (i + 2) := by
    rw [D.root_eq, ha, hb, root_path_eq_sub, root_path_eq_sub]
    dsimp only
    abel
  refine det_one_sub_affineMatrix_steinbergModifiedProduct_eq_zero D e x _ hρ hβ hlam hv hv0
    (fun m hm l hl h => ?_) ?_ (fun t m hm l hl h => ?_) (fun t => ?_) A c
  · rw [hroot] at h
    have := (pathWeight_add_nsmul_sub_eq_iff hβ lam (by omega : i < i + 2) hi (by omega) hl
      hm).mp h
    omega
  · exact rootSup_pathRoot_fixes hρ hβ hlam D.alpha (by omega : i < i + 2) hi hroot
      (by omega) (by omega) (by omega) hv hnα
  · have hz := (e t).2
    by_cases hr : (e t).1 ∈ Set.range β
    · obtain ⟨s, hs⟩ := hr
      rw [← hs, root_path_eq_sub] at h
      have hs2 := s.2
      have := (pathWeight_add_nsmul_sub_eq_iff hβ lam (by omega : (s : ℕ) < s + 1) (by omega)
        (by omega) hl hm).mp h
      apply hz.1
      rw [← hs, ha]
      congr 1
      ext
      simp only
      omega
    · exact pathWeight_add_nsmul_root_ne hβ hlam hr hm (i + 1) l h
  · have hz := (e t).2
    change (ρ.rationalMatrix (x (e t).1).reflectionRepresentative.point : Matrix d d k) *ᵥ v = v
    by_cases hr : (e t).1 ∈ Set.range β
    · obtain ⟨s, hs⟩ := hr
      have hs2 := s.2
      have hsa : (s : ℕ) ≠ i := fun h' => hz.1 (by rw [← hs, ha]; congr 1; ext; exact h')
      have hsb : (s : ℕ) ≠ i + 1 := fun h' => hz.2 (by rw [← hs, hb]; congr 1; ext; exact h')
      have key := canonicalReflection_path_fixes hρ hβ hlam s (x (β s)) (j := i + 1) (by omega)
        (by omega) (by omega) hv
      rw [hs] at key
      exact key
    · exact canonicalReflection_offPath_fixes hρ hβ hlam hr (x (e t).1) hv

/-- The polynomial form of `N'' ⊆ {f = 0}`: under the hypotheses of
`det_one_sub_affineMatrix_steinbergModifiedProduct_eq_zero_of_path`, the polynomial
`det (1 - M)` of the polynomial matrix `M` of `N''` is zero. -/
theorem det_one_sub_steinbergModifiedPolynomialMatrix_eq_zero_of_path
    (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam)
    {i : ℕ} (hi : i + 2 ≤ L) (ha : D.a = β ⟨i, by omega⟩) (hb : D.b = β ⟨i + 1, by omega⟩)
    (hnα : D.nAlpha.point ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root D.alpha)).carrier
          (Over.mk (𝟙 _)) ⊔
        (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root D.alpha)).carrier
          (Over.mk (𝟙 _)))
    {v : d → k} (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam (i + 1)))
    (hv0 : v ≠ 0) :
    (1 - steinbergModifiedPolynomialMatrix ρ D e x
      (canonicalSimpleReflectionRepresentatives x)).det = 0 := by
  have h := det_one_sub_affineMatrix_steinbergModifiedProduct_eq_zero_of_path D e x hρ hβ hlam
    hi ha hb hnα hv hv0 (VectorGroup.coordinateAlgebra (CommRingCat.of k) (q + 1))
    MvPolynomial.X
  rwa [VectorGroup.affinePoint_X (R := CommRingCat.of k) (r := q + 1), Category.id_comp,
    ← steinbergModifiedPolynomialMatrix_eq_affineMatrix] at h

end Langlands.GroupScheme.SplitPinning
