import Langlands.GroupScheme.Rational.PathLineStabilizers

/-! # Canonical reflection representatives on consecutive path lines -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace MatrixRepresentation.AdditiveDividedPowers

variable {k : Type u} [Field k] {d : Type} [Fintype d] [DecidableEq d]
  (σ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) d)

private theorem rationalMatrix_scalarPoint_aux (h : ∀ m, 2 ≤ m → dividedPower σ m = 0)
    (c : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) :
    (σ.rationalMatrix (VectorGroup.scalarPoint (CommRingCat.of k) _ c) : Matrix d d k) =
      1 + ((Scheme.ΓSpecIso (CommRingCat.of (CommAlgCat.of k k))).hom
        (((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k))).hom.appTop c)) •
          coefficientMatrix σ 1 := by
  let A : CommAlgCat.{u} k := CommAlgCat.of k k
  let T := (algSpec (CommRingCat.of k)).obj (op A)
  let c' : A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom (T.hom.appTop c)
  have hpt : (VectorGroup.groupScheme (CommRingCat.of k) 1).constantPoint
      (VectorGroup.scalarPoint (CommRingCat.of k) _ c) T =
      VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => c') := by
    rw [VectorGroup.affinePoint_eq_scalarPoint]
    unfold GroupScheme.constantPoint
    rw [VectorGroup.scalarPoint_comp]
    congr 1
    exact (CategoryTheory.Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of A)) _).symm
  have hconst := σ.affineMatrix_constantPoint (VectorGroup.scalarPoint (CommRingCat.of k) _ c) A
  rw [hpt] at hconst
  have hlin := affineMatrix_eq_one_add σ h A c'
  rw [hconst] at hlin
  have hid : ∀ y : k, algebraMap k A y = y := fun y => rfl
  ext a b
  have hab := congrFun (congrFun hlin a) b
  simp only [Matrix.GeneralLinearGroup.map] at hab
  simp only [Units.coe_map, hid, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul] at hab
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact hab

/-- With vanishing higher divided powers, every rational point of the additive group has matrix
`1 + c A₁` for some scalar `c`. -/
theorem exists_rationalMatrix_eq_one_add (h : ∀ m, 2 ≤ m → dividedPower σ m = 0)
    (g : rationalPoints (VectorGroup.groupScheme (CommRingCat.of k) 1)) :
    ∃ c : k, (σ.rationalMatrix g : Matrix d d k) = 1 + c • coefficientMatrix σ 1 := by
  rw [← VectorGroup.scalarPoint_coordinate _ g]
  exact ⟨_, rationalMatrix_scalarPoint_aux σ h _⟩

/-- With vanishing higher divided powers, the rational point with coordinate one has matrix
`1 + A₁`. -/
theorem rationalMatrix_scalarPoint_one (h : ∀ m, 2 ≤ m → dividedPower σ m = 0) :
    (σ.rationalMatrix (VectorGroup.scalarPoint (CommRingCat.of k) _ 1) : Matrix d d k) =
      1 + coefficientMatrix σ 1 := by
  rw [rationalMatrix_scalarPoint_aux σ h, map_one, map_one, one_smul]

/-- The action of `1 + c A₁` on a vector. -/
theorem one_add_smul_mulVec (c : k) (v : d → k) :
    (1 + c • coefficientMatrix σ 1) *ᵥ v = v + c • dividedPower σ 1 v := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dividedPower_eq_toLin,
    Matrix.toLin'_apply]

end MatrixRepresentation.AdditiveDividedPowers

namespace SplitPinning

open MatrixRepresentation MatrixRepresentation.AdditiveDividedPowers
open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {d : Type} [Fintype d] [DecidableEq d]

omit [IsAffineHom G.X.hom] in
/-- A rational point of a subgroup represented by an additive map with vanishing higher divided
powers has matrix `1 + c A₁`. -/
theorem exists_rationalMatrix_eq_one_add_of_isRepresentedBy (ρ : MatrixRepresentation G d)
    {F : SubgroupFunctor G} {y : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G}
    (hy : F.IsRepresentedBy y) (h : ∀ m, 2 ≤ m → dividedPower (ρ.restrict y) m = 0)
    {g : rationalPoints G} (hg : g ∈ F.carrier (Over.mk (𝟙 _))) :
    ∃ c : k, (ρ.rationalMatrix g : Matrix d d k) =
      1 + c • coefficientMatrix (ρ.restrict y) 1 := by
  rw [← hy.2, SubgroupFunctor.mem_range] at hg
  obtain ⟨w, rfl⟩ := hg
  rw [← rationalMatrix_restrict]
  exact exists_rationalMatrix_eq_one_add _ h w

variable {p : SplitPinning G}

/-- The normalized root point at coordinate one has matrix `1 + A₁`. -/
theorem NormalizedRootParametrization.rationalMatrix_unitPoint {a : p.base.support}
    (x : p.NormalizedRootParametrization a) (ρ : MatrixRepresentation G d)
    (h : ∀ m, 2 ≤ m → dividedPower (ρ.restrict x.hom) m = 0) :
    (ρ.rationalMatrix x.unitPoint : Matrix d d k) =
      1 + coefficientMatrix (ρ.restrict x.hom) 1 := by
  rw [x.unitPoint_eq, NormalizedRootParametrization.point, ← rationalMatrix_restrict]
  exact rationalMatrix_scalarPoint_one _ h

variable {ρ : MatrixRepresentation G d} {L : ℕ} {β : Fin L → p.base.support}
  {lam : characterLattice p.torus}

private theorem disjoint_succ (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam) {i : ℕ}
    (hi : i < L) :
    Disjoint (p.representationWeightSpace ρ (pathWeight β lam i))
      (p.representationWeightSpace ρ (pathWeight β lam (i + 1))) := by
  apply (iSupIndep_representationWeightSpace ρ).pairwiseDisjoint
  intro h
  have := pathWeight_injOn hβ hlam (by omega) (by omega) h
  omega

private theorem eq_zero_of_mem_both (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam)
    {i : ℕ} (hi : i < L) {z : d → k}
    (h1 : z ∈ p.representationWeightSpace ρ (pathWeight β lam i))
    (h2 : z ∈ p.representationWeightSpace ρ (pathWeight β lam (i + 1))) : z = 0 :=
  Submodule.disjoint_def.mp (disjoint_succ hβ hlam hi) z h1 h2

private theorem reflection_pathWeight_succ (hβ : IsPathComponent β)
    (hlam : IsPathFundamental β lam) {i : ℕ} (hi : i < L) :
    p.rootDatum.reflection (β ⟨i, hi⟩ : p.rootIndex) (pathWeight β lam (i + 1)) =
      pathWeight β lam i := by
  rw [← reflection_pathWeight_self hβ hlam hi, RootPairing.reflection_same]

section Vertex

variable (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
  (hlam : IsPathFundamental β lam) {i : ℕ} (hi : i < L)
  (x : p.NormalizedRootParametrization (β ⟨i, hi⟩))

include hρ hβ hlam in
/-- The canonical representative of the path vertex `β i` maps line `i + 1` into line `i` by the
first divided power of the normalized root map. -/
theorem canonicalReflection_mulVec_of_mem_succ {w : d → k}
    (hw : w ∈ p.representationWeightSpace ρ (pathWeight β lam (i + 1))) :
    (ρ.rationalMatrix x.reflectionRepresentative.point : Matrix d d k) *ᵥ w =
      dividedPower (ρ.restrict x.hom) 1 w := by
  obtain ⟨X⟩ := p.nonempty_linkedRootParametrization (β ⟨i, hi⟩ : p.rootIndex)
  have hxB : VectorGroup.IsTorusEquivariant p.inclusion x.hom
      (pathWeight β lam i - pathWeight β lam (i + 1)) := by
    have h := x.torus_equivariant
    rw [root_path_eq_sub] at h
    exact h
  have hyC : VectorGroup.IsTorusEquivariant p.inclusion X.negative
      (pathWeight β lam (i + 1) - pathWeight β lam i) := by
    have h := X.negative_equivariant
    have hr : -p.rootDatum.root (β ⟨i, hi⟩ : p.rootIndex) =
        pathWeight β lam (i + 1) - pathWeight β lam i := by
      rw [root_path_eq_sub, neg_sub]
    rw [hr] at h
    exact h
  have hB2 := fun m hm => pathRootMap_dividedPower_eq_zero hρ hβ hlam
    (by omega : i < i + 1) (by omega) hxB (m := m) hm
  have hC2 := fun m hm => negPathRootMap_dividedPower_eq_zero hρ hβ hlam
    (by omega : i < i + 1) (by omega) hyC (m := m) hm
  obtain ⟨c1, hc1⟩ := exists_rationalMatrix_eq_one_add_of_isRepresentedBy ρ X.negative_represents
    hC2 x.oppositeFactorPair_spec.1
  obtain ⟨c2, hc2⟩ := exists_rationalMatrix_eq_one_add_of_isRepresentedBy ρ X.negative_represents
    hC2 x.oppositeFactorPair_spec.2.1
  have hx1 := x.rationalMatrix_unitPoint ρ hB2
  have hCw : dividedPower (ρ.restrict X.negative) 1 w = 0 :=
    negPathRootMap_dividedPower_one_eq_zero hρ hβ hlam (by omega : i < i + 1) (by omega) hyC
      (by omega) (by omega) hw
  have hBw := pathRootMap_dividedPower_one_mem hβ (by omega : i < i + 1) (by omega) hxB hw
  have hCBw := negPathRootMap_dividedPower_one_mem hβ (by omega : i < i + 1) (by omega) hyC hBw
  have e2 : (1 + c2 • coefficientMatrix (ρ.restrict X.negative) 1) *ᵥ w = w := by
    rw [one_add_smul_mulVec, hCw, smul_zero, add_zero]
  have e1 : (1 + coefficientMatrix (ρ.restrict x.hom) 1) *ᵥ w =
      w + dividedPower (ρ.restrict x.hom) 1 w := by
    simpa using one_add_smul_mulVec (ρ.restrict x.hom) 1 w
  have e0 : (1 + c1 • coefficientMatrix (ρ.restrict X.negative) 1) *ᵥ
      (w + dividedPower (ρ.restrict x.hom) 1 w) =
      (w + c1 • dividedPower (ρ.restrict X.negative) 1 (dividedPower (ρ.restrict x.hom) 1 w)) +
        dividedPower (ρ.restrict x.hom) 1 w := by
    rw [one_add_smul_mulVec, map_add, hCw, zero_add]
    abel
  have hn : (ρ.rationalMatrix x.reflectionRepresentative.point : Matrix d d k) *ᵥ w =
      (w + c1 • dividedPower (ρ.restrict X.negative) 1 (dividedPower (ρ.restrict x.hom) 1 w)) +
        dividedPower (ρ.restrict x.hom) 1 w := by
    rw [NormalizedRootParametrization.reflectionRepresentative_point, map_mul, map_mul,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hc1, hx1, hc2,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, e1, e0]
  have hmem := SimpleReflectionRepresentative.rationalMatrix_mem_representationWeightSpace
    x.reflectionRepresentative ρ (pathWeight β lam (i + 1)) hw
  rw [reflection_pathWeight_succ hβ hlam hi] at hmem
  have hz : w + c1 • dividedPower (ρ.restrict X.negative) 1 (dividedPower (ρ.restrict x.hom) 1 w)
      = 0 := by
    apply eq_zero_of_mem_both hβ hlam hi
    · have : w + c1 • dividedPower (ρ.restrict X.negative) 1
          (dividedPower (ρ.restrict x.hom) 1 w) =
          (ρ.rationalMatrix x.reflectionRepresentative.point : Matrix d d k) *ᵥ w -
            dividedPower (ρ.restrict x.hom) 1 w := by
        rw [hn]
        abel
      rw [this]
      exact Submodule.sub_mem _ hmem hBw
    · exact Submodule.add_mem _ hw (Submodule.smul_mem _ _ hCBw)
  rw [hn, hz, zero_add]

include hρ hβ hlam in
/-- The first divided power of the normalized root map of `β i` is injective on line `i + 1`. -/
theorem dividedPower_one_injective_succ {w : d → k}
    (hw : w ∈ p.representationWeightSpace ρ (pathWeight β lam (i + 1)))
    (h0 : dividedPower (ρ.restrict x.hom) 1 w = 0) : w = 0 := by
  have h := canonicalReflection_mulVec_of_mem_succ hρ hβ hlam hi x hw
  rw [h0] at h
  set u := ρ.rationalMatrix x.reflectionRepresentative.point
  calc w = ((u⁻¹ : GL d k) : Matrix d d k) *ᵥ ((u : Matrix d d k) *ᵥ w) := by
        rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    _ = 0 := by rw [h, Matrix.mulVec_zero]

include hρ hβ hlam in
/-- The canonical representative of the path vertex `β i` maps line `i` into line `i + 1`, and
the first divided power of the normalized root map sends the image back to the negative of the
original vector. -/
theorem canonicalReflection_mulVec_of_mem {v : d → k}
    (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam i)) :
    (ρ.rationalMatrix x.reflectionRepresentative.point : Matrix d d k) *ᵥ v ∈
        p.representationWeightSpace ρ (pathWeight β lam (i + 1)) ∧
      dividedPower (ρ.restrict x.hom) 1
        ((ρ.rationalMatrix x.reflectionRepresentative.point : Matrix d d k) *ᵥ v) = -v := by
  obtain ⟨X⟩ := p.nonempty_linkedRootParametrization (β ⟨i, hi⟩ : p.rootIndex)
  have hxB : VectorGroup.IsTorusEquivariant p.inclusion x.hom
      (pathWeight β lam i - pathWeight β lam (i + 1)) := by
    have h := x.torus_equivariant
    rw [root_path_eq_sub] at h
    exact h
  have hyC : VectorGroup.IsTorusEquivariant p.inclusion X.negative
      (pathWeight β lam (i + 1) - pathWeight β lam i) := by
    have h := X.negative_equivariant
    have hr : -p.rootDatum.root (β ⟨i, hi⟩ : p.rootIndex) =
        pathWeight β lam (i + 1) - pathWeight β lam i := by
      rw [root_path_eq_sub, neg_sub]
    rw [hr] at h
    exact h
  have hB2 := fun m hm => pathRootMap_dividedPower_eq_zero hρ hβ hlam
    (by omega : i < i + 1) (by omega) hxB (m := m) hm
  have hC2 := fun m hm => negPathRootMap_dividedPower_eq_zero hρ hβ hlam
    (by omega : i < i + 1) (by omega) hyC (m := m) hm
  obtain ⟨c1, hc1⟩ := exists_rationalMatrix_eq_one_add_of_isRepresentedBy ρ X.negative_represents
    hC2 x.oppositeFactorPair_spec.1
  obtain ⟨c2, hc2⟩ := exists_rationalMatrix_eq_one_add_of_isRepresentedBy ρ X.negative_represents
    hC2 x.oppositeFactorPair_spec.2.1
  have hx1 := x.rationalMatrix_unitPoint ρ hB2
  set Bm := dividedPower (ρ.restrict x.hom) 1
  set Cm := dividedPower (ρ.restrict X.negative) 1
  have hBv : Bm v = 0 :=
    pathRootMap_dividedPower_one_eq_zero hρ hβ hlam (by omega : i < i + 1) (by omega) hxB
      (by omega) (by omega) hv
  have hCv := negPathRootMap_dividedPower_one_mem hβ (by omega : i < i + 1) (by omega) hyC hv
  have hCCv : Cm (Cm v) = 0 :=
    negPathRootMap_dividedPower_one_eq_zero hρ hβ hlam (by omega : i < i + 1) (by omega) hyC
      (by omega) (by omega) hCv
  have hBCv := pathRootMap_dividedPower_one_mem hβ (by omega : i < i + 1) (by omega) hxB hCv
  have hCBCv := negPathRootMap_dividedPower_one_mem hβ (by omega : i < i + 1) (by omega) hyC hBCv
  have e2 : (1 + c2 • coefficientMatrix (ρ.restrict X.negative) 1) *ᵥ v = v + c2 • Cm v :=
    one_add_smul_mulVec _ c2 v
  have e1 : (1 + coefficientMatrix (ρ.restrict x.hom) 1) *ᵥ (v + c2 • Cm v) =
      v + c2 • Cm v + c2 • Bm (Cm v) := by
    have h := one_add_smul_mulVec (ρ.restrict x.hom) 1 (v + c2 • Cm v)
    rw [one_smul, one_smul] at h
    rw [h, map_add, map_smul, hBv, zero_add]
  have e0 : (1 + c1 • coefficientMatrix (ρ.restrict X.negative) 1) *ᵥ
      (v + c2 • Cm v + c2 • Bm (Cm v)) =
      (v + c2 • Bm (Cm v)) + ((c1 + c2) • Cm v + (c1 * c2) • Cm (Bm (Cm v))) := by
    rw [one_add_smul_mulVec, map_add, map_add, map_smul, map_smul, hCCv, smul_zero, add_zero]
    module
  have hn : (ρ.rationalMatrix x.reflectionRepresentative.point : Matrix d d k) *ᵥ v =
      (v + c2 • Bm (Cm v)) + ((c1 + c2) • Cm v + (c1 * c2) • Cm (Bm (Cm v))) := by
    rw [NormalizedRootParametrization.reflectionRepresentative_point, map_mul, map_mul,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hc1, hx1, hc2,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, e1, e0]
  have hmem := SimpleReflectionRepresentative.rationalMatrix_mem_representationWeightSpace
    x.reflectionRepresentative ρ (pathWeight β lam i) hv
  rw [reflection_pathWeight_self hβ hlam hi] at hmem
  have hrest : (c1 + c2) • Cm v + (c1 * c2) • Cm (Bm (Cm v)) ∈
      p.representationWeightSpace ρ (pathWeight β lam (i + 1)) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hCv) (Submodule.smul_mem _ _ hCBCv)
  have hz : v + c2 • Bm (Cm v) = 0 := by
    apply eq_zero_of_mem_both hβ hlam hi
    · exact Submodule.add_mem _ hv (Submodule.smul_mem _ _ hBCv)
    · have : v + c2 • Bm (Cm v) =
          (ρ.rationalMatrix x.reflectionRepresentative.point : Matrix d d k) *ᵥ v -
            ((c1 + c2) • Cm v + (c1 * c2) • Cm (Bm (Cm v))) := by
        rw [hn]
        abel
      rw [this]
      exact Submodule.sub_mem _ hmem hrest
  refine ⟨hmem, ?_⟩
  have hz' : Bm (Cm v) + c2 • Bm (Cm (Bm (Cm v))) = 0 := by
    have := congrArg (fun z => Bm (Cm z)) hz
    simpa only [map_add, map_smul, map_zero] using this
  rw [hn, hz, zero_add, map_add, map_smul, map_smul]
  calc (c1 + c2) • Bm (Cm v) + (c1 * c2) • Bm (Cm (Bm (Cm v)))
      = (c1 + c2) • Bm (Cm v) + c1 • (c2 • Bm (Cm (Bm (Cm v)))) := by rw [mul_smul]
    _ = (c1 + c2) • Bm (Cm v) + c1 • (-Bm (Cm v)) := by
        rw [eq_neg_of_add_eq_zero_right hz']
    _ = c2 • Bm (Cm v) := by module
    _ = -v := eq_neg_of_add_eq_zero_right hz

end Vertex

/-! ### The normalized path basis -/

/-- The normalized root map of a path vertex is equivariant for the difference of consecutive path
weights. -/
theorem NormalizedRootParametrization.isTorusEquivariant_path {i : ℕ} (hi : i < L)
    (x : p.NormalizedRootParametrization (β ⟨i, hi⟩)) :
    VectorGroup.IsTorusEquivariant p.inclusion x.hom
      (pathWeight β lam i - pathWeight β lam (i + 1)) := by
  have h := x.torus_equivariant
  rw [root_path_eq_sub] at h
  exact h

/-- The first divided power of the normalized root map of `β i`, as a linear isomorphism from
line `i + 1` onto line `i`. -/
def pathSuccEquiv (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
    (hlam : IsPathFundamental β lam) {i : ℕ} (hi : i < L)
    (x : p.NormalizedRootParametrization (β ⟨i, hi⟩)) :
    p.representationWeightSpace ρ (pathWeight β lam (i + 1)) ≃ₗ[k]
      p.representationWeightSpace ρ (pathWeight β lam i) :=
  LinearMap.linearEquivOfInjective
    (pathLineShiftMap (ρ := ρ) (NormalizedRootParametrization.isTorusEquivariant_path hi x) (m := 1)
      (by rw [one_smul, add_sub_cancel]))
    (by
      intro w w' h
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      simp only [pathLineShiftMap_apply] at h'
      apply sub_eq_zero.mp
      apply dividedPower_one_injective_succ hρ hβ hlam hi x (Submodule.sub_mem _ w.2 w'.2)
      rw [map_sub, h', sub_self])
    (by
      rw [finrank_pathWeightSpace hρ hβ hlam (by omega),
        finrank_pathWeightSpace hρ hβ hlam (by omega)])

@[simp] theorem pathSuccEquiv_apply (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
    (hlam : IsPathFundamental β lam) {i : ℕ} (hi : i < L)
    (x : p.NormalizedRootParametrization (β ⟨i, hi⟩))
    (w : p.representationWeightSpace ρ (pathWeight β lam (i + 1))) :
    (pathSuccEquiv hρ hβ hlam hi x w : d → k) = dividedPower (ρ.restrict x.hom) 1 w := rfl

/-- The normalized path vectors: `v 0` is supplied, and `v (i + 1)` is the unique vector of line
`i + 1` whose image under the first divided power of the normalized root map of `β i` is `v i`. -/
def normalizedPathVector (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
    (hlam : IsPathFundamental β lam) (x : p.NormalizedSimpleRootParametrizations)
    (v₀ : p.representationWeightSpace ρ (pathWeight β lam 0)) :
    (i : ℕ) → p.representationWeightSpace ρ (pathWeight β lam i)
  | 0 => v₀
  | i + 1 =>
    if hi : i < L then
      (pathSuccEquiv hρ hβ hlam hi (x (β ⟨i, hi⟩))).symm
        (normalizedPathVector hρ hβ hlam x v₀ i)
    else 0

section Normalized

variable (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
  (hlam : IsPathFundamental β lam) (x : p.NormalizedSimpleRootParametrizations)
  (v₀ : p.representationWeightSpace ρ (pathWeight β lam 0))

@[simp] theorem normalizedPathVector_zero : normalizedPathVector hρ hβ hlam x v₀ 0 = v₀ := rfl

/-- The normalized root map of `β i` sends `v (i + 1)` to `v i`. -/
theorem dividedPower_normalizedPathVector_succ {i : ℕ} (hi : i < L) :
    dividedPower (ρ.restrict (x (β ⟨i, hi⟩)).hom) 1
        (normalizedPathVector hρ hβ hlam x v₀ (i + 1) : d → k) =
      normalizedPathVector hρ hβ hlam x v₀ i := by
  have h : normalizedPathVector hρ hβ hlam x v₀ (i + 1) =
      (pathSuccEquiv hρ hβ hlam hi (x (β ⟨i, hi⟩))).symm
        (normalizedPathVector hρ hβ hlam x v₀ i) := by
    simp only [normalizedPathVector, dite_eq_left hi]
  rw [h, ← pathSuccEquiv_apply hρ hβ hlam hi, LinearEquiv.apply_symm_apply]

/-- The normalized path vectors are nonzero when `v 0` is. -/
theorem normalizedPathVector_ne_zero (hv₀ : v₀ ≠ 0) {i : ℕ} (hi : i ≤ L) :
    (normalizedPathVector hρ hβ hlam x v₀ i : d → k) ≠ 0 := by
  induction i with
  | zero =>
    intro h
    exact hv₀ (Subtype.ext h)
  | succ i ih =>
    intro h
    apply ih (by omega)
    rw [← dividedPower_normalizedPathVector_succ hρ hβ hlam x v₀ (by omega : i < L), h, map_zero]

/-- The canonical representative of `β i` sends `v (i + 1)` to `v i`. -/
theorem canonicalReflection_normalizedPathVector_succ {i : ℕ} (hi : i < L) :
    (ρ.rationalMatrix (x (β ⟨i, hi⟩)).reflectionRepresentative.point : Matrix d d k) *ᵥ
        (normalizedPathVector hρ hβ hlam x v₀ (i + 1) : d → k) =
      normalizedPathVector hρ hβ hlam x v₀ i := by
  rw [canonicalReflection_mulVec_of_mem_succ hρ hβ hlam hi (x (β ⟨i, hi⟩))
    (normalizedPathVector hρ hβ hlam x v₀ (i + 1)).2,
    dividedPower_normalizedPathVector_succ hρ hβ hlam x v₀ hi]

/-- The canonical representative of `β i` sends `v i` to `-v (i + 1)`. -/
theorem canonicalReflection_normalizedPathVector_self {i : ℕ} (hi : i < L) :
    (ρ.rationalMatrix (x (β ⟨i, hi⟩)).reflectionRepresentative.point : Matrix d d k) *ᵥ
        (normalizedPathVector hρ hβ hlam x v₀ i : d → k) =
      -(normalizedPathVector hρ hβ hlam x v₀ (i + 1) : d → k) := by
  obtain ⟨hmem, hB⟩ := canonicalReflection_mulVec_of_mem hρ hβ hlam hi (x (β ⟨i, hi⟩))
    (normalizedPathVector hρ hβ hlam x v₀ i).2
  have hsum := dividedPower_one_injective_succ hρ hβ hlam hi (x (β ⟨i, hi⟩))
    (Submodule.add_mem _ hmem (normalizedPathVector hρ hβ hlam x v₀ (i + 1)).2)
    (by rw [map_add, hB, dividedPower_normalizedPathVector_succ hρ hβ hlam x v₀ hi,
      neg_add_cancel])
  exact eq_neg_of_add_eq_zero_left hsum

end Normalized

end SplitPinning

end Langlands.GroupScheme
