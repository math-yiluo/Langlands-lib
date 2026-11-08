import Langlands.GroupScheme.Rational.PathRootActions
import Langlands.GroupScheme.Rational.SteinbergPolynomialAction
import Langlands.GroupScheme.Rational.SteinbergCanonicalRepresentatives
import Langlands.GroupScheme.Reductive.LinkedRootParametrization
import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterSpan

/-! # Rational root points fixing path weight lines -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Stabilizers of vectors in rational points -/

namespace MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The rational points of `G` whose matrix in the actual representation fixes the vector `v`. -/
def rationalStabilizer (ρ : MatrixRepresentation G n) (v : n → k) :
    Subgroup (rationalPoints G) where
  carrier := {g | (ρ.rationalMatrix g : Matrix n n k) *ᵥ v = v}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, map_one, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [Matrix.mulVec_mulVec, map_inv, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

@[simp] theorem mem_rationalStabilizer (ρ : MatrixRepresentation G n) (v : n → k)
    (g : rationalPoints G) :
    g ∈ ρ.rationalStabilizer v ↔ (ρ.rationalMatrix g : Matrix n n k) *ᵥ v = v := Iff.rfl

namespace AdditiveDividedPowers

variable (σ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)

/-- If every positive divided power kills `v`, every rational point of the additive group fixes
`v`. -/
theorem rationalMatrix_mulVec_eq_self {v : n → k}
    (hv : ∀ m, 1 ≤ m → dividedPower σ m v = 0)
    (g : rationalPoints (VectorGroup.groupScheme (CommRingCat.of k) 1)) :
    (σ.rationalMatrix g : Matrix n n k) *ᵥ v = v := by
  let A : CommAlgCat.{u} k := CommAlgCat.of k k
  let c : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤) :=
    (VectorGroup.coordinates (CommRingCat.of k) 1 _ g).toAdd 0
  have hg : VectorGroup.scalarPoint (CommRingCat.of k) _ c = g :=
    VectorGroup.scalarPoint_coordinate _ g
  let T := (algSpec (CommRingCat.of k)).obj (op A)
  let c' : A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom (T.hom.appTop c)
  have hpt : (VectorGroup.groupScheme (CommRingCat.of k) 1).constantPoint g T =
      VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => c') := by
    rw [VectorGroup.affinePoint_eq_scalarPoint, ← hg]
    unfold GroupScheme.constantPoint
    rw [VectorGroup.scalarPoint_comp]
    congr 1
    exact (CategoryTheory.Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of A)) _).symm
  have hconst := σ.affineMatrix_constantPoint g A
  rw [hpt] at hconst
  have hsum := affineMatrix_mulVec_eq_sum σ A c' v
  rw [hconst] at hsum
  have hsum' : ∑ m ∈ Finset.range (degreeBound σ),
      c' ^ m • (fun i => algebraMap k A (dividedPower σ m v i)) =
        fun i => algebraMap k A (v i) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro m _ hm
      rw [hv m (by omega)]
      funext i
      simp
    · intro h
      exact absurd (Finset.mem_range.mpr (by unfold degreeBound; omega)) h
  rw [hsum'] at hsum
  funext i
  have hi := congrFun hsum i
  have hid : ∀ y : k, algebraMap k A y = y := fun y => rfl
  simp only [Matrix.mulVec, dotProduct, Matrix.GeneralLinearGroup.map] at hi
  simp only [Units.coe_map, hid] at hi
  exact hi

end AdditiveDividedPowers

end MatrixRepresentation

/-! ### Rational points of represented subgroups and of root subgroups -/

namespace SplitPinning

open MatrixRepresentation MatrixRepresentation.AdditiveDividedPowers
open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {n : Type} [Fintype n] [DecidableEq n]

omit [IsAffineHom G.X.hom] in
/-- A rational point of a subgroup represented by an additive map fixes `v` when every positive
divided power of the map kills `v`. -/
theorem rationalMatrix_mulVec_eq_self_of_isRepresentedBy (ρ : MatrixRepresentation G n)
    {F : SubgroupFunctor G} {y : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G}
    (hy : F.IsRepresentedBy y) {v : n → k}
    (hv : ∀ m, 1 ≤ m → dividedPower (ρ.restrict y) m v = 0) {g : rationalPoints G}
    (hg : g ∈ F.carrier (Over.mk (𝟙 _))) :
    (ρ.rationalMatrix g : Matrix n n k) *ᵥ v = v := by
  rw [← hy.2, SubgroupFunctor.mem_range] at hg
  obtain ⟨w, rfl⟩ := hg
  have h := rationalMatrix_mulVec_eq_self (ρ.restrict y) hv w
  rwa [rationalMatrix_restrict] at h

variable {p : SplitPinning G} {ρ : MatrixRepresentation G n} {L : ℕ}
  {β : Fin L → p.base.support} {lam : characterLattice p.torus}

/-- Let `r` be a root such that no positive multiple of `± α_r` moves the path weight `ε_j` to a
path weight. Then every rational point in the subgroup generated by the root subgroups of `α_r`
and `-α_r` fixes every vector of the line of `ε_j`. -/
theorem rationalMatrix_mulVec_eq_self_of_mem_rootSup (hρ : p.IsHighestWeight ρ lam)
    (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam) (r : p.rootIndex) {j : ℕ}
    (hpos : ∀ m, 1 ≤ m → ∀ l ≤ L,
      pathWeight β lam j + m • p.rootDatum.root r ≠ pathWeight β lam l)
    (hneg : ∀ m, 1 ≤ m → ∀ l ≤ L,
      pathWeight β lam j + m • (-p.rootDatum.root r) ≠ pathWeight β lam l)
    {v : n → k} (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam j))
    {g : rationalPoints G}
    (hg : g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
        (Over.mk (𝟙 _)) ⊔
      (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root r)).carrier (Over.mk (𝟙 _))) :
    (ρ.rationalMatrix g : Matrix n n k) *ᵥ v = v := by
  obtain ⟨X⟩ := p.nonempty_linkedRootParametrization r
  have hle : (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
        (Over.mk (𝟙 _)) ⊔
      (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root r)).carrier (Over.mk (𝟙 _)) ≤
      ρ.rationalStabilizer v := by
    refine sup_le ?_ ?_
    · intro g hg
      exact rationalMatrix_mulVec_eq_self_of_isRepresentedBy ρ X.positive_represents
        (fun m hm => dividedPower_eq_zero_of_shift_ne hρ hβ hlam X.positive_equivariant
          (hpos m hm) hv) hg
    · intro g hg
      exact rationalMatrix_mulVec_eq_self_of_isRepresentedBy ρ X.negative_represents
        (fun m hm => dividedPower_eq_zero_of_shift_ne hρ hβ hlam X.negative_equivariant
          (hneg m hm) hv) hg
  exact hle hg

/-- The root of a path vertex is the difference of consecutive path weights. -/
theorem root_path_eq_sub (i : Fin L) :
    p.rootDatum.root (β i : p.rootIndex) = pathWeight β lam i - pathWeight β lam (i + 1) := by
  rw [← pathRoot_eq_sub, pathRoot_of_lt β i.2]

/-- The canonical reflection representative of the path vertex `β t` fixes every path line
other than lines `t` and `t + 1`. -/
theorem canonicalReflection_path_fixes (hρ : p.IsHighestWeight ρ lam)
    (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam) (t : Fin L)
    (x : p.NormalizedRootParametrization (β t)) {j : ℕ} (hj : j ≤ L) (hjt : j ≠ t)
    (hjt' : j ≠ (t : ℕ) + 1) {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam j)) :
    (ρ.rationalMatrix x.reflectionRepresentative.point : Matrix n n k) *ᵥ v = v := by
  have ht := t.2
  refine rationalMatrix_mulVec_eq_self_of_mem_rootSup hρ hβ hlam (β t : p.rootIndex)
    (fun m hm l hl h => ?_) (fun m hm l hl h => ?_) hv
    x.reflectionRepresentative_mem_generated
  · rw [root_path_eq_sub] at h
    exact hjt' ((pathWeight_add_nsmul_sub_eq_iff hβ lam (by omega : (t : ℕ) < t + 1)
      (by omega) hj hl hm).mp h).2.1
  · rw [root_path_eq_sub, neg_sub] at h
    exact hjt ((pathWeight_add_nsmul_sub_eq_iff' hβ lam (by omega : (t : ℕ) < t + 1)
      (by omega) hj hl hm).mp h).2.1

/-- The canonical reflection representative of a simple root off the path fixes every path
line. -/
theorem canonicalReflection_offPath_fixes (hρ : p.IsHighestWeight ρ lam)
    (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam) {z : p.base.support}
    (hz : z ∉ Set.range β) (x : p.NormalizedRootParametrization z) {j : ℕ} {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam j)) :
    (ρ.rationalMatrix x.reflectionRepresentative.point : Matrix n n k) *ᵥ v = v :=
  rationalMatrix_mulVec_eq_self_of_mem_rootSup hρ hβ hlam (z : p.rootIndex)
    (fun _ hm l _ => pathWeight_add_nsmul_root_ne hβ hlam hz hm j l)
    (fun _ hm l _ => pathWeight_add_nsmul_neg_root_ne hβ hlam hz hm j l) hv
    x.reflectionRepresentative_mem_generated

/-- A rational point generated by the root subgroups of `± (ε_i - ε_l)` (`i < l ≤ L`) fixes
every path line other than lines `i` and `l`. -/
theorem rootSup_pathRoot_fixes (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β)
    (hlam : IsPathFundamental β lam) (r : p.rootIndex) {i l : ℕ} (hil : i < l) (hl : l ≤ L)
    (hr : p.rootDatum.root r = pathWeight β lam i - pathWeight β lam l) {j : ℕ} (hj : j ≤ L)
    (hji : j ≠ i) (hjl : j ≠ l) {v : n → k}
    (hv : v ∈ p.representationWeightSpace ρ (pathWeight β lam j)) {g : rationalPoints G}
    (hg : g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
        (Over.mk (𝟙 _)) ⊔
      (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root r)).carrier (Over.mk (𝟙 _))) :
    (ρ.rationalMatrix g : Matrix n n k) *ᵥ v = v := by
  refine rationalMatrix_mulVec_eq_self_of_mem_rootSup hρ hβ hlam r
    (fun m hm l' hl' h => ?_) (fun m hm l' hl' h => ?_) hv hg
  · rw [hr] at h
    exact hjl ((pathWeight_add_nsmul_sub_eq_iff hβ lam hil hl hj hl' hm).mp h).2.1
  · rw [hr, neg_sub] at h
    exact hji ((pathWeight_add_nsmul_sub_eq_iff' hβ lam hil hl hj hl' hm).mp h).2.1

end SplitPinning

end Langlands.GroupScheme
