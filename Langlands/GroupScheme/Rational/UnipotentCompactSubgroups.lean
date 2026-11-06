import Langlands.Algebra.GradedHopf.TrivialGrading
import Langlands.GroupScheme.AffineCoordinateEvaluation
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.Rational.MatrixEntryBoundedCompactness
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-!
# Compact subsets of unipotent rational points lie in compact subgroups

A unipotent affine group scheme of finite type over a field has a closed matrix
representation whose matrices are upper unitriangular. Over a nonarchimedean local
field, conjugating by a diagonal matrix of powers of a small scalar shows that every
compact set of rational points lies in a compact subgroup cut out by integrality
of the rescaled entries. The property passes to the rational-point image
of a closed embedding.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix TensorProduct

namespace Langlands.GroupScheme

section Unitriangular

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {n : ℕ}

/-- A group closedly embedded into upper unitriangular invertible matrices over a
nonarchimedean local field: every compact subset lies in a compact subgroup. -/
theorem exists_isCompact_subgroup_superset_of_unitriangular
    (φ : Γ →* GL (Fin n) F) (hφ : IsClosedEmbedding φ)
    (hdiag : ∀ x i, (φ x : Matrix (Fin n) (Fin n) F) i i = 1)
    (hlow : ∀ x i j, j < i → (φ x : Matrix (Fin n) (Fin n) F) i j = 0)
    (C : Set Γ) (hC : IsCompact C) :
    ∃ K : Subgroup Γ, IsCompact (K : Set Γ) ∧ C ⊆ K := by
  classical
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let v := ValuativeRel.valuation F
  have hent : ∀ i j, Continuous fun x : Γ => (φ x : Matrix (Fin n) (Fin n) F) i j :=
    fun i j => (continuous_apply j).comp
      ((continuous_apply i).comp
        ((Units.continuous_val (M := Matrix (Fin n) (Fin n) F)).comp hφ.continuous))
  have hinv : ∀ i j, Continuous fun x : Γ =>
      (((φ x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j :=
    fun i j => (continuous_apply j).comp
      ((continuous_apply i).comp
        ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) F)).comp hφ.continuous))
  -- A common bound for all entries of the matrices and their inverses on `C`.
  let D : Set F := ⋃ i, ⋃ j,
    ((fun x => (φ x : Matrix (Fin n) (Fin n) F) i j) '' C ∪
      (fun x => (((φ x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) '' C)
  have hD : IsCompact D := isCompact_iUnion fun i => isCompact_iUnion fun j =>
    (hC.image (hent i j)).union (hC.image (hinv i j))
  obtain ⟨b, -, hb⟩ := IsCompact.exists_valuative_bound hD
  obtain ⟨c, hc0, hbc, hc1⟩ : ∃ c : F, c ≠ 0 ∧ v b ≤ v c ∧ 1 ≤ v c := by
    rcases le_total (v b) 1 with h | h
    · exact ⟨1, one_ne_zero, by rwa [map_one], (map_one v).ge⟩
    · refine ⟨b, ?_, le_rfl, h⟩
      rintro rfl
      rw [map_zero] at h
      exact one_ne_zero (le_antisymm h zero_le)
  let t : F := c⁻¹
  have htc : v t * v c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  have ht1 : v t ≤ 1 := by
    calc v t = v t * 1 := (mul_one _).symm
      _ ≤ v t * v c := mul_le_mul' le_rfl hc1
      _ = 1 := htc
  -- The rescaled integrality condition, i.e. integrality after conjugation by
  -- `diag(t^i)`.
  let P : Γ → Prop := fun x =>
    ∀ i j, v ((φ x : Matrix (Fin n) (Fin n) F) i j * t ^ ((j : ℕ) - (i : ℕ))) ≤ 1
  have hP1 : P 1 := by
    intro i j
    rw [map_one, Units.val_one, Matrix.one_apply]
    split_ifs with h
    · subst h
      simp
    · simp
  have hPmul : ∀ x y, P x → P y → P (x * y) := by
    intro x y hx hy i j
    rw [φ.map_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_mul]
    refine Valuation.map_sum_le v fun l _ => ?_
    rcases lt_or_ge l i with hli | hil
    · rw [hlow x i l hli, zero_mul, zero_mul, map_zero]
      exact zero_le
    rcases lt_or_ge j l with hjl | hlj
    · rw [hlow y l j hjl, mul_zero, zero_mul, map_zero]
      exact zero_le
    have hil' : (i : ℕ) ≤ l := hil
    have hlj' : (l : ℕ) ≤ j := hlj
    have hk : (j : ℕ) - i = ((l : ℕ) - i) + ((j : ℕ) - l) := by omega
    have hsplit : (φ x : Matrix (Fin n) (Fin n) F) i l * (φ y : Matrix (Fin n) (Fin n) F) l j *
        t ^ ((j : ℕ) - i) =
        ((φ x : Matrix (Fin n) (Fin n) F) i l * t ^ ((l : ℕ) - i)) *
          ((φ y : Matrix (Fin n) (Fin n) F) l j * t ^ ((j : ℕ) - l)) := by
      rw [hk, pow_add]
      ring
    rw [hsplit, map_mul]
    exact mul_le_one' (hx i l) (hy l j)
  let K : Subgroup Γ :=
    { carrier := {x | P x ∧ P x⁻¹}
      mul_mem' := fun {x y} hx hy =>
        ⟨hPmul x y hx.1 hy.1, by rw [mul_inv_rev]; exact hPmul _ _ hy.2 hx.2⟩
      one_mem' := ⟨hP1, by rw [inv_one]; exact hP1⟩
      inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩ }
  -- Bounded entries satisfy the rescaled condition.
  have hscale : ∀ y : Γ, (∀ i j, v ((φ y : Matrix (Fin n) (Fin n) F) i j) ≤ v b) → P y := by
    intro y hy i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hk : (j : ℕ) - i ≠ 0 := by
        have : (i : ℕ) < j := hij
        omega
      rw [map_mul, map_pow]
      calc v ((φ y : Matrix (Fin n) (Fin n) F) i j) * v t ^ ((j : ℕ) - i)
          ≤ v c * v t := mul_le_mul' ((hy i j).trans hbc) (pow_le_of_le_one zero_le ht1 hk)
        _ = 1 := by rw [mul_comm]; exact htc
    · rw [hdiag, Nat.sub_self, pow_zero, mul_one, map_one]
    · rw [hlow y i j hji, zero_mul, map_zero]
      exact zero_le
  have hCK : C ⊆ K := by
    intro x hx
    refine ⟨hscale x fun i j => (v.vle_iff_le).mp (hb _ ?_),
      hscale x⁻¹ fun i j => (v.vle_iff_le).mp (hb _ ?_)⟩
    · exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Or.inl ⟨x, hx, rfl⟩⟩⟩
    · rw [map_inv]
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Or.inr ⟨x, hx, rfl⟩⟩⟩
  -- `K` is closed.
  have hB1 : IsClosed {z : F | v z ≤ 1} :=
    (IsNonarchimedeanLocalField.isCompact_closedBall F 1).isClosed
  have hKc : IsClosed (K : Set Γ) := by
    have h1 : IsClosed {x : Γ | P x} := by
      simp only [P, Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        hB1.preimage ((hent i j).mul continuous_const)
    have h2 : IsClosed {x : Γ | P x⁻¹} := by
      simp only [P, Set.ofPred_forall, map_inv]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        hB1.preimage ((hinv i j).mul continuous_const)
    exact h1.inter h2
  -- `K` lies in a compact set of matrices with bounded entries and inverse entries.
  let γ : ValuativeRel.ValueGroupWithZero F := v c ^ n
  have hbound : ∀ (m : F) (k : ℕ), k ≤ n → v (m * t ^ k) ≤ 1 → v m ≤ γ := by
    intro m k hk h
    have hm : m = m * t ^ k * c ^ k := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hc0, one_pow, mul_one]
    rw [hm, map_mul, map_pow]
    calc v (m * t ^ k) * v c ^ k ≤ 1 * v c ^ k := mul_le_mul' h le_rfl
      _ = v c ^ k := one_mul _
      _ ≤ v c ^ n := pow_le_pow_right₀ hc1 hk
  let Kb : Set (Matrix (Fin n) (Fin n) F) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => {z | v z ≤ γ}
  have hKb : IsCompact Kb := isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall F γ
  let e := Units.embedProduct (Matrix (Fin n) (Fin n) F) ∘ φ
  have he : IsClosedEmbedding e := Units.isClosedEmbedding_embedProduct.comp hφ
  have hsub : (K : Set Γ) ⊆ e ⁻¹' (Kb ×ˢ (MulOpposite.opHomeomorph '' Kb)) := by
    intro x hx
    refine ⟨fun i _ j _ => hbound _ _ ((Nat.sub_le _ _).trans j.isLt.le) (hx.1 i j),
      ⟨(((φ x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F), fun i _ j _ => ?_, rfl⟩⟩
    have h := hx.2 i j
    rw [map_inv] at h
    exact hbound _ _ ((Nat.sub_le _ _).trans j.isLt.le) h
  have hprod : IsCompact (Kb ×ˢ (MulOpposite.opHomeomorph '' Kb)) :=
    hKb.prod (hKb.image MulOpposite.opHomeomorph.continuous)
  exact ⟨K, (he.isCompact_preimage hprod).of_isClosed_subset hKc hsub, hCK⟩

/-- The compact-subgroup property passes to the range of a closed embedding. -/
theorem exists_isCompact_subgroup_superset_range {Δ : Type*} [Group Δ] [TopologicalSpace Δ]
    (f : Γ →* Δ) (hf : IsClosedEmbedding f)
    (h : ∀ C : Set Γ, IsCompact C → ∃ K : Subgroup Γ, IsCompact (K : Set Γ) ∧ C ⊆ K)
    (C : Set f.range) (hC : IsCompact C) :
    ∃ K : Subgroup f.range, IsCompact (K : Set f.range) ∧ C ⊆ K := by
  obtain ⟨K, hK, hCK⟩ := h (f ⁻¹' (Subtype.val '' C))
    (hf.isCompact_preimage (hC.image continuous_subtype_val))
  refine ⟨K.map f.rangeRestrict, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact hK.image (continuous_induced_rng.2 hf.continuous)
  · intro y hy
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, hCK ⟨y, hy, hx.symm⟩, Subtype.ext hx⟩

end Unitriangular

section Unipotent

variable {F : Type u} [Field F]

/-- The matrix of a test point under the closed linear embedding attached to a matrix
of Hopf coefficients evaluates those coefficients at the point. -/
theorem pointMatrix_toGLHom_apply (U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine U.X.left] {n : ℕ} (M : Matrix (Fin n) (Fin n) (AffineCoordinates.algebra U))
    (hcomul : ∀ i j, AffineLinearEmbedding.comul (AffineCoordinates.corepresentation U)
      (M i j) = ∑ l, M i l ⊗ₜ[CommRingCat.of F] M l j)
    (hcounit : ∀ i j, AffineLinearEmbedding.counit (AffineCoordinates.corepresentation U)
      (M i j) = (1 : Matrix (Fin n) (Fin n) (CommRingCat.of F)) i j)
    (T : Over (Spec (CommRingCat.of F))) (x : T ⟶ U.X) (i j : Fin n) :
    (MatrixRepresentation.pointMatrix (G := U) (n := Fin n)
        ((AffineCoordinates.groupSchemeIso U).inv ≫
          AffineLinearEmbedding.toGLHom (AffineCoordinates.corepresentation U) M hcomul
            hcounit) T x : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) i j =
      AffineCoordinates.pointAlgebraHom U T x (M i j) := by
  rw [MatrixRepresentation.pointMatrix_apply]
  change (GeneralLinear.pointsEquiv (Fin n) (CommRingCat.of F) T
    ((x ≫ (AffineCoordinates.groupSchemeIso U).inv.hom.hom) ≫
      (AffineLinearEmbedding.toGLHom (AffineCoordinates.corepresentation U) M hcomul
        hcounit).hom.hom) : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) i j = _
  have h := congrArg (fun g => (Units.val g) i j)
    (Corepresented.groupSchemeMap_points (AffineCoordinates.corepresentation U)
      (GeneralLinear.corepresentableBy (Fin n) (CommRingCat.of F))
      (AffineLinearEmbedding.toGL (AffineCoordinates.corepresentation U) M hcomul hcounit)
      (x ≫ (AffineCoordinates.groupSchemeIso U).inv.hom.hom))
  exact h.trans rfl

/-- A unipotent affine group scheme of finite type over a field has a closed matrix
representation whose rational matrices are upper unitriangular. -/
theorem exists_unitriangular_closedRepresentation
    (U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine U.X.left]
    [LocallyOfFiniteType U.X.hom] (hU : IsUnipotent U) :
    ∃ (n : ℕ) (ρ : MatrixRepresentation U (Fin n)), IsClosedSubgroup ρ ∧
      (∀ (g : rationalPoints U) i, (ρ.rationalMatrix g : Matrix (Fin n) (Fin n) F) i i = 1) ∧
      ∀ (g : rationalPoints U) i j, j < i →
        (ρ.rationalMatrix g : Matrix (Fin n) (Fin n) F) i j = 0 := by
  let A := AffineCoordinates.hopfAlgebra U
  have : Algebra.FiniteType F A := AffineCoordinates.algebraFiniteType U
  obtain ⟨n, M, hcomul, hcounit, hgen, hdiag, hlow⟩ :=
    Algebra.GradedHopf.exists_unitriangular_matrixCoefficients A
      (IsUnipotent.of_iso (AffineCoordinates.hopfSpecIso U) hU)
  let e := AffineCoordinates.corepresentation U
  let M' : Matrix (Fin n) (Fin n) (AffineCoordinates.algebra U) := M
  have hcomul' : ∀ i j, AffineLinearEmbedding.comul e (M' i j) =
      ∑ l, M' i l ⊗ₜ[CommRingCat.of F] M' l j := fun i j =>
    (LinearMap.congr_fun (AffineCoordinates.corepresentation_comul U) (M i j)).trans
      (hcomul i j)
  have hcounit' : ∀ i j, AffineLinearEmbedding.counit e (M' i j) =
      (1 : Matrix (Fin n) (Fin n) (CommRingCat.of F)) i j := fun i j => by
    rw [Matrix.one_apply]
    exact (LinearMap.congr_fun (AffineCoordinates.corepresentation_counit U) (M i j)).trans
      (hcounit i j)
  let ρ : MatrixRepresentation U (Fin n) :=
    (AffineCoordinates.groupSchemeIso U).inv ≫ AffineLinearEmbedding.toGLHom e M' hcomul' hcounit'
  have hρ : IsClosedSubgroup ρ := by
    have hmodel := AffineLinearEmbedding.isClosedSubgroup_toGLHom e M' hcomul' hcounit' hgen
    have : IsIso (AffineCoordinates.groupSchemeIso U).inv.hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map
        (AffineCoordinates.groupSchemeIso U).inv.hom.hom))
    have : IsClosedImmersion
        (AffineLinearEmbedding.toGLHom e M' hcomul' hcounit').hom.hom.left := hmodel
    change IsClosedImmersion ((AffineCoordinates.groupSchemeIso U).inv.hom.hom.left ≫
      (AffineLinearEmbedding.toGLHom e M' hcomul' hcounit').hom.hom.left)
    infer_instance
  have hentry (g : rationalPoints U) (i j : Fin n) :
      (ρ.rationalMatrix g : Matrix (Fin n) (Fin n) F) i j =
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom
          (AffineCoordinates.pointAlgebraHom U _ g (M' i j)) := by
    rw [← pointMatrix_toGLHom_apply U M' hcomul' hcounit']
    rfl
  refine ⟨n, ρ, hρ, fun g i => ?_, fun g i j hji => ?_⟩
  · rw [hentry]
    have hd : M' i i = 1 := hdiag i
    rw [hd, map_one]
    exact map_one _
  · rw [hentry]
    have hl : M' i j = 0 := hlow i j hji
    rw [hl, map_zero]
    exact map_zero _

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Every compact set of rational points of a unipotent affine group scheme of finite
type over a nonarchimedean local field lies in a compact subgroup. -/
theorem exists_isCompact_subgroup_superset_of_isUnipotent
    (U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine U.X.left]
    [LocallyOfFiniteType U.X.hom] (hU : IsUnipotent U) :
    letI : TopologicalSpace (rationalPoints U) := rationalPointTopology F U.X
    ∀ C : Set (rationalPoints U), IsCompact C →
      ∃ K : Subgroup (rationalPoints U), IsCompact (K : Set (rationalPoints U)) ∧ C ⊆ K := by
  let : TopologicalSpace (rationalPoints U) := rationalPointTopology F U.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  obtain ⟨n, ρ, hρ, hdiag, hlow⟩ := exists_unitriangular_closedRepresentation U hU
  exact exists_isCompact_subgroup_superset_of_unitriangular ρ.rationalMatrix
    (ρ.isClosedEmbedding_rationalMatrix hρ) hdiag hlow

/-- The rational-point image of a closed unipotent subgroup of finite type of an affine
group scheme over a nonarchimedean local field: every compact subset lies in a compact
subgroup. -/
theorem exists_isCompact_subgroup_superset_range_of_isUnipotent
    {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    [LocallyOfFiniteType U.X.hom] (j : U ⟶ G) (hj : IsClosedSubgroup j)
    (hU : IsUnipotent U) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ C : Set (rationalPoints.map j).range, IsCompact C →
      ∃ K : Subgroup (rationalPoints.map j).range,
        IsCompact (K : Set (rationalPoints.map j).range) ∧ C ⊆ K := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffine U.X.left := isAffine_of_isAffineHom j.hom.hom.left
  let : TopologicalSpace (rationalPoints U) := rationalPointTopology F U.X
  exact exists_isCompact_subgroup_superset_range (rationalPoints.map j)
    (isClosedEmbedding_rationalPointMap F j.hom.hom)
    (exists_isCompact_subgroup_superset_of_isUnipotent U hU)

end Unipotent

end Langlands.GroupScheme
