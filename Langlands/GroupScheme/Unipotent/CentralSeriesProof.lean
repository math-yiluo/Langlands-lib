import Langlands.GroupScheme.Unipotent.CentralSeriesStatement
import Langlands.GroupScheme.Absolute.TriangularCoordinateSeries
import Langlands.GroupScheme.Rational.UnipotentCompactSubgroups

/-! # Central series with additive factors for unipotent groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

open TriangularLayer AffineLinearEmbedding

/-- The generating Hopf coefficients give a closed representation whose matrices are
unitriangular on every test scheme. -/
private theorem exists_unitriangular_representation {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hG : IsUnipotent G) :
    ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        ρ.pointMatrix T x ∈ W Γ(T.left, ⊤) N 0 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let A := AffineCoordinates.hopfAlgebra G
  have : Algebra.FiniteType k A := AffineCoordinates.algebraFiniteType G
  obtain ⟨N, M, hcomul, hcounit, hgen, hdiag, hlow⟩ :=
    Algebra.GradedHopf.exists_unitriangular_matrixCoefficients A
      (IsUnipotent.of_iso (AffineCoordinates.hopfSpecIso G) hG)
  let e := AffineCoordinates.corepresentation G
  let M' : Matrix (Fin N) (Fin N) (AffineCoordinates.algebra G) := M
  have hcomul' (i j : Fin N) : comul e (M' i j) =
      ∑ l, M' i l ⊗ₜ[CommRingCat.of k] M' l j :=
    (LinearMap.congr_fun (AffineCoordinates.corepresentation_comul G) (M i j)).trans
      (hcomul i j)
  have hcounit' (i j : Fin N) :
      counit e (M' i j) = (1 : Matrix (Fin N) (Fin N) (CommRingCat.of k)) i j := by
    rw [Matrix.one_apply]
    exact (LinearMap.congr_fun (AffineCoordinates.corepresentation_counit G) (M i j)).trans
      (hcounit i j)
  let ρ : MatrixRepresentation G (Fin N) :=
    (AffineCoordinates.groupSchemeIso G).inv ≫ toGLHom e M' hcomul' hcounit'
  refine ⟨N, ρ, ?_, fun T x => ?_⟩
  · have : IsClosedImmersion (toGLHom e M' hcomul' hcounit').hom.hom.left :=
      isClosedSubgroup_toGLHom e M' hcomul' hcounit' hgen
    have : IsIso (AffineCoordinates.groupSchemeIso G).inv.hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map
        (AffineCoordinates.groupSchemeIso G).inv.hom.hom))
    change IsClosedImmersion ((AffineCoordinates.groupSchemeIso G).inv.hom.hom.left ≫
      (toGLHom e M' hcomul' hcounit').hom.hom.left)
    infer_instance
  · rw [mem_W]
    intro i j hij
    rw [Matrix.sub_apply, sub_eq_zero,
      pointMatrix_toGLHom_apply G M' hcomul' hcounit' T x i j]
    by_cases he : i = j
    · subst j
      rw [show M' i i = 1 from hdiag i, map_one, Matrix.one_apply_eq]
      rfl
    · have hlt : j < i := lt_of_le_of_ne (show j ≤ i from hij) (Ne.symm he)
      rw [show M' i j = 0 from hlow i j hlt, map_zero, Matrix.one_apply_ne he]
      rfl

/-- Unitriangular conjugation fixes the layer, so the commutator lies in the
next full superdiagonal term. -/
private theorem commutator_mem_next_level {A : Type*} [CommRing A] {N a : ℕ}
    {g x : GL (Fin N) A} (hg : g ∈ W A N 0) (hx : x ∈ W A N a) :
    g * x * g⁻¹ * x⁻¹ ∈ W A N (a + 1) := by
  have hgInv := (W A N 0).inv_mem hg
  have hgUpper := W_le_upper 0 hgInv
  have hconj : g * x * g⁻¹ ∈ W A N a := by
    simpa only [inv_inv] using W_conj hgUpper hx
  have hconjLayer := layer_conj hgUpper hx
  rw [scale_of_mem_W hgInv, inv_inv] at hconjLayer
  apply mem_W_succ ((W A N a).mul_mem hconj ((W A N a).inv_mem hx))
  rw [layer_mul hconj ((W A N a).inv_mem hx), layer_inv hx, hconjLayer, add_neg_cancel]

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {N : ℕ}

/-- For each row, take its entry on the current superdiagonal when that entry exists. -/
private def seriesCoordinate (ρ : MatrixRepresentation G (Fin N)) (t : ℕ) :
    seriesScheme ρ t ⟶ VectorGroup.groupScheme R 1 :=
  if h : t % N + t / N + 1 < N then
    filtrationCoordinate ρ (t / N) (t % N)
      ⟨t % N, Nat.mod_lt t (lt_of_le_of_lt (Nat.zero_le _) h)⟩ ⟨t % N + t / N + 1, h⟩
  else 0

/-- Milne, *Algebraic Groups* (2017), Proposition 14.21. -/
theorem unipotentAdditiveCentralSeries : UnipotentAdditiveCentralSeriesStatement.{u} := by
  intro k _ G _ _ hG
  obtain ⟨N, ρ, hclosed, hρ⟩ := exists_unitriangular_representation G hG
  have : IsClosedImmersion ρ.hom.hom.left := hclosed
  have : Mono ρ.hom.hom := Over.mono_of_mono_left _
  have size_pos (j : Fin (N * N)) : 0 < N := by
    apply Nat.pos_of_ne_zero
    intro h
    subst N
    exact Fin.elim0 j
  refine ⟨N * N, fun j => seriesScheme ρ j, fun j => seriesHom ρ j,
    fun j => seriesCoordinate ρ j, fun j => isClosedSubgroup_filtrationHom ρ _ _,
    ?_, range_seriesHom_last ρ, ?_, ?_, ?_⟩
  · change SubgroupFunctor.range (seriesHom ρ 0) = ⊤
    rw [range_seriesHom_zero]
    ext T x
    rw [mem_range_filtrationHom, refinedW_zero, SubgroupFunctor.top_carrier]
    exact iff_of_true (hρ T x) (Subgroup.mem_top x)
  · intro j
    exact seriesHom_succ_le ρ (size_pos j) j
  · intro j T y
    let t : ℕ := j
    change y ≫ (seriesCoordinate ρ t).hom.hom = 1 ↔
      y ≫ (seriesHom ρ t).hom.hom ∈ (SubgroupFunctor.range (seriesHom ρ (t + 1))).carrier T
    by_cases h : t % N + t / N + 1 < N
    · have : IsClosedImmersion (seriesHom ρ t).hom.hom.left :=
        isClosedSubgroup_filtrationHom ρ _ _
      have : Mono (seriesHom ρ t).hom.hom := Over.mono_of_mono_left _
      rw [seriesCoordinate, dite_eq_left h, ← range_kernel_seriesCoordinate ρ (size_pos j) t h,
        ← mem_range_kernelι_iff]
      simp only [SubgroupFunctor.mem_range, Grp.comp_hom_hom, ← Category.assoc, cancel_mono]
    · rw [seriesCoordinate, dite_eq_right h, range_seriesHom_succ_of_out_of_range ρ (size_pos j) t
        (Nat.le_of_not_gt h)]
      exact ⟨fun _ => SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩, fun _ => MonObj.comp_one y⟩
  · intro j T g x hx
    let t : ℕ := j
    change x ∈ (SubgroupFunctor.range (seriesHom ρ t)).carrier T at hx
    change g * x * g⁻¹ * x⁻¹ ∈ (SubgroupFunctor.range (seriesHom ρ (t + 1))).carrier T
    rw [mem_range_filtrationHom] at hx
    rw [range_seriesHom_succ ρ (size_pos j), mem_range_filtrationHom]
    simp only [map_mul, map_inv]
    apply refinedW_anti (t / N) (Nat.succ_le_of_lt (Nat.mod_lt t (size_pos j)))
    rw [refinedW_top]
    exact commutator_mem_next_level (hρ T g) hx.1

end Langlands.GroupScheme
