import Langlands.GroupScheme.Absolute.StronglyRegularTorusPointStatement
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.MatrixRepresentationConjugate
import Langlands.GroupScheme.MatrixRepresentation.RationalStableCoordinates
import Langlands.GroupScheme.SplitTorusGenericWeights
import Langlands.GroupScheme.FlagDualLineNeighbourhood
import Langlands.GroupScheme.Torus.Integral
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Matrix
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace StronglyRegularTorusPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : GroupScheme (Spec (CommRingCat.of k))}
variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
variable {n : Type} [Fintype n] [DecidableEq n]

omit [IsAlgClosed k] in
/-- Changing basis by a rational matrix preserves faithfulness and diagonalizes the
restriction of a representation to a split torus on rational points. -/
theorem exists_rationalDiagonal (ρ : MatrixRepresentation G n) [Mono ρ.hom.hom]
    (j : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) :
    ∃ (σ : MatrixRepresentation G n), Mono σ.hom.hom ∧
      ∀ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X,
        ∃ d : n → k, ((σ.restrict j).rationalMatrix t : Matrix n n k) = diagonal d := by
  classical
  obtain ⟨I, _, P, wt, τ, hτ, hsurj⟩ :=
    SplitTorusGenericWeights.exists_splitTorusDiagonal hT (ρ.restrict j)
  let B : GL n Γ(Spec (CommRingCat.of k), ⊤) :=
    Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom P⁻¹
  let g := (GeneralLinear.pointsEquiv n (CommRingCat.of k)
    (Over.mk (𝟙 (Spec (CommRingCat.of k))))).symm B
  let σ := ρ.conjugate g
  have hmono : Mono σ.hom.hom := by
    dsimp [σ, MatrixRepresentation.conjugate]
    infer_instance
  refine ⟨σ, hmono, ?_⟩
  intro t
  obtain ⟨s, rfl⟩ := hsurj t
  refine ⟨fun i => (FlagCore.charValue wt s i : k), ?_⟩
  have hB : Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom B = P⁻¹ := by
    apply Units.ext
    ext i j
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.apply_symm_apply _
  have hσ : (σ.restrict j).rationalMatrix (τ s) =
      P⁻¹ * (ρ.restrict j).rationalMatrix (τ s) * P := by
    change Matrix.GeneralLinearGroup.map _ ((σ.restrict j).pointMatrix _ _) = _
    rw [← MatrixRepresentation.conjugate_restrict, MatrixRepresentation.conjugate_pointMatrix,
      constantPoint_self, MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv]
    erw [hB]
    rw [inv_inv]
    rfl
  rw [hσ]
  simp only [Units.val_mul]
  rw [hτ s]
  have hPiP : ((P⁻¹ : GL n k) : Matrix n n k) * (P : Matrix n n k) = 1 := P.inv_val
  simp only [← Matrix.mul_assoc]
  rw [hPiP, Matrix.one_mul, Matrix.mul_assoc, hPiP, Matrix.mul_one]

/-- A representation which is diagonal at every rational torus point has a diagonal
universal matrix, and hence is diagonal on every test scheme. -/
theorem universal_diagonal (ρ : MatrixRepresentation T.toGrp n)
    [IsReduced T.X.left] [LocallyOfFiniteType T.X.hom]
    (hρ : ∀ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X,
      ∃ d : n → k, (ρ.rationalMatrix t : Matrix n n k) = diagonal d) :
    (ρ.pointMatrix T.X (𝟙 T.X) : Matrix n n Γ(T.X.left, ⊤)) =
      diagonal (fun i => ρ.pointMatrix T.X (𝟙 T.X) i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [diagonal_apply_ne _ hij]
    apply eq_of_rationalEval
    intro t
    obtain ⟨d, hd⟩ := hρ t
    have h := congrArg (fun M : GL n k => M i j) (map_rationalEval_pointMatrix ρ t)
    change rationalEval t _ = _ at h
    rw [hd, diagonal_apply_ne _ hij] at h
    simpa using h

omit [IsAlgClosed k] in
/-- The universal diagonal identity pulls back to every scheme-valued point. -/
theorem point_diagonal (ρ : MatrixRepresentation T.toGrp n)
    (d : n → Γ(T.X.left, ⊤))
    (hd : (ρ.pointMatrix T.X (𝟙 T.X) : Matrix n n Γ(T.X.left, ⊤)) = diagonal d)
    (Z : Over (Spec (CommRingCat.of k))) (y : Z ⟶ T.X) :
    (ρ.pointMatrix Z y : Matrix n n Γ(Z.left, ⊤)) =
      diagonal (fun i => y.left.appTop (d i)) := by
  have hy := ρ.pointMatrix_naturality y (𝟙 T.X)
  rw [Category.comp_id] at hy
  rw [hy]
  change (ρ.pointMatrix T.X (𝟙 T.X) : Matrix n n Γ(T.X.left, ⊤)).map
    y.left.appTop.hom = _
  rw [hd]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [diagonal_apply_ne _ hij]

omit [IsAlgClosed k] [DecidableEq n] in
/-- The basic open of the product of distinct diagonal differences is nonempty,
and all its rational points separate those differences. -/
theorem exists_separatingOpen [IsIntegral T.X.left] (d : n → Γ(T.X.left, ⊤)) :
    ∃ U : T.X.left.Opens, (U : Set T.X.left).Nonempty ∧
      ∀ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X,
        Set.range t.left ⊆ U → ∀ i j, d i ≠ d j →
          rationalEval t (d i - d j) ≠ 0 := by
  classical
  let f : n × n → Γ(T.X.left, ⊤) :=
    fun p => if d p.1 = d p.2 then 1 else d p.1 - d p.2
  let F : Γ(T.X.left, ⊤) := ∏ p, f p
  have hF : F ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p _
    dsimp [f]
    split_ifs with h
    · exact one_ne_zero
    · exact sub_ne_zero.mpr h
  refine ⟨T.X.left.basicOpen F, ?_, ?_⟩
  · apply (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp
    intro h
    exact hF ((basicOpen_eq_bot_iff F).mp h)
  · intro t ht i j hij he
    have hFeval : rationalEval t F = 0 := by
      change rationalEval t (∏ p, f p) = 0
      rw [map_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ (i, j))
      simpa [f, hij] using he
    have happ : t.left.appTop F = 0 := by
      apply (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective
      exact hFeval.trans (map_zero _).symm
    have hmem : IsLocalRing.closedPoint k ∈ t.left ⁻¹ᵁ T.X.left.basicOpen F :=
      ht ⟨IsLocalRing.closedPoint k, rfl⟩
    rw [Scheme.preimage_basicOpen_top, happ, Scheme.basicOpen_zero] at hmem
    exact hmem

omit [Field k] [IsAlgClosed k] in
/-- A matrix commuting with one diagonal matrix commutes with any diagonal
matrix whose unequal entries are separated by units in the first. -/
theorem commute_diagonal_of_units {A : Type u} [CommRing A]
    (M : Matrix n n A) (a b : n → A)
    (hsep : ∀ i j, b i = b j ∨ IsUnit (a i - a j))
    (hc : M * diagonal a = diagonal a * M) :
    M * diagonal b = diagonal b * M := by
  ext i j
  simp only [mul_diagonal, diagonal_mul]
  rcases hsep i j with h | h
  · rw [h, mul_comm]
  · have hij := congrArg (fun N : Matrix n n A => N i j) hc
    simp only [mul_diagonal, diagonal_mul] at hij
    have hz : (a i - a j) * M i j = 0 := by
      calc
        (a i - a j) * M i j = a i * M i j - M i j * a j := by ring
        _ = 0 := sub_eq_zero.mpr hij.symm
    have hzero := h.mul_right_eq_zero.mp hz
    rw [hzero, zero_mul, mul_zero]

omit [IsAlgClosed k] in
/-- A rational torus point separating the universal diagonal entries has
its all-test centralizer contained in the centralizer of the whole torus. -/
theorem mem_centralizer_of_separating
    (σ : MatrixRepresentation G n) [Mono σ.hom.hom] (j : T.toGrp ⟶ G)
    (d : n → Γ(T.X.left, ⊤))
    (hd : ((σ.restrict j).pointMatrix T.X (𝟙 T.X) : Matrix n n Γ(T.X.left, ⊤)) =
      diagonal d)
    (t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X)
    (hsep : ∀ i j, d i ≠ d j → rationalEval t (d i - d j) ≠ 0)
    {Z : Over (Spec (CommRingCat.of k))} (c : Z ⟶ G.X)
    (hc : c * (toUnit Z ≫ t ≫ j.hom.hom) = (toUnit Z ≫ t ≫ j.hom.hom) * c) :
    c ∈ (torusCentralizer j).carrier Z := by
  classical
  have hr : ((σ.restrict j).rationalMatrix t : Matrix n n k) =
      diagonal (fun i => rationalEval t (d i)) := by
    rw [← map_rationalEval_pointMatrix (σ.restrict j) t]
    change (((σ.restrict j).pointMatrix T.X (𝟙 T.X) : Matrix n n Γ(T.X.left, ⊤)).map
      (rationalEval t)) = _
    rw [hd]
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [diagonal_apply_ne _ hij]
  have htV (V : Over (Spec (CommRingCat.of k))) :
      (σ.pointMatrix V (toUnit V ≫ t ≫ j.hom.hom) : Matrix n n Γ(V.left, ⊤)) =
        diagonal (fun i => scalarMap V (rationalEval t (d i))) := by
    rw [← Category.assoc, ← MatrixRepresentation.pointMatrix_restrict,
      MatrixRepresentation.pointMatrix_constant]
    change (((σ.restrict j).rationalMatrix t : Matrix n n k).map (scalarMap V)) = _
    rw [hr]
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [diagonal_apply_ne _ hij]
  intro V a y
  apply σ.pointMatrix_injective V
  simp only [map_mul]
  apply Units.ext
  simp only [Units.val_mul]
  change (σ.pointMatrix V (a ≫ c) : Matrix n n Γ(V.left, ⊤)) *
      (σ.pointMatrix V (y ≫ j.hom.hom) : Matrix n n Γ(V.left, ⊤)) = _
  rw [← MatrixRepresentation.pointMatrix_restrict,
    point_diagonal (σ.restrict j) d hd V y]
  apply commute_diagonal_of_units _ (fun i => scalarMap V (rationalEval t (d i)))
  · intro i j
    by_cases hij : d i = d j
    · exact Or.inl (congrArg y.left.appTop hij)
    · right
      simpa only [map_sub] using
        (isUnit_iff_ne_zero.mpr (hsep i j hij)).map (scalarMap V)
  · have hca : (a ≫ c) * (toUnit V ≫ t ≫ j.hom.hom) =
        (toUnit V ≫ t ≫ j.hom.hom) * (a ≫ c) := by
      have h := congrArg (fun f => a ≫ f) hc
      simpa only [MonObj.comp_mul, ← Category.assoc, comp_toUnit] using h
    have hmat := congrArg (fun f => (σ.pointMatrix V f : Matrix n n Γ(V.left, ⊤))) hca
    simp only [map_mul, Units.val_mul] at hmat
    rw [htV] at hmat
    exact hmat

end StronglyRegularTorusPoint

/-- Strongly regular points form a nonempty open subset of a maximal torus
in a connected reductive group over an algebraically closed field. -/
theorem algClosedStronglyRegularTorusPoint :
    AlgClosedStronglyRegularTorusPointStatement.{u} := by
  classical
  intro k _ _ G hG T j hj
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : Smooth T.X.hom := hj.1.smooth
  have : IsIntegral T.X.left := hj.1.isIntegral
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : Mono ρ.hom.hom := Over.mono_of_mono_left _
  have hT : IsSplitTorus T.toGrp :=
    hj.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨σ, hσ, hdiag⟩ := StronglyRegularTorusPoint.exists_rationalDiagonal ρ j hT
  let : Mono σ.hom.hom := hσ
  let d : Fin N → Γ(T.X.left, ⊤) := fun i => (σ.restrict j).pointMatrix T.X (𝟙 T.X) i i
  have hd := StronglyRegularTorusPoint.universal_diagonal (σ.restrict j) hdiag
  obtain ⟨U, hUne, hUsep⟩ := StronglyRegularTorusPoint.exists_separatingOpen d
  refine ⟨U, U.isOpen, hUne, ?_⟩
  intro t ht Z c hc
  have hcT := StronglyRegularTorusPoint.mem_centralizer_of_separating σ j d hd t
    (hUsep t ht) c hc
  rw [algClosedMaximalTorusCentralizer_fromQuotient dynamicCentralizerReductive
    solvableTorusQuotient k G hG T j hj] at hcT
  exact SubgroupFunctor.mem_range.mp hcT

end Langlands.GroupScheme
