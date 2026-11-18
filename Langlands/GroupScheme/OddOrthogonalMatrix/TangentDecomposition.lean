import Langlands.GroupScheme.OddOrthogonalMatrix.AffineSubgroupMatrices

/-! # Actual even and short factorization of odd identity tangent points -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

open GeneralLinear.DualNumber

variable {l : Type} [Fintype l] [DecidableEq l] (K : Type u) [Field K]

local notation "𝔻" => CommAlgCat.of (CommRingCat.of K) (DualNumber K)

omit [Fintype l] in
/-- The polynomial short family has the expected epsilon coefficient in
every characteristic. -/
theorem shortMatrix_epsilon (a : l ⊕ l) (c : K) :
    shortMatrix a (TrivSqZeroExt.inr c : DualNumber K) =
      1 + epsilonMatrix (c • shortVector a) := by
  have htwo : (2 : DualNumber K).fst = (2 : K) := rfl
  apply Matrix.ext
  intro i j
  simp only [shortMatrix, shortVector, Matrix.add_apply, Matrix.smul_apply,
    Matrix.single_apply, epsilonMatrix_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.snd_mul, htwo] <;> ring

/-- The actual short subgroup has precisely the short-family tangent matrix. -/
theorem affineMatrix_shortMap_epsilon (a : l ⊕ l) (c : K) :
    affineMatrix K 𝔻 (additiveAffinePoint K 𝔻 (TrivSqZeroExt.inr c) ≫ (shortMap K a).hom.hom) =
      matrixUnit (c • shortVector a) := by
  rw [affineMatrix_shortMap]
  apply Units.ext
  exact shortMatrix_epsilon K a c

/-- Prescribed additive affine coordinates commute with coefficient changes. -/
theorem additiveAffinePoint_naturality {A B : CommAlgCat.{u} (CommRingCat.of K)}
    (f : A ⟶ B) (c : A) :
    (algSpec (CommRingCat.of K)).map f.op ≫ additiveAffinePoint K A c =
      additiveAffinePoint K B (f.hom c) := by
  apply (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of K) 1)
    (VectorGroup.corepresentableBy (CommRingCat.of K) 1) B).injective
  rw [Corepresented.affinePointsEquiv_naturality]
  simp only [additiveAffinePoint, MulEquiv.apply_symm_apply]
  rfl

/-- Zero is the actual additive identity point. -/
theorem additiveAffinePoint_zero (A : CommAlgCat.{u} (CommRingCat.of K)) :
    additiveAffinePoint K A 0 = 1 := by
  change (Corepresented.affinePointsEquiv (VectorGroup.functor (CommRingCat.of K) 1)
    (VectorGroup.corepresentableBy (CommRingCat.of K) 1) A).symm 1 = 1
  exact MulEquiv.map_one _

/-- The additive epsilon-parameter point reduces to the identity. -/
theorem additiveAffinePoint_epsilon_reduction (c : K) :
    (algSpec (CommRingCat.of K)).map
      (CommAlgCat.ofHom (TrivSqZeroExt.fstHom K K K)).op ≫
        additiveAffinePoint K 𝔻 (TrivSqZeroExt.inr c) = 1 := by
  rw [additiveAffinePoint_naturality]
  exact additiveAffinePoint_zero K _

/-- The even block of an odd tangent coefficient defines an actual dual-number
even orthogonal point. -/
def evenTangentPoint (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    (algSpec (CommRingCat.of K)).obj (op 𝔻) ⟶
      (OrthogonalMatrix.groupScheme l (CommRingCat.of K)).X :=
  (OrthogonalMatrix.affinePointsEquiv l (CommRingCat.of K) 𝔻).symm
    ⟨1 + epsilonMatrix (evenPart Y),
      (OrthogonalMatrix.one_add_epsilonMatrix_mem_iff (evenPart Y)).2
        (isAlt_evenPart_lieDefect ((mem_lieMatrices_iff Y).1 hY).1)⟩

/-- The prescribed matrix of the even tangent point. -/
theorem evenTangentPoint_matrix (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    (OrthogonalMatrix.affinePointsEquiv l (CommRingCat.of K) 𝔻 (evenTangentPoint K Y hY) :
      Matrix (l ⊕ l) (l ⊕ l) (DualNumber K)) = 1 + epsilonMatrix (evenPart Y) := by
  exact congrArg (fun g : OrthogonalMatrix.orthogonalGroup l (DualNumber K) =>
    (g : Matrix (l ⊕ l) (l ⊕ l) (DualNumber K)))
      ((OrthogonalMatrix.affinePointsEquiv l (CommRingCat.of K) 𝔻).apply_symm_apply _)

/-- The image of the even tangent point is the embedded even coefficient matrix;
the determinant correction has zero epsilon coefficient. -/
theorem affineMatrix_evenTangentPoint (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    affineMatrix K 𝔻 (evenTangentPoint K Y hY ≫ (evenMap K).hom.hom) =
      matrixUnit (evenEmbed (evenPart Y)) := by
  rw [affineMatrix_evenMap]
  apply Units.ext
  change evenBlock (OrthogonalMatrix.affinePointsEquiv l (CommRingCat.of K) 𝔻
    (evenTangentPoint K Y hY)) = 1 + epsilonMatrix (evenEmbed (evenPart Y))
  have ht := trace_evenPart_eq_zero ((mem_lieMatrices_iff Y).1 hY).1
  unfold evenBlock
  rw [evenTangentPoint_matrix, SpecialLinear.det_one_add_epsilonMatrix, ht,
    TrivSqZeroExt.inr_zero, add_zero]
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [evenEmbed, epsilonMatrix_apply, Matrix.one_apply]

/-- The even tangent point reduces to the identity. -/
theorem evenTangentPoint_reduction (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    (algSpec (CommRingCat.of K)).map
      (CommAlgCat.ofHom (TrivSqZeroExt.fstHom K K K)).op ≫ evenTangentPoint K Y hY = 1 := by
  apply (OrthogonalMatrix.affinePointsEquiv l (CommRingCat.of K)
    (CommAlgCat.of (CommRingCat.of K) K)).injective
  change Corepresented.affinePointsEquiv (OrthogonalMatrix.functor l (CommRingCat.of K))
    (OrthogonalMatrix.corepresentableBy l (CommRingCat.of K)) _ _ = _
  rw [Corepresented.affinePointsEquiv_naturality,
    (OrthogonalMatrix.affinePointsEquiv l (CommRingCat.of K)
      (CommAlgCat.of (CommRingCat.of K) K)).map_one]
  apply Subtype.ext
  change (OrthogonalMatrix.affinePointsEquiv l (CommRingCat.of K) 𝔻
    (evenTangentPoint K Y hY) : Matrix (l ⊕ l) (l ⊕ l) (DualNumber K)).map
      (TrivSqZeroExt.fstHom K K K).toRingHom = _
  rw [evenTangentPoint_matrix]
  ext i j
  by_cases hij : i = j <;> simp [hij]

private theorem matrixUnit_list_prod {I : Type*} (s : List I)
    (f : I → Matrix (Index l) (Index l) K) :
    (s.map (fun i => matrixUnit (f i))).prod = matrixUnit ((s.map f).sum) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    rw [List.map_cons, List.prod_cons, ih, ← matrixUnit_add, List.map_cons, List.sum_cons]

/-- Every actual normalized tangent point factors as an even tangent image and
one short tangent image per signed coordinate. -/
theorem tangentPoint_factorization (Y : Matrix (Index l) (Index l) K) (hY : Y ∈ lieMatrices) :
    tangentPoint K Y hY =
      (evenTangentPoint K Y hY ≫ (evenMap K).hom.hom) *
        ((Finset.univ.toList : List (l ⊕ l)).map (fun a =>
          additiveAffinePoint K 𝔻 (TrivSqZeroExt.inr (Y (Sum.inr a) (Sum.inl ()))) ≫
            (shortMap K a.swap).hom.hom)).prod := by
  have hs :
      ((Finset.univ.toList : List (l ⊕ l)).map (fun a =>
        affineMatrix K 𝔻
          (additiveAffinePoint K 𝔻 (TrivSqZeroExt.inr (Y (Sum.inr a) (Sum.inl ()))) ≫
            (shortMap K a.swap).hom.hom))).prod =
      ((Finset.univ.toList : List (l ⊕ l)).map (fun a =>
        matrixUnit (Y (Sum.inr a) (Sum.inl ()) • shortVector a.swap))).prod := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro a _
    exact affineMatrix_shortMap_epsilon K a.swap _
  apply affineMatrix_injective K 𝔻
  rw [affineMatrix_tangentPoint, (affineMatrix K 𝔻).map_mul,
    affineMatrix_evenTangentPoint, map_list_prod, List.map_map]
  change matrixUnit Y = matrixUnit (evenEmbed (evenPart Y)) *
    ((Finset.univ.toList : List (l ⊕ l)).map (fun a =>
        affineMatrix K 𝔻
          (additiveAffinePoint K 𝔻 (TrivSqZeroExt.inr (Y (Sum.inr a) (Sum.inl ()))) ≫
            (shortMap K a.swap).hom.hom))).prod
  rw [hs, matrixUnit_list_prod, ← matrixUnit_add]
  congr 1
  simpa using lieMatrix_decomposition hY

/-- An arbitrary actual identity tangent point is the constructed point of its
unique coefficient matrix. -/
theorem tangentPoint_coefficient (x : lieKernel (groupScheme l K) K) :
    tangentPoint K (tangentCoefficient K x) (tangentCoefficient_mem K x) = x.val := by
  apply affineMatrix_injective K 𝔻
  rw [affineMatrix_tangentPoint]
  exact matrixUnit_tangentCoefficient K x

end Langlands.GroupScheme.OddOrthogonalMatrix
