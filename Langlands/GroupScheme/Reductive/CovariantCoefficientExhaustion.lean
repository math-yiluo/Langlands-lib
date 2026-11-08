import Langlands.GroupScheme.Reductive.EigenMatrixCoefficient
import Langlands.GroupScheme.Reductive.CovariantSocleIrreducible
import Langlands.GroupScheme.MatrixRepresentation.RationalIrreducibility

/-! # Exhausting covariant coordinates by a fixed matrix-coefficient row -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Module
open scoped Matrix CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace AffineCoordinates

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

local instance covariantCoefficientExhaustionIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Fixing the covector makes the original matrix coefficient linear in the vector. -/
def matrixCoefficientLinearMap (ρ : MatrixRepresentation G n) (ξ : n → k) :
    (n → k) →ₗ[k] algebra G where
  toFun v := matrixCoefficient G ρ ξ v
  map_add' v w := by
    apply (globalAlgEquiv G).injective
    simp only [matrixCoefficient, map_add, AlgEquiv.apply_symm_apply]
    simp only [coefficientValue, Pi.add_apply, map_add]
    change _ ⬝ᵥ (_ *ᵥ ((fun b => scalarMap G.X (v b)) +
      (fun b => scalarMap G.X (w b)))) = _
    rw [Matrix.mulVec_add, dotProduct_add]
  map_smul' c v := by
    apply (globalAlgEquiv G).injective
    simp only [matrixCoefficient, map_smul, AlgEquiv.apply_symm_apply]
    simp only [coefficientValue, Pi.smul_apply, smul_eq_mul, map_mul]
    change _ ⬝ᵥ (_ *ᵥ (scalarMap G.X c • (fun b => scalarMap G.X (v b)))) = _
    rw [Matrix.mulVec_smul, dotProduct_smul]
    rfl

@[simp]
theorem matrixCoefficientLinearMap_apply (ρ : MatrixRepresentation G n) (ξ v : n → k) :
    matrixCoefficientLinearMap G ρ ξ v = matrixCoefficient G ρ ξ v := rfl

/-- Acting on the source vector is right translation by the constant rational point,
on every original relative scheme test. -/
theorem pointAlgebraHom_matrixCoefficient_rationalRepresentation
    (ρ : MatrixRepresentation G n) (ξ v : n → k)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    pointAlgebraHom G T g
        (matrixCoefficient G ρ ξ (ρ.rationalRepresentation a v)) =
      pointAlgebraHom G T
        (g * (CartesianMonoidalCategory.toUnit T ≫ a)) (matrixCoefficient G ρ ξ v) := by
  rw [pointAlgebraHom_matrixCoefficient, pointAlgebraHom_matrixCoefficient,
    coefficientValue, coefficientValue, map_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, MatrixRepresentation.pointMatrix_constant]
  congr 2
  funext i
  exact (scalarMap T).map_mulVec (ρ.rationalMatrix a : Matrix n n k) v i

/-- The kernel of a fixed-row coefficient map is a rational-point subrepresentation. -/
def matrixCoefficientKernel (ρ : MatrixRepresentation G n) (ξ : n → k) :
    Subrepresentation ρ.rationalRepresentation where
  toSubmodule := LinearMap.ker (matrixCoefficientLinearMap G ρ ξ)
  apply_mem_toSubmodule a v hv := by
    change matrixCoefficientLinearMap G ρ ξ (ρ.rationalRepresentation a v) = 0
    apply (globalAlgEquiv G).injective
    change pointAlgebraHom G G.X (𝟙 G.X)
      (matrixCoefficient G ρ ξ (ρ.rationalRepresentation a v)) = _
    rw [pointAlgebraHom_matrixCoefficient_rationalRepresentation]
    change pointAlgebraHom G G.X _ (matrixCoefficientLinearMap G ρ ξ v) = _
    rw [LinearMap.mem_ker.mp hv, map_zero, map_zero]

/-- A nonzero covector defines a nonzero coefficient map. -/
theorem matrixCoefficientLinearMap_ne_zero (ρ : MatrixRepresentation G n)
    {ξ : n → k} (hξ : ξ ≠ 0) :
    matrixCoefficientLinearMap G ρ ξ ≠ 0 := by
  intro hC
  apply hξ
  funext i
  have he := congrArg
    (pointAlgebraHom G (Over.mk (𝟙 (Spec (CommRingCat.of k)))) 1)
      (LinearMap.congr_fun hC (Pi.single i 1))
  rw [matrixCoefficientLinearMap_apply, pointAlgebraHom_matrixCoefficient,
    coefficientValue_one, LinearMap.zero_apply, map_zero] at he
  have hscalar : scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))) (ξ i) = 0 := by
    simpa only [dotProduct_single_one] using he
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom hscalar
  simpa [scalarMap] using h

/-- Rational-point irreducibility and a nonzero fixed row make the coefficient map injective. -/
theorem matrixCoefficientLinearMap_injective (ρ : MatrixRepresentation G n)
    (hρ : ρ.rationalRepresentation.IsIrreducible) {ξ : n → k} (hξ : ξ ≠ 0) :
    Function.Injective (matrixCoefficientLinearMap G ρ ξ) := by
  let := hρ
  rcases eq_bot_or_eq_top (matrixCoefficientKernel G ρ ξ) with h | h
  · apply LinearMap.ker_eq_bot.mp
    exact congrArg Subrepresentation.toSubmodule h
  · have hk : LinearMap.ker (matrixCoefficientLinearMap G ρ ξ) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    exact False.elim (matrixCoefficientLinearMap_ne_zero G ρ hξ
      (LinearMap.ker_eq_top.mp hk))

section Covariant

variable {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

local instance covariantCoefficientExhaustionIsAffine2 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

variable (ρ : MatrixRepresentation G n) (ξ : n → k) (i : H ⟶ G) (χ : algebra H)
  (hξ : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X),
    (fun a => scalarMap T (ξ a)) ᵥ*
        (ρ.pointMatrix T (h ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) =
      pointValue H T h χ • fun a => scalarMap T (ξ a))

/-- The coefficient map with an eigen-row has codomain the entire covariant subspace. -/
def covariantCoefficientLinearMap : (n → k) →ₗ[k] leftCovariantSubspace i χ :=
  (matrixCoefficientLinearMap G ρ ξ).codRestrict (leftCovariantSubspace i χ)
    (fun v => matrixCoefficient_mem_leftCovariantSubspace ρ ξ v i χ hξ)

@[simp]
theorem covariantCoefficientLinearMap_coe (v : n → k) :
    (covariantCoefficientLinearMap G ρ ξ i χ hξ v : algebra G) =
      matrixCoefficient G ρ ξ v := rfl

/-- The restricted coefficient map remains injective. -/
theorem covariantCoefficientLinearMap_injective
    (hρ : ρ.rationalRepresentation.IsIrreducible) (hξ0 : ξ ≠ 0) :
    Function.Injective (covariantCoefficientLinearMap G ρ ξ i χ hξ) := by
  intro v w he
  exact matrixCoefficientLinearMap_injective G ρ hρ hξ0 (congrArg Subtype.val he)

/-- An independent upper bound on the whole covariant space and lower bound on the
source force coefficient exhaustion. -/
theorem covariantCoefficientLinearMap_bijective
    [Module.Finite k (leftCovariantSubspace i χ)]
    (hρ : ρ.rationalRepresentation.IsIrreducible) (hξ0 : ξ ≠ 0)
    (D : ℕ) (hlower : D ≤ Module.finrank k (n → k))
    (hupper : Module.finrank k (leftCovariantSubspace i χ) ≤ D) :
    Function.Bijective (covariantCoefficientLinearMap G ρ ξ i χ hξ) := by
  have hinj := covariantCoefficientLinearMap_injective G ρ ξ i χ hξ hρ hξ0
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have heq : Module.finrank k (n → k) =
      Module.finrank k (leftCovariantSubspace i χ) :=
    le_antisymm hle (hupper.trans hlower)
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hinj⟩

include hξ in
/-- Every original covariant coordinate is a coefficient with the same fixed row. -/
theorem exists_matrixCoefficient_of_finrank_bounds
    [Module.Finite k (leftCovariantSubspace i χ)]
    (hρ : ρ.rationalRepresentation.IsIrreducible) (hξ0 : ξ ≠ 0)
    (D : ℕ) (hlower : D ≤ Module.finrank k (n → k))
    (hupper : Module.finrank k (leftCovariantSubspace i χ) ≤ D)
    {f : algebra G} (hf : f ∈ leftCovariantSubspace i χ) :
    ∃ v : n → k, matrixCoefficient G ρ ξ v = f := by
  obtain ⟨v, hv⟩ :=
    (covariantCoefficientLinearMap_bijective G ρ ξ i χ hξ hρ hξ0 D hlower hupper).2 ⟨f, hf⟩
  exact ⟨v, congrArg Subtype.val hv⟩

end Covariant

end AffineCoordinates

namespace Chevalley

open AffineCoordinates AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance covariantCoefficientExhaustionIsAffine3 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable (V : Submodule k (algebra G)) {d : ℕ} (b : Basis (Fin d) k V)
  (hV : letI := (bialgebra (corepresentation G)).toCoalgebra
    ∀ (ψ : Module.Dual k (algebra G)) (w : algebra G),
      w ∈ V → rightAct ψ w ∈ V)

/-- The rational regular action is right translation on every relative test scheme. -/
theorem pointAlgebraHom_affineRegularCoordinateMap_rationalRepresentation
    (v : Fin d → k) (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    pointAlgebraHom G T g (affineRegularCoordinateMap G V b
        ((affineRegularRepresentation G V b hV).rationalRepresentation a v)) =
      pointAlgebraHom G T (g * (CartesianMonoidalCategory.toUnit T ≫ a))
        (affineRegularCoordinateMap G V b v) := by
  rw [pointAlgebraHom_affineRegularCoordinateMap_mul G V b hV,
    affineRegularCoordinateMap_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, Algebra.smul_def, mul_comm,
    MatrixRepresentation.pointMatrix_constant]
  congr 1
  exact (scalarMap T).map_mulVec
    ((affineRegularRepresentation G V b hV).rationalMatrix a : Matrix (Fin d) (Fin d) k) v i

end Chevalley

namespace AffineCoordinates

open Chevalley AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

local instance covariantCoefficientExhaustionIsAffine4 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance covariantCoefficientExhaustionIsAffine5 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

variable (ρ : MatrixRepresentation G n) (ξ : n → k) (i : H ⟶ G) (χ : algebra H)
  (hξ : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X),
    (fun a => scalarMap T (ξ a)) ᵥ*
        (ρ.pointMatrix T (h ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) =
      pointValue H T h χ • fun a => scalarMap T (ξ a))
  {d : ℕ} (b : Basis (Fin d) k (leftCovariantSubspace i χ))

/-- Matrix-coefficient vectors in any basis of the full covariant space. -/
def covariantCoefficientBasisMap : (n → k) →ₗ[k] (Fin d → k) :=
  b.equivFun.toLinearMap.comp (covariantCoefficientLinearMap G ρ ξ i χ hξ)

/-- The basis map represents the original coefficient coordinate. -/
theorem affineRegularCoordinateMap_covariantCoefficientBasisMap (v : n → k) :
    affineRegularCoordinateMap G (leftCovariantSubspace i χ) b
        (covariantCoefficientBasisMap G ρ ξ i χ hξ b v) =
      matrixCoefficient G ρ ξ v := by
  change ((b.equivFun.symm
    (b.equivFun (covariantCoefficientLinearMap G ρ ξ i χ hξ v)) :
      leftCovariantSubspace i χ) : algebra G) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The original coefficient map intertwines the two rational-point actions. -/
theorem covariantCoefficientBasisMap_rationalRepresentation
    (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (v : n → k) :
    covariantCoefficientBasisMap G ρ ξ i χ hξ b (ρ.rationalRepresentation a v) =
      (affineRegularRepresentation G (leftCovariantSubspace i χ) b
        (fun ψ _ hw => rightAct_mem_leftCovariantSubspace i χ ψ hw)).rationalRepresentation a
          (covariantCoefficientBasisMap G ρ ξ i χ hξ b v) := by
  apply affineRegularCoordinateMap_injective G (leftCovariantSubspace i χ) b
  apply (globalAlgEquiv G).injective
  change pointAlgebraHom G G.X (𝟙 G.X) _ = pointAlgebraHom G G.X (𝟙 G.X) _
  rw [affineRegularCoordinateMap_covariantCoefficientBasisMap,
    pointAlgebraHom_matrixCoefficient_rationalRepresentation,
    pointAlgebraHom_affineRegularCoordinateMap_rationalRepresentation,
    affineRegularCoordinateMap_covariantCoefficientBasisMap]

/-- Matching whole-space dimension bounds identify every regular basis with the source. -/
theorem covariantCoefficientBasisMap_bijective
    (hρ : ρ.rationalRepresentation.IsIrreducible) (hξ0 : ξ ≠ 0)
    (D : ℕ) (hlower : D ≤ Module.finrank k (n → k))
    (hupper : Module.finrank k (leftCovariantSubspace i χ) ≤ D) :
    Function.Bijective (covariantCoefficientBasisMap G ρ ξ i χ hξ b) := by
  let := Module.Finite.of_basis b
  exact b.equivFun.bijective.comp
    (covariantCoefficientLinearMap_bijective G ρ ξ i χ hξ hρ hξ0 D hlower hupper)

include hξ in
/-- Coefficient exhaustion transfers rational irreducibility to the entire induced space
with any actual regular basis. -/
theorem affineRegularRepresentation_rationalRepresentation_isIrreducible_of_coefficient_bounds
    (hρ : ρ.rationalRepresentation.IsIrreducible) (hξ0 : ξ ≠ 0)
    (D : ℕ) (hlower : D ≤ Module.finrank k (n → k))
    (hupper : Module.finrank k (leftCovariantSubspace i χ) ≤ D) :
    (affineRegularRepresentation G (leftCovariantSubspace i χ) b
      (fun ψ _ hw => rightAct_mem_leftCovariantSubspace i χ ψ hw)).rationalRepresentation.IsIrreducible := by
  let σ := affineRegularRepresentation G (leftCovariantSubspace i χ) b
    (fun ψ _ hw => rightAct_mem_leftCovariantSubspace i χ ψ hw)
  let C := covariantCoefficientBasisMap G ρ ξ i χ hξ b
  have hC : Function.Bijective C :=
    covariantCoefficientBasisMap_bijective G ρ ξ i χ hξ b hρ hξ0 D hlower hupper
  have hact (a) (v) : C (ρ.rationalRepresentation a v) = σ.rationalRepresentation a (C v) :=
    covariantCoefficientBasisMap_rationalRepresentation G ρ ξ i χ hξ b a v
  let := hρ
  let := (isIrreducible_of_rationalRepresentation ρ hρ).1
  have : Nontrivial (Fin d → k) := hC.1.nontrivial
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro he
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
  · intro W
    let P : Subrepresentation ρ.rationalRepresentation :=
      { toSubmodule := W.toSubmodule.comap C
        apply_mem_toSubmodule := fun a v hv => by
          change C (ρ.rationalRepresentation a v) ∈ W
          rw [hact]
          exact W.apply_mem_toSubmodule a hv }
    rcases eq_bot_or_eq_top P with he | he
    · left
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm _ bot_le
      intro w hw
      obtain ⟨v, rfl⟩ := hC.2 w
      have hv : v ∈ P := hw
      rw [he] at hv
      change v = 0 at hv
      simp [hv]
    · right
      apply Subrepresentation.toSubmodule_injective
      apply top_unique
      intro w _
      obtain ⟨v, rfl⟩ := hC.2 w
      have hv : v ∈ P := by rw [he]; trivial
      exact hv

include hξ in
/-- The full regular representation is irreducible on all affine tests after coefficient
exhaustion; the hypotheses impose no reducedness restriction on those tests. -/
theorem affineRegularRepresentation_isIrreducible_of_coefficient_bounds
    (hρ : ρ.rationalRepresentation.IsIrreducible) (hξ0 : ξ ≠ 0)
    (D : ℕ) (hlower : D ≤ Module.finrank k (n → k))
    (hupper : Module.finrank k (leftCovariantSubspace i χ) ≤ D) :
    (affineRegularRepresentation G (leftCovariantSubspace i χ) b
      (fun ψ _ hw => rightAct_mem_leftCovariantSubspace i χ ψ hw)).IsIrreducible :=
  isIrreducible_of_rationalRepresentation _
    (affineRegularRepresentation_rationalRepresentation_isIrreducible_of_coefficient_bounds
      G ρ ξ i χ hξ b hρ hξ0 D hlower hupper)

end AffineCoordinates

end Langlands.GroupScheme
