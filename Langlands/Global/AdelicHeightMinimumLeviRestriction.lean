import Langlands.Global.AdelicHeightChain
import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates
import Langlands.GroupScheme.Chevalley.UnipotentLine

/-! # Restricting actual height minima through a fixed right factor -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) {n : ℕ}

/-- Every point of the specified actual adelic subgroup fixes the principal vector
in the actual adelic representation. -/
def IsOrbitVectorFixedBy (ρ : MatrixRepresentation G (Fin n)) (v : Fin n → F)
    (N : Subgroup (AdelicGroupPoints F G)) : Prop :=
  ∀ x ∈ N, (adelicMatrix F G ρ x).val *ᵥ PrimitiveAdelicHeight.rational F n v =
    PrimitiveAdelicHeight.rational F n v

/-- Restricting the algebraic representation gives its actual adelic matrix
after the induced adelic-point map. -/
theorem adelicMatrix_restrict
    (H : GroupScheme (Spec (CommRingCat.of F))) (f : H ⟶ G)
    (ρ : MatrixRepresentation G (Fin n)) (h : AdelicGroupPoints F H) :
    adelicMatrix F H (ρ.restrict f) h = adelicMatrix F G ρ (map F H G f h) := by
  exact ρ.affineMatrix_restrict f (CommAlgCat.of F (Adeles F)) h

/-- The same actual vector height is computed before or after restriction. -/
theorem orbitHeight_restrict
    (H : GroupScheme (Spec (CommRingCat.of F))) (f : H ⟶ G)
    (ρ : MatrixRepresentation G (Fin n)) (v : Fin n → F)
    (h : AdelicGroupPoints F H) :
    orbitHeight F H (ρ.restrict f) v h =
      orbitHeight F G ρ v (map F H G f h) := by
  simp only [orbitHeight, adelicMatrix_restrict]

/-- All-test fixedness supplies fixedness on the actual adelic image. -/
theorem isOrbitVectorFixedBy_range_of_isFixedVector
    (U : GroupScheme (Spec (CommRingCat.of F))) (z : U ⟶ G)
    (ρ : MatrixRepresentation G (Fin n)) (v : Fin n → F)
    (hv : (ρ.restrict z).IsFixedVector v) :
    IsOrbitVectorFixedBy F G ρ v (map F U G z).toMonoidHom.range := by
  rintro x ⟨y, rfl⟩
  exact hv.affine (CommAlgCat.of F (Adeles F)) y

/-- An actual unipotent subgroup preserving a coordinate line fixes its principal
coordinate vector on the entire adelic image. -/
theorem isOrbitVectorFixedBy_range_of_isUnipotent
    (U : GroupScheme (Spec (CommRingCat.of F))) (z : U ⟶ G)
    (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hline : (ρ.restrict z).PreservesCoordinateLine j) (hU : IsUnipotent U) :
    IsOrbitVectorFixedBy F G ρ (Pi.single j 1)
      (map F U G z).toMonoidHom.range := by
  apply isOrbitVectorFixedBy_range_of_isFixedVector F G U z ρ (Pi.single j 1)
  intro T x
  have hs : (fun l => scalarMap T ((Pi.single j 1 : Fin n → F) l)) =
      (Pi.single j 1 : Fin n → Γ(T.left, ⊤)) := by
    funext l
    by_cases hlj : l = j <;> simp [hlj]
  rw [hs]
  exact (ρ.restrict z).fixed_coordinateLine_of_isUnipotent j hline hU T x

/-- A fixed right factor can be removed from the actual orbit height. -/
theorem orbitHeight_mul_eq_of_fixed
    (ρ : MatrixRepresentation G (Fin n)) (v : Fin n → F)
    (N : Subgroup (AdelicGroupPoints F G)) (hfix : IsOrbitVectorFixedBy F G ρ v N)
    (g x : AdelicGroupPoints F G) (hx : x ∈ N) :
    orbitHeight F G ρ v (g * x) = orbitHeight F G ρ v g := by
  simp only [orbitHeight, PrimitiveAdelicHeight.rationalHeight, map_mul,
    Units.val_mul, ← Matrix.mulVec_mulVec, hfix x hx]

/-- After a right translation normalizing the fixing subgroup, the intervening
fixed factor can still be removed. -/
theorem orbitHeight_mul_mul_eq_of_normalizer
    (ρ : MatrixRepresentation G (Fin n)) (v : Fin n → F)
    (N : Subgroup (AdelicGroupPoints F G)) (hfix : IsOrbitVectorFixedBy F G ρ v N)
    (g x q : AdelicGroupPoints F G) (hx : x ∈ N)
    (hq : q ∈ Subgroup.normalizer (N : Set (AdelicGroupPoints F G))) :
    orbitHeight F G ρ v (g * x * q) = orbitHeight F G ρ v (g * q) := by
  have hconj : q⁻¹ * x * q ∈ N :=
    (Subgroup.mem_normalizer_iff''.mp hq x).mp hx
  have heq : g * x * q = (g * q) * (q⁻¹ * x * q) := by group
  rw [heq, orbitHeight_mul_eq_of_fixed F G ρ v N hfix _ _ hconj]

/-- Ambient minimum inequalities descend to a chosen norm-one point of a subgroup
after removing a fixed right factor. The family can be restricted and reindexed,
and only the tested rational points must normalize the fixing subgroup. -/
theorem mem_chainHeightMinimalSet_restrict_of_fixed_factor
    (H : GroupScheme (Spec (CommRingCat.of F))) (f : H ⟶ G)
    (r s : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (v : (i : ℕ) → Fin (d i) → F)
    (Q : ℕ → Subgroup (RationalGroupPoints F G))
    (R : ℕ → Subgroup (RationalGroupPoints F H))
    (σ : ℕ → ℕ) (hσ : ∀ i, i < s → σ i < r)
    (N : Subgroup (AdelicGroupPoints F G))
    (hfix : ∀ i, i < s → IsOrbitVectorFixedBy F G (ρ (σ i)) (v (σ i)) N)
    (hQ : ∀ i, i < s → ∀ q : R i,
      H.affinePointsTarget f (CommAlgCat.of F F) q ∈ Q (σ i))
    (hnorm : ∀ i, i < s → ∀ q : R i,
      rational F G (H.affinePointsTarget f (CommAlgCat.of F F) q) ∈
        Subgroup.normalizer (N : Set (AdelicGroupPoints F G)))
    (c : ℝ) (h : normOneSubgroup F H) (x : AdelicGroupPoints F G) (hx : x ∈ N)
    (p : normOneSubgroup F G)
    (hp : (p : AdelicGroupPoints F G) = map F H G f h * x)
    (hmin : p ∈ chainHeightMinimalSet F G r d ρ v Q c) :
    h ∈ chainHeightMinimalSet F H s (fun i => d (σ i))
      (fun i => (ρ (σ i)).restrict f) (fun i => v (σ i)) R c := by
  intro i hi q
  let qG : Q (σ i) :=
    ⟨H.affinePointsTarget f (CommAlgCat.of F F) q, hQ i hi q⟩
  have hm := hmin (σ i) (hσ i hi) qG
  change orbitHeight F G (ρ (σ i)) (v (σ i)) (p : AdelicGroupPoints F G) ≤
    c * orbitHeight F G (ρ (σ i)) (v (σ i))
      ((p : AdelicGroupPoints F G) *
        rational F G (H.affinePointsTarget f (CommAlgCat.of F F) q)) at hm
  rw [hp, orbitHeight_mul_eq_of_fixed F G _ _ N (hfix i hi) _ _ hx,
    orbitHeight_mul_mul_eq_of_normalizer F G _ _ N (hfix i hi) _ _ _ hx
      (hnorm i hi q)] at hm
  have hnat :
      map F H G f (rational F H q) =
        rational F G (H.affinePointsTarget f (CommAlgCat.of F F) q) :=
    (DFunLike.congr_fun (rational_naturality F H f) (q : RationalGroupPoints F H)).symm
  simpa only [orbitHeight_restrict, map_mul, hnat] using hm

/-- For an actual unipotent subgroup, line preservation and normalization by the
actual adelic image of the restricting group discharge the fixed-factor premises. -/
theorem mem_chainHeightMinimalSet_restrict_of_unipotent_factor
    (H : GroupScheme (Spec (CommRingCat.of F))) (f : H ⟶ G)
    (U : GroupScheme (Spec (CommRingCat.of F))) (z : U ⟶ G) (hU : IsUnipotent U)
    (r s : ℕ) (d : ℕ → ℕ)
    (ρ : (i : ℕ) → MatrixRepresentation G (Fin (d i)))
    (j : (i : ℕ) → Fin (d i))
    (Q : ℕ → Subgroup (RationalGroupPoints F G))
    (R : ℕ → Subgroup (RationalGroupPoints F H))
    (σ : ℕ → ℕ) (hσ : ∀ i, i < s → σ i < r)
    (hline : ∀ i, i < s → ((ρ (σ i)).restrict z).PreservesCoordinateLine (j (σ i)))
    (hQ : ∀ i, i < s → ∀ q : R i,
      H.affinePointsTarget f (CommAlgCat.of F F) q ∈ Q (σ i))
    (hnorm : (map F H G f).toMonoidHom.range ≤
      Subgroup.normalizer ((map F U G z).toMonoidHom.range : Set (AdelicGroupPoints F G)))
    (c : ℝ) (h : normOneSubgroup F H) (x : AdelicGroupPoints F U)
    (p : normOneSubgroup F G)
    (hp : (p : AdelicGroupPoints F G) = map F H G f h * map F U G z x)
    (hmin : p ∈ chainHeightMinimalSet F G r d ρ (fun i => Pi.single (j i) 1) Q c) :
    h ∈ chainHeightMinimalSet F H s (fun i => d (σ i))
      (fun i => (ρ (σ i)).restrict f) (fun i => Pi.single (j (σ i)) 1) R c := by
  refine mem_chainHeightMinimalSet_restrict_of_fixed_factor F G H f r s d ρ
    (fun i => Pi.single (j i) 1) Q R σ hσ (map F U G z).toMonoidHom.range
    ?_ hQ ?_ c h (map F U G z x) ⟨x, rfl⟩ p hp hmin
  · intro i hi
    exact isOrbitVectorFixedBy_range_of_isUnipotent F G U z (ρ (σ i))
      (j (σ i)) (hline i hi) hU
  · intro i hi q
    apply hnorm
    refine ⟨rational F H q, ?_⟩
    exact (DFunLike.congr_fun (rational_naturality F H f)
      (q : RationalGroupPoints F H)).symm

end Langlands.Global.RepresentationGrowth
