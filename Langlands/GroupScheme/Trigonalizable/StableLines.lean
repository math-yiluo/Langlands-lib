import Langlands.GroupScheme.Trigonalizable
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation

/-! # Stable lines and stable subspaces of matrix representations

A stable line in the sense of `IsStableLine` is tested on points with values in every scheme,
while `IsStableSubspace` is tested on affine points through linear functionals. For affine
groups over a field the two notions agree for the line spanned by a vector. This module also
transports stable lines along intertwiners and restrictions, and extracts the vanishing of
matrix coefficients from a stable subspace on every scheme test.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A stable line gives the corresponding eigenvector equation at every affine point, with
the multiplier in the test algebra itself. -/
theorem IsStableLine.affine {ρ : MatrixRepresentation G n} {v : n → k}
    (hv : ρ.IsStableLine v) (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) :
    ∃ c : A, (ρ.affineMatrix A x : Matrix n n A) *ᵥ (fun i => algebraMap k A (v i)) =
      c • fun i => algebraMap k A (v i) := by
  obtain ⟨c, hc⟩ := hv _ x
  let e := Corepresented.affineSectionsAlgEquiv A
  refine ⟨e c, ?_⟩
  rw [pointMatrix_eq_affineMatrix] at hc
  have hs (r : k) : scalarMap ((algSpec (CommRingCat.of k)).obj (op A)) r =
      e.symm (algebraMap k A r) := UnipotentMatrixCriterion.scalarMap_affine A r
  simp only [hs] at hc
  funext i
  apply e.symm.injective
  refine (e.symm.toRingHom.map_mulVec _ _ i).trans ((congrFun hc i).trans ?_)
  show _ = e.symm (e c * algebraMap k A (v i))
  rw [map_mul]
  exact congrArg (fun z => z * e.symm (algebraMap k A (v i))) (e.symm_apply_apply c).symm

/-- The line spanned by a vector spanning a stable line is a stable subspace. -/
theorem IsStableLine.isStableSubspace {ρ : MatrixRepresentation G n} {v : n → k}
    (hv : ρ.IsStableLine v) : ρ.IsStableSubspace (k ∙ v) := by
  intro A x w hw ℓ
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  obtain ⟨c, hc⟩ := hv.affine A x
  have hs (t : k) (b : A) : ℓ (algebraMap k A t * b) = t * ℓ b := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hav : (fun i => algebraMap k A ((a • v) i)) =
      algebraMap k A a • fun i => algebraMap k A (v i) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [hav, Matrix.mulVec_smul, hc]
  refine Submodule.mem_span_singleton.mpr ⟨a * ℓ c, ?_⟩
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show algebraMap k A a * (c * algebraMap k A (v i)) =
      algebraMap k A (a * v i) * c by rw [map_mul]; ring, hs]
  ring

/-- For an affine group, a vector whose span is a stable subspace spans a stable line on
every scheme test. -/
theorem isStableLine_of_isStableSubspace [IsAffineHom G.X.hom]
    {ρ : MatrixRepresentation G n} {v : n → k} (h : ρ.IsStableSubspace (k ∙ v)) :
    ρ.IsStableLine v := by
  classical
  by_cases hv : v = 0
  · subst hv
    intro T g
    refine ⟨0, ?_⟩
    simp only [Pi.zero_apply, map_zero, zero_smul]
    exact Matrix.mulVec_zero _
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext hcon)
  let B : Matrix n Unit k := fun i _ => v i
  let C : Matrix Unit n k := fun _ i => if i = i₀ then (v i₀)⁻¹ else 0
  have hCv : C *ᵥ v = fun _ => 1 := by
    funext u
    simp [C, Matrix.mulVec, dotProduct, hi₀]
  have hBc (c : k) : B *ᵥ (fun _ => c) = c • v := by
    funext i
    simp [B, Matrix.mulVec, dotProduct, mul_comm]
  have hcols : ∀ j, (fun i => B i j) ∈ k ∙ v := fun _ => Submodule.mem_span_singleton_self v
  have hproj : ∀ w, w ∈ k ∙ v → (B * C) *ᵥ w = w := by
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hCv, hBc, one_smul]
  have hst := h.isStableCoordinates B C hcols hproj
  intro T g
  set M := (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) with hM
  set c := (C.map (scalarMap T) * M * B.map (scalarMap T)) () () with hc
  refine ⟨c, ?_⟩
  have key : M * B.map (scalarMap T) =
      B.map (scalarMap T) * Matrix.of (fun (_ : Unit) (_ : Unit) => c) := by
    rw [hst T g]
    congr 1
  have hvT : (fun i => scalarMap T (v i)) = B.map (scalarMap T) *ᵥ (fun _ => 1) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.univ_unique, Finset.sum_singleton, mul_one]
    rfl
  have hcT : Matrix.of (fun (_ : Unit) (_ : Unit) => c) *ᵥ (fun _ => (1 : Γ(T.left, ⊤))) =
      c • fun _ => 1 := by
    funext u
    simp [Matrix.mulVec, dotProduct]
  rw [hvT, Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, hcT, Matrix.mulVec_smul]

/-- For an affine group, a vector spans a stable line exactly when its span is stable. -/
theorem isStableLine_iff_isStableSubspace [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G n) (v : n → k) :
    ρ.IsStableLine v ↔ ρ.IsStableSubspace (k ∙ v) :=
  ⟨IsStableLine.isStableSubspace, isStableLine_of_isStableSubspace⟩

/-- A stable line stays stable after restriction along a homomorphism. -/
theorem IsStableLine.restrict {ρ : MatrixRepresentation G n} {v : n → k}
    (hv : ρ.IsStableLine v) (f : H ⟶ G) : (ρ.restrict f).IsStableLine v := by
  intro T g
  rw [pointMatrix_restrict]
  exact hv T (g ≫ f.hom.hom)

/-- A coordinate map intertwining two representations on every scheme test carries stable
lines to stable lines. -/
theorem IsStableLine.of_intertwines {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {B : Matrix n m k}
    (hB : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) * B.map (scalarMap T) =
        B.map (scalarMap T) * (σ.pointMatrix T x : Matrix m m Γ(T.left, ⊤)))
    {v : m → k} (hv : σ.IsStableLine v) : ρ.IsStableLine (B *ᵥ v) := by
  intro T x
  obtain ⟨c, hc⟩ := hv T x
  refine ⟨c, ?_⟩
  have hmap : (fun i => scalarMap T ((B *ᵥ v) i)) =
      B.map (scalarMap T) *ᵥ fun i => scalarMap T (v i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  rw [hmap, Matrix.mulVec_mulVec, hB T x, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]

omit [Fintype m] [DecidableEq m] in
/-- A stable subspace controls the action on every scheme test: a matrix of linear functionals
vanishing on the subspace kills the image of each of its vectors. -/
theorem IsStableSubspace.mulVec_pointMatrix_eq_zero [IsAffineHom G.X.hom]
    {ρ : MatrixRepresentation G n} {V : Submodule k (n → k)} (hV : ρ.IsStableSubspace V)
    (φ : Matrix m n k) (hφ : ∀ w ∈ V, φ *ᵥ w = 0) {v : n → k} (hv : v ∈ V)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    φ.map (scalarMap T) *ᵥ ((ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
      fun i => scalarMap T (v i)) = 0 := by
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates V
  have hst := hV.isStableCoordinates B C hcols hproj
  have hφB : φ * B = 0 := by
    ext i j
    exact congrFun (hφ _ (hcols j)) i
  have hvT : (fun i => scalarMap T (v i)) =
      B.map (scalarMap T) *ᵥ (fun j => scalarMap T ((C *ᵥ v) j)) := by
    funext i
    refine Eq.trans ?_ (RingHom.map_mulVec (scalarMap T) B (C *ᵥ v) i)
    rw [Matrix.mulVec_mulVec, hproj v hv]
  rw [hvT, Matrix.mulVec_mulVec _ _ (B.map (scalarMap T)), hst T x, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec _ (φ.map (scalarMap T)), ← Matrix.map_mul, hφB,
    Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]

end Langlands.GroupScheme.MatrixRepresentation
