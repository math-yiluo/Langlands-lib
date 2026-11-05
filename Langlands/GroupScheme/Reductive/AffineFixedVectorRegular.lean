import Langlands.GroupScheme.Reductive.FixedVectorRegularCoefficient
import Langlands.GroupScheme.AffineCorepresented

/-! # Normalized regular maps for arbitrary affine group schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- An affine-test intertwiner for an affine group intertwines on every scheme test. -/
theorem Intertwines.points {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    {C : Matrix m n k} (hC : Intertwines ρ σ C)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    C.map (scalarMap T) * (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) =
      (σ.pointMatrix T g : Matrix m m Γ(T.left, ⊤)) * C.map (scalarMap T) := by
  obtain ⟨⟨A⟩, ⟨j⟩⟩ := (essImage_algSpec (G := G.X)).mpr inferInstance
  let f : A →+* Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) :=
    (Corepresented.affineSectionsIso A).inv.hom.toRingHom
  have h₀ := congrArg (fun M : Matrix m n A => M.map f) (hC A j.hom)
  simp only [Matrix.map_mul, Matrix.map_map] at h₀
  have hC₀ : C.map (f ∘ algebraMap k A) =
      C.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) := by
    ext r s
    exact (UnipotentMatrixCriterion.scalarMap_affine A _).symm
  rw [hC₀] at h₀
  have h₁ : C.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) *
      (ρ.pointMatrix ((algSpec (CommRingCat.of k)).obj (op A)) j.hom : Matrix n n Γ(_, ⊤)) =
      (σ.pointMatrix ((algSpec (CommRingCat.of k)).obj (op A)) j.hom : Matrix m m Γ(_, ⊤)) *
        C.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) := by
    rw [pointMatrix_eq_affineMatrix, pointMatrix_eq_affineMatrix]
    exact h₀
  let a := g ≫ j.inv
  have h₂ := congrArg (fun M : Matrix m n
      Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤) =>
        M.map a.left.appTop.hom) h₁
  simp only [Matrix.map_mul, Matrix.map_map] at h₂
  have hC₁ : C.map (a.left.appTop.hom ∘
      scalarMap ((algSpec (CommRingCat.of k)).obj (op A))) = C.map (scalarMap T) := by
    ext r s
    exact scalarMap_naturality a _
  rw [hC₁] at h₂
  have hρ := ρ.pointMatrix_naturality a j.hom
  have hσ := σ.pointMatrix_naturality a j.hom
  have ha : a ≫ j.hom = g := by simp [a]
  rw [ha] at hρ hσ
  rw [hρ, hσ]
  exact h₂

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding MatrixRepresentation

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- The finite regular representation in chosen coordinates, transported to the affine group. -/
def affineRegularRepresentation
    (V : Submodule k (AffineCoordinates.algebra G)) {d : ℕ} (b : Basis (Fin d) k V)
    (hV : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
      ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (w : AffineCoordinates.algebra G),
        w ∈ V → rightAct f w ∈ V) : MatrixRepresentation G (Fin d) :=
  (regularRepresentation (AffineCoordinates.corepresentation G) (Field.toIsField k) V b hV).restrict
    (AffineCoordinates.groupSchemeIso G).inv

variable {G} {n : Type} [Fintype n] [DecidableEq n]

/-- Every nonzero fixed vector of an arbitrary affine group maps to the constant one
in an actual finite regular representation, without a supplied corepresentation. -/
theorem exists_affine_finite_regular_map_to_one
    (ρ : MatrixRepresentation G n) (v : n → k) (hv0 : v ≠ 0) (hv : ρ.IsFixedVector v) :
    ∃ (V : Submodule k (AffineCoordinates.algebra G)) (d : ℕ) (b : Basis (Fin d) k V)
      (hV : letI := (bialgebra (AffineCoordinates.corepresentation G)).toCoalgebra
        ∀ (f : Module.Dual k (AffineCoordinates.algebra G)) (w : AffineCoordinates.algebra G),
          w ∈ V → rightAct f w ∈ V)
      (C : Matrix (Fin d) n k),
      Intertwines ρ (affineRegularRepresentation G V b hV) C ∧
        ∑ l, (C *ᵥ v) l • (b l : AffineCoordinates.algebra G) = 1 := by
  let e := AffineCoordinates.groupSchemeIso G
  have hv' : (ρ.restrict e.hom).IsFixedVector v := by
    intro T g
    rw [pointMatrix_restrict]
    exact hv T (g ≫ e.hom.hom.hom)
  obtain ⟨V, d, b, hV, C, hC, h1⟩ := exists_finite_regular_map_to_one
    (AffineCoordinates.corepresentation G) (ρ.restrict e.hom) v hv0 hv'
  refine ⟨V, d, b, hV, C, ?_, h1⟩
  intro A g
  have h := hC A (g ≫ e.inv.hom.hom)
  rw [affineMatrix_restrict] at h
  have he : (g ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = g := by
    simp only [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom,
      Category.comp_id]
  rw [he] at h
  exact h

end Langlands.GroupScheme.Chevalley
