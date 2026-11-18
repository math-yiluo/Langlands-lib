import Langlands.GroupScheme.Dynamic.UnitriangularEmbedding
import Langlands.GroupScheme.MatrixRepresentation.StableComplements
import Langlands.GroupScheme.Chevalley.ReindexRepresentation
import Langlands.GroupScheme.Multiplicative
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Reindexing actual matrix representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

@[simp]
theorem reindexGL_val {R : Type*} [CommRing R] (e : n ≃ m) (M : GL n R) :
    (Chevalley.reindexGL e M : Matrix m m R) = (M : Matrix n n R).submatrix e.symm e.symm := rfl

theorem reindexGL_map {R S : Type*} [CommRing R] [CommRing S]
    (e : n ≃ m) (g : R →+* S) (M : GL n R) :
    Chevalley.reindexGL e (Matrix.GeneralLinearGroup.map g M) =
      Matrix.GeneralLinearGroup.map g (Chevalley.reindexGL e M) :=
  GeneralLinear.matrixReindex_map e g M

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}

/-- Reuse the published actual Chevalley reindexing construction. -/
abbrev reindex (ρ : MatrixRepresentation G n) (e : n ≃ m) : MatrixRepresentation G m :=
  Chevalley.reindexRepresentation e R ρ

theorem reindex_pointMatrix (ρ : MatrixRepresentation G n) (e : n ≃ m)
    (T : Over (Spec R)) (x : T ⟶ G.X) :
    (ρ.reindex e).pointMatrix T x = Chevalley.reindexGL e (ρ.pointMatrix T x) :=
  Chevalley.reindexRepresentation_pointMatrix e R ρ T x

theorem reindex_affineMatrix (ρ : MatrixRepresentation G n) (e : n ≃ m)
    (A : CommAlgCat.{u} R) (x : (algSpec R).obj (op A) ⟶ G.X) :
    (ρ.reindex e).affineMatrix A x = Chevalley.reindexGL e (ρ.affineMatrix A x) := by
  have h := reindex_pointMatrix ρ e ((algSpec R).obj (op A)) x
  rw [pointMatrix_eq_affineMatrix, pointMatrix_eq_affineMatrix] at h
  erw [reindexGL_map] at h
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.map (Corepresented.affineSectionsIso A).inv.hom.toRingHom :
        GL m A → GL m Γ(((algSpec R).obj (op A)).left, ⊤)) := by
    intro M N hMN
    apply Units.ext
    ext i j
    exact (Corepresented.affineSectionsAlgEquiv A).symm.injective
      (congrArg (fun B : GL m Γ(((algSpec R).obj (op A)).left, ⊤) => B.val i j) hMN)
  exact hinj h

@[simp]
theorem reindex_symm (ρ : MatrixRepresentation G n) (e : n ≃ m) :
    (ρ.reindex e).reindex e.symm = ρ := by
  apply hom_ext_points
  intro T x
  apply (GeneralLinear.pointsEquiv n R T).injective
  change ((ρ.reindex e).reindex e.symm).pointMatrix T x = ρ.pointMatrix T x
  rw [reindex_pointMatrix, reindex_pointMatrix]
  apply Units.ext
  ext i j
  simp only [reindexGL_val, Matrix.submatrix_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]

section Field

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The coordinate linear equivalence used by actual reindexing. -/
def reindexVector (e : n ≃ m) : (n → k) ≃ₗ[k] (m → k) :=
  LinearEquiv.piCongrLeft' k (fun _ : n => k) e

/-- Reindexing commutes with every affine coefficient operation. -/
theorem reindex_coefficient (ρ : MatrixRepresentation G n) (e : n ≃ m)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X)
    (v : n → k) (ell : A →ₗ[k] k) :
    (fun i => ell ((((ρ.reindex e).affineMatrix A x : Matrix m m A) *ᵥ
      (fun j => algebraMap k A (reindexVector e v j))) i)) =
      reindexVector e (fun i => ell (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
        (fun j => algebraMap k A (v j))) i)) := by
  rw [reindex_affineMatrix, reindexGL_val]
  change (fun i => ell ((((ρ.affineMatrix A x : Matrix n n A).submatrix e.symm e.symm) *ᵥ
      (fun j => algebraMap k A (v (e.symm j)))) i)) = _
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  rfl

/-- Stable subspaces correspond under actual finite-coordinate reindexing. -/
theorem isStableSubspace_reindex_map_iff (ρ : MatrixRepresentation G n) (e : n ≃ m)
    (V : Submodule k (n → k)) :
    (ρ.reindex e).IsStableSubspace (V.map (reindexVector e).toLinearMap) ↔
      ρ.IsStableSubspace V := by
  constructor
  · intro h A x v hv ell
    have hv' : reindexVector e v ∈ V.map (reindexVector e).toLinearMap :=
      ⟨v, hv, rfl⟩
    have h' := h A x _ hv' ell
    rw [reindex_coefficient] at h'
    rcases h' with ⟨w, hw, heq⟩
    exact (reindexVector e).injective heq ▸ hw
  · intro h A x v hv ell
    rcases hv with ⟨w, hw, rfl⟩
    erw [reindex_coefficient]
    exact ⟨_, h A x w hw ell, rfl⟩

/-- Semisimplicity in the exact stable-subspace sense is invariant under
finite-coordinate reindexing. -/
theorem isSemisimple_reindex_iff (ρ : MatrixRepresentation G n) (e : n ≃ m) :
    (ρ.reindex e).IsSemisimple ↔ ρ.IsSemisimple := by
  rw [isSemisimple_iff_exists_stable_complement,
    isSemisimple_iff_exists_stable_complement]
  let E := reindexVector (k := k) e
  let O := Submodule.orderIsoMapComap E
  constructor
  · intro h V hV
    obtain ⟨W, hW, hc⟩ := h (O V) ((isStableSubspace_reindex_map_iff ρ e V).mpr hV)
    refine ⟨O.symm W, ?_, ?_⟩
    · apply (isStableSubspace_reindex_map_iff ρ e (O.symm W)).mp
      change (ρ.reindex e).IsStableSubspace (O (O.symm W))
      rw [O.apply_symm_apply]
      exact hW
    · have hh := O.symm.isCompl_iff.mp hc
      simpa only [O.symm_apply_apply] using hh
  · intro h V hV
    have hV' : ρ.IsStableSubspace (O.symm V) := by
      apply (isStableSubspace_reindex_map_iff ρ e (O.symm V)).mp
      change (ρ.reindex e).IsStableSubspace (O (O.symm V))
      rw [O.apply_symm_apply]
      exact hV
    obtain ⟨W, hW, hc⟩ := h (O.symm V) hV'
    refine ⟨O W, (isStableSubspace_reindex_map_iff ρ e W).mpr hW, ?_⟩
    have hh := O.isCompl_iff.mp hc
    simpa only [O.apply_symm_apply] using hh

/-- Linear reductivity expressed using `Fin d` also controls every finite
coordinate type. -/
theorem isSemisimple_of_fin_linearlyReductive
    (hLR : ∀ d (σ : MatrixRepresentation G (Fin d)), σ.IsSemisimple)
    (ρ : MatrixRepresentation G n) : ρ.IsSemisimple :=
  (isSemisimple_reindex_iff ρ (Fintype.equivFin n)).mp
    (hLR _ (ρ.reindex (Fintype.equivFin n)))

end Field

end Langlands.GroupScheme.MatrixRepresentation
