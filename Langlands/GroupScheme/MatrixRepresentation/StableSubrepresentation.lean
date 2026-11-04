import Langlands.GroupScheme.Lie.RepresentationSubquotient
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedRepresentation

/-! # Stable subspaces and equivariant inverse images of actual representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n m p : Type} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

/-- A subspace is invariant if all linear coefficients of every affine translate
of each of its vectors lie in the same subspace. This includes every test algebra. -/
def IsStableSubspace (ρ : MatrixRepresentation G n) (V : Submodule k (n → k)) : Prop :=
  ∀ (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X)
    (v : n → k), v ∈ V → ∀ ℓ : A →ₗ[k] k,
      (fun i => ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
        (fun j => algebraMap k A (v j))) i)) ∈ V

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Applying a ground-field linear functional commutes with a constant matrix. -/
theorem linearFunctional_mulVec_rectangular
    {A : Type*} [CommRing A] [Algebra k A]
    (C : Matrix m n k) (w : n → A) (ℓ : A →ₗ[k] k) :
    (fun i => ℓ ((C.map (algebraMap k A) *ᵥ w) i)) =
      C *ᵥ (fun j => ℓ (w j)) := by
  funext i
  have hs (c : k) (a : A) : ℓ (algebraMap k A c * a) = c * ℓ a := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, hs]

/-- An intertwiner transports coefficient vectors of an affine translate. -/
theorem Intertwines.linearFunctional_mulVec {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k}
    (hC : Intertwines ρ σ C)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X)
    (v : n → k) (ℓ : A →ₗ[k] k) :
    C *ᵥ (fun j => ℓ (((ρ.affineMatrix A x : Matrix n n A) *ᵥ
        (fun l => algebraMap k A (v l))) j)) =
      fun i => ℓ (((σ.affineMatrix A x : Matrix m m A) *ᵥ
        (fun l => algebraMap k A ((C *ᵥ v) l))) i) := by
  rw [← linearFunctional_mulVec_rectangular]
  rw [Matrix.mulVec_mulVec, hC A x, ← Matrix.mulVec_mulVec]
  have hv : C.map (algebraMap k A) *ᵥ (fun l => algebraMap k A (v l)) =
      (fun l => algebraMap k A ((C *ᵥ v) l)) := by
    funext i
    exact ((algebraMap k A).map_mulVec C v i).symm
  rw [hv]

/-- Equivariant inverse images of stable subspaces are stable. -/
theorem IsStableSubspace.comap {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k}
    {V : Submodule k (m → k)} (hV : IsStableSubspace σ V)
    (hC : Intertwines ρ σ C) :
    IsStableSubspace ρ (V.comap C.mulVecLin) := by
  intro A x v hv ℓ
  change C *ᵥ _ ∈ V
  rw [hC.linearFunctional_mulVec A x v ℓ]
  exact hV A x (C *ᵥ v) hv ℓ

/-- The image of an intertwiner is stable, including on nonreduced affine tests. -/
theorem Intertwines.isStableSubspace_range {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k}
    (hC : Intertwines ρ σ C) :
    IsStableSubspace σ (LinearMap.range C.mulVecLin) := by
  intro A x v hv ℓ
  obtain ⟨w, rfl⟩ := hv
  refine ⟨_, hC.linearFunctional_mulVec A x w ℓ⟩

omit [DecidableEq m] in
/-- A stable subspace and split coordinates give stability of the actual matrices. -/
theorem IsStableSubspace.isStableCoordinates [IsAffineHom G.X.hom]
    {ρ : MatrixRepresentation G n} {V : Submodule k (n → k)}
    (hV : IsStableSubspace ρ V) (B : Matrix n m k) (C : Matrix m n k)
    (hcols : ∀ j, (fun i => B i j) ∈ V)
    (hproj : ∀ v, v ∈ V → (B * C) *ᵥ v = v) :
    ρ.IsStableCoordinates B C := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨⟨A⟩, ⟨j⟩⟩ := (essImage_algSpec (G := G.X)).mpr inferInstance
  apply isStableCoordinates_of_affine_model ρ j B C
  have he : (ρ.affineMatrix A j.hom : Matrix n n A) * B.map (algebraMap k A) =
      (B * C).map (algebraMap k A) *
        ((ρ.affineMatrix A j.hom : Matrix n n A) * B.map (algebraMap k A)) := by
    ext r s
    have hs := projection_mulVec_eq_of_coefficients (B * C)
      ((ρ.affineMatrix A j.hom : Matrix n n A) *ᵥ
        (fun a => algebraMap k A (B a s)))
      (fun ℓ => hproj _ (hV A j.hom _ (hcols s) ℓ))
    exact (congrFun hs r).symm
  rw [Matrix.map_mul] at he
  simpa only [Matrix.mul_assoc] using he

/-- Invariant split-coordinate restriction intertwines on every affine test. -/
theorem intertwines_restrictCoordinates (ρ : MatrixRepresentation G n)
    (B : Matrix n m k) (C : Matrix m n k) (hCB : C * B = 1)
    (hstable : ρ.IsStableCoordinates B C) :
    Intertwines (restrictCoordinates ρ B C hCB hstable) ρ B := by
  intro A x
  have h := restrictCoordinates_intertwines ρ B C hCB hstable
    ((algSpec (CommRingCat.of k)).obj (op A)) x
  let e := Corepresented.affineSectionsAlgEquiv A
  have hb : (B.map (scalarMap ((algSpec (CommRingCat.of k)).obj (op A)))).map
      e.toRingHom = B.map (algebraMap k A) := by
    ext i j
    exact e.commutes _
  have he (τ : MatrixRepresentation G n) :
      (τ.pointMatrix ((algSpec (CommRingCat.of k)).obj (op A)) x :
        Matrix n n Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)).map e.toRingHom = (τ.affineMatrix A x : Matrix n n A) := by
    rw [pointMatrix_eq_affineMatrix]
    ext i j
    exact e.apply_symm_apply _
  have he' (τ : MatrixRepresentation G m) :
      (τ.pointMatrix ((algSpec (CommRingCat.of k)).obj (op A)) x :
        Matrix m m Γ(((algSpec (CommRingCat.of k)).obj (op A)).left, ⊤)).map e.toRingHom = (τ.affineMatrix A x : Matrix m m A) := by
    rw [pointMatrix_eq_affineMatrix]
    ext i j
    exact e.apply_symm_apply _
  have hh := congrArg (fun M : Matrix n m Γ(((algSpec (CommRingCat.of k)).obj
    (op A)).left, ⊤) => M.map e.toRingHom) h
  erw [Matrix.map_mul (f := e.toRingHom),
    Matrix.map_mul (f := e.toRingHom)] at hh
  erw [hb, he ρ, he' (restrictCoordinates ρ B C hCB hstable)] at hh
  exact hh.symm

/-- Composition of actual intertwiners is matrix composition. -/
theorem Intertwines.comp {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {π : MatrixRepresentation G p}
    {C : Matrix m n k} {D : Matrix p m k}
    (hC : Intertwines ρ σ C) (hD : Intertwines σ π D) :
    Intertwines ρ π (D * C) := by
  intro A x
  rw [Matrix.map_mul, Matrix.mul_assoc, hC A x, ← Matrix.mul_assoc,
    hD A x, Matrix.mul_assoc]

/-- Equivariance can be cancelled through an injective actual intertwiner. -/
theorem Intertwines.of_comp_injective {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {π : MatrixRepresentation G p}
    {C : Matrix m n k} {D : Matrix p m k}
    (hD : Intertwines σ π D) (hi : Function.Injective D.mulVecLin)
    (hDC : Intertwines ρ π (D * C)) :
    Intertwines ρ σ C := by
  intro A x
  have h : D.map (algebraMap k A) *
        (C.map (algebraMap k A) * (ρ.affineMatrix A x : Matrix n n A)) =
      D.map (algebraMap k A) *
        ((σ.affineMatrix A x : Matrix m m A) * C.map (algebraMap k A)) := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, hDC A x,
      Matrix.map_mul, ← Matrix.mul_assoc, ← hD A x, Matrix.mul_assoc]
  apply Matrix.ext_of_mulVec_single
  intro j
  apply Lie.mulVecLin_map_injective D hi
  change D.map (algebraMap k A) *ᵥ
      ((C.map (algebraMap k A) * (ρ.affineMatrix A x : Matrix n n A)) *ᵥ
        Pi.single j 1) =
    D.map (algebraMap k A) *ᵥ
      (((σ.affineMatrix A x : Matrix m m A) * C.map (algebraMap k A)) *ᵥ
        Pi.single j 1)
  simpa only [Matrix.mulVec_mulVec] using
    congrArg (fun M => M *ᵥ Pi.single j 1) h

section Subquotient

variable [IsAffineHom G.X.hom]

/-- A subrepresentation of an equivariant quotient is an actual subquotient:
take its equivariant inverse image, with finite split coordinates. -/
theorem isSubquotientOf_of_common_quotient
    {n m p : ℕ}
    (ρ : MatrixRepresentation G (Fin m))
    (σ : MatrixRepresentation G (Fin n))
    (π : MatrixRepresentation G (Fin p))
    (C : Matrix (Fin p) (Fin m) k) (D : Matrix (Fin p) (Fin n) k)
    (hC : Intertwines ρ π C) (hs : Function.Surjective C.mulVecLin)
    (hD : Intertwines σ π D) (hi : Function.Injective D.mulVecLin) :
    IsSubquotientOf σ ρ := by
  let V := (LinearMap.range D.mulVecLin).comap C.mulVecLin
  have hV : IsStableSubspace ρ V := hD.isStableSubspace_range.comap hC
  obtain ⟨r, B, P, hPB, hcols, hproj⟩ := exists_subspace_split_coordinates V
  have hstable := hV.isStableCoordinates B P hcols hproj
  let τ := restrictCoordinates ρ B P hPB hstable
  have hB : Intertwines τ ρ B :=
    intertwines_restrictCoordinates ρ B P hPB hstable
  obtain ⟨l, hl⟩ :=
    D.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  let L := LinearMap.toMatrix' l
  have hLD : L * D = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    exact hl
  let Q := L * C * B
  have hDQ : D * Q = C * B := by
    apply Matrix.ext_of_mulVec_single
    intro j
    dsimp only [Q]
    simp_rw [← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec_single_one]
    obtain ⟨w, hw⟩ := hcols j
    change D *ᵥ w = C *ᵥ (fun a => B a j) at hw
    change D *ᵥ (L *ᵥ (C *ᵥ (fun a => B a j))) = C *ᵥ (fun a => B a j)
    rw [← hw]
    have hw' : L *ᵥ (D *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, hLD, Matrix.one_mulVec]
    exact congrArg (D.mulVec) hw'
  have hQ : Intertwines τ σ Q := by
    apply hD.of_comp_injective hi
    rw [hDQ]
    exact hB.comp hC
  refine ⟨r, τ, B, Q, hB, ?_, hQ, ?_⟩
  · exact coordinateInclusion_injective (R := CommRingCat.of k) B P hPB
  · intro w
    obtain ⟨v, hv⟩ := hs (D *ᵥ w)
    have hvV : v ∈ V := ⟨w, hv.symm⟩
    refine ⟨P *ᵥ v, ?_⟩
    change Q *ᵥ (P *ᵥ v) = w
    calc
      _ = L *ᵥ (C *ᵥ ((B * P) *ᵥ v)) := by
        simp only [Q, ← Matrix.mulVec_mulVec]
      _ = L *ᵥ (D *ᵥ w) := by rw [hproj v hvV]; exact congrArg L.mulVec hv
      _ = w := by rw [Matrix.mulVec_mulVec, hLD, Matrix.one_mulVec]

end Subquotient

end Langlands.GroupScheme.MatrixRepresentation
