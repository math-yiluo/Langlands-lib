import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterSpan
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedRepresentation
import Langlands.GroupScheme.MatrixRepresentation.InverseCharacter

/-! # Actual representations on a normal-subgroup character span -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section AffineCoordinates

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The restricted representation has the expected matrix on every affine algebra. -/
theorem restrictCoordinates_affineMatrix (ρ : MatrixRepresentation G n)
    (B : Matrix n m R) (C : Matrix m n R) (hCB : C * B = 1)
    (hstable : ρ.IsStableCoordinates B C)
    (A : CommAlgCat.{u} R) (x : G.affinePoints A) :
    ((restrictCoordinates ρ B C hCB hstable).affineMatrix A x : Matrix m m A) =
      C.map (algebraMap R A) * (ρ.affineMatrix A x : Matrix n n A) *
        B.map (algebraMap R A) := by
  let T := (algSpec R).obj (op A)
  let e : A →+* Γ(T.left, ⊤) := (Corepresented.affineSectionsIso A).inv.hom.toRingHom
  have hi : Function.Injective e := by
    intro a b hab
    have hc := congrArg (Corepresented.affineSectionsIso A).hom.hom hab
    have hleft (a : A) : (Corepresented.affineSectionsIso A).hom.hom (e a) = a :=
      ConcreteCategory.congr_hom (Corepresented.affineSectionsIso A).inv_hom_id a
    exact (hleft a).symm.trans (hc.trans (hleft b))
  have hB : (B.map (algebraMap R A)).map e = B.map (scalarMap T) := by
    ext r s
    exact (UnipotentMatrixCriterion.scalarMap_affine A _).symm
  have hC : (C.map (algebraMap R A)).map e = C.map (scalarMap T) := by
    ext r s
    exact (UnipotentMatrixCriterion.scalarMap_affine A _).symm
  have he := congrArg Units.val (restrictCoordinates_pointMatrix ρ B C hCB hstable T x)
  change ((restrictCoordinates ρ B C hCB hstable).pointMatrix T x :
      Matrix m m Γ(T.left, ⊤)) =
    C.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
      B.map (scalarMap T) at he
  rw [pointMatrix_eq_affineMatrix, pointMatrix_eq_affineMatrix] at he
  ext r s
  apply hi
  have hj := congrArg (fun M : Matrix m m Γ(T.left, ⊤) => M r s) he
  change (((restrictCoordinates ρ B C hCB hstable).affineMatrix A x :
      Matrix m m A).map e) r s =
    ((C.map (algebraMap R A) * (ρ.affineMatrix A x : Matrix n n A) *
      B.map (algebraMap R A)).map e) r s
  rw [Matrix.map_mul, Matrix.map_mul, hC, hB]
  exact hj

end AffineCoordinates

section CharacterCoordinates

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Projection onto stable split coordinates preserves the subgroup character
of every vector fixed by the corresponding coordinate projection. -/
theorem characterSpace_restrictCoordinates (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (B : Matrix n m k) (C : Matrix m n k) (hCB : C * B = 1)
    (hstable : ρ.IsStableCoordinates B C)
    {χ : rationalCharacters H} {v : n → k}
    (hv : v ∈ (ρ.restrict i).characterSpace χ) (hproj : (B * C) *ᵥ v = v) :
    C *ᵥ v ∈ ((restrictCoordinates ρ B C hCB hstable).restrict i).characterSpace χ := by
  rw [mem_characterSpace_iff]
  unfold universalCharacterMatrix
  rw [affineMatrix_restrict, restrictCoordinates_affineMatrix]
  let A := CharacterUnits.Coord H
  let vA : n → A := fun r => algebraMap k A (v r)
  have hvec : (fun s => algebraMap k A ((C *ᵥ v) s)) =
      C.map (algebraMap k A) *ᵥ vA := by
    funext s
    exact (algebraMap k A).map_mulVec _ _ s
  have hp : B.map (algebraMap k A) *ᵥ (C.map (algebraMap k A) *ᵥ vA) = vA := by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul]
    funext r
    exact ((algebraMap k A).map_mulVec (B * C) v r).symm.trans
      (congrArg (fun w : n → k => algebraMap k A (w r)) hproj)
  rw [hvec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hp]
  have he := characterSpace_affine hv A (CharacterUnits.universalPoint H)
  rw [affineMatrix_restrict] at he
  rw [he, Matrix.mulVec_smul]
  rfl

/-- When split coordinates cover exactly the sum of the subgroup character
spaces, the restricted subgroup representation is spanned by its characters. -/
theorem characterSpan_restrictCoordinates (ρ : MatrixRepresentation G n) (i : H ⟶ G)
    (B : Matrix n m k) (C : Matrix m n k) (hCB : C * B = 1)
    (hstable : ρ.IsStableCoordinates B C)
    (hcols : ∀ s, (fun r => B r s) ∈ (ρ.restrict i).characterSpan)
    (hproj : ∀ v, v ∈ (ρ.restrict i).characterSpan → (B * C) *ᵥ v = v) :
    ((restrictCoordinates ρ B C hCB hstable).restrict i).characterSpan = ⊤ := by
  let σ := restrictCoordinates ρ B C hCB hstable
  have hmaps (v : n → k) (hv : v ∈ (ρ.restrict i).characterSpan) :
      C *ᵥ v ∈ (σ.restrict i).characterSpan := by
    refine Submodule.iSup_induction (ρ.restrict i).characterSpace
      (motive := fun v => C *ᵥ v ∈ (σ.restrict i).characterSpan) hv ?_ ?_ ?_
    · intro χ v hv
      apply Submodule.mem_iSup_of_mem χ
      exact characterSpace_restrictCoordinates ρ i B C hCB hstable hv
        (hproj _ (Submodule.mem_iSup_of_mem χ hv))
    · simpa only [Matrix.mulVec_zero] using (σ.restrict i).characterSpan.zero_mem
    · intro v w hv hw
      rw [Matrix.mulVec_add]
      exact (σ.restrict i).characterSpan.add_mem hv hw
  apply eq_top_iff.mpr
  intro w _
  have hB : B *ᵥ w ∈ (ρ.restrict i).characterSpan := by
    rw [Matrix.mulVec_eq_sum]
    apply Submodule.sum_mem
    intro s _
    rw [op_smul_eq_smul]
    change (w s • fun r => B r s) ∈ (ρ.restrict i).characterSpan
    exact (ρ.restrict i).characterSpan.smul_mem (w s) (hcols s)
  have hw := hmaps _ hB
  simpa only [Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec] using hw

/-- Over an algebraically closed field with a reduced locally finite-type ambient
group, every nonzero normal-subgroup character vector has an inverse-character
vector in another actual ambient representation. -/
theorem exists_inverse_normal_characterVector [IsAlgClosed k]
    [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]
    (ρ : MatrixRepresentation G n) (i : H ⟶ G) [Mono i.hom.hom]
    (hN : (SubgroupFunctor.range i).IsNormal)
    (χ : rationalCharacters H) {v : n → k}
    (hv : v ∈ (ρ.restrict i).characterSpace χ) (hne : v ≠ 0) :
    ∃ (d : ℕ) (σ : MatrixRepresentation G (Fin d)) (w : Fin d → k),
      w ≠ 0 ∧ w ∈ (σ.restrict i).characterSpace (-χ) := by
  classical
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ :=
    exists_subspace_split_coordinates (ρ.restrict i).characterSpan
  have hs := isStableCoordinates_characterSpan ρ i hN B C hcols hproj
  let τ := restrictCoordinates ρ B C hCB hs
  have hvspan : v ∈ (ρ.restrict i).characterSpan := Submodule.mem_iSup_of_mem χ hv
  have hv' : C *ᵥ v ∈ (τ.restrict i).characterSpace χ :=
    characterSpace_restrictCoordinates ρ i B C hCB hs hv (hproj v hvspan)
  have hne' : C *ᵥ v ≠ 0 := by
    intro hz
    apply hne
    have he := hproj v hvspan
    rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero] at he
    exact he.symm
  have hspan : (⨆ ψ, (τ.restrict i).characterSpace ψ) = ⊤ :=
    characterSpan_restrictCoordinates ρ i B C hCB hs hcols hproj
  obtain ⟨w, hw, hχ⟩ := exists_inverse_characterVector (τ.restrict i) hspan χ hv' hne'
  refine ⟨d, τ.dual, w, hw, ?_⟩
  simpa only [dual_restrict] using hχ

/-- An actual ambient representation containing a nonzero vector of a specified
subgroup character. -/
structure NormalCharacterVector (i : H ⟶ G) (χ : rationalCharacters H) where
  dimension : ℕ
  representation : MatrixRepresentation G (Fin dimension)
  vector : Fin dimension → k
  nonzero : vector ≠ 0
  character_mem : vector ∈ (representation.restrict i).characterSpace χ

/-- Choose an actual ambient representation and a nonzero inverse-character
vector from a nonzero normal-subgroup character vector. -/
def inverseNormalCharacterVector [IsAlgClosed k]
    [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]
    (ρ : MatrixRepresentation G n) (i : H ⟶ G) [Mono i.hom.hom]
    (hN : (SubgroupFunctor.range i).IsNormal)
    (χ : rationalCharacters H) {v : n → k}
    (hv : v ∈ (ρ.restrict i).characterSpace χ) (hne : v ≠ 0) :
    NormalCharacterVector i (-χ) := by
  apply Classical.choice
  obtain ⟨d, σ, w, hw, hχ⟩ := exists_inverse_normal_characterVector ρ i hN χ hv hne
  exact ⟨⟨d, σ, w, hw, hχ⟩⟩

end CharacterCoordinates
end Langlands.GroupScheme.MatrixRepresentation
