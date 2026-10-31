import Langlands.AlgebraicGeometry.LocalSectionDeterminant

/-! # Local section bases and determinants through actual sheaf isomorphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace Langlands.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {U : X.Opens}
    {M N : X.Modules}

/-- Evaluate an actual isomorphism of local module sheaves on sections. -/
def localSectionIso (h : M.over U ≅ N.over U) (V : Over U) :
    Γ(M, V.left) ≃ₗ[Γ(X, V.left)] Γ(N, V.left) :=
  ((SheafOfModules.evaluation (X.ringCatSheaf.over U) (op V)).mapIso h).toLinearEquiv

@[simp]
lemma localSectionIso_apply (h : M.over U ≅ N.over U) (V : Over U)
    (x : Γ(M, V.left)) :
    localSectionIso h V x = h.hom.val.app (op V) x := rfl

@[simp]
lemma localSectionIso_symm (h : M.over U ≅ N.over U) (V : Over U) :
    (localSectionIso h V).symm = localSectionIso h.symm V := rfl

/-- Evaluation of the isomorphism commutes with actual restriction maps. -/
lemma localSectionIso_restrict (h : M.over U ≅ N.over U)
    {V W : Over U} (j : V ⟶ W) (x : Γ(M, W.left)) :
    localSectionIso h V (M.presheaf.map j.left.op x) =
      N.presheaf.map j.left.op (localSectionIso h W x) :=
  PresheafOfModules.naturality_apply h.hom.val j.op x

variable {I : Type u} [Fintype I]

local instance : DecidableEq I := Classical.decEq I

/-- Composing a trivialization with a sheaf isomorphism transports its actual basis. -/
lemma localSectionBasis_iso_apply
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (h : M.over U ≅ N.over U) (V : Over U) (i : I) :
    localSectionBasis (e ≪≫ h) V i =
      localSectionIso h V (localSectionBasis e V i) := by
  simp only [localSectionBasis_apply]
  rfl

/-- The basis of the composed chart is the mapped section basis. -/
lemma localSectionBasis_iso
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (h : M.over U ≅ N.over U) (V : Over U) :
    localSectionBasis (e ≪≫ h) V = (localSectionBasis e V).map (localSectionIso h V) := by
  ext i
  exact localSectionBasis_iso_apply e h V i

/-- A local sheaf intertwining equation gives the section intertwining equation. -/
lemma localSectionIso_intertwine (h : M.over U ≅ N.over U)
    (a : End (M.over U)) (b : End (N.over U))
    (hab : a ≫ h.hom = h.hom ≫ b) (V : Over U) (x : Γ(M, V.left)) :
    localSectionIso h V (localSectionEndomorphism M V a x) =
      localSectionEndomorphism N V b (localSectionIso h V x) := by
  exact congrArg (fun t : M.over U ⟶ N.over U => t.val.app (op V) x) hab

/-- Intertwined endomorphisms have equal matrices in the constructed transported bases. -/
theorem localSectionEndomorphism_toMatrix_iso
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (h : M.over U ≅ N.over U)
    (a : End (M.over U)) (b : End (N.over U))
    (hab : a ≫ h.hom = h.hom ≫ b) (V : Over U) :
    LinearMap.toMatrix (localSectionBasis e V) (localSectionBasis e V)
        (localSectionEndomorphism M V a) =
      LinearMap.toMatrix (localSectionBasis (e ≪≫ h) V)
        (localSectionBasis (e ≪≫ h) V) (localSectionEndomorphism N V b) := by
  rw [localSectionBasis_iso, LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  apply LinearMap.ext
  intro x
  change localSectionEndomorphism M V a x =
    (localSectionIso h V).symm
      (localSectionEndomorphism N V b (localSectionIso h V x))
  rw [← localSectionIso_intertwine h a b hab]
  exact ((localSectionIso h V).symm_apply_apply _).symm

variable {ι : Type v} [Fintype ι]

/-- Universal matrices agree under an actual intertwining local sheaf isomorphism. -/
theorem localSectionDeterminant_matrix_iso
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (h : M.over U ≅ N.over U)
    (a : ι → End (M.over U)) (b : ι → End (N.over U))
    (hab : ∀ i, a i ≫ h.hom = h.hom ≫ b i) (V : Over U) :
    Langlands.Shimura.HodgeDeterminant.matrix (localSectionBasis e V)
        (fun i => localSectionEndomorphism M V (a i)) =
      Langlands.Shimura.HodgeDeterminant.matrix (localSectionBasis (e ≪≫ h) V)
        (fun i => localSectionEndomorphism N V (b i)) := by
  apply Matrix.ext
  intro j k
  simp only [Langlands.Shimura.HodgeDeterminant.matrix,
    localSectionEndomorphism_toMatrix_iso e h _ _ (hab _)]

/-- Determinant polynomials agree on every smaller open under local sheaf transport. -/
theorem localSectionDeterminant_iso
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (h : M.over U ≅ N.over U)
    (a : ι → End (M.over U)) (b : ι → End (N.over U))
    (hab : ∀ i, a i ≫ h.hom = h.hom ≫ b i) (V : Over U) :
    localSectionDeterminant e a V = localSectionDeterminant (e ≪≫ h) b V := by
  unfold localSectionDeterminant Langlands.Shimura.HodgeDeterminant.polynomial
  exact congrArg Matrix.det (localSectionDeterminant_matrix_iso e h a b hab V)

/-- Every other finite target chart computes the same transported polynomial. -/
theorem localSectionDeterminant_iso_any_chart
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U)
    (h : M.over U ≅ N.over U)
    {J : Type u} [Fintype J]
    (e' : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅ N.over U)
    (a : ι → End (M.over U)) (b : ι → End (N.over U))
    (hab : ∀ i, a i ≫ h.hom = h.hom ≫ b i) (V : Over U) :
    localSectionDeterminant e a V = localSectionDeterminant e' b V := by
  rw [localSectionDeterminant_iso e h a b hab V]
  exact localSectionDeterminant_trivialization_independent _ _ b V

end Langlands.Scheme.Modules
