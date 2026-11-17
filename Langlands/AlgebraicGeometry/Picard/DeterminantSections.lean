import Langlands.AlgebraicGeometry.Picard.FiniteLocallyFreeDeterminant
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof

/-! # Actual determinant sections and affine basis loci -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames

open Langlands.SchemeModule Langlands.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules} {ι : Type u} {T : ι → X.Opens}
  {k : ℕ}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
    (ULift.{u} (Fin k)) ≅ M.over (T i))

/-- The determinant of the coordinates of a tuple of actual global sections. -/
def determinantCoefficient (s : Fin k → Γ(M, ⊤)) (i : ι)
    {U : X.Opens} (hi : U ≤ T i) : Γ(X, U) :=
  ((basis e i hi).toMatrix
    (fun j ↦ M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (s j))).det

lemma determinantCoefficient_restrict (s : Fin k → Γ(M, ⊤)) (i : ι)
    {U V : X.Opens} (hi : U ≤ T i) (h : V ≤ U) :
    X.presheaf.map (homOfLE h).op (determinantCoefficient e s i hi) =
      determinantCoefficient e s i (h.trans hi) := by
  unfold determinantCoefficient
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply]
  rw [← basis_repr_restrict e i hi h]
  congr 2
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma unit_mul_determinantCoefficient (s : Fin k → Γ(M, ⊤)) (i j : ι)
    {U : X.Opens} (hi : U ≤ T i) (hj : U ≤ T j) :
    (unit e i j hi hj : Γ(X, U)) * determinantCoefficient e s j hj =
      determinantCoefficient e s i hi := by
  simp only [unit, Langlands.LinearAlgebra.FiniteBasisDeterminant.unit_same,
    Langlands.LinearAlgebra.FiniteBasisDeterminant.sameUnit_val,
    determinantCoefficient]
  rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix]

lemma determinantCoefficient_compatible (s : Fin k → Γ(M, ⊤)) :
    CocycleGluing.IsCompatibleFamily (cocycle e)
      (fun i ↦ determinantCoefficient e s i le_rfl) := by
  intro i j
  rw [determinantCoefficient_restrict, determinantCoefficient_restrict]
  exact (unit_mul_determinantCoefficient e s i j inf_le_left inf_le_right).symm

/-- The global section of the actual determinant line furnished by a tuple. -/
def determinantSection (hT : (⨆ i, T i) = ⊤) (s : Fin k → Γ(M, ⊤)) :
    GlobalSections (lineBundle e hT).obj :=
  CocycleGluing.globalSec (cocycle e) (determinantCoefficient_compatible e s)

/-- On each frame chart, the section generates exactly where its matrix determinant
is invertible. -/
theorem inf_trivializationOpen_determinantSection
    (hT : (⨆ i, T i) = ⊤) (s : Fin k → Γ(M, ⊤)) (i : ι) :
    T i ⊓ trivializationOpen (lineBundle e hT).obj (determinantSection e hT s) =
      X.basicOpen (determinantCoefficient e s i le_rfl) :=
  CocycleGluing.inf_trivializationOpen_globalSec (cocycle e) (isCocycle e)
    (determinantCoefficient_compatible e s) i

/-- Identify the whole generation open from its determinant equations on a cover. -/
theorem trivializationOpen_determinantSection
    (hT : (⨆ i, T i) = ⊤) (s : Fin k → Γ(M, ⊤)) (U : X.Opens)
    (hU : ∀ i, X.basicOpen (determinantCoefficient e s i le_rfl) = T i ⊓ U) :
    trivializationOpen (lineBundle e hT).obj (determinantSection e hT s) = U := by
  calc
    _ = (⨆ i, T i) ⊓ trivializationOpen (lineBundle e hT).obj
        (determinantSection e hT s) := by rw [hT, top_inf_eq]
    _ = ⨆ i, T i ⊓ trivializationOpen (lineBundle e hT).obj
        (determinantSection e hT s) := iSup_inf_eq _ _
    _ = ⨆ i, T i ⊓ U := iSup_congr fun i ↦
      (inf_trivializationOpen_determinantSection e hT s i).trans (hU i)
    _ = (⨆ i, T i) ⊓ U := (iSup_inf_eq _ _).symm
    _ = U := by rw [hT, top_inf_eq]

/-- A cover by affine determinant basis loci makes the actual determinant ample. -/
theorem isAmple_of_affine_basisLoci
    (hT : (⨆ i, T i) = ⊤) [CompactSpace X]
    {α : Type u} (U : α → X.Opens) (hcover : (⨆ a, U a) = ⊤)
    (haffine : ∀ a, IsAffineOpen (U a))
    (s : α → Fin k → Γ(M, ⊤))
    (hbasis : ∀ a i,
      X.basicOpen (determinantCoefficient e (s a) i le_rfl) = T i ⊓ U a) :
    (lineBundle e hT).IsAmple := by
  refine ⟨inferInstance, fun x ↦ ?_⟩
  have hx : x ∈ (⨆ a, U a) := hcover ▸ trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let t : (lineBundle e hT).powSections 1 :=
    (tensorRightUnitor (lineBundle e hT).obj).inv.app ⊤ (determinantSection e hT (s a))
  have ht : (lineBundle e hT).sectionOpen t = U a :=
    (trivializationOpen_mapIso (tensorRightUnitor (lineBundle e hT).obj).symm
      (determinantSection e hT (s a))).trans
        (trivializationOpen_determinantSection e hT (s a) (U a) (hbasis a))
  exact ⟨1, le_rfl, t, ht ▸ ha, ht ▸ haffine a⟩

end Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

/-- The affine basis-locus criterion applies to the standard actual determinant,
independently of its chosen local frames. -/
theorem finiteLocallyFreeDeterminant_isAmple_of_affine_basisLoci
    {X : Scheme.{u}} [CompactSpace X] {M : X.Modules}
    (hM : HasFiniteLocalBasis M)
    {ι : Type u} {T : ι → X.Opens} {k : ℕ}
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
      (ULift.{u} (Fin k)) ≅ M.over (T i))
    (hT : (⨆ i, T i) = ⊤)
    {α : Type u} (U : α → X.Opens) (hcover : (⨆ a, U a) = ⊤)
    (haffine : ∀ a, IsAffineOpen (U a))
    (s : α → Fin k → Γ(M, ⊤))
    (hbasis : ∀ a i,
      X.basicOpen (VariableDeterminantFrames.determinantCoefficient e (s a) i le_rfl) =
        T i ⊓ U a) :
    (finiteLocallyFreeDeterminant hM).IsAmple := by
  let a : FiniteLocalFrames M :=
    ⟨ι, T, hT, fun _ ↦ k, e⟩
  exact (VariableDeterminantFrames.isAmple_of_affine_basisLoci e hT U hcover
    haffine s hbasis).of_iso
      ((LineBundle.forget X).mapIso (finiteLocallyFreeDeterminantPresentationIso a hM))

end Langlands.AlgebraicGeometry.Picard
