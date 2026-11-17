import Langlands.LinearAlgebra.FiniteBasisProductDeterminant
import Langlands.AlgebraicGeometry.Modules.FiniteFrameRankLoci
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleTensor
import Langlands.AlgebraicGeometry.Picard.AffineBaseLineTwistAmple
import Langlands.AlgebraicGeometry.Picard.FiniteLocallyFreeDeterminantPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Actual determinant factorization for module-sheaf biproducts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Scheme.Modules

variable {X : Scheme.{u}}

/-- Sections of the genuine module-sheaf biproduct are the product of the
actual section modules; the forward map is the two actual projections. -/
def biprodSectionsEquiv (M N : X.Modules) (U : X.Opens) :
    Γ(M ⊞ N, U) ≃ₗ[Γ(X, U)] Γ(M, U) × Γ(N, U) where
  toFun s := ((biprod.fst : M ⊞ N ⟶ M).app U s,
    (biprod.snd : M ⊞ N ⟶ N).app U s)
  invFun s := (biprod.inl : M ⟶ M ⊞ N).app U s.1 +
    (biprod.inr : N ⟶ M ⊞ N).app U s.2
  left_inv s := by
    have h := congrArg (fun f : M ⊞ N ⟶ M ⊞ N => f.app U s) (biprod.total (X := M) (Y := N))
    exact h
  right_inv s := by
    apply Prod.ext
    · simp only [map_add]
      change ((biprod.inl ≫ biprod.fst : M ⟶ M).app U) s.1 +
        ((biprod.inr ≫ biprod.fst : N ⟶ M).app U) s.2 = s.1
      simp
    · simp only [map_add]
      change ((biprod.inl ≫ biprod.snd : M ⟶ N).app U) s.1 +
        ((biprod.inr ≫ biprod.snd : N ⟶ N).app U) s.2 = s.2
      simp
  map_add' s t := by ext <;> exact map_add _ _ _
  map_smul' r s := by ext <;> exact Scheme.Modules.Hom.app_smul _ _ _

@[simp]
theorem biprodSectionsEquiv_fst (M N : X.Modules) (U : X.Opens) (s : Γ(M ⊞ N, U)) :
    (biprodSectionsEquiv M N U s).1 = (biprod.fst : M ⊞ N ⟶ M).app U s := rfl

@[simp]
theorem biprodSectionsEquiv_snd (M N : X.Modules) (U : X.Opens) (s : Γ(M ⊞ N, U)) :
    (biprodSectionsEquiv M N U s).2 = (biprod.snd : M ⊞ N ⟶ N).app U s := rfl

/-- The actual product-section equivalence commutes with restrictions. -/
theorem biprodSectionsEquiv_restrict (M N : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (s : Γ(M ⊞ N, U)) :
    biprodSectionsEquiv M N V ((M ⊞ N).presheaf.map (homOfLE h).op s) =
      (M.presheaf.map (homOfLE h).op (biprodSectionsEquiv M N U s).1,
        N.presheaf.map (homOfLE h).op (biprodSectionsEquiv M N U s).2) := by
  apply Prod.ext
  · exact (PresheafOfModules.naturality_apply
      (biprod.fst : M ⊞ N ⟶ M).val (homOfLE h).op s)
  · exact (PresheafOfModules.naturality_apply
      (biprod.snd : M ⊞ N ⟶ N).val (homOfLE h).op s)

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard.BiproductDeterminant

open Langlands.Scheme.Modules
open Langlands.LinearAlgebra.FiniteBasisDeterminant

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type u}
    {T : ι → X.Opens} {n m : ι → ℕ}
    (eM : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
      (ULift.{u} (Fin (n i))) ≅ M.over (T i))
    (eN : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
      (ULift.{u} (Fin (m i))) ≅ N.over (T i))

/-- The actual product section basis on every open inside two supplied frames. -/
def sectionBasis (i : ι) {U : X.Opens} (hi : U ≤ T i) :
    Module.Basis (Fin (n i + m i)) Γ(X, U) Γ(M ⊞ N, U) :=
  (productBasis (VariableDeterminantFrames.basis eM i hi)
    (VariableDeterminantFrames.basis eN i hi)).map (biprodSectionsEquiv M N U).symm

/-- The product section basis restricts to the product section basis. -/
theorem sectionBasis_restrict (i : ι) {U V : X.Opens}
    (hi : U ≤ T i) (h : V ≤ U) (j : Fin (n i + m i)) :
    (M ⊞ N).presheaf.map (homOfLE h).op (sectionBasis eM eN i hi j) =
      sectionBasis eM eN i (h.trans hi) j := by
  apply (biprodSectionsEquiv M N V).injective
  rw [biprodSectionsEquiv_restrict]
  simp only [sectionBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j <;> ext <;>
    simp only [productBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply,
      Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inl_snd,
      Module.Basis.prod_apply_inr_fst, Module.Basis.prod_apply_inr_snd,
      map_zero, VariableDeterminantFrames.basis_restrict]

/-- Product bases determine actual free frames of the genuine biproduct. -/
def frame (i : ι) :
    SheafOfModules.free (R := X.ringCatSheaf.over (T i))
        (ULift.{u} (Fin (n i + m i))) ≅ (M ⊞ N).over (T i) :=
  affineBasisFrame (M ⊞ N) (T i) (ULift.{u} (Fin (n i + m i)))
    (fun j => sectionBasis eM eN i le_rfl j.down)
    (fun W _ => by
      refine ⟨(sectionBasis eM eN i W.hom.le).reindex Equiv.ulift.symm, fun j => ?_⟩
      rw [Module.Basis.reindex_apply]
      change sectionBasis eM eN i W.hom.le j.down =
        (M ⊞ N).presheaf.map W.hom.op (sectionBasis eM eN i le_rfl j.down)
      have hW : W.hom = homOfLE W.hom.le := Subsingleton.elim _ _
      rw [hW]
      exact (sectionBasis_restrict eM eN i le_rfl W.hom.le j.down).symm)

/-- The section bases of the actual product frames are the specified product bases. -/
theorem frame_basis (i : ι) {U : X.Opens} (hi : U ≤ T i) :
    VariableDeterminantFrames.basis (frame eM eN) i hi = sectionBasis eM eN i hi := by
  apply DFunLike.ext
  intro j
  rw [VariableDeterminantFrames.basis_apply]
  change localSectionBasis
    (affineBasisFrame (M ⊞ N) (T i) (ULift.{u} (Fin (n i + m i))) _ _)
      (Over.mk (homOfLE hi)) ⟨j⟩ = _
  rw [affineBasisFrame_basis]
  exact sectionBasis_restrict eM eN i le_rfl hi j

/-- The mixed determinant transition unit of the biproduct frame factors into
those of the two actual summand frames, with variable ranks allowed. -/
theorem frame_unit (i j : ι) {U : X.Opens} (hi : U ≤ T i) (hj : U ≤ T j) :
    VariableDeterminantFrames.unit (frame eM eN) i j hi hj =
      VariableDeterminantFrames.unit eM i j hi hj *
        VariableDeterminantFrames.unit eN i j hi hj := by
  unfold VariableDeterminantFrames.unit
  rw [frame_basis, frame_basis]
  unfold sectionBasis
  rw [unit_map, unit_productBasis]

/-- The actual biproduct determinant cocycle is the product of both actual
summand determinant cocycles. -/
theorem frame_cocycle :
    VariableDeterminantFrames.cocycle (frame eM eN) =
      VariableDeterminantFrames.cocycle eM * VariableDeterminantFrames.cocycle eN := by
  funext i j
  exact frame_unit eM eN i j inf_le_left inf_le_right


/-- The actual line of the product frames is the tensor of the two actual
frame determinant lines. -/
def frameLineIso (hT : (⨆ i, T i) = ⊤) :
    VariableDeterminantFrames.lineBundle (frame eM eN) hT ≅
      LineBundle.tensor pullbackTensorComparisonIsIso
        (VariableDeterminantFrames.lineBundle eM hT)
        (VariableDeterminantFrames.lineBundle eN hT) :=
  ObjectProperty.isoMk _
    (eqToIso (congrArg CocycleGluing.glued (frame_cocycle eM eN)) ≪≫
      (CocycleGluing.tensorIso (VariableDeterminantFrames.isCocycle eM)
        (VariableDeterminantFrames.isCocycle eN) hT).symm)

end Langlands.AlgebraicGeometry.Picard.BiproductDeterminant

namespace Langlands.AlgebraicGeometry.Picard.FiniteLocalFrames

open Langlands.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The common intersections of two actual finite frame covers. -/
def productOpens (a : FiniteLocalFrames M) (b : FiniteLocalFrames N) :
    a.I × b.I → X.Opens := fun i => a.opens i.1 ⊓ b.opens i.2

theorem productOpens_covers (a : FiniteLocalFrames M) (b : FiniteLocalFrames N) :
    (⨆ i, productOpens a b i) = ⊤ := by
  apply le_antisymm le_top
  intro x _
  have ha : x ∈ (⨆ i, a.opens i) := by rw [a.covers]; trivial
  have hb : x ∈ (⨆ i, b.opens i) := by rw [b.covers]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp ha
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hb
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩

/-- The first actual frame family restricted to the common intersections. -/
def productLeft (a : FiniteLocalFrames M) (b : FiniteLocalFrames N) :
    FiniteLocalFrames M where
  I := a.I × b.I
  opens := productOpens a b
  covers := productOpens_covers a b
  rank i := a.rank i.1
  frame i := subopenFrame (a.frame i.1) inf_le_left

/-- The second actual frame family restricted to the common intersections. -/
def productRight (a : FiniteLocalFrames M) (b : FiniteLocalFrames N) :
    FiniteLocalFrames N where
  I := a.I × b.I
  opens := productOpens a b
  covers := productOpens_covers a b
  rank i := b.rank i.2
  frame i := subopenFrame (b.frame i.2) inf_le_right

/-- Actual finite frames of the genuine biproduct, of the sum of the local ranks. -/
def biprod (a : FiniteLocalFrames M) (b : FiniteLocalFrames N) :
    FiniteLocalFrames (M ⊞ N) where
  I := a.I × b.I
  opens := productOpens a b
  covers := productOpens_covers a b
  rank i := a.rank i.1 + b.rank i.2
  frame := BiproductDeterminant.frame (productLeft a b).frame (productRight a b).frame

/-- The determinant of the actual product frames factors as the tensor of
both refined actual determinant lines. -/
def biprodLineIso (a : FiniteLocalFrames M) (b : FiniteLocalFrames N) :
    (a.biprod b).lineBundle ≅
      LineBundle.tensor pullbackTensorComparisonIsIso
        (productLeft a b).lineBundle (productRight a b).lineBundle :=
  BiproductDeterminant.frameLineIso (productLeft a b).frame (productRight a b).frame
    (productOpens_covers a b)

end Langlands.AlgebraicGeometry.Picard.FiniteLocalFrames

namespace Langlands.Scheme.Modules

open Langlands.AlgebraicGeometry.Picard

/-- Finite local bases are closed under the genuine module-sheaf biproduct. -/
theorem HasFiniteLocalBasis.biprod {X : Scheme.{u}} {M N : X.Modules}
    (hM : HasFiniteLocalBasis M) (hN : HasFiniteLocalBasis N) :
    HasFiniteLocalBasis (M ⊞ N) :=
  ((FiniteLocalFrames.choose hM).biprod (FiniteLocalFrames.choose hN)).hasFiniteLocalBasis

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

variable {X S : Scheme.{u}}

/-- The existing chosen determinant of a genuine biproduct is the actual
tensor product of the existing chosen summand determinants, with variable ranks. -/
def finiteLocallyFreeDeterminantBiprodIso {M N : X.Modules}
    (hM : HasFiniteLocalBasis M) (hN : HasFiniteLocalBasis N)
    (hP : HasFiniteLocalBasis (M ⊞ N)) :
    finiteLocallyFreeDeterminant hP ≅
      LineBundle.tensor pullbackTensorComparisonIsIso
        (finiteLocallyFreeDeterminant hM) (finiteLocallyFreeDeterminant hN) := by
  let a := FiniteLocalFrames.choose hM
  let b := FiniteLocalFrames.choose hN
  let EM : (a.productLeft b).lineBundle.obj ≅ (finiteLocallyFreeDeterminant hM).obj :=
    (LineBundle.forget X).mapIso
      (finiteLocallyFreeDeterminantPresentationIso (a.productLeft b) hM)
  let EN : (a.productRight b).lineBundle.obj ≅ (finiteLocallyFreeDeterminant hN).obj :=
    (LineBundle.forget X).mapIso
      (finiteLocallyFreeDeterminantPresentationIso (a.productRight b) hN)
  let EP : (finiteLocallyFreeDeterminant hP).obj ≅ (a.biprod b).lineBundle.obj :=
    ((LineBundle.forget X).mapIso
      (finiteLocallyFreeDeterminantPresentationIso (a.biprod b) hP)).symm
  let E : (a.biprod b).lineBundle.obj ≅
      tensorObj (a.productLeft b).lineBundle.obj (a.productRight b).lineBundle.obj :=
    (LineBundle.forget X).mapIso (a.biprodLineIso b)
  exact ObjectProperty.isoMk _
    (EP ≪≫ E ≪≫ (tensorFunctor X).mapIso (EM.prod EN))

/-- For a summand pulled back from the base, its actual chosen determinant
factor is the actual pullback of the existing base determinant line. -/
def finiteLocallyFreeDeterminantBiprodPullbackIso
    {M : X.Modules} {C : S.Modules} (hM : HasFiniteLocalBasis M)
    (hC : HasFiniteLocalBasis C) (p : X ⟶ S)
    (hP : HasFiniteLocalBasis (M ⊞ (Scheme.Modules.pullback p).obj C)) :
    finiteLocallyFreeDeterminant hP ≅
      LineBundle.tensor pullbackTensorComparisonIsIso
        (finiteLocallyFreeDeterminant hM)
        ((LineBundle.pullback p).obj (finiteLocallyFreeDeterminant hC)) :=
  ObjectProperty.isoMk _
    ((LineBundle.forget X).mapIso (finiteLocallyFreeDeterminantBiprodIso hM (hC.pullback p) hP) ≪≫
      (tensorFunctor X).mapIso ((Iso.refl _).prod
        ((LineBundle.forget X).mapIso (finiteLocallyFreeDeterminantPullbackIso hC p)).symm))

/-- An actual base-summand stabilization does not change ampleness of the
actual determinant over an affine base. -/
theorem finiteLocallyFreeDeterminant_biprod_pullback_isAmple_iff
    [CompactSpace X] [QuasiSeparatedSpace X] [IsAffine S]
    {M : X.Modules} {C : S.Modules} (hM : HasFiniteLocalBasis M)
    (hC : HasFiniteLocalBasis C) (p : X ⟶ S)
    (hP : HasFiniteLocalBasis (M ⊞ (Scheme.Modules.pullback p).obj C)) :
    (finiteLocallyFreeDeterminant hP).IsAmple ↔ (finiteLocallyFreeDeterminant hM).IsAmple :=
  isAmple_iff_of_affine_base_twist p _ _ (finiteLocallyFreeDeterminant hC)
    ((LineBundle.forget _).mapIso (finiteLocallyFreeDeterminantBiprodPullbackIso hM hC p hP))

end Langlands.AlgebraicGeometry.Picard
