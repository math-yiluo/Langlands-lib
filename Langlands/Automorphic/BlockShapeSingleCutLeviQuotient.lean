import Langlands.Automorphic.BlockShapeSingleCut
import Langlands.Global.LeftCosetSemidirectIntegral

/-! # The adelic unipotent complement of a single block cut -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField Opposite MeasureTheory Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.GeneralLinear Langlands.Global Langlands.GroupScheme
  Langlands.GroupScheme.GeneralLinear

variable {n : ℕ} (B : BlockShape n)

section Matrix

variable (A : Type u) [CommRing A] (i : Fin B.length) (c : Fin (B.size i - 1))

local notation "uCut" => blockUnipotentSubgroup A (oneCutWeight c)
local notation "vCut" => (blockUnipotentSubgroup A
    (standardBlockWeight (insert (blockShapeSingleCut B i c) B.cuts)) ⊓
      blockLeviSubgroup A (standardBlockWeight B.cuts) : Subgroup (GeneralLinear n A))

private theorem singleEmbedding_injective : Function.Injective (blockShapeSingleEmbedding B A i) := by
  intro x y h
  have h' := B.leviEmbedding_injective A h
  simpa only [Pi.mulSingle_eq_same] using
    congrFun (show (Pi.mulSingle i x : B.Levi A) = Pi.mulSingle i y from h') i

omit c in
private theorem singleEmbedding_map {C : Type u} [CommRing C] (f : A →+* C)
    (x : GeneralLinear (B.size i) A) :
    Matrix.GeneralLinearGroup.map f (blockShapeSingleEmbedding B A i x) =
      blockShapeSingleEmbedding B C i (Matrix.GeneralLinearGroup.map f x) := by
  apply Units.ext
  ext k l
  obtain ⟨j, a, rfl⟩ := exists_eq_index B k
  obtain ⟨j', b, rfl⟩ := exists_eq_index B l
  change f (B.leviEmbedding A (Pi.mulSingle i x) (B.index j a) (B.index j' b)) =
    B.leviEmbedding C (Pi.mulSingle i (Matrix.GeneralLinearGroup.map f x)) (B.index j a) (B.index j' b)
  by_cases hjj' : j = j'
  · subst j'
    rw [B.leviEmbedding_apply_same, B.leviEmbedding_apply_same]
    by_cases hj : j = i
    · subst j
      simp only [Pi.mulSingle_eq_same, Matrix.GeneralLinearGroup.map_apply]
    · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
      exact congrArg (fun y : GeneralLinear (B.size j) C => y a b)
        (map_one (Matrix.GeneralLinearGroup.map f))
  · rw [B.leviEmbedding_apply_ne A _ a b hjj', B.leviEmbedding_apply_ne C _ a b hjj', map_zero]

/-- The one-block radical and the complement in the original Levi are
isomorphic by the single block embedding on matrices. -/
def singleCutLeviMatrixEquiv : (uCut) ≃* (vCut) := by
  let f : (uCut) →* (vCut) := ((blockShapeSingleEmbedding B A i).comp (uCut).subtype).codRestrict
    (vCut) (fun x => (blockUnipotent_inf_levi_insert_singleCut B A i c).symm ▸
      (show blockShapeSingleEmbedding B A i x.val ∈
        (uCut).map (blockShapeSingleEmbedding B A i) from ⟨x.val, x.property, rfl⟩))
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (singleEmbedding_injective B A i (congrArg Subtype.val h))
  · intro y
    have hy : y.val ∈ (uCut).map (blockShapeSingleEmbedding B A i) :=
      (congrArg (fun S : Subgroup (GeneralLinear n A) => y.val ∈ S)
        (blockUnipotent_inf_levi_insert_singleCut B A i c)).mp y.property
    obtain ⟨x, hx, he⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem singleCutLeviMatrixEquiv_val (x : uCut) :
    (singleCutLeviMatrixEquiv B A i c x).val = blockShapeSingleEmbedding B A i x.val := rfl

variable [TopologicalSpace A] [IsTopologicalRing A]

/-- The inverse is continuous because it reads the corresponding Levi block. -/
def singleCutLeviMatrixHomeomorph : (uCut) ≃ₜ* (vCut) where
  toMulEquiv := singleCutLeviMatrixEquiv B A i c
  continuous_toFun := by
    have h : Continuous (fun x : uCut => B.leviEmbedding A (Pi.mulSingle i x.val)) :=
      (B.leviEmbeddingContinuous A).continuous.comp
        ((continuous_mulSingle (A := fun j => GeneralLinear (B.size j) A) i).comp continuous_subtype_val)
    exact h.subtype_mk _
  continuous_invFun := by
    let e := singleCutLeviMatrixEquiv B A i c
    let l := B.leviEquivContinuous A
    have hl (x : vCut) : x.val ∈ B.leviSubgroup A := by
      have hS : blockLeviSubgroup A (standardBlockWeight B.cuts) = B.leviSubgroup A := by
        rw [standardBlockWeight_eq_blockShapeWeight B, blockLeviSubgroup_blockShapeWeight]
      exact (congrArg (fun S : Subgroup (GeneralLinear n A) => x.val ∈ S) hS).mp x.property.2
    let cls (x : vCut) : B.leviSubgroup A := ⟨x.val, hl x⟩
    have hcls : Continuous cls := continuous_subtype_val.subtype_mk _
    have he (x : vCut) : (e.symm x).val = l.symm (cls x) i := by
      obtain ⟨y, rfl⟩ := e.surjective x
      have hval : cls (e y) = l (Pi.mulSingle i y.val) := Subtype.ext rfl
      rw [e.symm_apply_apply, hval, l.symm_apply_apply]
      simp only [Pi.mulSingle_eq_same]
    apply IsInducing.subtypeVal.continuous_iff.mpr
    exact ((continuous_apply i).comp (l.symm.continuous.comp hcls)).congr (fun x => (he x).symm)

end Matrix

section Adelic

variable (F : Type u) [Field F] [NumberField F] (i : Fin B.length) (c : Fin (B.size i - 1))

local notation "RF" => CommRingCat.of F
local notation "G" => GroupScheme.GeneralLinear.groupScheme (Fin n) RF
local notation "H" => GroupScheme.GeneralLinear.groupScheme (Fin (B.size i)) RF
local notation "w" => standardBlockWeight B.cuts
local notation "e" => standardBlockWeight (insert (blockShapeSingleCut B i c) B.cuts)
local notation "U" => blockUnipotent (Fin (B.size i)) RF (oneCutWeight c)
local notation "V" => leviUnipotent (Fin n) RF e w

open AdelicSubgroupPoints

private def singleCutBlockAdelicMatrixHomeomorph :
    adelicPoints F H U ≃ₜ* blockUnipotentSubgroup (Adeles F) (oneCutWeight c) where
  toMulEquiv := blockUnipotentAffineEquiv RF (oneCutWeight c) (CommAlgCat.of F (Adeles F))
  continuous_toFun := ((GeneralLinearGroupPoints.adelicHomeomorph F _).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((GeneralLinearGroupPoints.adelicHomeomorph F _).symm.continuous.comp
    continuous_subtype_val).subtype_mk _

private def singleCutLeviAdelicMatrixHomeomorph :
    adelicPoints F G V ≃ₜ* (blockUnipotentSubgroup (Adeles F) e ⊓
      blockLeviSubgroup (Adeles F) w : Subgroup (AdelicGL F n)) where
  toMulEquiv := leviUnipotentAffineEquiv RF e w (CommAlgCat.of F (Adeles F))
  continuous_toFun := ((GeneralLinearGroupPoints.adelicHomeomorph F n).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous.comp
    continuous_subtype_val).subtype_mk _

/-- The actual adelic unipotent complement is topologically isomorphic to the
one-block radical by the single block embedding. -/
def singleCutLeviAdelicEquiv : adelicPoints F H U ≃ₜ* adelicPoints F G V :=
  (singleCutBlockAdelicMatrixHomeomorph B F i c).trans
    ((singleCutLeviMatrixHomeomorph B (Adeles F) i c).trans
      (singleCutLeviAdelicMatrixHomeomorph B F i c).symm)

theorem singleCutLeviAdelicEquiv_val (x : adelicPoints F H U) :
    GeneralLinearGroupPoints.adelicEquiv F n (singleCutLeviAdelicEquiv B F i c x).val =
      blockShapeSingleEmbedding B (Adeles F) i
        (GeneralLinearGroupPoints.adelicEquiv F (B.size i) x.val) := by
  let z := singleCutLeviMatrixEquiv B (Adeles F) i c
    (singleCutBlockAdelicMatrixHomeomorph B F i c x)
  have h := (singleCutLeviAdelicMatrixHomeomorph B F i c).apply_symm_apply z
  exact congrArg Subtype.val h

/-- The same single block embedding identifies the rational radical points. -/
def singleCutLeviRationalEquiv : rationalPoints F H U ≃* rationalPoints F G V :=
  (blockUnipotentAffineEquiv RF (oneCutWeight c) (CommAlgCat.of F F)).trans
    ((singleCutLeviMatrixEquiv B F i c).trans
      (leviUnipotentAffineEquiv RF e w (CommAlgCat.of F F)).symm)

omit [NumberField F] in
theorem singleCutLeviRationalEquiv_val (x : rationalPoints F H U) :
    GeneralLinearGroupPoints.rationalEquiv F n (singleCutLeviRationalEquiv B F i c x).val =
      blockShapeSingleEmbedding B F i (GeneralLinearGroupPoints.rationalEquiv F (B.size i) x.val) := by
  let a := blockUnipotentAffineEquiv RF (oneCutWeight c) (CommAlgCat.of F F)
  let d := leviUnipotentAffineEquiv RF e w (CommAlgCat.of F F)
  exact congrArg Subtype.val (d.apply_symm_apply (singleCutLeviMatrixEquiv B F i c (a x)))

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 800000 in
theorem singleCutLeviAdelicEquiv_rational (x : rationalPoints F H U) :
    singleCutLeviAdelicEquiv B F i c (AdelicSubgroupPoints.rational F H U x) =
      AdelicSubgroupPoints.rational F G V (singleCutLeviRationalEquiv B F i c x) := by
  let z : rationalPoints F G V := singleCutLeviRationalEquiv B F i c x
  let h : RationalGL F (B.size i) := GeneralLinearGroupPoints.rationalEquiv F (B.size i) x.val
  let a := GeneralLinearGroupPoints.adelicEquiv F n
  let b := GeneralLinearGroupPoints.adelicEquiv F (B.size i)
  let l : adelicPoints F G V :=
    singleCutLeviAdelicEquiv B F i c (AdelicSubgroupPoints.rational F H U x)
  let r : adelicPoints F G V := AdelicSubgroupPoints.rational F G V z
  have hmatrix : a l.val = a r.val := by
    calc
      a l.val = blockShapeSingleEmbedding B (Adeles F) i
          (b (AdelicGroupPoints.rational F H x.val)) :=
        singleCutLeviAdelicEquiv_val B F i c (AdelicSubgroupPoints.rational F H U x)
      _ = blockShapeSingleEmbedding B (Adeles F) i (AdelicGL.rational F (B.size i) h) :=
        congrArg (blockShapeSingleEmbedding B (Adeles F) i)
          (GeneralLinearGroupPoints.adelicEquiv_rational F (B.size i) x.val)
      _ = AdelicGL.rational F n (blockShapeSingleEmbedding B F i h) :=
        (singleEmbedding_map B F i (algebraMap F (Adeles F)) h).symm
      _ = AdelicGL.rational F n (GeneralLinearGroupPoints.rationalEquiv F n z.val) :=
        congrArg (AdelicGL.rational F n) (singleCutLeviRationalEquiv_val B F i c x).symm
      _ = a r.val := (GeneralLinearGroupPoints.adelicEquiv_rational F n z.val).symm
  exact Subtype.ext (a.injective hmatrix)

theorem singleCutLeviAdelicEquiv_mem_rationalSubgroup_iff (x : adelicPoints F H U) :
    singleCutLeviAdelicEquiv B F i c x ∈ rationalSubgroup F G V ↔
      x ∈ rationalSubgroup F H U := by
  let a := singleCutLeviAdelicEquiv B F i c
  let q := singleCutLeviRationalEquiv B F i c
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := q.surjective y
    exact ⟨z, a.injective ((singleCutLeviAdelicEquiv_rational B F i c z).trans hy)⟩
  · rintro ⟨z, rfl⟩
    exact ⟨q z, (singleCutLeviAdelicEquiv_rational B F i c z).symm⟩

end Adelic

end Langlands.Automorphic
