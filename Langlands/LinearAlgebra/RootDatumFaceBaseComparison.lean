import Langlands.LinearAlgebra.RootDatumFaceHeight

/-! # Independence of integral face heights from the adapted base -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.LinearAlgebra.RootDatumFaceBaseComparison

open RootDatumWeylChambers RootDatumBasedCorrection RootDatumFaceHeight
open IsAddIndecomposable

variable {J M N : Type*} [AddCommGroup M] [AddCommGroup N]
  (P : RootDatum J M N)

private theorem maps_baseOf_of_signs (f g : M →+ ℤ) (w : P.Aut)
    (hpos : ∀ i, 0 < f (P.root i) ↔ 0 < g (P.root (w.indexEquiv i))) :
    ∀ i ∈ baseOf P.root f, w.indexEquiv i ∈ baseOf P.root g := by
  intro i hi
  refine ⟨(hpos i).mp hi.1, ?_⟩
  intro j hj k hk hdec
  change 0 < g (P.root j) at hj
  change 0 < g (P.root k) at hk
  have hroot (l : J) :
      w.weightEquiv.symm (P.root l) = P.root (w.indexEquiv.symm l) := by
    apply w.weightEquiv.injective
    simp [RootPairing.Hom.root_weightMap_apply]
  have hd := congrArg w.weightEquiv.symm hdec
  simp only [map_add, hroot, Equiv.symm_apply_apply] at hd
  have hj' : 0 < f (P.root (w.indexEquiv.symm j)) := by
    apply (hpos _).mpr
    simpa only [Equiv.apply_symm_apply] using hj
  have hk' : 0 < f (P.root (w.indexEquiv.symm k)) := by
    apply (hpos _).mpr
    simpa only [Equiv.apply_symm_apply] using hk
  rcases hi.2 _ hj' _ hk' hd with hj0 | hk0
  · exact False.elim (P.ne_zero _ hj0)
  · exact False.elim (P.ne_zero _ hk0)

/-- A root-datum automorphism matching two positive-root sign systems maps
their indecomposable positive-root sets bijectively. -/
theorem mem_baseOf_iff_of_signs (f g : M →+ ℤ) (w : P.Aut)
    (hpos : ∀ i, 0 < f (P.root i) ↔ 0 < g (P.root (w.indexEquiv i))) (i : J) :
    i ∈ baseOf P.root f ↔ w.indexEquiv i ∈ baseOf P.root g := by
  constructor
  · exact maps_baseOf_of_signs P f g w hpos i
  · intro hi
    have hpos' (j : J) :
        0 < g (P.root j) ↔ 0 < f (P.root (w.symm.indexEquiv j)) := by
      simpa only [RootPairing.Equiv.inv_indexEquiv, Equiv.apply_symm_apply] using
        (hpos (w.indexEquiv.symm j)).symm
    simpa using maps_baseOf_of_signs P g f w.symm hpos' (w.indexEquiv i) hi

variable [Fintype J] [P.IsReduced] (cv : N)
  [Finite (reflectionSubgroup P {i | P.root' i cv = 0})]

/-- Two sign-refining bases of the same coweight face are aligned by a
reflection-group element generated only by its zero roots. -/
structure FaceAlignment (F F' : RootDatumCoweightFace.Face P cv) where
  weyl : reflectionSubgroup P {i | P.root' i cv = 0}
  support : ∀ i, i ∈ F.base.support ↔ weyl.val.indexEquiv i ∈ F'.base.support

theorem nonempty_faceAlignment (F F' : RootDatumCoweightFace.Face P cv) :
    Nonempty (FaceAlignment P cv F F') := by
  obtain ⟨w, hw⟩ := exists_same_signs P {i | P.root' i cv = 0} F.nonzero F'.nonzero
  have heval : ∀ i, P.root' (w.val.indexEquiv i) cv = P.root' i cv :=
    root_evaluation_eq P w.val cv (fixes_coweight P cv w)
  have hsign (i : J) :
      0 < P.root' i F.regular ↔ 0 < P.root' (w.val.indexEquiv i) F'.regular := by
    by_cases hi : P.root' i cv = 0
    · have h := hw i hi
      have he := w.val.root'_coweightEquiv i (w.val.coweightEquiv F'.regular)
      simp only [LinearEquiv.symm_apply_apply] at he
      rwa [← he] at h
    · have hi' : P.root' (w.val.indexEquiv i) cv ≠ 0 := by rwa [heval i]
      exact (F.signs i hi).trans ((by rw [heval i] :
        0 < P.root' i cv ↔ 0 < P.root' (w.val.indexEquiv i) cv).trans
          (F'.signs _ hi').symm)
  refine ⟨⟨w, fun i => ?_⟩⟩
  have h := mem_baseOf_iff_of_signs P
    ((P.flip.toLinearMap F.regular) : M →+ ℤ)
    ((P.flip.toLinearMap F'.regular) : M →+ ℤ) w.val hsign i
  simpa only [← F.support_eq, ← F'.support_eq, Finset.mem_coe] using h

/-- Choose an alignment of two bases adapted to one coweight face. -/
def faceAlignment (F F' : RootDatumCoweightFace.Face P cv) : FaceAlignment P cv F F' :=
  Classical.choice (nonempty_faceAlignment P cv F F')

/-- The exact integral face height is independent of the sign-refining base.
No positive rescaling occurs in this equality on the entire root span. -/
theorem faceHeight_eq (F F' : RootDatumCoweightFace.Face P cv) :
    faceHeight F.base cv = faceHeight F'.base cv := by
  let A := faceAlignment P cv F F'
  have hcomp : (faceHeight F'.base cv).comp (rootSpanMap A.weyl.val) =
      faceHeight F.base cv := by
    apply F.base.toWeightBasisInt.ext
    intro a
    have ha : F.base.toWeightBasisInt a = P.rootSpanMem ℤ a := by
      ext
      simp
    rw [LinearMap.comp_apply, ha, rootSpanMap_rootSpanMem,
      faceHeight_simple F'.base cv _ ((A.support a).mp a.property),
      faceHeight_simple F.base cv a a.property,
      root_evaluation_eq P A.weyl.val cv (fixes_coweight P cv A.weyl) a]
  exact hcomp.symm.trans
    (faceHeight_comp_rootSpanMap_of_mem (face_dominant F') A.weyl.property)

end Langlands.LinearAlgebra.RootDatumFaceBaseComparison
