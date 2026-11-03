import Langlands.Global.CurvePlaceNonemptyLevelColimitStatement
import Langlands.Global.CurvePlaceAdeleLevelTopologyProof
import Langlands.Global.FiniteAdeleLevelColimitProof

/-! # Colimits over nonempty finite sets of actual curve places -/

noncomputable section

universe u

open CategoryTheory Limits Topology

namespace Langlands.Global

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  [Nonempty (AlgebraicCurve.Place k F)]

theorem exists_mem_curvePlaceNonemptyAdeleLevel (a : CurvePlaceAdeleRing k F) :
    ∃ S : CurvePlaceNonemptyLevelIndex k F, a ∈ curvePlaceAdeleLevel k F S.val := by
  obtain ⟨S, ha⟩ := exists_mem_curvePlaceAdeleLevel k F a
  let p : AlgebraicCurve.Place k F := Classical.choice inferInstance
  exact ⟨curvePlaceNonemptyLevelEnlarge k F p S,
    curvePlaceAdeleLevel_mono k F (curvePlaceNonemptyLevelEnlarge_le k F p S) ha⟩

theorem continuous_iff_curvePlaceNonemptyAdeleLevel {X : Type u} [TopologicalSpace X]
    (f : CurvePlaceAdeleRing k F → X) :
    Continuous f ↔ ∀ S : CurvePlaceNonemptyLevelIndex k F,
      Continuous (f ∘ (curvePlaceAdeleLevel k F S.val).subtype) := by
  refine ⟨fun h _ => h.comp continuous_subtype_val, ?_⟩
  intro h
  rw [continuous_iff_continuousAt]
  intro a
  obtain ⟨S, ha⟩ := exists_mem_curvePlaceNonemptyAdeleLevel k F a
  exact ((isOpen_curvePlaceAdeleLevel k F S.val).isOpenEmbedding_subtypeVal.continuousAt_iff).mp
    ((h S).continuousAt (x := ⟨a, ha⟩))

/-- Extend a compatible family by applying the subring-cover construction to enlarged levels. -/
def curvePlaceNonemptyAdeleLevelRingDesc
    (c : Cocone (curvePlaceNonemptyAdeleLevelRingDiagram k F)) :
    CurvePlaceAdeleRing k F →+* c.pt :=
  let p : AlgebraicCurve.Place k F := Classical.choice inferInstance
  let E := curvePlaceNonemptyLevelEnlarge k F p
  SubringCover.desc (B := c.pt) (fun S => curvePlaceAdeleLevel k F (E S).val)
    (fun _ _ h => curvePlaceAdeleLevel_mono k F (E.monotone h))
    (fun a => by
      obtain ⟨S, ha⟩ := exists_mem_curvePlaceAdeleLevel k F a
      exact ⟨S, curvePlaceAdeleLevel_mono k F
        (curvePlaceNonemptyLevelEnlarge_le k F p S) ha⟩)
    (fun S => (c.ι.app (E S)).hom)
    (fun _S _T h => congrArg CommRingCat.Hom.hom (c.w (homOfLE (E.monotone h))))

theorem curvePlaceNonemptyAdeleLevelRingDesc_apply
    (c : Cocone (curvePlaceNonemptyAdeleLevelRingDiagram k F))
    (S : CurvePlaceNonemptyLevelIndex k F) (a : curvePlaceAdeleLevel k F S.val) :
    curvePlaceNonemptyAdeleLevelRingDesc k F c a.val = (c.ι.app S).hom a := by
  let p : AlgebraicCurve.Place k F := Classical.choice inferInstance
  let E := curvePlaceNonemptyLevelEnlarge k F p
  let b : curvePlaceAdeleLevel k F (E S.val).val :=
    ⟨a.val, curvePlaceAdeleLevel_mono k F
      (curvePlaceNonemptyLevelEnlarge_le k F p S.val) a.property⟩
  calc
    curvePlaceNonemptyAdeleLevelRingDesc k F c a.val = (c.ι.app (E S.val)).hom b :=
      SubringCover.desc_apply (B := c.pt)
        (fun T => curvePlaceAdeleLevel k F (E T).val)
        (fun _ _ h => curvePlaceAdeleLevel_mono k F (E.monotone h))
        (fun x => by
          obtain ⟨T, hx⟩ := exists_mem_curvePlaceAdeleLevel k F x
          exact ⟨T, curvePlaceAdeleLevel_mono k F
            (curvePlaceNonemptyLevelEnlarge_le k F p T) hx⟩)
        (fun T => (c.ι.app (E T)).hom)
        (fun _T _U h => congrArg CommRingCat.Hom.hom (c.w (homOfLE (E.monotone h))))
        S.val b
    _ = (c.ι.app S).hom a :=
      congrArg (fun f => f.hom a)
        (c.w (homOfLE (curvePlaceNonemptyLevelEnlarge_le k F p S.val) : S ⟶ E S.val))

def curvePlaceNonemptyAdeleLevelRingIsColimit :
    IsColimit (curvePlaceNonemptyAdeleLevelRingCocone k F) where
  desc c := CommRingCat.ofHom (curvePlaceNonemptyAdeleLevelRingDesc k F c)
  fac c S := by
    ext a
    exact curvePlaceNonemptyAdeleLevelRingDesc_apply k F c S a
  uniq c m hm := by
    ext a
    obtain ⟨S, ha⟩ := exists_mem_curvePlaceNonemptyAdeleLevel k F a
    have h := congrArg (fun f => f.hom ⟨a, ha⟩) (hm S)
    exact h.trans (curvePlaceNonemptyAdeleLevelRingDesc_apply k F c S ⟨a, ha⟩).symm

def curvePlaceNonemptyAdeleLevelIsColimit :
    IsColimit (curvePlaceNonemptyAdeleLevelCocone k F) where
  desc c := by
    let f : CurvePlaceAdeleRing k F →+* c.pt :=
      curvePlaceNonemptyAdeleLevelRingDesc k F
        ((forget₂ TopCommRingCat CommRingCat).mapCocone c)
    refine ⟨f, ?_⟩
    apply (continuous_iff_curvePlaceNonemptyAdeleLevel k F (X := c.pt) f).mpr
    intro S
    have heq : (f ∘ (curvePlaceAdeleLevel k F S.val).subtype) =
        (c.ι.app S).val := by
      funext a
      exact curvePlaceNonemptyAdeleLevelRingDesc_apply k F _ S a
    exact heq.symm ▸ (c.ι.app S).property
  fac c S := by
    apply Subtype.ext
    ext a
    exact curvePlaceNonemptyAdeleLevelRingDesc_apply k F _ S a
  uniq c m hm := by
    apply Subtype.ext
    ext a
    obtain ⟨S, ha⟩ := exists_mem_curvePlaceNonemptyAdeleLevel k F a
    have h := congrArg (fun f => f.val ⟨a, ha⟩) (hm S)
    exact h.trans (curvePlaceNonemptyAdeleLevelRingDesc_apply k F
      ((forget₂ TopCommRingCat CommRingCat).mapCocone c) S ⟨a, ha⟩).symm

/-- The exact exhaustion, final topology and both categorical colimit assertions. -/
theorem curvePlaceNonemptyLevelColimit : CurvePlaceNonemptyLevelColimitStatement.{u} := by
  intro k F _ _ _ _
  exact ⟨exists_mem_curvePlaceNonemptyAdeleLevel k F,
    fun _ _ => continuous_iff_curvePlaceNonemptyAdeleLevel k F,
    ⟨curvePlaceNonemptyAdeleLevelIsColimit k F⟩,
    ⟨curvePlaceNonemptyAdeleLevelRingIsColimit k F⟩⟩

end Langlands.Global
