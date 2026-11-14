import Langlands.GroupScheme.SmoothMonoLocalIso
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Equality of smooth subgroup images near a residue fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H K : GroupScheme S}

/-- A factorization between monic subgroup presentations with equal images is an isomorphism. -/
theorem isIso_factor_of_range_eq (i : H ⟶ G) (j : K ⟶ G) (f : H ⟶ K)
    [Mono i.hom.hom] [Mono j.hom.hom]
    (hf : f ≫ j = i) (heq : range i = range j) : IsIso f := by
  let hi : (range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hj : (range i).IsRepresentedBy j := ⟨inferInstance, heq.symm⟩
  let e := hi.isoOfIsRepresentedBy hj
  have hfe : f = e.hom := hj.hom_ext (hf.trans (hi.isoOfIsRepresentedBy_hom_comp hj).symm)
  rw [hfe]
  infer_instance

/-- The factor through a monic subgroup containing the image. -/
def rangeFactor (i : H ⟶ G) (j : K ⟶ G) [Mono j.hom.hom.left]
    (hle : range i ≤ range j) : H ⟶ K :=
  (show (range j).IsRepresentedBy j from ⟨Over.mono_of_mono_left _, rfl⟩).factorHom i hle

theorem rangeFactor_comp (i : H ⟶ G) (j : K ⟶ G) [Mono j.hom.hom.left]
    (hle : range i ≤ range j) : rangeFactor i j hle ≫ j = i :=
  IsRepresentedBy.factorHom_comp _ _ _

instance rangeFactor_mono (i : H ⟶ G) (j : K ⟶ G)
    [Mono i.hom.hom.left] [Mono j.hom.hom.left] (hle : range i ≤ range j) :
    Mono (rangeFactor i j hle).hom.hom.left :=
  mono_of_mono_fac (congrArg (fun a => a.hom.hom.left) (rangeFactor_comp i j hle))

/-- The canonical base open on which a smooth subgroup inclusion is an isomorphism. -/
def rangeEqualityOpen (i : H ⟶ G) (j : K ⟶ G)
    [Smooth H.X.hom] [Smooth K.X.hom] [Mono j.hom.hom.left]
    (hle : range i ≤ range j) : S.Opens :=
  SmoothMonoLocalIso.unitEtaleOpen (rangeFactor i j hle)

theorem mem_rangeEqualityOpen_of_residue_range_eq (i : H ⟶ G) (j : K ⟶ G)
    [Smooth H.X.hom] [Smooth K.X.hom]
    [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (hle : range i ≤ range j) (s : S)
    (heq : range ((GroupScheme.baseChange (S.fromSpecResidueField s)).map i) =
      range ((GroupScheme.baseChange (S.fromSpecResidueField s)).map j)) :
    s ∈ rangeEqualityOpen i j hle := by
  let B := GroupScheme.baseChange (S.fromSpecResidueField s)
  have hf : B.map (rangeFactor i j hle) ≫ B.map j = B.map i := by
    rw [← B.map_comp, rangeFactor_comp]
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : Mono (B.map i).hom.hom := by
    change Mono ((Over.pullback (S.fromSpecResidueField s)).map i.hom.hom)
    infer_instance
  have : Mono (B.map j).hom.hom := by
    change Mono ((Over.pullback (S.fromSpecResidueField s)).map j.hom.hom)
    infer_instance
  have : IsIso (B.map (rangeFactor i j hle)) :=
    isIso_factor_of_range_eq (B.map i) (B.map j) _ hf heq
  have hs : IsIso ((B.map (rangeFactor i j hle)).hom.hom.left) :=
    inferInstanceAs (IsIso (((Grp.forget _).comp (Over.forget _)).map
      (B.map (rangeFactor i j hle))))
  exact SmoothMonoLocalIso.mem_unitEtaleOpen_of_residueFiber _ s hs

/-- On the canonical equality open the two subgroup images agree on every test scheme. -/
theorem range_eq_on_rangeEqualityOpen (i : H ⟶ G) (j : K ⟶ G)
    [Smooth H.X.hom] [Smooth K.X.hom]
    [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    [GeometricallyConnected K.X.hom] (hle : range i ≤ range j) :
    range ((GroupScheme.baseChange (rangeEqualityOpen i j hle).ι).map i) =
      range ((GroupScheme.baseChange (rangeEqualityOpen i j hle).ι).map j) := by
  let V := rangeEqualityOpen i j hle
  let B := GroupScheme.baseChange V.ι
  let f := B.map (rangeFactor i j hle)
  have : IsIso f.hom.hom.left := SmoothMonoLocalIso.isIso_unitEtaleOpen _
  have : IsIso ((Over.forget _).map f.hom.hom) := by
    change IsIso f.hom.hom.left
    infer_instance
  have : IsIso f.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map f.hom) := by
    change IsIso f.hom.hom
    infer_instance
  have : IsIso f.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map f) := by
    change IsIso f.hom
    infer_instance
  have : IsIso f := isIso_of_reflects_iso _ (Grp.forget₂Mon _)
  have hf : f ≫ B.map j = B.map i := by
    rw [← B.map_comp, rangeFactor_comp]
  rw [← hf]
  exact range_iso_comp (asIso f) _

/-- Containment and equality in one residue fibre give equality on an open neighbourhood. -/
theorem exists_open_range_eq_of_residue_range_eq (i : H ⟶ G) (j : K ⟶ G)
    [Smooth H.X.hom] [Smooth K.X.hom]
    [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    [GeometricallyConnected K.X.hom] (hle : range i ≤ range j) (s : S)
    (heq : range ((GroupScheme.baseChange (S.fromSpecResidueField s)).map i) =
      range ((GroupScheme.baseChange (S.fromSpecResidueField s)).map j)) :
    ∃ V : S.Opens, s ∈ V ∧ range ((GroupScheme.baseChange V.ι).map i) =
      range ((GroupScheme.baseChange V.ι).map j) :=
  ⟨rangeEqualityOpen i j hle, mem_rangeEqualityOpen_of_residue_range_eq i j hle s heq,
    range_eq_on_rangeEqualityOpen i j hle⟩

end Langlands.GroupScheme.SubgroupFunctor
