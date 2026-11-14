import Langlands.AlgebraicGeometry.FiberwiseOpenImmersion
import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # Relative maximal tori with smooth centralizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section GeneralBase

variable {S : Scheme.{u}} {G C : GroupScheme S} {T : CommGroupScheme S}
  (t : T.toGrp ⟶ G) (c : C ⟶ G)

/-- The canonical map into a smooth representative of the centralizer is an
isomorphism when the smooth source equals its centralizer on every residue fibre. -/
def torusCentralizerFactorIsoOfResidueFibres
    [Smooth T.X.hom] [Smooth C.X.hom]
    (ht : IsClosedSubgroup t)
    (hc : (torusCentralizer t).IsRepresentedBy c)
    (hself : ∀ s : S,
      torusCentralizer (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
          ((baseChange (S.fromSpecResidueField s)).map t) =
        SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map t)) :
    T.toGrp ≅ C := by
  let f := torusCentralizerFactor t hc
  have hf : f ≫ c = t := torusCentralizerFactor_comp t hc
  have hfib : ∀ s : S,
      IsIso ((Over.pullback (S.fromSpecResidueField s)).map f.hom.hom).left := by
    intro s
    let b := S.fromSpecResidueField s
    let B := baseChange b
    have hcB : (torusCentralizer
        (T := (CommGroupScheme.baseChange b).obj T) (B.map t)).IsRepresentedBy (B.map c) := by
      rw [torusCentralizer_baseChange]
      exact hc.baseChange b
    have htB : IsClosedSubgroup (B.map t) := ht.baseChange b
    let : IsClosedImmersion (B.map t).hom.hom.left := htB
    let : Mono (B.map t).hom.hom := Over.mono_of_mono_left _
    have htRep : (torusCentralizer
        (T := (CommGroupScheme.baseChange b).obj T) (B.map t)).IsRepresentedBy (B.map t) :=
      ⟨inferInstance, (hself s).symm⟩
    let e := htRep.isoOfIsRepresentedBy hcB
    have he : B.map f = e.hom := by
      apply hcB.hom_ext
      rw [SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp,
        ← Functor.map_comp, hf]
    have : IsIso (B.map f) := by rw [he]; infer_instance
    exact Functor.map_isIso
      (Grp.forget₂Mon _ ⋙ Mon.forget _ ⋙ Over.forget _) (B.map f)
  have hopen : IsOpenImmersion f.hom.hom.left :=
    Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise f.hom.hom
      (fun s => by have := hfib s; infer_instance)
  have hsurj : Surjective f.hom.hom.left := by
    refine ⟨fun w => ?_⟩
    let s : S := C.X.hom w
    obtain ⟨w', hw', -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := C.X.hom) (g := S.fromSpecResidueField s) w
      (IsLocalRing.closedPoint (S.residueField s))
      (Scheme.fromSpecResidueField_apply _ _).symm
    have := hfib s
    obtain ⟨x', hx'⟩ :=
      (((Over.pullback (S.fromSpecResidueField s)).map f.hom.hom).left).surjective w'
    have key : pullback.fst T.X.hom (S.fromSpecResidueField s) ≫ f.hom.hom.left =
        ((Over.pullback (S.fromSpecResidueField s)).map f.hom.hom).left ≫
          pullback.fst C.X.hom (S.fromSpecResidueField s) :=
      (pullback.lift_fst _ _ _).symm
    refine ⟨pullback.fst T.X.hom (S.fromSpecResidueField s) x', ?_⟩
    rw [← hw', ← hx', ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, key]
  have : IsIso f.hom.hom.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hopen, hsurj⟩
  have : IsIso ((Over.forget S).map f.hom.hom) := ‹IsIso f.hom.hom.left›
  have : IsIso f.hom.hom := isIso_of_reflects_iso _ (Over.forget S)
  have : IsIso ((Mon.forget _).map f.hom) := ‹IsIso f.hom.hom›
  have : IsIso f.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map f) := ‹IsIso f.hom›
  have : IsIso f := isIso_of_reflects_iso _ (Grp.forget₂Mon _)
  exact asIso f

@[reassoc (attr := simp)]
theorem torusCentralizerFactorIsoOfResidueFibres_hom_comp
    [Smooth T.X.hom] [Smooth C.X.hom]
    (ht : IsClosedSubgroup t)
    (hc : (torusCentralizer t).IsRepresentedBy c)
    (hself : ∀ s : S,
      torusCentralizer (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
          ((baseChange (S.fromSpecResidueField s)).map t) =
        SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map t)) :
    (torusCentralizerFactorIsoOfResidueFibres t c ht hc hself).hom ≫ c = t :=
  torusCentralizerFactor_comp t hc

/-- Smooth closed tori with self-centralizing residue fibres equal their
whole centralizer whenever that centralizer has a smooth representative. -/
theorem torusCentralizer_eq_range_of_residueFibres
    [Smooth T.X.hom] [Smooth C.X.hom]
    (ht : IsClosedSubgroup t)
    (hc : (torusCentralizer t).IsRepresentedBy c)
    (hself : ∀ s : S,
      torusCentralizer (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
          ((baseChange (S.fromSpecResidueField s)).map t) =
        SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map t)) :
    torusCentralizer t = SubgroupFunctor.range t := by
  let e := torusCentralizerFactorIsoOfResidueFibres t c ht hc hself
  have he : e.hom ≫ c = t :=
    torusCentralizerFactorIsoOfResidueFibres_hom_comp t c ht hc hself
  rw [← hc.2, ← he, SubgroupFunctor.range_iso_comp]

end GeneralBase

/-- A fibrewise maximal closed split torus in a reductive group over any
commutative ring is its whole centralizer on every test scheme. -/
theorem splitTorusCentralizer_eq_range_of_fibrewiseMaximal_overRing
    {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} (hG : IsReductive G)
    {T : CommGroupScheme (Spec R)} (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) :
    torusCentralizer t = SubgroupFunctor.range t := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth T.X.hom := hT.smooth
  obtain ⟨C, c, _, hCsmooth, hc⟩ :=
    splitTorusCentralizer_hasSmoothClosedRepresentative_overRing t hT hG.smooth
  let : Smooth C.X.hom := hCsmooth
  apply torusCentralizer_eq_range_of_residueFibres t c ht hc
  intro s
  exact maximalTorusCentralizer ((Spec R).residueField s)
    ((baseChange ((Spec R).fromSpecResidueField s)).obj G)
    (hG.isConnectedReductive_residueFiber s)
    ((CommGroupScheme.baseChange ((Spec R).fromSpecResidueField s)).obj T)
    ((baseChange ((Spec R).fromSpecResidueField s)).map t) (hmax s)

end Langlands.GroupScheme
