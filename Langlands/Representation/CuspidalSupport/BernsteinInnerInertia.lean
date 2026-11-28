import Langlands.Representation.CuspidalSupport.BernsteinInnerStandardInduction
import Langlands.Representation.CuspidalSupport.BernsteinLeviInertiaCofan
import Langlands.Representation.CuspidalSupport.StandardLeviInertialClass
import Langlands.Representation.Exponents.RepresentedSupercuspidalityTransport
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Intrinsic and nested cuspidal data of a represented standard Levi -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u v

variable {F : Type u} [Field F] [TopologicalSpace F]
  {G M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  {ν : cocharacterLattice T} {J : Finset (SimpleRoot i ν)} {j : M ⟶ G}

local instance ambientAffine {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom H.X.hom] : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

local instance standardLeviClosed {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom H.X.hom] (s : T.toGrp ⟶ H) (ζ : cocharacterLattice T)
    (I : Finset (SimpleRoot s ζ)) :
    IsClosedImmersion (Standard.leviHom s ζ (rootSet s ζ I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom s ζ (rootSet s ζ I)

local instance standardLeviAffine {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom H.X.hom] (s : T.toGrp ⟶ H) (ζ : cocharacterLattice T)
    (I : Finset (SimpleRoot s ζ)) : IsAffine (bernsteinLeviScheme s ζ I).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom s ζ (rootSet s ζ I)).hom.hom.left

local instance canonicalTopology (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left] :
    TopologicalSpace (rationalPoints H) := pointTopology

section Cuspidality

variable [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
  [LocallyCompactSpace (rationalPoints H)] [NonarchimedeanGroup (rationalPoints H)]

local instance : T2Space F := Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F

local instance standardLeviLocallyCompact (s : T.toGrp ⟶ H) (ζ : cocharacterLattice T)
    (I : Finset (SimpleRoot s ζ)) :
    LocallyCompactSpace (rationalPoints (bernsteinLeviScheme s ζ I)) := by
  have := (isClosed_levi s ζ I).locallyCompactSpace
  exact (leviRationalPointHomeomorph s ζ I).toHomeomorph.isClosedEmbedding.locallyCompactSpace

local instance standardLeviNonarchimedean (s : T.toGrp ⟶ H) (ζ : cocharacterLattice T)
    (I : Finset (SimpleRoot s ζ)) :
    NonarchimedeanGroup (rationalPoints (bernsteinLeviScheme s ζ I)) := by
  let e := leviRationalPointHomeomorph s ζ I
  have : IsTopologicalGroup (rationalPoints (bernsteinLeviScheme s ζ I)) :=
    Topology.IsInducing.isTopologicalGroup e.toMulEquiv e.toHomeomorph.isInducing
  exact NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMulEquiv.toMonoidHom
    e.symm.toHomeomorph.isOpenEmbedding

/-- Vanishing for all proper represented parabolics gives the intrinsic
standard-Jacquet tests used in a Bernstein datum. -/
theorem bernsteinLeviCuspidal_of_isSupercuspidal (s : T.toGrp ⟶ H) (ζ : cocharacterLattice T)
    (family : BernsteinStandardFamily s ζ) (I : Finset (SimpleRoot s ζ))
    (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints (bernsteinLeviScheme s ζ I)))
    (hρ : RepresentedParabolic.IsSupercuspidal ρ) :
    Langlands.Aubert.General.IsLeviCuspidal (parabolic s ζ) (levi s ζ) (unipotent s ζ)
      family.closedUnipotent I (family.closedLevi I) (family.leviDecomposition I)
      (bernsteinLiteralLeviRep s ζ I ρ) := by
  let L := bernsteinLeviScheme s ζ I
  let sL := bernsteinLeviTorus s ζ I
  let own := bernsteinLeviStandardFamily s ζ family I
  have : Mono sL.hom.hom.left := own.maximalSplitTorus.isSplitSubtorus.mono
  have hRoots := relativeRootSystem F L own.connectedReductive T sL own.maximalSplitTorus
  let := simpleRelativeRootFintype sL hRoots own.maximalSplitTorus.isSplitSubtorus.1 ζ
  have hc := RepresentedParabolic.isCuspidal_of_all_represented_parabolics_of_standardCocharacter
    sL ζ standardCocharacter own.connectedReductive own.maximalSplitTorus own.genericCocharacter
    hRoots own.closedUnipotent ρ hρ
  let e := leviRationalPointHomeomorph s ζ I
  exact (rationalLeviCuspidalityTransport dynamicLie standardCocharacter
    F H family.connectedReductive T s family.maximalSplitTorus ζ family.genericCocharacter I
    own.connectedReductive family.closedUnipotent own.closedUnipotent (family.closedLevi I)
    (family.leviDecomposition I) own.decomposition (bernsteinLiteralLeviRep s ζ I ρ)).mp
      (hc.of_iso (SmoothRep.pullbackSymmIso e.symm ρ))

namespace BernsteinLeviPresentation

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)]
  (D : BernsteinLeviPresentation i ν J j) (family : BernsteinStandardFamily i ν)

/-- Read an intrinsic cuspidal datum in the ambient family, retaining its
inducing Levi inside the coarse label. -/
def ambientDatum (a : BernsteinCuspidalDatum.{u, v} D.torus ν (D.standardFamily family)) :
    StandardLeviCuspidalDatum.{u, v} i ν family J := by
  let L := leviIndex J (D.innerIndex family a.roots)
  let e := (D.innerLeviIso family a.roots).symm
  let ρ := rationalIsoPullback e a.representation
  have hρ : ρ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff a.representation.representation
      (rationalPointIso e)).mpr a.irreducible
  have hc : RepresentedParabolic.IsSupercuspidal ρ :=
    RepresentedParabolic.isSupercuspidal_pullback_of_iso e (rationalPointIso e)
      (rationalPointIso_apply e) a.representation
      (a.isSupercuspidal D.torus ν (D.standardFamily family))
  exact ⟨⟨L, ρ, hρ, bernsteinLeviCuspidal_of_isSupercuspidal i ν family L ρ hc⟩,
    leviIndex_subset J (D.innerIndex family a.roots)⟩

end BernsteinLeviPresentation

end Cuspidality

section Pullback

variable [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {H H' L L' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [IsAffine H'.X.left] [IsAffine L.X.left] [IsAffine L'.X.left]
  {e : H ≅ H'} {f : L ≅ L'} {c : H ≅ L} {d : H' ≅ L'}

private def conjugacyPullbackIso (h : e.symm ≪≫ c = d ≪≫ f.symm)
    (B : SmoothRep.{0, u, v} ℂ (rationalPoints L)) :
    rationalIsoPullback e.symm (rationalIsoPullback c B) ≅
      rationalIsoPullback d (rationalIsoPullback f.symm B) :=
  rationalIsoPullbackTransIso e.symm c B ≪≫
    eqToIso (congrArg (fun t => rationalIsoPullback t B) h) ≪≫
    (rationalIsoPullbackTransIso d f.symm B).symm

private theorem conjugacyPullback_nonempty_iff (h : e.symm ≪≫ c = d ≪≫ f.symm)
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints H))
    (B : SmoothRep.{0, u, v} ℂ (rationalPoints L)) :
    Nonempty (A ≅ rationalIsoPullback c B) ↔
      Nonempty (rationalIsoPullback e.symm A ≅
        rationalIsoPullback d (rationalIsoPullback f.symm B)) := by
  let t := conjugacyPullbackIso h B
  constructor
  · rintro ⟨a⟩
    exact ⟨(SmoothRep.pullbackFunctor (rationalPointIso e.symm)).mapIso a ≪≫ t⟩
  · rintro ⟨a⟩
    exact ⟨(rationalIsoPullbackCancelIso e A).symm ≪≫
      (SmoothRep.pullbackFunctor (rationalPointIso e)).mapIso (a ≪≫ t.symm) ≪≫
      rationalIsoPullbackCancelIso e _⟩

private theorem conjugacyPullback_inertia_iff
    [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType H'.X.hom]
    (h : e.symm ≪≫ c = d ≪≫ f.symm)
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints H))
    (B : SmoothRep.{0, u, v} ℂ (rationalPoints L)) :
    IsRationalInertiaRelated H A (rationalIsoPullback c B) ↔
      IsRationalInertiaRelated H' (rationalIsoPullback e.symm A)
        (rationalIsoPullback d (rationalIsoPullback f.symm B)) := by
  let t := conjugacyPullbackIso h B
  constructor
  · intro hAB
    exact (hAB.rationalIsoPullback e.symm).trans (.of_iso t)
  · intro hAB
    have h' := (hAB.trans (.of_iso t.symm)).rationalIsoPullback e
    exact (IsRationalInertiaRelated.of_iso (rationalIsoPullbackCancelIso e A).symm).trans
      (h'.trans (.of_iso (rationalIsoPullbackCancelIso e _)))

end Pullback

namespace BernsteinLeviPresentation

variable (D : BernsteinLeviPresentation i ν J j) (family : BernsteinStandardFamily i ν)

private abbrev intrinsicInclusion (K : Finset (SimpleRoot D.torus ν)) :=
  Standard.leviHom D.torus ν (rootSet D.torus ν K)

private abbrev ambientInclusion (K : Finset (SimpleRoot D.torus ν)) :=
  Standard.leviHom i ν (rootSet i ν (leviIndex J (D.innerIndex family K)))

variable {K L : Finset (SimpleRoot D.torus ν)}

/-- An intrinsic conjugacy gives an ambient conjugacy by the image of the
same rational point. -/
def ambientConjugacy (c : RationalLeviConjugacy (D.intrinsicInclusion K) (D.intrinsicInclusion L)) :
    RationalLeviConjugacy (D.ambientInclusion family K) (D.ambientInclusion family L) where
  point := rationalPoints.map j c.point
  iso := (D.innerLeviIso family K).symm ≪≫ c.iso ≪≫ D.innerLeviIso family L
  commutes := by
    let e := D.innerLeviIso family K
    let f := D.innerLeviIso family L
    have hinner : (M.innerIso c.point).hom ≫ j =
        j ≫ (G.innerIso (rationalPoints.map j c.point)).hom :=
      innerIso_hom_comp j c.point
    apply (cancel_epi e.hom).mp
    calc
      e.hom ≫ (D.ambientInclusion family K ≫ (G.innerIso (rationalPoints.map j c.point)).hom) =
          (D.intrinsicInclusion K ≫ (M.innerIso c.point).hom) ≫ j := by
        rw [← Category.assoc, D.innerLeviIso_hom_comp family K, Category.assoc,
          ← hinner, Category.assoc]
      _ = c.iso.hom ≫ (f.hom ≫ D.ambientInclusion family L) := by
        rw [c.commutes, Category.assoc, D.innerLeviIso_hom_comp family L]
      _ = e.hom ≫ ((e.symm ≪≫ c.iso ≪≫ f).hom ≫ D.ambientInclusion family L) := by
        simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

/-- An ambient conjugacy whose point belongs to the coarse Levi lifts to an
intrinsic conjugacy. -/
def intrinsicConjugacy
    (c : RationalLeviConjugacy (D.ambientInclusion family K) (D.ambientInclusion family L))
    (hc : c.point ∈ levi i ν J) :
    RationalLeviConjugacy (D.intrinsicInclusion K) (D.intrinsicInclusion L) where
  point := D.points.symm ⟨c.point, hc⟩
  iso := D.innerLeviIso family K ≪≫ c.iso ≪≫ (D.innerLeviIso family L).symm
  commutes := by
    have : Mono j.hom.hom := D.represented.1
    have : Mono j := ⟨fun f g hfg => Grp.hom_ext _ _ ((cancel_mono j.hom.hom).mp
      (by simpa only [Grp.comp_hom_hom] using congrArg (fun p => p.hom.hom) hfg))⟩
    have hp : rationalPoints.map j (D.points.symm ⟨c.point, hc⟩) = c.point := by
      rw [← D.points_apply_coe, D.points.apply_symm_apply]
    change D.points.symm ⟨c.point, hc⟩ ≫ j.hom.hom = c.point at hp
    let e := D.innerLeviIso family K
    let f := D.innerLeviIso family L
    apply (cancel_mono j).mp
    calc
      (D.intrinsicInclusion K ≫ (M.innerIso (D.points.symm ⟨c.point, hc⟩)).hom) ≫ j =
          e.hom ≫ (D.ambientInclusion family K ≫ (G.innerIso c.point).hom) := by
        rw [Category.assoc, innerIso_hom_comp, hp, ← Category.assoc,
          ← D.innerLeviIso_hom_comp family K, Category.assoc]
      _ = e.hom ≫ (c.iso.hom ≫ D.ambientInclusion family L) := by rw [c.commutes]
      _ = ((e ≪≫ c.iso ≪≫ f.symm).hom ≫ D.intrinsicInclusion L) ≫ j := by
        simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
        rw [← D.innerLeviIso_hom_comp family L, Iso.inv_hom_id_assoc]

private theorem ambientConjugacy_point_mem
    (c : RationalLeviConjugacy (D.intrinsicInclusion K) (D.intrinsicInclusion L)) :
    (D.ambientConjugacy family c).point ∈ levi i ν J := by
  change rationalPoints.map j c.point ∈ levi i ν J
  rw [← D.points_apply_coe]
  exact (D.points c.point).property

private theorem ambientConjugacy_square
    (c : RationalLeviConjugacy (D.intrinsicInclusion K) (D.intrinsicInclusion L)) :
    (D.innerLeviIso family K).symm ≪≫ c.iso =
      (D.ambientConjugacy family c).iso ≪≫ (D.innerLeviIso family L).symm := by
  simp [ambientConjugacy]

private theorem intrinsicConjugacy_square
    (c : RationalLeviConjugacy (D.ambientInclusion family K) (D.ambientInclusion family L))
    (hc : c.point ∈ levi i ν J) :
    (D.innerLeviIso family K).symm ≪≫ (D.intrinsicConjugacy family c hc).iso =
      c.iso ≪≫ (D.innerLeviIso family L).symm := by
  simp [intrinsicConjugacy]

/-- Association by an intrinsic conjugating point is equivalent to association of the
transported inducing objects by an ambient conjugating point in the coarse Levi. -/
theorem conjugatePullback_iff [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints (bernsteinLeviScheme D.torus ν K)))
    (B : SmoothRep.{0, u, v} ℂ (rationalPoints (bernsteinLeviScheme D.torus ν L))) :
    (∃ c : RationalLeviConjugacy (D.intrinsicInclusion K) (D.intrinsicInclusion L),
      Nonempty (A ≅ rationalIsoPullback c.iso B)) ↔
    ∃ c : RationalLeviConjugacy (D.ambientInclusion family K) (D.ambientInclusion family L),
      c.point ∈ levi i ν J ∧
      Nonempty (rationalIsoPullback (D.innerLeviIso family K).symm A ≅
        rationalIsoPullback c.iso (rationalIsoPullback (D.innerLeviIso family L).symm B)) := by
  constructor
  · rintro ⟨c, h⟩
    exact ⟨D.ambientConjugacy family c, D.ambientConjugacy_point_mem family c,
      (conjugacyPullback_nonempty_iff (D.ambientConjugacy_square family c) A B).mp h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨D.intrinsicConjugacy family c hc,
      (conjugacyPullback_nonempty_iff (D.intrinsicConjugacy_square family c hc) A B).mpr h⟩

variable [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType M.X.hom]
  [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)]

local instance standardLeviFiniteType {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] (s : T.toGrp ⟶ H)
    (ζ : cocharacterLattice T) (I : Finset (SimpleRoot s ζ)) :
    LocallyOfFiniteType (bernsteinLeviScheme s ζ I).X.hom := by
  rw [← (Standard.leviHom s ζ (rootSet s ζ I)).hom.hom.w]
  infer_instance

/-- The transport of cuspidal data preserves and reflects inertia in the coarse Levi. -/
theorem inertiaRelated_iff
    (a b : BernsteinCuspidalDatum.{u, v} D.torus ν (D.standardFamily family)) :
    IsBernsteinInertiaRelated D.torus ν (D.standardFamily family) a b ↔
      IsStandardLeviInertiaRelated i ν family (D.ambientDatum family a) (D.ambientDatum family b) := by
  constructor
  · rintro ⟨c, h⟩
    exact ⟨D.ambientConjugacy family c, D.ambientConjugacy_point_mem family c,
      (conjugacyPullback_inertia_iff (D.ambientConjugacy_square family c)
        a.representation b.representation).mp h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨D.intrinsicConjugacy family c hc,
      (conjugacyPullback_inertia_iff (D.intrinsicConjugacy_square family c hc)
        a.representation b.representation).mpr h⟩

/-- Write the intrinsic inertial classes in the ambient standard labels. -/
def inertialClassEmbedding :
    BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family) ↪
      StandardLeviInertialClass.{u, v} i ν family J where
  toFun := Quotient.lift (fun a => standardLeviInertialClass i ν family (D.ambientDatum family a))
    (fun a b h => (standardLeviInertialClass_eq_iff i ν family _ _).mpr
      ((D.inertiaRelated_iff family a b).mp h))
  inj' := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b h
    exact (bernsteinInertialClass_eq_iff D.torus ν (D.standardFamily family) a b).mpr
      ((D.inertiaRelated_iff family a b).mpr
        ((standardLeviInertialClass_eq_iff i ν family _ _).mp h))

@[simp]
theorem inertialClassEmbedding_class
    (a : BernsteinCuspidalDatum.{u, v} D.torus ν (D.standardFamily family)) :
    D.inertialClassEmbedding family (bernsteinInertialClass D.torus ν (D.standardFamily family) a) =
      standardLeviInertialClass i ν family (D.ambientDatum family a) := rfl

end BernsteinLeviPresentation

/-- Intrinsic inertial classes embed into the nested standard inertia quotient. -/
def BernsteinInnerInertiaStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G M : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType M.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (family : BernsteinStandardFamily i ν)
    (J : Finset (SimpleRoot i ν)) (j : M ⟶ G) (D : BernsteinLeviPresentation i ν J j),
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [LocallyCompactSpace (rationalPoints M)] [NonarchimedeanGroup (rationalPoints M)],
      ∃ e : BernsteinInertialClass.{u, v} D.torus ν (D.standardFamily family) ↪
          StandardLeviInertialClass.{u, v} i ν family J,
        ∀ a, e (bernsteinInertialClass D.torus ν (D.standardFamily family) a) =
          standardLeviInertialClass i ν family (D.ambientDatum family a)

/-- The embedding descends the transport of cuspidal data. -/
theorem bernsteinInnerInertia : BernsteinInnerInertiaStatement.{u, v} := by
  intro F _ _ _ _ G M _ _ _ _ T i ν family J j D _ _ _ _
  exact ⟨D.inertialClassEmbedding family, D.inertialClassEmbedding_class family⟩

end Langlands.CuspidalSupport
