import Langlands.GroupScheme.ChevalleyIntegral.NeutralCoordinates
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-! # Neutral field isomorphisms from nonempty open cells -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ChevalleyIntegral

open SplitExistence SplitExistence.ChevalleyData

variable {I J : Type u}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base}
  (D : ChevalleyData P b)
  (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K)
  {N : GroupScheme (Spec (CommRingCat.of R))}
  {iN : N ⟶ (genericModel D R K C).group}
  (hi : IsRelativeIdentityComponent (genericModel D R K C).group iN)
  [GeometricallyConnected N.X.hom] [Smooth N.X.hom] [IsAffineHom N.X.hom]
  (k : Type u) [Field k] [Algebra R k] (H : D.ChevGroup k)

/-- A nonempty full-fibre open contained in the field Chevalley subgroup makes its
closed embedding into the neutral fibre an isomorphism. -/
theorem isIso_neutralFieldEmbedding_of_open
    (U : (fieldModel D R K C k (CommRingCat.ofHom (algebraMap R k))).X.left.Opens)
    (hUne : U.1.Nonempty)
    (hU : U.1 ⊆ Set.range
      (fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H).hom.hom.left) :
    IsIso (neutralFieldEmbedding D R K C hi k H) := by
  let Nk := (baseChange (Spec.algebraMap R k)).obj N
  let j := (baseChange (Spec.algebraMap R k)).map iN
  let f := neutralFieldEmbedding D R K C hi k H
  let e := fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H
  have hcomp : f.hom.hom.left ≫ j.hom.hom.left = e.hom.hom.left :=
    congrArg (fun a => a.hom.hom.left) (neutralFieldEmbedding_comp D R K C hi k H)
  have hpoint (y : H.H.X.left) : j.hom.hom.left (f.hom.hom.left y) = e.hom.hom.left y :=
    congrArg (fun a => a y) hcomp
  let V : Set Nk.X.left := j.hom.hom.left ⁻¹' U.1
  have hVo : IsOpen V := U.isOpen.preimage j.hom.hom.left.continuous
  have hVne : V.Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    obtain ⟨y, hy⟩ := hU hx
    refine ⟨f.hom.hom.left y, ?_⟩
    change j.hom.hom.left (f.hom.hom.left y) ∈ U.1
    rw [hpoint, hy]
    exact hx
  have hj : IsOpenImmersion j.hom.hom.left :=
    (hi.baseChange (Spec.algebraMap R k)).isOpenImmersion
  let := hj
  have hVrange : V ⊆ Set.range f.hom.hom.left := by
    intro x hx
    obtain ⟨y, hy⟩ := hU hx
    refine ⟨y, j.hom.hom.left.isOpenEmbedding.injective ?_⟩
    exact (hpoint y).trans hy
  let : Smooth Nk.X.hom :=
    inferInstanceAs (Smooth (pullback.snd N.X.hom (Spec.algebraMap R k)))
  let : IsAffineHom Nk.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd N.X.hom (Spec.algebraMap R k)))
  let : ConnectedSpace Nk.X.left :=
    connectedSpace_baseChange_of_geometricallyConnected N (Spec.algebraMap R k)
  let : GeometricallyIntegral Nk.X.hom :=
    smoothConnectedAffineGeometry.1 k Nk inferInstance inferInstance inferInstance
  let : IsIntegral Nk.X.left := GeometricallyIntegral.isIntegral_of_subsingleton Nk.X.hom
  have hf : IsClosedImmersion f.hom.hom.left := neutralFieldEmbedding_closed D R K C hi k H
  let := hf
  let : Surjective f.hom.hom.left := ⟨fun x =>
    (hVo.dense hVne).induction hVrange
      (IsClosedImmersion.isClosedEmbedding f.hom.hom.left).isClosed_range x⟩
  have : IsIso f.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map f.hom.hom) := ‹IsIso f.hom.hom.left›
  have : IsIso f.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map f.hom) := ‹IsIso f.hom.hom›
  have : IsIso f.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map f) := ‹IsIso f.hom›
  exact isIso_of_reflects_iso f (Grp.forget₂Mon _)

/-- The actual field comparison obtained from an open cell in the full field fibre. -/
def neutralFieldIsoOfOpen
    (U : (fieldModel D R K C k (CommRingCat.ofHom (algebraMap R k))).X.left.Opens)
    (hUne : U.1.Nonempty)
    (hU : U.1 ⊆ Set.range
      (fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H).hom.hom.left) :
    H.H ≅ (baseChange (Spec.algebraMap R k)).obj N := by
  let := isIso_neutralFieldEmbedding_of_open D R K C hi k H U hUne hU
  exact asIso (neutralFieldEmbedding D R K C hi k H)

@[reassoc]
theorem neutralFieldIsoOfOpen_hom_comp
    (U : (fieldModel D R K C k (CommRingCat.ofHom (algebraMap R k))).X.left.Opens)
    (hUne : U.1.Nonempty)
    (hU : U.1 ⊆ Set.range
      (fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H).hom.hom.left) :
    (neutralFieldIsoOfOpen D R K C hi k H U hUne hU).hom ≫
        (baseChange (Spec.algebraMap R k)).map iN =
      fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H :=
  neutralFieldEmbedding_comp D R K C hi k H

variable [Fintype I] [DecidableEq I]

/-- Nonempty opens contained in the field Chevalley subgroups supply all comparisons
for the same smooth affine neutral family. -/
theorem hasFieldComparisons_of_fullFieldOpen [Finite J]
    (h : ∀ (k : Type u) [Field k] [Algebra R k],
      ∃ (H : D.ChevGroup k)
        (U : (fieldModel D R K C k (CommRingCat.ofHom (algebraMap R k))).X.left.Opens),
        U.1.Nonempty ∧ U.1 ⊆ Set.range
          (fieldEmbedding D R K C k (CommRingCat.ofHom (algebraMap R k)) H).hom.hom.left) :
    HasFieldComparisons D N (neutralCoordinateTorus D R K C hi) := by
  apply hasFieldComparisons_of_neutralFieldEmbedding_isIso D R K C hi
  intro k _ _
  obtain ⟨H, U, hUne, hU⟩ := h k
  exact ⟨H, isIso_neutralFieldEmbedding_of_open D R K C hi k H U hUne hU⟩

end Langlands.GroupScheme.ChevalleyIntegral
