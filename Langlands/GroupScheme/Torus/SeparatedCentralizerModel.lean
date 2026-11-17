import Langlands.GroupScheme.FixedSubgroupRepresentabilityProof
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Torus.RelativeCentralizerDescent
import Mathlib.LinearAlgebra.TensorProduct.Free

/-! # Closed centralizers of relative tori in separated groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Diagonalizable

/-- The coordinates of an actual diagonalizable group form a free module,
via the relative global-sections comparison with its group algebra. -/
theorem free_coordinateModule (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ] :
    Module.Free R (((algΓ R).obj (groupScheme R Λ).toGrp.X).unop) := by
  exact Module.Free.of_equiv
    (Corepresented.affineSectionsAlgEquiv (algebra R Λ)).toLinearEquiv.symm

/-- The identity extension witnesses fpqc projectivity of diagonalizable
coordinates, without a finite-generation hypothesis on the character group. -/
theorem hasFpqcProjectiveCoordinateModule (R : CommRingCat.{u}) (Λ : Type u)
    [AddCommGroup Λ] : HasFpqcProjectiveCoordinateModule (groupScheme R Λ).toGrp := by
  let : Module.Free R (((algΓ R).obj (groupScheme R Λ).toGrp.X).unop) :=
    free_coordinateModule R Λ
  exact ⟨CommAlgCat.of R R, inferInstance, inferInstance⟩

/-- A diagonalizable group is flat over its affine base because its group
algebra is a free module. -/
theorem flat_structure (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ] :
    Flat (groupScheme R Λ).toGrp.X.hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R Λ))))
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- The centralizer of any diagonalizable-group homomorphism into a separated
group over an affine base has an actual closed representative. -/
theorem centralizer_isClosedRepresentable (R : CommRingCat.{u}) (Λ : Type u)
    [AddCommGroup Λ] {G : GroupScheme (Spec R)} [IsSeparated G.X.hom]
    (t : (groupScheme R Λ).toGrp ⟶ G) :
    (torusCentralizer t).IsClosedRepresentable := by
  have h := fixedSubgroupRepresentability R (groupScheme R Λ).toGrp G
    inferInstance (flat_structure R Λ) (hasFpqcProjectiveCoordinateModule R Λ)
    inferInstance (AutomorphicAction.conjugation t)
  rwa [AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer] at h

end Diagonalizable

/-- Over an affine base, a split torus has a closed centralizer in every
separated ambient group, without smoothness or affineness assumptions. -/
theorem splitTorusCentralizer_isClosedRepresentable_overRing
    {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsSeparated G.X.hom]
    {T : CommGroupScheme (Spec R)} (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) :
    (torusCentralizer t).IsClosedRepresentable := by
  classical
  obtain ⟨I, hI, ⟨eT⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let e := Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ)) ≪≫ eT.symm
  have h := Diagonalizable.centralizer_isClosedRepresentable R (I → ℤ) (e.hom ≫ t)
  rw [torusCentralizer_eq_centralizer_range, SubgroupFunctor.range_precomp_iso,
    ← torusCentralizer_eq_centralizer_range] at h
  exact h

/-- Closed centralizer representability descends along an etale cover. -/
theorem torusCentralizer_isClosedRepresentable_of_etaleCover
    {S : Scheme.{u}} {G : GroupScheme S} {T : CommGroupScheme S}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S) (t : T.toGrp ⟶ G)
    (h : ∀ i, ((torusCentralizer t).baseChange (𝒰.f i)).IsClosedRepresentable) :
    (torusCentralizer t).IsClosedRepresentable := by
  rw [torusCentralizer_eq_coverDescent 𝒰 t]
  exact SubgroupFunctor.CoverDescent.isClosedRepresentable_subgroup_etale 𝒰 _
    (SubgroupFunctor.CoverDescent.isMatching_baseChange 𝒰 (torusCentralizer t)) h

/-- A split torus has a closed centralizer in a separated ambient group over
an arbitrary base. -/
theorem splitTorusCentralizer_isClosedRepresentable_of_separated
    {S : Scheme.{u}} {G : GroupScheme S} [IsSeparated G.X.hom]
    {T : CommGroupScheme S} (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) :
    (torusCentralizer t).IsClosedRepresentable := by
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    S.affineOpenCover.openCover.changeProp (fun i => inferInstance)
  apply torusCentralizer_isClosedRepresentable_of_etaleCover 𝒰 t
  intro i
  let b := S.affineOpenCover.f i
  let B := baseChange b
  let : IsSeparated (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  change ((torusCentralizer t).baseChange b).IsClosedRepresentable
  rw [← torusCentralizer_baseChange b (T := T) t]
  exact splitTorusCentralizer_isClosedRepresentable_overRing
    (T := (CommGroupScheme.baseChange b).obj T) (B.map t) (hT.baseChange b)

/-- Every relative-torus homomorphism into a separated group has an actual
closed centralizer, on all schemes over an arbitrary base. -/
theorem relativeTorusCentralizer_isClosedRepresentable_of_separated
    {S : Scheme.{u}} {G : GroupScheme S} [IsSeparated G.X.hom]
    {T : CommGroupScheme S} (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp) :
    (torusCentralizer t).IsClosedRepresentable := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  apply torusCentralizer_isClosedRepresentable_of_etaleCover 𝒰 t
  intro i
  let b := 𝒰.f i
  let B := baseChange b
  let : IsSeparated (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  change ((torusCentralizer t).baseChange b).IsClosedRepresentable
  rw [← torusCentralizer_baseChange b (T := T) t]
  exact splitTorusCentralizer_isClosedRepresentable_of_separated
    (T := (CommGroupScheme.baseChange b).obj T) (B.map t) (h𝒰 i)

/-- Choose the actual closed centralizer and its all-test representing
homomorphism in a separated ambient group. -/
def separatedRelativeTorusCentralizerModel
    {S : Scheme.{u}} {G : GroupScheme S} [IsSeparated G.X.hom]
    {T : CommGroupScheme S} (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp) :
    SubgroupFunctor.ClosedRepresentative (torusCentralizer t) :=
  SubgroupFunctor.ClosedRepresentative.ofIsClosedRepresentable
    (relativeTorusCentralizer_isClosedRepresentable_of_separated t hT)

end Langlands.GroupScheme
