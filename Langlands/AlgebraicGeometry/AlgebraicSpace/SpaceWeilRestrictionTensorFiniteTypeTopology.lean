import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionDiagonalProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionAffineEtaleAtlasProof

/-! # Finite-type geometry for the tensor Weil point homeomorphism -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

namespace WeilRestrictionTensorTopology

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  (C : Type u) [NontriviallyNormedField C] [Algebra R C]
  {ι : Type u} [Finite ι] (D : ι → Type u)
  [∀ i, NontriviallyNormedField (D i)] [∀ i, Algebra C (D i)] [∀ i, ContinuousSMul C (D i)]
  [∀ i, FiniteDimensional C (D i)] [∀ i, IsModuleTopology C (D i)]
  [∀ i, Algebra B (D i)]
  (e : C ⊗[R] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[R] b) i = algebraMap B (D i) b)
  (X : AlgebraicSpace (Spec (CommRingCat.of B)))
  (h : IsAlgebraicSpace _ ((ringWeilRestriction R B).obj X.toSheaf))
  (hqs : IsQuasiSeparated X) (hft : FiniteTypeOverRing B X)
  (hC : IsHenselianValuedField C) (hD : ∀ i, IsHenselianValuedField (D i))

/-- For a quasi-separated finite-type space, finite-projective Weil
representability supplies every geometric input to the original tensor
field homeomorphism. -/
def finiteTypeTensorPointHomeomorph :
    letI : TopologicalSpace
        (RingPoints R (ringWeilRestrictionSpace R B X h) C) :=
      fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) (AlgHom.id R C)
    letI : ∀ i, TopologicalSpace (RingPoints B X (D i)) :=
      fun i => fieldValuedPointTopology B X (AlgHom.id B (D i))
    RingPoints R (ringWeilRestrictionSpace R B X h) C ≃ₜ
      (∀ i, RingPoints B X (D i)) := by
  let wr : SpaceWeilRestrictionStatement.{u} :=
    spaceWeilRestriction_of_geometricInputs
      weilRestrictionDiagonal_proof weilRestrictionAffineEtaleAtlas
  let Y := baseChange (Spec.algebraMap B (∀ i, D i)) X
  have hYqs : IsQuasiSeparated Y := hqs.baseChange
  have hYft : FiniteTypeOverRing (∀ i, D i) Y := hft.baseChange
  let (i : ι) : Module.Projective C (D i) := Module.Projective.of_free
  have hfqs (i : ι) : IsQuasiSeparated (WeilRestrictionFiniteProduct.factorSpace D Y i) :=
    hYqs.baseChange
  have hfft (i : ι) :
      FiniteTypeOverRing (D i) (WeilRestrictionFiniteProduct.factorSpace D Y i) :=
    hYft.baseChange
  let hf (i : ι) := (wr C (D i)
    (WeilRestrictionFiniteProduct.factorSpace D Y i) (hfqs i) (hfft i)).choose
  have hfgeom (i : ι) := (wr C (D i)
    (WeilRestrictionFiniteProduct.factorSpace D Y i) (hfqs i) (hfft i)).choose_spec
  have hWgeom := (wr C (∀ i, D i) Y hYqs hYft).choose_spec
  exact tensorPointHomeomorph R B C D e he X h hf hC hD
    (fun i => ⟨hfqs i, (hfft i).mono (fun _ _ _ hp => hp.1)⟩)
    ⟨hWgeom.1, hWgeom.2.1.mono (fun _ _ _ hp => hp.1)⟩
    (fun i => ⟨(hfgeom i).1, (hfgeom i).2.1.mono (fun _ _ _ hp => hp.1)⟩)

@[simp]
theorem finiteTypeTensorPointHomeomorph_apply
    (x : RingPoints R (ringWeilRestrictionSpace R B X h) C) (i : ι) :
    finiteTypeTensorPointHomeomorph R B C D e he X h hqs hft hC hD x i =
      completedTensorSpaceWeilRestrictionPointMap R B C D e he X h x i := by
  simp only [finiteTypeTensorPointHomeomorph, tensorPointHomeomorph_apply]

include hqs hft hC hD in
/-- The actual original-coefficient tensor map is a homeomorphism for a
quasi-separated finite-type space, with original Weil algebraicity and
the norm, module-topology and henselian hypotheses retained. -/
theorem isHomeomorph_completedTensorSpaceWeilRestrictionPointMap_finiteType :
    @IsHomeomorph _ _
      (fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) (AlgHom.id R C))
      (coordinateProductTopology B X D D (fun i => AlgHom.id B (D i)))
      (completedTensorSpaceWeilRestrictionPointMap R B C D e he X h) := by
  let : TopologicalSpace
      (RingPoints R (ringWeilRestrictionSpace R B X h) C) :=
    fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) (AlgHom.id R C)
  let (i : ι) : TopologicalSpace (RingPoints B X (D i)) :=
    fieldValuedPointTopology B X (AlgHom.id B (D i))
  have heq :
      (finiteTypeTensorPointHomeomorph R B C D e he X h hqs hft hC hD :
        RingPoints R (ringWeilRestrictionSpace R B X h) C →
          ∀ i, RingPoints B X (D i)) =
        completedTensorSpaceWeilRestrictionPointMap R B C D e he X h :=
    funext fun x => funext fun i =>
      finiteTypeTensorPointHomeomorph_apply R B C D e he X h hqs hft hC hD x i
  rw [← heq]
  exact (finiteTypeTensorPointHomeomorph R B C D e he X h hqs hft hC hD).isHomeomorph

end WeilRestrictionTensorTopology

end Langlands.AlgebraicGeometry.AlgebraicSpace
