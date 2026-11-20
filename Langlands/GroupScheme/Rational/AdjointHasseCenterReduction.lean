import Langlands.GroupScheme.Rational.AdjointHasseAbsolute
import Langlands.GroupScheme.Rational.CentralSplitTorsionHasseReduction
import Langlands.GroupScheme.Rational.CentralWeilTorsionHasseReduction
import Langlands.GroupScheme.Rational.SimplyConnectedHasseAbsolute
import Langlands.GroupScheme.SimplyConnected.CoverExistenceProof
import Langlands.GroupScheme.Reductive.AffineAdjointWeilRestrictionProof
import Langlands.GroupScheme.Reductive.FiniteProductHomKernel
import Langlands.GroupScheme.Adjoint.Assembly
import Langlands.GroupScheme.CentralIsogeny.AlmostSimpleTransfer

/-! # Adjoint Hasse reduction to the models of the central kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- A central isogeny onto an adjoint group has the full scheme-theoretic
centre of its source as kernel. -/
theorem IsCentralIsogeny.isSchemeTheoreticCenter_kernelι_of_isAdjoint
    {F : Type u} [Field F] {C H : GroupScheme (Spec (CommRingCat.of F))} {f : C ⟶ H}
    (hf : IsCentralIsogeny f) (hH : IsAdjoint H) :
    IsSchemeTheoreticCenter (kernelι f) := by
  let : Flat f.hom.hom.left := hf.flat
  let : Surjective f.hom.hom.left := hf.surjective
  let : IsAffineHom H.X.hom := hH.isSemisimple.isConnectedReductive.isAffineHom
  apply isSchemeTheoreticCenter_kernelι_of_range_eq f
  apply le_antisymm hf.kernel_range_le_center
  intro T x hx
  apply (mem_range_kernelι_iff f x).mpr
  have h := mem_center_comp_of_flat_surjective f hx
  rw [hH.center_eq_bot] at h
  change x ≫ f.hom.hom ∈ (⊥ : Subgroup (T ⟶ H.X)) at h
  exact Subgroup.mem_bot.mp h

/-- Absolute almost-simplicity ascends to a semisimple central cover. -/
theorem IsCentralIsogeny.isAbsolutelyAlmostSimple_source
    {F : Type u} [Field F] {C H : GroupScheme (Spec (CommRingCat.of F))} {f : C ⟶ H}
    (hf : IsCentralIsogeny f) (hC : IsSemisimple C) (hH : IsAbsolutelyAlmostSimple H) :
    IsAbsolutelyAlmostSimple C := by
  refine ⟨IsAlmostSimple.of_isCentralIsogeny f hf hH.1 hC.isConnectedReductive.smooth
    hC.isConnectedReductive.connectedSpace, ?_⟩
  let b := toAlgebraicClosure F
  have hc : IsSemisimple ((GroupScheme.baseChange b).obj C) :=
    isSemisimpleFieldExtension F (AlgebraicClosure F) C hC
  exact IsAlmostSimple.of_isCentralIsogeny ((GroupScheme.baseChange b).map f) (hf.baseChange b) hH.2
    hc.isConnectedReductive.smooth hc.isConnectedReductive.connectedSpace

/-- A kernel has one of the models needed by the number-field arithmetic reductions. -/
def HasNumberFieldCentralKernelModel {F : Type u} [Field F]
    (Z : GroupScheme (Spec (CommRingCat.of F))) : Prop :=
  (∃ n : ℕ, 0 < n ∧ Nonempty (Z ≅ (mu (Spec (CommRingCat.of F)) n).toGrp)) ∨
  (∃ (I : Type u) (_ : Finite I) (n : I → ℕ), (∀ i, 0 < n i) ∧
    Nonempty (Z ≅ splitRootsOfUnityProduct F n)) ∨
  (∃ (B : Type u) (_ : Field B) (_ : Algebra F B) (_ : NumberField B) (_ : FiniteDimensional F B)
    (n : ℕ), 0 < n ∧ Nonempty (Z ≅ WeilGm.weilTorsion F B n)) ∨
  (∃ (B : Type u) (_ : Field B) (_ : Algebra F B) (_ : NumberField B) (_ : FiniteDimensional F B)
    (n : ℕ), 0 < n ∧ (Module.finrank F B = 2 ∨ (Module.finrank F B).Coprime n) ∧
      Nonempty (Z ≅ WeilGm.normOneTorsion F B n))

/-- The model classification for the actual kernel of a simply connected central
cover of an absolutely almost-simple adjoint group over a number field. -/
def NumberFieldAbsolutelyAlmostSimpleAdjointCenterStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (C H : GroupScheme (Spec (CommRingCat.of F)))
    (f : C ⟶ H), IsAdjoint H → IsAbsolutelyAlmostSimple H → IsSimplyConnectedCover f →
      HasNumberFieldCentralKernelModel (kernel f)

/-- The simply connected Hasse kernel and the actual centre models imply the
absolutely almost-simple adjoint kernel. -/
theorem numberFieldAbsolutelyAlmostSimpleAdjointHasse_of_center
    (hsc : NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u})
    (hZ : NumberFieldAbsolutelyAlmostSimpleAdjointCenterStatement.{u}) :
    NumberFieldAbsolutelyAlmostSimpleAdjointGaloisHasseKernelStatement.{u} := by
  intro F _ _ H hH hsimple L _ _ _ _ ξ hξ
  obtain ⟨C, f, hf⟩ := simplyConnectedCoverExistence F H hH.isSemisimple
  rcases hZ F C H f hH hsimple hf with h | h | h | h
  · obtain ⟨n, hn, e⟩ := h
    exact numberFieldMuKernelHasse_of_simplyConnected hsc F C H f hf.isSimplyConnected
      hf.isCentralIsogeny n hn e L ξ hξ
  · obtain ⟨I, _, n, hn, e⟩ := h
    exact numberFieldSplitTorsionKernelHasse_of_simplyConnected hsc F C H f hf.isSimplyConnected
      hf.isCentralIsogeny I n hn e L ξ hξ
  · obtain ⟨B, _, _, _, _, n, hn, e⟩ := h
    exact numberFieldWeilTorsionKernelHasse_of_simplyConnected hsc F B C H f hf.isSimplyConnected
      hf.isCentralIsogeny n hn e L ξ hξ
  · obtain ⟨B, _, _, _, _, n, hn, hB, e⟩ := h
    exact numberFieldNormOneKernelHasse_of_simplyConnected hsc F B C H f hf.isSimplyConnected
      hf.isCentralIsogeny n hn e hB L ξ hξ

/-- The full adjoint Hasse kernel follows from the simply connected kernel and the
centre classification of absolutely almost-simple groups. -/
theorem numberFieldAdjointGaloisHasseKernel_of_center
    (hsc : NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u})
    (hZ : NumberFieldAbsolutelyAlmostSimpleAdjointCenterStatement.{u}) :
    NumberFieldAdjointGaloisHasseKernelStatement.{u} :=
  numberFieldAdjointGaloisHasseKernel_of_absolute affineAdjointWeilRestriction
    (numberFieldAbsolutelyAlmostSimpleAdjointHasse_of_center hsc hZ)

/-- The Hasse principle on the published finite separable covers follows from
the absolute simply connected arithmetic kernel, the centre models, and
the number-field quadratic isometry theorem. -/
theorem numberFieldHassePrinciple_of_absolute_and_center
    (hsc : NumberFieldAbsolutelyAlmostSimpleSimplyConnectedGaloisHasseKernelStatement.{u})
    (hZ : NumberFieldAbsolutelyAlmostSimpleAdjointCenterStatement.{u})
    (hq : NumberFieldQuadraticIsometryStatement.{u}) :
    NumberFieldHassePrincipleStatement.{u} :=
  let h := numberFieldSimplyConnectedGaloisHasseKernel_of_absolute hsc
  numberFieldHassePrinciple_of_arithmetic h (numberFieldAdjointGaloisHasseKernel_of_center h hZ) hq

end Langlands.GroupScheme
