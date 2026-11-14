import Langlands.GroupScheme.Rational.RootKernelReflection
import Langlands.GroupScheme.Rational.RootKernelIdentityTorus
import Langlands.GroupScheme.Rational.RelativeReflection

/-! # Actual relative reflections from full-kernel normalizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- A root-flipping normalizer centralizing the full character kernel gives
an actual relative reflection on the rational root span. -/
theorem IsSplitTorus.isRelativeReflection_of_mem_kernelCentralizer
    (hT : IsSplitTorus T.toGrp) (a : characterLattice T)
    (ha : a ∈ relativeRoots i) (n : normalizerPoints i)
    (hflip : weylAction i n a = -a)
    (hc : n.val ∈ (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 _))) :
    IsRelativeReflection i a (QuotientGroup.mk n) := by
  obtain ⟨ν, ⟨hpair, hact⟩, _⟩ :=
    hT.existsUnique_coroot_of_mem_kernelCentralizer i a ha.1 n hflip hc
  have hself : RelativeRootSystem.corootFunctional i ν
      (RelativeRootSystem.rootVector i ⟨a, ha⟩) = 2 := by
    rw [RelativeRootSystem.corootFunctional_rootVector, hpair]
    norm_num
  refine ⟨ha, RelativeRootSystem.corootFunctional i ν, hself, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range (RelativeRootSystem.span_range_rootVector i)
  intro β
  change relativeWeylAction i (QuotientGroup.mk n)
      (RelativeRootSystem.rootVector i β) =
    Module.reflection hself (RelativeRootSystem.rootVector i β)
  unfold RelativeRootSystem.rootVector at ⊢
  rw [relativeWeylAction_mk_toRat i n β.property]
  apply Subtype.ext
  change toRat (weylAction i n β.val) = toRat β.val -
    RelativeRootSystem.corootFunctional i ν (RelativeRootSystem.rootVector i β) • toRat a
  rw [RelativeRootSystem.corootFunctional_rootVector, hact, map_sub,
    map_zsmul, Int.cast_smul_eq_zsmul]

namespace RelativeRoot

variable {C : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth C.X.hom] [IsAffineHom C.X.hom]

/-- Any normalizer in the actual identity component of the full character-kernel
centralizer which negates the root maps to its ambient relative reflection. -/
theorem isRelativeReflection_kernelCentralizerIdentityNormalizerMap
    (hT : IsSplitTorus T.toGrp) (a : characterLattice T)
    (ha : a ∈ relativeRoots i) (j : C ⟶ G)
    (hj : (kernelCentralizer i a).IsRepresentedBy j)
    (n : normalizerPoints (kernelCentralizerIdentityTorus i hT a j hj))
    (hflip : weylAction i (kernelCentralizerIdentityNormalizerMap i hT a j hj n) a = -a) :
    IsRelativeReflection i a
      (QuotientGroup.mk (kernelCentralizerIdentityNormalizerMap i hT a j hj n)) :=
  hT.isRelativeReflection_of_mem_kernelCentralizer i a ha _ hflip
    (kernelCentralizerIdentityNormalizerMap_mem i hT a j hj n)

/-- The ambient relative reflection represented by a supplied root-flipping
normalizer in the full-kernel centralizer identity component. -/
def kernelCentralizerIdentityNormalizerReflection
    (hT : IsSplitTorus T.toGrp) (a : characterLattice T)
    (ha : a ∈ relativeRoots i) (j : C ⟶ G)
    (hj : (kernelCentralizer i a).IsRepresentedBy j)
    (n : normalizerPoints (kernelCentralizerIdentityTorus i hT a j hj))
    (hflip : weylAction i (kernelCentralizerIdentityNormalizerMap i hT a j hj n) a = -a) :
    {w : relativeWeylGroup i // IsRelativeReflection i a w} :=
  ⟨QuotientGroup.mk (kernelCentralizerIdentityNormalizerMap i hT a j hj n),
    isRelativeReflection_kernelCentralizerIdentityNormalizerMap i hT a ha j hj n hflip⟩

end RelativeRoot

end Langlands.GroupScheme
