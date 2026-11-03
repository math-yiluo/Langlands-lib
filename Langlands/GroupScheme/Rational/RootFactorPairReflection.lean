import Langlands.GroupScheme.Rational.QuotientActionComparisonProof
import Langlands.GroupScheme.Rational.RootKernelReflection
import Langlands.GroupScheme.Rational.RootRankOneFactorizationStatement

/-! # Full-kernel centralization and integral coroots of actual factor pairs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

namespace RelativeRoot

section Kernel

variable {B : Scheme.{u}} {T : CommGroupScheme B} {G : GroupScheme B}
  (i : T.toGrp ⟶ G) (a : characterLattice T)

/-- Centralizing the full kernel of a character also centralizes the full
kernel of its negative, on every test scheme. -/
theorem kernelCentralizer_le_neg :
    kernelCentralizer i a ≤ kernelCentralizer i (-a) := by
  intro U g hg
  rw [mem_kernelCentralizer] at hg ⊢
  intro V b c
  let s := c ≫ (characterKernelι (-a)).hom.hom
  have hsneg : s ≫ (CommGroupScheme.groupHom (-a)).hom.hom = 1 :=
    (kernelPointsEquiv (CommGroupScheme.groupHom (-a)) V c).property
  have heval : s ≫ (CommGroupScheme.groupHom (-a)).hom.hom =
      (s ≫ (CommGroupScheme.groupHom a).hom.hom)⁻¹ :=
    congrArg Additive.toMul ((evalPoint s).map_neg a)
  have hs : s ≫ (CommGroupScheme.groupHom a).hom.hom = 1 := by
    rw [heval] at hsneg
    exact inv_eq_one.mp hsneg
  let c' : V ⟶ (characterKernel a).X :=
    (kernelPointsEquiv (CommGroupScheme.groupHom a) V).symm ⟨s, hs⟩
  have hc' : c' ≫ (characterKernelι a).hom.hom = s :=
    congrArg Subtype.val ((kernelPointsEquiv (CommGroupScheme.groupHom a) V).apply_symm_apply
      ⟨s, hs⟩)
  change Commute (b ≫ g) (s ≫ i.hom.hom)
  simpa only [Grp.comp_hom_hom, ← Category.assoc, hc'] using hg V b c'

/-- The full scheme-theoretic kernel centralizer is invariant under negating
its character, including for nonsmooth kernels. -/
theorem kernelCentralizer_neg : kernelCentralizer i (-a) = kernelCentralizer i a := by
  apply le_antisymm
  · simpa only [neg_neg] using kernelCentralizer_le_neg i (-a)
  · exact kernelCentralizer_le_neg i a

/-- Every actual root subgroup point centralizes the whole character kernel. -/
theorem subgroup_le_kernelCentralizer : subgroup i a ≤ kernelCentralizer i a := by
  rintro U g ⟨e, he, _⟩
  exact mem_kernelCentralizer_of_isOrbitExtension i a he

/-- The opposite root subgroup centralizes the same full character kernel. -/
theorem opposite_subgroup_le_kernelCentralizer :
    subgroup i (-a) ≤ kernelCentralizer i a := by
  rw [← kernelCentralizer_neg i a]
  exact subgroup_le_kernelCentralizer i (-a)

end Kernel

section FactorPair

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G)
  {a : characterLattice T} {x : rationalPoints G}
  {p : rationalPoints G × rationalPoints G}

/-- The normalizing product of an actual opposite pair centralizes the
full kernel of the middle point's character. -/
theorem IsOppositeFactorPair.mem_kernelCentralizer
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    (hp : IsOppositeFactorPair i a x p) :
    p.1 * x * p.2 ∈ (kernelCentralizer i a).carrier (Over.mk (𝟙 _)) :=
  Subgroup.mul_mem _
    (Subgroup.mul_mem _ (opposite_subgroup_le_kernelCentralizer i a _ hp.1)
      (subgroup_le_kernelCentralizer i a _ hx))
    (opposite_subgroup_le_kernelCentralizer i a _ hp.2.1)

variable [Mono i.hom.hom.left]

/-- The actual integral coroot determined by a root-flipping normalizing
opposite pair. Its existence follows from full-kernel centralization. -/
def IsOppositeFactorPair.corootOfFlip
    (hT : IsSplitTorus T.toGrp) (ha : a ≠ 0)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    (hp : IsOppositeFactorPair i a x p)
    (hn : weylAction i (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i) a = -a) :
    cocharacterLattice T :=
  Classical.choose (hT.existsUnique_coroot_of_mem_kernelCentralizer i a ha
    ⟨p.1 * x * p.2, hp.2.2⟩ hn (hp.mem_kernelCentralizer i hx))

/-- The constructed coroot pairs to two and gives the reflection formula on
all integral characters. -/
theorem IsOppositeFactorPair.corootOfFlip_spec
    (hT : IsSplitTorus T.toGrp) (ha : a ≠ 0)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    (hp : IsOppositeFactorPair i a x p)
    (hn : weylAction i (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i) a = -a) :
    latticePairing T a (hp.corootOfFlip i hT ha hx hn) = 2 ∧
      ∀ χ : characterLattice T,
        weylAction i (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i) χ =
          χ - latticePairing T χ (hp.corootOfFlip i hT ha hx hn) • a :=
  (Classical.choose_spec (hT.existsUnique_coroot_of_mem_kernelCentralizer i a ha
    ⟨p.1 * x * p.2, hp.2.2⟩ hn (hp.mem_kernelCentralizer i hx))).1

variable [IsAffineHom G.X.hom]

/-- A root-flipping opposite pair represents the exact relative reflection
on the existing rational root span. -/
theorem IsOppositeFactorPair.isRelativeReflection_of_flip
    (hT : IsSplitTorus T.toGrp) (ha : a ∈ relativeRoots i)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    (hp : IsOppositeFactorPair i a x p)
    (hn : weylAction i (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i) a = -a) :
    IsRelativeReflection i a
      (QuotientGroup.mk (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i)) := by
  let ν := hp.corootOfFlip i hT ha.1 hx hn
  obtain ⟨hpair, hact⟩ := hp.corootOfFlip_spec i hT ha.1 hx hn
  have hf : RelativeRootSystem.corootFunctional i ν
      ⟨toRat a, toRat_mem_ratSpan ha⟩ = 2 := by
    change RelativeRootSystem.corootFunctional i ν
      (RelativeRootSystem.rootVector i ⟨a, ha⟩) = 2
    rw [RelativeRootSystem.corootFunctional_rootVector]
    change (latticePairing T a (hp.corootOfFlip i hT ha.1 hx hn) : ℚ) = 2
    rw [hpair]
    norm_num
  refine ⟨ha, RelativeRootSystem.corootFunctional i ν, hf, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range (RelativeRootSystem.span_range_rootVector i)
  intro β
  change relativeWeylAction i
      (QuotientGroup.mk (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i))
      (RelativeRootSystem.rootVector i β) =
    Module.reflection hf (RelativeRootSystem.rootVector i β)
  rw [Module.reflection_apply]
  apply Subtype.ext
  change toRat (weylAction i _ β.val) =
    toRat β.val - RelativeRootSystem.corootFunctional i ν
      (RelativeRootSystem.rootVector i β) • toRat a
  rw [RelativeRootSystem.corootFunctional_rootVector, hact, map_sub, map_zsmul,
    Int.cast_smul_eq_zsmul]

end FactorPair

end RelativeRoot

end Langlands.GroupScheme
