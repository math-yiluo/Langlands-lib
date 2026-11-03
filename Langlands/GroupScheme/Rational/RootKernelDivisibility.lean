import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.Rational.RootKernelNormalizer
import Langlands.GroupScheme.Rational.CharacterFpqcProof

/-! # Integral divisibility from full character-kernel centralization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Descent

variable {B : Scheme.{u}} {T : CommGroupScheme B} {G : GroupScheme B}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (n : normalizerPoints i)
  (a : characterLattice T)
  (hc : n.val ∈ (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 B)))
  [QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left]
  [Flat (CommGroupScheme.groupHom a).hom.hom.left]
  [Surjective (CommGroupScheme.groupHom a).hom.hom.left]

/-- Factor identity minus the inverse normalizing automorphism through the
actual fpqc character. The resulting morphism is an integral cocharacter. -/
def normalizerKernelQuotient : cocharacterLattice T :=
  Additive.ofMul (FpqcHomDescent.hom (CommGroupScheme.groupHom a)
    (CommGroupScheme.groupHom (normalizerDifference i n))
    (normalizerDifference_kills_characterKernel n a hc))

/-- Pulling back the descended cocharacter along the actual character recovers
the difference endomorphism. -/
theorem character_comp_normalizerKernelQuotient :
    a ≫ normalizerKernelQuotient i n a hc = normalizerDifference i n :=
  congrArg Additive.ofMul (FpqcHomDescent.fac (CommGroupScheme.groupHom a)
    (CommGroupScheme.groupHom (normalizerDifference i n))
    (normalizerDifference_kills_characterKernel n a hc))

end Descent

section Field

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
  [Mono i.hom.hom.left] (n : normalizerPoints i) (a : characterLattice T)
  (hc : n.val ∈ (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 _)))
  [QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left]
  [Flat (CommGroupScheme.groupHom a).hom.hom.left]
  [Surjective (CommGroupScheme.groupHom a).hom.hom.left]

/-- The whole-character difference is an integral multiple of the actual
character, with coefficient computed by the descended cocharacter. -/
theorem normalizerKernelQuotient_formula (χ : characterLattice T) :
    χ - weylAction i n χ =
      latticePairing T χ (normalizerKernelQuotient i n a hc) • a := by
  calc
    χ - weylAction i n χ = normalizerDifference i n ≫ χ := by
      rw [normalizerDifference, Preadditive.sub_comp, Category.id_comp, weylAction_apply]
    _ = (a ≫ normalizerKernelQuotient i n a hc) ≫ χ := by
      rw [character_comp_normalizerKernelQuotient]
    _ = a ≫ (normalizerKernelQuotient i n a hc ≫ χ) := Category.assoc _ _ _
    _ = a ≫ (latticePairing T χ (normalizerKernelQuotient i n a hc) • 𝟙 _) := by
      rw [latticePairing_apply, ← eq_gmEndEquiv_zsmul k]
    _ = _ := by rw [Preadditive.comp_zsmul, Category.comp_id]

end Field

/-- A point normalizing a split torus and centralizing the full kernel of a
nonzero character has integral character differences divisible by that
character. No primitivity or smoothness of the kernel is needed. -/
theorem exists_integral_difference_of_mem_kernelCentralizer
    {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    [Mono i.hom.hom.left] (hT : IsSplitTorus T.toGrp) (a : characterLattice T)
    (ha : a ≠ 0) (n : normalizerPoints i)
    (hc : n.val ∈ (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 _))) :
    ∀ χ : characterLattice T, ∃ m : ℤ, χ - weylAction i n χ = m • a := by
  obtain ⟨hqc, hflat, hsurj⟩ := RelativeRoot.characterFpqc k T hT a ha
  let := hqc
  let := hflat
  let := hsurj
  intro χ
  exact ⟨latticePairing T χ (normalizerKernelQuotient i n a hc),
    normalizerKernelQuotient_formula i n a hc χ⟩

end Langlands.GroupScheme
