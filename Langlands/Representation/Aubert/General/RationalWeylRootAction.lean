import Langlands.Representation.Aubert.General.RationalWeylComparisonTarget

/-!
# Actual relative Weyl action on the character lattice

The action descends through the full scheme centralizer and is transported
through the representative-preserving comparison with the actual point quotient.
No root-sign or Coxeter realization is assumed or proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- The published normalizer action on actual characters, descended through
the full scheme-centralizer point subgroup. -/
def schemeWeylCharacterAction :
    relativeWeylGroup i →* (characterLattice T ≃ₗ[ℤ] characterLattice T) :=
  QuotientGroup.lift _ (weylAction i) (centralizerPoints_subgroupOf_le_ker i)

@[simp] theorem schemeWeylCharacterAction_mk (n : normalizerPoints i) :
    schemeWeylCharacterAction i (QuotientGroup.mk n) = weylAction i n :=
  rfl

/-- The action of the actual torus-image normalizer/full-centralizer quotient.
Both scheme-to-point subgroup comparisons remain explicit premises. -/
def weylCharacterAction
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i) :
    Weyl i →* (characterLattice T ≃ₗ[ℤ] characterLattice T) :=
  (schemeWeylCharacterAction i).comp (weylEquiv i hN hZ).symm.toMonoidHom

@[simp] theorem weylCharacterAction_weylEquiv
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (w : relativeWeylGroup i) :
    weylCharacterAction i hN hZ (weylEquiv i hN hZ w) =
      schemeWeylCharacterAction i w := by
  simp [weylCharacterAction]

/-- On each scheme normalizer class the action is exactly the published action
of that representative, with the source's inverse pullback on characters. -/
theorem weylCharacterAction_mk
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (n : normalizerPoints i) :
    weylCharacterAction i hN hZ (QuotientGroup.mk (normalizerEquiv i hN n)) =
      weylAction i n := by
  rw [← weylEquiv_mk i hN hZ n, weylCharacterAction_weylEquiv,
    schemeWeylCharacterAction_mk]

/-- The representative formula covers every actual point-image normalizer. -/
theorem weylCharacterAction_point_mk
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) :
    weylCharacterAction i hN hZ (QuotientGroup.mk n) =
      weylAction i ((normalizerEquiv i hN).symm n) := by
  simpa using weylCharacterAction_mk i hN hZ ((normalizerEquiv i hN).symm n)

variable [IsAffineHom G.X.hom]

theorem schemeWeylCharacterAction_image_relativeRoots (w : relativeWeylGroup i) :
    schemeWeylCharacterAction i w '' relativeRoots i = relativeRoots i := by
  induction w using Quotient.inductionOn' with
  | h n => exact weylAction_image_relativeRoots i n

/-- The actual quotient action permutes the exact relative-root set. -/
theorem weylCharacterAction_image_relativeRoots
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (w : Weyl i) :
    weylCharacterAction i hN hZ w '' relativeRoots i = relativeRoots i :=
  schemeWeylCharacterAction_image_relativeRoots i ((weylEquiv i hN hZ).symm w)

theorem weylCharacterAction_mem_relativeRoots_iff
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (w : Weyl i) (α : characterLattice T) :
    weylCharacterAction i hN hZ w α ∈ relativeRoots i ↔ α ∈ relativeRoots i := by
  constructor
  · intro h
    have himage := weylCharacterAction_image_relativeRoots i hN hZ w
    rcases himage.symm ▸ h with ⟨β, hβ, heq⟩
    exact (weylCharacterAction i hN hZ w).injective heq ▸ hβ
  · intro h
    rw [← weylCharacterAction_image_relativeRoots i hN hZ w]
    exact ⟨α, h, rfl⟩

end Langlands.Aubert.General.RationalPointFamily
