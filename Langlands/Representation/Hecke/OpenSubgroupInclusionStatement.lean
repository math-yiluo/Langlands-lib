import Langlands.Representation.Hecke.CompactInductionModels
import Langlands.HarmonicAnalysis.HomogeneousFunctions

/-!
# Induction from an open subgroup: the Hecke inclusion (Renard III.2.6, final Remark)

For an open subgroup `H` of a t.d. group `G`, the relative modular character `δ_{H\G}` is
trivial, the pseudo-forgetful functor is isomorphic to the forgetful functor, and, when the
Haar measure of `H` is the restriction of that of `G`, extension by zero is an inclusion of
Hecke algebras `H(H) ↪ H(G)` through which the canonical `H(H)`-bimodule structure of `H(G)`
is left and right multiplication.
-/

namespace Langlands.Hecke.Homomorphism

open MeasureTheory

universe uG v

/-- Renard III.2.6, final Remark: let `H` be an open subgroup of a t.d. group `G`, with Haar
measures `μG` and `μH`. Then `δ_{H\G}` is trivial (in both published forms), the Hecke
pseudo-forgetful functor is isomorphic to the forgetful functor, and if `μH` is the
restriction of `μG`, extension by zero is a ring homomorphism `H(H) → H(G)` onto the
functions supported in `H`, with `a · T = ext(a) * T` and `T · a = T * ext(a)` for the
canonical bimodule structure of III.2.1. -/
def OpenSubgroupHeckeInclusionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [T2Space G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [μG.IsHaarMeasure]
    (H : Subgroup G) (hH : IsOpen (H : Set G)),
    letI : LocallyCompactSpace H := (Subgroup.isClosed_of_isOpen H hH).locallyCompactSpace
    ∀ (μH : Measure H) [μH.IsHaarMeasure],
      (∀ h : H, ((relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom h :
          ℂ) = 1) ∧
      (∀ h : H, HarmonicAnalysis.HomogeneousFunctions.relativeModular H
          (Subgroup.isClosed_of_isOpen H hH) h = 1) ∧
      Nonempty (pseudoF.{uG, uG, v} μG μH H.subtype continuous_subtype_val ≅
        F.{uG, uG, v} μG μH H.subtype continuous_subtype_val) ∧
      ((∀ s : Set H, μH s = μG (Subtype.val '' s)) →
        ∃ ext : HeckeAlgebra μH →ₙ+* HeckeAlgebra μG,
          (∀ (a : HeckeAlgebra μH) (h : H), ext a (h : G) = a h) ∧
          (∀ (a : HeckeAlgebra μH) (x : G), x ∉ H → ext a x = 0) ∧
          (∀ T : HeckeAlgebra μG, (∀ x : G, x ∉ H → T x = 0) → ∃ a, ext a = T) ∧
          (letI := leftModule μG μH H.subtype continuous_subtype_val
            ∀ (a : HeckeAlgebra μH) (T : HeckeAlgebra μG), a • T = ext a * T) ∧
          (letI := rightModule μG μH H.subtype continuous_subtype_val
            ∀ (a : HeckeAlgebra μH) (T : HeckeAlgebra μG),
              MulOpposite.op a • T = T * ext a))

end Langlands.Hecke.Homomorphism
