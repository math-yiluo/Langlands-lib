import Langlands.Representation.Hecke.HomomorphismRight
import Langlands.Representation.Hecke.NondegenerateModuleEquivalenceStatement
import Langlands.Representation.Mirabolic.MixedProducts

/-! # Transport of the four Hecke functors to smooth representations

Renard III.2.1, through the specific functors of III.1.4.
The equivalence proofs consumed here are explicit; this file does not prove III.1.4.
-/

noncomputable section

open CategoryTheory MeasureTheory

namespace Langlands.Hecke.Homomorphism

universe uG uH v

section Pullback

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]

/-- The existing smooth pullback functor, i.e. `Fφ` in (III.2.1.1).
Its action is `h ↦ π(φ(h))`, with the same carrier and intertwining maps. -/
abbrev restriction (φ : H →* G) (hφ : Continuous φ) :
    SmoothRep.{0, uG, v} ℂ G ⥤ SmoothRep.{0, uH, v} ℂ H :=
  MixedProductTensor.pullbackFunctor φ hφ

end Pullback

section Transport

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] [T2Space H]
  [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
  (φ : H →* G) (hφ : Continuous φ)

/-- Transport of the tensor forgetful functor along the published Hecke functors.
`eH` is precisely the III.1.4 equivalence assertion for `H`. -/
def smoothF
    (eH : (heckeNondegenerateModuleFunctor.{uH, max uG v} μH).IsEquivalence) :
    SmoothRep.{0, uG, max uG v} ℂ G ⥤ SmoothRep.{0, uH, max uG v} ℂ H := by
  letI := eH
  exact heckeNondegenerateModuleFunctor μG ⋙ F μG μH φ hφ ⋙
    (heckeNondegenerateModuleFunctor μH).inv

/-- Transport of the pseudo-forgetful functor via the same equivalence of `H`. -/
def smoothPseudoF
    (eH : (heckeNondegenerateModuleFunctor.{uH, max uG v} μH).IsEquivalence) :
    SmoothRep.{0, uG, max uG v} ℂ G ⥤ SmoothRep.{0, uH, max uG v} ℂ H := by
  letI := eH
  exact heckeNondegenerateModuleFunctor μG ⋙ pseudoF μG μH φ hφ ⋙
    (heckeNondegenerateModuleFunctor μH).inv

/-- Transport of right induction via the III.1.4 equivalence of `G`. -/
def smoothI
    (eG : (heckeNondegenerateModuleFunctor.{uG, max uG v} μG).IsEquivalence) :
    SmoothRep.{0, uH, max uG v} ℂ H ⥤ SmoothRep.{0, uG, max uG v} ℂ G := by
  letI := eG
  exact heckeNondegenerateModuleFunctor μH ⋙ I μG μH φ hφ ⋙
    (heckeNondegenerateModuleFunctor μG).inv

/-- Transport of left induction via the same III.1.4 equivalence of `G`. -/
def smoothP
    (eG : (heckeNondegenerateModuleFunctor.{uG, max uG v} μG).IsEquivalence) :
    SmoothRep.{0, uH, max uG v} ℂ H ⥤ SmoothRep.{0, uG, max uG v} ℂ G := by
  letI := eG
  exact heckeNondegenerateModuleFunctor μH ⋙ P μG μH φ hφ ⋙
    (heckeNondegenerateModuleFunctor μG).inv

end Transport

end Langlands.Hecke.Homomorphism
