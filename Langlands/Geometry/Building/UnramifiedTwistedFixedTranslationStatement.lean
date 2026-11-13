import Langlands.Geometry.Building.TorusUnitFixedPoint
import Langlands.Geometry.Building.GaloisApartmentQuotientAction
import Langlands.GroupScheme.Rational.RelativeCentralDirections

/-! # Twisted coefficient-fixed translations of a special apartment -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- The image of the real cocharacter space of the extended torus `S_K` in the
reduced translation space `V(T_K) / (common kernel of the roots)` of the extended
torus `T_K`, along the extension of `f : S ⟶ T`. This is only the literal quotient
image. When `G` is connected reductive and `S` is a maximal `F`-split torus, as in
`UnramifiedTwistedFixedTranslationStatement`, it plays the role of the space `V(S′)`
of Kaletha–Prasad §9.3. For a non-maximal split subtorus it can differ from `V(S′)`. -/
def splitTranslationDirections (k K : Type u) [Field k] [Field K] [Algebra k K]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (iT : T.toGrp ⟶ G) (f : S ⟶ T) :
    Submodule ℝ (TranslationSpace (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map iT)) :=
  (LinearMap.range (RealTorusSpace.cocharacterMapReal
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f))).map
    (Langlands.Geometry.Building.rootAnnihilator
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map iT)).mkQ

/-- Let `h ∈ G(K)` centralize the `K`-points of the maximal `F`-split torus `S`
and let `n_σ = h⁻¹ σ(h)` lie in the normalizer of `T_K` for every
`σ ∈ Aut(K/F)`, so that `h T_K h⁻¹` is the extension of an `F`-torus containing `S`.
Every reduced translation of the `T_K`-apartment fixed by all twisted coefficient
maps `v ↦ n_σ · σ(v)` lies in the image of `V(S_K)` (KP Proposition 9.3.13, first
paragraph of the proof: `V(T′)^Γ = V(S′)`). -/
def UnramifiedTwistedFixedTranslationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G),
    IsMaximalSplitTorus iS →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T),
    CommGroupScheme.groupHom f ≫ iT = iS →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
      ∀ (h : rationalPoints (baseChanged F (inertiaFixedField F) G)),
        (∀ s : rationalPoints (baseChanged F (inertiaFixedField F) S.toGrp),
          Commute h (rationalPoints.map
            ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iS) s)) →
      ∀ (n : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
          normalizerPoints
            (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
        (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          ((n σ : rationalPoints (baseChanged F (inertiaFixedField F) G))) =
            h⁻¹ * rationalConjugate F (inertiaFixedField F) G σ h) →
      ∀ v : TranslationSpace
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT),
        (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          translationAction
              (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
              ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) (n σ)
            (galoisTranslationAction F (inertiaFixedField F) iT σ v) = v) →
        v ∈ splitTranslationDirections F (inertiaFixedField F) iT f

end Langlands.Geometry.Building
