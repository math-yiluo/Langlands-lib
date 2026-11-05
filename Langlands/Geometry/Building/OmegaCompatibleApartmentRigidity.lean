import Langlands.Geometry.Building.OmegaCompatibleApartmentComparison
import Langlands.Geometry.Building.OmegaCompatibleApartmentValueComparison
import Langlands.Geometry.Building.CrossTorusApartmentComparison
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence

/-! # Apartment class rigidity from actual opposite factor pairs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

/-- The conditional class-rigidity step of KP Proposition 6.2.6.
Actual opposite-factor-pair existence is retained as an additional premise. -/
def OmegaCompatibleApartmentRigidityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
      [Mono i.hom.hom.left],
      IsMaximalSplitTorus i →
      RelativeRoot.HasOppositeFactorPairs i →
      ∀ (C : CentralizerDatum i)
        (D E : KPApartmentData i (localFieldOrder F)),
        D.IsOmegaCompatible C → E.IsOmegaCompatible C → D = E

namespace IsRootDatumValuation

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {φ ψ : RootFunctionFamily S G}

/-- The Library's off-domain infinity normalization and V 1's identity value
reduce equality of the extended families to nonidentity root-group points. -/
theorem eq_of_eq_on_nonidentity_root_points
    (hφ : IsRootDatumValuation i φ) (hψ : IsRootDatumValuation i ψ)
    (h : ∀ (α : relativeRoots i) (g : rationalPoints G),
      g ∈ rootGroupPoints i α → g ≠ 1 → φ α g = ψ α g) :
    φ = ψ := by
  apply RootFunctionFamily.ext
  intro a g
  by_cases ha : a ∈ relativeRoots i
  · by_cases hg : g ∈ rootGroupPoints i a
    · by_cases hg1 : g = 1
      · rw [(hφ.eq_top_iff a ha g hg).2 hg1,
          (hψ.eq_top_iff a ha g hg).2 hg1]
      · exact h ⟨a, ha⟩ g hg hg1
    · rw [hφ.eq_top_of_not_mem a ha g hg, hψ.eq_top_of_not_mem a ha g hg]
  · rw [hφ.eq_top_of_not_mem_roots a ha g, hψ.eq_top_of_not_mem_roots a ha g]

end IsRootDatumValuation

namespace KPApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    (D E : KPApartmentData i (localFieldOrder F))
    (C : CentralizerDatum i)
    (hD : D.IsOmegaCompatible C) (hE : E.IsOmegaCompatible C)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)

include C hD hE hG hi in
/-- Under actual opposite-pair existence, the equivariant comparison preserves
the entire original root-function family. -/
theorem val_eq_of_equivariant_affineEquiv_of_hasOppositeFactorPairs
    (hpair : RelativeRoot.HasOppositeFactorPairs i)
    (f : D.Apartment ≃ᵃ[ℝ] E.Apartment)
    (hlinear : f.linear = LinearEquiv.refl ℝ (TranslationSpace i))
    (hequiv : ∀ (n : normalizerPoints i) (x : D.Apartment), f (n • x) = n • f x)
    (x : D.Apartment) :
    (f x).val = x.val := by
  apply (f x).isValuation.eq_of_eq_on_nonidentity_root_points x.isValuation
  intro α g hg hg1
  obtain ⟨p, hp⟩ := hpair α α.2 g hg hg1
  exact D.value_eq_of_equivariant_affineEquiv_of_oppositeFactorPair E C hD hE
    hG hi f hlinear hequiv α g hg hg1 p hp x

include C hD hE hG hi in
/-- An equivariant comparison with identity derivative identifies the full
apartment classes whenever every actual root point admits an opposite pair. -/
theorem eq_of_equivariant_affineEquiv_of_hasOppositeFactorPairs
    (hpair : RelativeRoot.HasOppositeFactorPairs i)
    (f : D.Apartment ≃ᵃ[ℝ] E.Apartment)
    (hlinear : f.linear = LinearEquiv.refl ℝ (TranslationSpace i))
    (hequiv : ∀ (n : normalizerPoints i) (x : D.Apartment), f (n • x) = n • f x) :
    D = E := by
  obtain ⟨x⟩ := (inferInstance : Nonempty D.Apartment)
  apply eq_of_common_mem x.mem
  rw [← D.val_eq_of_equivariant_affineEquiv_of_hasOppositeFactorPairs E C hD hE
    hG hi hpair f hlinear hequiv x]
  exact (f x).mem

include hD hE hG hi in
/-- Conditional class uniqueness obtained from the actual affine comparison
and actual opposite-pair existence. -/
theorem eq_of_isOmegaCompatible_of_hasOppositeFactorPairs
    (hpair : RelativeRoot.HasOppositeFactorPairs i) :
    D = E := by
  exact D.eq_of_equivariant_affineEquiv_of_hasOppositeFactorPairs E C hD hE hG hi
    hpair (D.omegaCompatibleApartmentAffineEquiv E C hD hE hG hi)
    (D.omegaCompatibleApartmentAffineEquiv_linear E C hD hE hG hi)
    (D.omegaCompatibleApartmentAffineEquiv_smul E C hD hE hG hi)

end KPApartmentData

/-- Full omega-compatible classes coincide under actual opposite-pair existence. -/
theorem omegaCompatibleApartmentRigidity :
    OmegaCompatibleApartmentRigidityStatement.{u} := by
  intro F _ _ _ _ G _ hG S i _ hi hpair C D E hD hE
  exact D.eq_of_isOmegaCompatible_of_hasOppositeFactorPairs E C hD hE hG hi hpair

end Langlands.Geometry.Building
