import Langlands.Representation.Induction.CompactNormalizationTransport

/-! # Normalizing a natural split-stages comparison family -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe uG uL uV uW uC uE

open CategoryTheory

namespace Langlands.Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (P H : Subgroup G) (hker : r.ker ≤ P) (hHP : H ≤ P)
variable (hH : IsClosed (H : Set G)) (hsH : ∀ l : P.comap s, s (l : L) ∈ H)

local notation "K" => P.comap s
local notation "rP" => splitStagesRetraction r s hrs P hker
local notation "sP" => s.subgroupComap P
local notation "HP" => H.subgroupOf P
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)
local notation "hHPc" => hH.preimage (continuous_subtype_val : Continuous P.subtype)
local notation "χI" => Jacquet.complexCharacter (splitKernelHaarRatio rP sP HP hsH hHPc)

variable [LocallyCompactSpace (splitStagesRetraction r s hrs P hker).ker]

local instance familyKernelMeasurable : MeasurableSpace (rP).ker := borel _
local instance familyKernelBorel : BorelSpace (rP).ker := ⟨rfl⟩
local instance familyIntersectionMeasurable : MeasurableSpace ((HP).comap (rP).ker.subtype) := borel _
local instance familyIntersectionBorel : BorelSpace ((HP).comap (rP).ker.subtype) := ⟨rfl⟩

/-- A natural split-stages equivalence family, with all action indices fixed
before a geometric coefficient functor is substituted. -/
def SplitStagesComparisonFamily : Type (max uG uL (uV + 1)) :=
  { E : ∀ A : SmoothRep.{0,uG,uV} ℂ H,
      Representation.Equiv
        (((compactInduced H A.representation).toCoinvariants r.ker).comp s)
        (compactInduced K
          (twist χI (splitKernelCoefficientAction rP sP HP hsH
            (A.representation.comp φ)))) //
    ∀ (A B : SmoothRep.{0,uG,uV} ℂ H) (f : A ⟶ B) x,
      E B (Representation.Coinvariants.map _ _
        (Jacquet.restrictMap (compactInducedMap H (SmoothRep.hom f)) r.ker) x) =
      compactInducedMap K
        (splitStagesCoefficientMap r s hrs P H hker hHP hH hsH A.representation
          (SmoothRep.hom f)) (E A x) }

namespace SplitStagesComparisonFamily

variable (F : SplitStagesComparisonFamily.{uG,uL,uV} r s hrs P H hker hHP hH hsH)
variable {J : Subgroup L} (hK : P.comap s = J) (χ : SmoothCharacter ℂ L)
variable (A B : SmoothRep.{0,uG,uV} ℂ H)

local notation "κA" => twist χI
  (splitKernelCoefficientAction rP sP HP hsH (A.representation.comp φ))
local notation "κB" => twist χI
  (splitKernelCoefficientAction rP sP HP hsH (B.representation.comp φ))

variable {V : Type uW} [AddCommGroup V] [Module ℂ V]
  {W : Type uC} [AddCommGroup W] [Module ℂ W]

/-- Naturality of normalization is derived while the split-stages action
indices are still abstract. -/
theorem normalized_natural
    (τ : Representation ℂ J V) (τ' : Representation ℂ J W)
    (e : Representation.Equiv
      ((twist (χ.toMonoidHom.comp (K).subtype) κA).comp
        (MulEquiv.subgroupCongr hK).symm.toMonoidHom) τ)
    (e' : Representation.Equiv
      ((twist (χ.toMonoidHom.comp (K).subtype) κB).comp
        (MulEquiv.subgroupCongr hK).symm.toMonoidHom) τ')
    (f : A ⟶ B) (U : τ.IntertwiningMap τ')
    (he : ∀ a, e'
      (splitStagesCoefficientMap r s hrs P H hker hHP hH hsH A.representation
        (SmoothRep.hom f) a) = U (e a))
    (x : Representation.Coinvariants ((compactInduced H A.representation).comp r.ker.subtype)) :
    CompactNormalizationTransport.normalizedTransport hK _ _ τ' χ (F.val B) e'
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap (compactInducedMap H (SmoothRep.hom f)) r.ker) x) =
      compactInducedMap J U
        (CompactNormalizationTransport.normalizedTransport hK _ _ τ χ (F.val A) e x) := by
  exact CompactNormalizationTransport.normalizedTransport_natural hK _ _ _ _ τ τ' χ
    (F.val A) (F.val B) e e'
    (restrictAlongMap s (normalCoinvariantsMap r.ker (compactInducedMap H (SmoothRep.hom f))))
    (splitStagesCoefficientMap r s hrs P H hker hHP hH hsH A.representation (SmoothRep.hom f))
    U (F.property A B f) he x

end SplitStagesComparisonFamily

end Langlands.Induction
