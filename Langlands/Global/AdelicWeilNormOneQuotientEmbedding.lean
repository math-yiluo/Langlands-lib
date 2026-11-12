import Langlands.Global.AdelicWeilNormOneMap
import Langlands.Global.AdelicWeilNormOneQuotient

/-! # Closed embedding of actual norm-one Weil rational quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicWeilRestriction

open Langlands.GroupScheme AdelicGroupPoints

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] (G : GroupScheme (Spec (CommRingCat.of L)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The fixed full adelic comparison carries exactly the actual principal subgroups. -/
theorem map_rationalSubgroup :
    (rationalSubgroup F (AffineWeil.groupScheme F L G)).map
      (adelicPointsEquiv F L G).toMonoidHom = rationalSubgroup L G := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨rationalPointsEquiv F L G q, (adelicPointsEquiv_rational F L G q).symm⟩
  · rintro ⟨q, rfl⟩
    refine ⟨rational F _ ((rationalPointsEquiv F L G).symm q), ⟨_, rfl⟩, ?_⟩
    change adelicPointsEquiv F L G
      (rational F _ ((rationalPointsEquiv F L G).symm q)) = _
    rw [adelicPointsEquiv_rational, MulEquiv.apply_symm_apply]

/-- The full actual adelic Weil comparison descends to the actual rational quotients. -/
def rationalQuotientHomeomorph :
    RationalQuotient F (AffineWeil.groupScheme F L G) ≃ₜ RationalQuotient L G :=
  LeftCosetSpace.congrHomeomorph _ _ (adelicPointsContinuousEquiv F L G)
    (map_rationalSubgroup F L G)

@[simp] theorem rationalQuotientHomeomorph_mk
    (g : AdelicGroupPoints F (AffineWeil.groupScheme F L G)) :
    rationalQuotientHomeomorph F L G (LeftCosetSpace.mk (rationalSubgroup F _) g) =
      LeftCosetSpace.mk (rationalSubgroup L G) (adelicPointsEquiv F L G g) := rfl

/-- The restricted canonical map descends to the original norm-one rational quotients. -/
def normOneQuotientMap :
    NormOneRationalQuotient F (AffineWeil.groupScheme F L G) →
      NormOneRationalQuotient L G :=
  LeftCosetSpace.lift (rationalNormOneSubgroup F (AffineWeil.groupScheme F L G))
    (fun x => LeftCosetSpace.mk (rationalNormOneSubgroup L G) (normOneMap F L G x))
    (by
      rintro ⟨_, q, rfl⟩ x
      rw [map_mul, normOneMap_rational]
      exact LeftCosetSpace.mk_subgroup_mul (rationalNormOneSubgroup L G)
        ⟨rationalNormOne L G (rationalPointsEquiv F L G q), ⟨_, rfl⟩⟩ _)

@[simp] theorem normOneQuotientMap_mk
    (g : normOneSubgroup F (AffineWeil.groupScheme F L G)) :
    normOneQuotientMap F L G (LeftCosetSpace.mk (rationalNormOneSubgroup F _) g) =
      LeftCosetSpace.mk (rationalNormOneSubgroup L G) (normOneMap F L G g) := rfl

/-- Compatibility with the closed inclusions into full actual rational quotients. -/
theorem normOneQuotientInclusion_comp_normOneQuotientMap :
    normOneQuotientInclusion L G ∘ normOneQuotientMap F L G =
      rationalQuotientHomeomorph F L G ∘
        normOneQuotientInclusion F (AffineWeil.groupScheme F L G) := by
  funext q
  induction q using Quotient.inductionOn with
  | _ g => rfl

/-- Closedness needs only the forward norm-one inclusion, not character classification. -/
theorem isClosedEmbedding_normOneQuotientMap :
    IsClosedEmbedding (normOneQuotientMap F L G) := by
  apply IsClosedEmbedding.of_comp (isClosedEmbedding_normOneQuotientInclusion L G).isEmbedding
  rw [normOneQuotientInclusion_comp_normOneQuotientMap]
  exact (rationalQuotientHomeomorph F L G).isClosedEmbedding.comp
    (isClosedEmbedding_normOneQuotientInclusion F (AffineWeil.groupScheme F L G))

/-- Upper-field compact representatives give ground-field Weil compact representatives. -/
theorem hasCompactNormOneRationalCover_of_upper
    (h : HasCompactNormOneRationalCover G) :
    HasCompactNormOneRationalCover (AffineWeil.groupScheme F L G) := by
  let : CompactSpace (NormOneRationalQuotient L G) := h.compactSpace
  exact hasCompactNormOneRationalCover_of_isClosedEmbedding (normOneQuotientMap F L G)
    (isClosedEmbedding_normOneQuotientMap F L G) isClosed_closure.isCompact

end Langlands.Global.AdelicWeilRestriction
