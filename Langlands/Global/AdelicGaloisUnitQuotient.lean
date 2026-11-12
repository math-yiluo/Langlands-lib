import Langlands.GroupScheme.AffineWeilUnitGalois
import Langlands.Global.LeftCosetFixedSubgroup
import Langlands.Global.AdelicWeilNormOneQuotientEmbedding
import Langlands.Global.AdelicGroupPolish
import Langlands.GroupScheme.AffinePointClosedImmersion

/-! # Closed scalar-extension quotient embeddings through the Galois Weil unit -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

abbrev W := AffineWeil.groupScheme F L (AffineWeil.unitBaseChange F L G)

/-- The original actual adelic map of the published scalar-extension Weil unit. -/
def unitMap : AdelicGroupPoints F G →ₜ* AdelicGroupPoints F (W F L G) :=
  AdelicGroupPoints.map F G (W F L G) (AffineWeil.unit F L G)

theorem isEmbedding_unitMap : IsEmbedding (unitMap F L G) := by
  let : IsClosedImmersion (AffineWeil.unit F L G).hom.hom.left :=
    AffineWeil.isClosedImmersion_unit_of_field F L G
  exact G.isEmbedding_affinePointsTarget (W F L G) (CommAlgCat.of F (Adeles F))
    (AffineWeil.unit F L G)

/-- The existing unit identifies the source adelic topology with its image topology. -/
def unitRangeEquiv : AdelicGroupPoints F G ≃ₜ* (unitMap F L G).toMonoidHom.range where
  toMulEquiv := MonoidHom.ofInjective (isEmbedding_unitMap F L G).injective
  continuous_toFun := (unitMap F L G).continuous.subtype_mk _
  continuous_invFun := by
    apply (isEmbedding_unitMap F L G).continuous_iff.mpr
    have he : (unitMap F L G) ∘
        (MonoidHom.ofInjective (isEmbedding_unitMap F L G).injective).symm =
        (fun x : (unitMap F L G).toMonoidHom.range => (x : AdelicGroupPoints F (W F L G))) := by
      funext x
      exact congrArg Subtype.val
        ((MonoidHom.ofInjective (isEmbedding_unitMap F L G).injective).apply_symm_apply x)
    change Continuous ((unitMap F L G) ∘
      (MonoidHom.ofInjective (isEmbedding_unitMap F L G).injective).symm)
    rw [he]
    exact continuous_subtype_val

@[simp] theorem unitRangeEquiv_val (x : AdelicGroupPoints F G) :
    (unitRangeEquiv F L G x : AdelicGroupPoints F (W F L G)) = unitMap F L G x := rfl

variable [IsGalois F L]

/-- On the actual adele coefficients, the unit image is the common fixed subgroup. -/
theorem mem_unitRange_iff (x : AdelicGroupPoints F (W F L G)) :
    x ∈ (unitMap F L G).toMonoidHom.range ↔
      ∀ σ : L ≃ₐ[F] L,
        AdelicGroupPoints.map F (W F L G) (W F L G)
          (AffineWeil.unitGaloisAction F L G σ) x = x :=
  AffineWeil.mem_range_unit_iff_galois_fixed F L G (CommAlgCat.of F (Adeles F)) x

/-- The unit image has precisely the original source principal subgroup. -/
theorem map_rationalSubgroup_unitRange :
    (rationalSubgroup F G).map (unitRangeEquiv F L G).toMonoidHom =
      (rationalSubgroup F (W F L G)).subgroupOf (unitMap F L G).toMonoidHom.range := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨G.affinePointsTarget (AffineWeil.unit F L G) (CommAlgCat.of F F) q, ?_⟩
    exact DFunLike.congr_fun (rational_naturality F G (AffineWeil.unit F L G)) q
  · intro hx
    obtain ⟨q, hq⟩ := hx
    have hqfixed : ∀ σ : L ≃ₐ[F] L,
        (W F L G).affinePointsTarget (AffineWeil.unitGaloisAction F L G σ)
          (CommAlgCat.of F F) q = q := by
      intro σ
      apply rational_injective F (W F L G)
      have hn := DFunLike.congr_fun
        (rational_naturality F (W F L G) (AffineWeil.unitGaloisAction F L G σ)) q
      simp only [MonoidHom.comp_apply] at hn
      change rational F (W F L G)
        ((W F L G).affinePointsTarget (AffineWeil.unitGaloisAction F L G σ)
          (CommAlgCat.of F F) q) = _
      rw [hn, hq]
      exact (mem_unitRange_iff F L G x).mp x.property σ
    obtain ⟨p, hp⟩ := (AffineWeil.mem_range_unit_iff_galois_fixed F L G
      (CommAlgCat.of F F) q).mpr hqfixed
    refine ⟨rational F G p, ⟨p, rfl⟩, ?_⟩
    apply Subtype.ext
    change unitMap F L G (rational F G p) = (x : AdelicGroupPoints F (W F L G))
    have hn := DFunLike.congr_fun (rational_naturality F G (AffineWeil.unit F L G)) p
    exact hn.symm.trans ((congrArg (rational F (W F L G)) hp).trans hq)

/-- Source rational quotient as the quotient of the fixed image subgroup. -/
def unitRangeQuotientHomeomorph : RationalQuotient F G ≃ₜ
    LeftCosetSpace ((rationalSubgroup F (W F L G)).subgroupOf
      (unitMap F L G).toMonoidHom.range) :=
  LeftCosetSpace.congrHomeomorph _ _ (unitRangeEquiv F L G)
    (map_rationalSubgroup_unitRange F L G)

/-- The original unit map on full actual rational quotients. -/
def fullQuotientMap : RationalQuotient F G → RationalQuotient F (W F L G) :=
  LeftCosetSpace.subgroupInclusion (rationalSubgroup F (W F L G))
    (unitMap F L G).toMonoidHom.range ∘ unitRangeQuotientHomeomorph F L G

@[simp] theorem fullQuotientMap_mk (x : AdelicGroupPoints F G) :
    fullQuotientMap F L G (LeftCosetSpace.mk (rationalSubgroup F G) x) =
      LeftCosetSpace.mk (rationalSubgroup F (W F L G)) (unitMap F L G x) := rfl

/-- Galois fixed points give a closed embedding on the full actual rational quotients. -/
theorem isClosedEmbedding_fullQuotientMap : IsClosedEmbedding (fullQuotientMap F L G) := by
  apply IsClosedEmbedding.comp _ (unitRangeQuotientHomeomorph F L G).isClosedEmbedding
  apply LeftCosetSpace.isClosedEmbedding_subgroupInclusion_fixed
    (rationalSubgroup F (W F L G)) (unitMap F L G).toMonoidHom.range
    (fun σ : L ≃ₐ[F] L => AdelicGroupPoints.map F (W F L G) (W F L G)
      (AffineWeil.unitGaloisAction F L G σ))
    (rationalSubgroup_isClosed F (W F L G))
  · intro σ _ hq
    obtain ⟨q, rfl⟩ := hq
    refine ⟨(W F L G).affinePointsTarget (AffineWeil.unitGaloisAction F L G σ)
      (CommAlgCat.of F F) q, ?_⟩
    exact DFunLike.congr_fun
      (rational_naturality F (W F L G) (AffineWeil.unitGaloisAction F L G σ)) q
  · exact mem_unitRange_iff F L G

/-- The original unit induces a closed embedding on the actual norm-one rational quotients. -/
theorem isClosedEmbedding_normOneQuotientMap :
    IsClosedEmbedding (normOneRationalQuotientMap F G (W F L G) (AffineWeil.unit F L G)) := by
  apply IsClosedEmbedding.of_comp (isClosedEmbedding_normOneQuotientInclusion F (W F L G)).isEmbedding
  have he : normOneQuotientInclusion F (W F L G) ∘
      normOneRationalQuotientMap F G (W F L G) (AffineWeil.unit F L G) =
      fullQuotientMap F L G ∘ normOneQuotientInclusion F G := by
    funext q
    induction q using Quotient.inductionOn with
    | _ x => rfl
  rw [he]
  exact (isClosedEmbedding_fullQuotientMap F L G).comp
    (isClosedEmbedding_normOneQuotientInclusion F G)

/-- The exact scalar-extension map on actual norm-one rational quotients. -/
def scalarExtensionQuotientMap : NormOneRationalQuotient F G →
    NormOneRationalQuotient L (AffineWeil.unitBaseChange F L G) :=
  AdelicWeilRestriction.normOneQuotientMap F L (AffineWeil.unitBaseChange F L G) ∘
    normOneRationalQuotientMap F G (W F L G) (AffineWeil.unit F L G)

@[simp] theorem scalarExtensionQuotientMap_mk (x : normOneSubgroup F G) :
    scalarExtensionQuotientMap F L G
        (LeftCosetSpace.mk (rationalNormOneSubgroup F G) x) =
      LeftCosetSpace.mk (rationalNormOneSubgroup L (AffineWeil.unitBaseChange F L G))
        (AdelicWeilRestriction.normOneMap F L (AffineWeil.unitBaseChange F L G)
          (mapNormOne F G (W F L G) (AffineWeil.unit F L G) x)) := rfl

/-- Finite Galois scalar extension is a closed embedding of actual norm-one rational quotients. -/
theorem isClosedEmbedding_scalarExtensionQuotientMap :
    IsClosedEmbedding (scalarExtensionQuotientMap F L G) :=
  (AdelicWeilRestriction.isClosedEmbedding_normOneQuotientMap F L
    (AffineWeil.unitBaseChange F L G)).comp (isClosedEmbedding_normOneQuotientMap F L G)

/-- Compact principal representatives descend along finite Galois scalar extension. -/
theorem hasCompactNormOneRationalCover_of_baseChange
    (h : HasCompactNormOneRationalCover (AffineWeil.unitBaseChange F L G)) :
    HasCompactNormOneRationalCover G := by
  let : CompactSpace (NormOneRationalQuotient L (AffineWeil.unitBaseChange F L G)) :=
    h.compactSpace
  exact hasCompactNormOneRationalCover_of_isClosedEmbedding (scalarExtensionQuotientMap F L G)
    (isClosedEmbedding_scalarExtensionQuotientMap F L G) isClosed_closure.isCompact

end Langlands.Global.AdelicGaloisUnit
