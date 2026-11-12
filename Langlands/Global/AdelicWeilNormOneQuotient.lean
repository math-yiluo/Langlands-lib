import Langlands.Global.AdelicWeilNormOneComparison
import Langlands.Global.AdelicNormOneQuotientClosedEmbedding

/-! # Actual norm-one rational quotients under Weil comparison -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global

namespace LeftCosetSpace

variable {H : Type u} {J : Type v} [Group H] [Group J]
  [TopologicalSpace H] [TopologicalSpace J]

/-- A topological group equivalence carrying one subgroup onto another descends to the
existing left homogeneous quotients, without a normality hypothesis. -/
def congrHomeomorph (Γ : Subgroup H) (Δ : Subgroup J) (e : H ≃ₜ* J)
    (hΓ : Γ.map e.toMonoidHom = Δ) : LeftCosetSpace Γ ≃ₜ LeftCosetSpace Δ where
  toEquiv := Quotient.congr e.toEquiv (fun x y => by
    have hmem (z : H) : e z ∈ Δ ↔ z ∈ Γ := by
      rw [← hΓ, Subgroup.mem_map]
      exact ⟨fun ⟨w, hw, he⟩ => e.injective he ▸ hw, fun hz => ⟨z, hz, rfl⟩⟩
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change y * x⁻¹ ∈ Γ ↔ e y * (e x)⁻¹ ∈ Δ
    rw [← map_inv, ← map_mul, hmem])
  continuous_toFun := (continuous_iff Γ).mpr ((continuous_mk Δ).comp e.continuous)
  continuous_invFun := (continuous_iff Δ).mpr ((continuous_mk Γ).comp e.symm.continuous)

@[simp] theorem congrHomeomorph_mk (Γ : Subgroup H) (Δ : Subgroup J) (e : H ≃ₜ* J)
    (hΓ : Γ.map e.toMonoidHom = Δ) (x : H) :
    congrHomeomorph Γ Δ e hΓ (mk Γ x) = mk Δ (e x) := rfl

end LeftCosetSpace

namespace AdelicWeilRestriction

open Langlands.GroupScheme AdelicGroupPoints

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] (G : GroupScheme (Spec (CommRingCat.of L)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (htop : IsHomeomorph (adelicPointsEquiv F L G))
  (hnorm : (normOneSubgroup F (AffineWeil.groupScheme F L G)).map
      (adelicPointsEquiv F L G).toMonoidHom = normOneSubgroup L G)

/-- Restriction of the fixed canonical Weil equivalence to the actual norm-one groups,
conditional on the two exact topological and character-kernel comparison assertions. -/
def normOnePointsEquiv :
    normOneSubgroup F (AffineWeil.groupScheme F L G) ≃ₜ* normOneSubgroup L G where
  toMulEquiv := ((adelicPointsEquiv F L G).subgroupMap
    (normOneSubgroup F (AffineWeil.groupScheme F L G))).trans (MulEquiv.subgroupCongr hnorm)
  continuous_toFun := (htop.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (((Equiv.isHomeomorph_iff (adelicPointsEquiv F L G).toEquiv).mp htop).2.comp
      continuous_subtype_val).subtype_mk _

@[simp] theorem normOnePointsEquiv_val
    (g : normOneSubgroup F (AffineWeil.groupScheme F L G)) :
    (normOnePointsEquiv F L G htop hnorm g : AdelicGroupPoints L G) =
      adelicPointsEquiv F L G g := rfl

variable (hprincipal : ∀ q : RationalGroupPoints F (AffineWeil.groupScheme F L G),
  adelicPointsEquiv F L G (rational F _ q) =
    rational L G (rationalPointsEquiv F L G q))

include htop hnorm hprincipal

/-- The restricted canonical comparison has exactly the prescribed principal-point square. -/
@[simp] theorem normOnePointsEquiv_rational
    (q : RationalGroupPoints F (AffineWeil.groupScheme F L G)) :
    normOnePointsEquiv F L G htop hnorm (rationalNormOne F _ q) =
      rationalNormOne L G (rationalPointsEquiv F L G q) := by
  apply Subtype.ext
  exact hprincipal q

/-- The actual principal subgroup is carried onto the actual upper-field principal subgroup. -/
theorem map_rationalNormOneSubgroup :
    (rationalNormOneSubgroup F (AffineWeil.groupScheme F L G)).map
      (normOnePointsEquiv F L G htop hnorm).toMonoidHom = rationalNormOneSubgroup L G := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨rationalPointsEquiv F L G q,
      (normOnePointsEquiv_rational F L G htop hnorm hprincipal q).symm⟩
  · rintro ⟨q, rfl⟩
    refine ⟨rationalNormOne F _ ((rationalPointsEquiv F L G).symm q),
      ⟨_, rfl⟩, ?_⟩
    change normOnePointsEquiv F L G htop hnorm
      (rationalNormOne F _ ((rationalPointsEquiv F L G).symm q)) = _
    rw [normOnePointsEquiv_rational F L G htop hnorm hprincipal,
      MulEquiv.apply_symm_apply]

/-- The canonical norm-one comparison descends to a homeomorphism of the actual rational
quotients, conditional on precisely its three comparison assertions. -/
def normOneRationalQuotientHomeomorph :
    NormOneRationalQuotient F (AffineWeil.groupScheme F L G) ≃ₜ
      NormOneRationalQuotient L G :=
  LeftCosetSpace.congrHomeomorph _ _ (normOnePointsEquiv F L G htop hnorm)
    (map_rationalNormOneSubgroup F L G htop hnorm hprincipal)

@[simp] theorem normOneRationalQuotientHomeomorph_mk
    (g : normOneSubgroup F (AffineWeil.groupScheme F L G)) :
    normOneRationalQuotientHomeomorph F L G htop hnorm hprincipal
        (LeftCosetSpace.mk (rationalNormOneSubgroup F _) g) =
      LeftCosetSpace.mk (rationalNormOneSubgroup L G)
        (normOnePointsEquiv F L G htop hnorm g) := rfl

/-- The exact Weil comparison transfers compact principal rational representatives in both
directions; it supplies none of the three comparison assertions. -/
theorem hasCompactNormOneRationalCover_iff :
    HasCompactNormOneRationalCover (AffineWeil.groupScheme F L G) ↔
      HasCompactNormOneRationalCover G := by
  rw [hasCompactNormOneRationalCover_iff_compactSpace,
    hasCompactNormOneRationalCover_iff_compactSpace]
  let e := normOneRationalQuotientHomeomorph F L G htop hnorm hprincipal
  exact ⟨fun h => @Homeomorph.compactSpace _ _ _ _ h e,
    fun h => @Homeomorph.compactSpace _ _ _ _ h e.symm⟩

end AdelicWeilRestriction
end Langlands.Global
