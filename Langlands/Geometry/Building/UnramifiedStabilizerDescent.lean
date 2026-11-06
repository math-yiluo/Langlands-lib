import Langlands.Geometry.Building.KPCharacterValuationDescentProof
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData

/-! # Stabilizer descent along a supplied maximal-unramified building embedding -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

section EquivalentValuations

variable {k : Type u} [Field k]
  {Γ₁ : Type v} [LinearOrderedCommGroupWithZero Γ₁]
  {Γ₂ : Type w} [LinearOrderedCommGroupWithZero Γ₂]
  {v₁ : Valuation k Γ₁} {v₂ : Valuation k Γ₂}

/-- Equivalent valuations have the same actual rational-character unit kernel. -/
theorem characterValuationKernel_eq_of_isEquiv
    (h : v₁.IsEquiv v₂) (G : GroupScheme (Spec (CommRingCat.of k))) :
    characterValuationKernel v₁ G = characterValuationKernel v₂ G := by
  ext g
  rw [mem_characterValuationKernel, mem_characterValuationKernel]
  exact forall_congr' fun _ => h.eq_one_iff_eq_one

end EquivalentValuations

namespace MaximalUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private instance baseAffine
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] :
    IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

private instance extensionAffineHom
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

/-- The integer-normalized character kernel descends exactly to the original
local-field rational norm kernel. -/
theorem characterValuationKernel_comap
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] :
    (characterValuationKernel (valuation F)
        (baseChanged F (UnramifiedClosure F) G)).comap
      (rationalExtend F (UnramifiedClosure F) G) =
        Plancherel.rationalCommonNormKernel G := by
  rw [characterValuationKernel_eq_of_isEquiv (valuation_isEquiv F)]
  exact characterValuationKernelDescent_proof F G

variable {F}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  (C : BuildingData F (baseChanged F (UnramifiedClosure F) G))
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (hinj : Function.Injective e)
  (he : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
    e (g • z) = rationalExtend F (UnramifiedClosure F) G g • e z)

include hinj he

/-- Injectivity and equivariance identify the full point fixers as actual
subgroups of the original rational-point group. -/
theorem fixer_comap (z : B.ReducedBuilding) :
    (C.fixer (e z)).comap (rationalExtend F (UnramifiedClosure F) G) =
      B.fixer z := by
  ext g
  change rationalExtend F (UnramifiedClosure F) G g ∈ C.fixer (e z) ↔
    g ∈ B.fixer z
  rw [C.mem_fixer, B.mem_fixer, ← he]
  exact hinj.eq_iff

/-- The same descent identity holds for the pointwise fixer of every subset,
using its actual image under the supplied embedding. -/
theorem pointwiseFixer_comap (Y : Set B.ReducedBuilding) :
    (C.pointwiseFixer (e '' Y)).comap
        (rationalExtend F (UnramifiedClosure F) G) =
      B.apartment.pointwiseFixer Y := by
  ext g
  change rationalExtend F (UnramifiedClosure F) G g ∈ C.pointwiseFixer (e '' Y) ↔
    g ∈ B.apartment.pointwiseFixer Y
  rw [C.apartment.mem_pointwiseFixer, B.apartment.mem_pointwiseFixer,
    Set.forall_mem_image]
  constructor
  · intro h z hz
    apply hinj
    rw [he]
    exact h hz
  · intro h z hz
    rw [← he, h z hz]

/-- The upstairs integer-valued norm-one stabilizer has exactly the original
local-field compact stabilizer as its rational-point preimage. -/
theorem oneStabilizer_comap (z : B.ReducedBuilding) :
    (C.oneStabilizer (e z)).comap
        (rationalExtend F (UnramifiedClosure F) G) =
      B.compactStabilizer z := by
  change (characterValuationKernel (valuation F)
      (baseChanged F (UnramifiedClosure F) G) ⊓ C.fixer (e z)).comap
        (rationalExtend F (UnramifiedClosure F) G) =
    Plancherel.rationalCommonNormKernel G ⊓ B.fixer z
  rw [Subgroup.comap_inf, characterValuationKernel_comap,
    fixer_comap B C e hinj he z]

/-- Actual scalar extension restricted to the original compact stabilizer and
the upstairs integer-valued norm-one stabilizer. -/
def oneStabilizerExtend (z : B.ReducedBuilding) :
    B.compactStabilizer z →* C.oneStabilizer (e z) where
  toFun g := ⟨rationalExtend F (UnramifiedClosure F) G g, by
    change (g : rationalPoints G) ∈
      (C.oneStabilizer (e z)).comap (rationalExtend F (UnramifiedClosure F) G)
    rw [oneStabilizer_comap B C e hinj he z]
    exact g.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ (g : rationalPoints G) (h : rationalPoints G))

@[simp] theorem coe_oneStabilizerExtend (z : B.ReducedBuilding)
    (g : B.compactStabilizer z) :
    (oneStabilizerExtend B C e hinj he z g :
        rationalPoints (baseChanged F (UnramifiedClosure F) G)) =
      rationalExtend F (UnramifiedClosure F) G (g : rationalPoints G) :=
  rfl

/-- The restricted extension retains the injectivity of extension on affine
rational points; no finite-dimensionality of the extension is needed. -/
theorem oneStabilizerExtend_injective (z : B.ReducedBuilding) :
    Function.Injective (oneStabilizerExtend B C e hinj he z) := by
  intro g h hgh
  apply Subtype.ext
  apply (rationalCoeffEquiv F G).injective
  apply GaloisPoint.extend_injective F (UnramifiedClosure F) G
  have hr : rationalExtend F (UnramifiedClosure F) G (g : rationalPoints G) =
      rationalExtend F (UnramifiedClosure F) G (h : rationalPoints G) :=
    congrArg Subtype.val hgh
  have hc := congrArg (baseChangeCoeffEquiv F (UnramifiedClosure F) G) hr
  simpa only [baseChangeCoeffEquiv_rationalExtend] using hc

end MaximalUnramified

end Langlands.Geometry.Building
