import Langlands.GroupScheme.SimplyConnected.LocalGaloisCocycleVanishingStatement
import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedSplittingStatement
import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedCocycleVanishingStatement
import Langlands.GroupScheme.CocycleDescent
import Langlands.GroupScheme.BaseChangeReflection

/-! # From finite unramified covers to finite Galois covers

A cocycle on a finite Galois cover `Spec M` is refined to the fibre product
`Spec M ⊗ Spec E` with a finite unramified extension `E` over which it splits. Twisting the
refinement by the splitting point makes it trivial on the fibres of the projection to
`Spec E`, so it descends to a cocycle on `Spec E`, which is trivial by unramified vanishing.
Triviality is then reflected back to `Spec M`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Splitting over finite unramified extensions and vanishing on finite unramified covers give
vanishing on finite Galois covers. -/
theorem localSimplyConnectedGaloisCocycleVanishing_of_unramified
    (hS : LocalSimplyConnectedUnramifiedSplittingStatement.{u})
    (hBT : LocalSimplyConnectedUnramifiedCocycleVanishingStatement.{u}) :
    LocalSimplyConnectedGaloisCocycleVanishingStatement.{u} := by
  intro F _ _ _ _ G _ hG M _ _ _ _ ξ
  obtain ⟨E, hfin, hE, g, hg⟩ := hS F G hG M ξ
  let U : Over (Spec (CommRingCat.of F)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F M)))
  let W : Over (Spec (CommRingCat.of F)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E)))
  obtain ⟨hU₁, hU₂, hU₃⟩ := fieldExtension_fpqc F M
  obtain ⟨hW₁, hW₂, hW₃⟩ := fieldExtension_fpqc F E
  have : Surjective U.hom := hU₁
  have : Flat U.hom := hU₂
  have : QuasiCompact U.hom := hU₃
  have : Surjective W.hom := hW₁
  have : Flat W.hom := hW₂
  have : QuasiCompact W.hom := hW₃
  have : Surjective (fst U W).left := inferInstanceAs (Surjective (Limits.pullback.fst _ _))
  have : Flat (fst U W).left := inferInstanceAs (Flat (Limits.pullback.fst _ _))
  have : QuasiCompact (fst U W).left := inferInstanceAs (QuasiCompact (Limits.pullback.fst _ _))
  have : Surjective (snd U W).left := inferInstanceAs (Surjective (Limits.pullback.snd _ _))
  have : Flat (snd U W).left := inferInstanceAs (Flat (Limits.pullback.snd _ _))
  have : QuasiCompact (snd U W).left := inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
  let ξ' : Cocycle G U := ξ
  let ζ := (ξ'.refine (fst U W)).twist g
  have hζ : ∀ {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ U ⊗ W),
      a ≫ snd U W = b ≫ snd U W → ζ.toFun a b = 1 := by
    intro Z a b hab
    change (a ≫ g)⁻¹ * ξ.toFun (a ≫ fst U W) (b ≫ fst U W) * (b ≫ g) = 1
    rw [hg a b hab]
    group
  have hW : ∀ ν : Cocycle G W, ν.IsTrivial := fun ν => hBT F G hG E hE ν
  have hζt : ζ.IsTrivial := Cocycle.isTrivial_of_comp_eq ζ (snd U W) hζ hW
  exact (ξ'.isTrivial_refine_iff (fst U W)).mp (Cocycle.IsTrivial.of_twist hζt)

end Langlands.GroupScheme
