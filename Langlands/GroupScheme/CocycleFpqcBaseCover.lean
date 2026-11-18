import Langlands.GroupScheme.CocycleCohomology

/-! # Comparison of cocycles on an fpqc cover of the base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {S : Scheme.{u}} {G : GroupScheme S} {U V : Over S}

/-- Two parallel morphisms of covers give cohomologous refinements. -/
theorem cohomologous_refine_maps (ξ : Cocycle G U) (r s : V ⟶ U) :
    (ξ.refine r).Cohomologous (ξ.refine s) := by
  refine ⟨ξ.toFun r s, fun a b => ?_⟩
  change ξ.toFun (a ≫ s) (b ≫ s) =
    (a ≫ ξ.toFun r s)⁻¹ * ξ.toFun (a ≫ r) (b ≫ r) * (b ≫ ξ.toFun r s)
  rw [← ξ.naturality, ← ξ.naturality, mul_assoc, ← ξ.cocycle (a ≫ r) (b ≫ r) (b ≫ s),
    ξ.cocycle (a ≫ r) (a ≫ s) (b ≫ s), inv_mul_cancel_left]

set_option backward.isDefEq.respectTransparency false in
/-- Cohomology on a refinement reflects to the original cover when the
refining scheme is fpqc over the base. -/
theorem Cohomologous.of_refine_fpqcCover {ξ ζ : Cocycle G U} (r : V ⟶ U)
    [QuasiCompact V.hom] [Flat V.hom] [Surjective V.hom]
    (h : (ξ.refine r).Cohomologous (ζ.refine r)) : ξ.Cohomologous ζ := by
  let p := fst U V
  let q := snd U V
  have : QuasiCompact p.left :=
    inferInstanceAs (QuasiCompact (pullback.fst U.hom V.hom))
  have : Flat p.left := inferInstanceAs (Flat (pullback.fst U.hom V.hom))
  have : Surjective p.left := inferInstanceAs (Surjective (pullback.fst U.hom V.hom))
  have hq : (ξ.refine (q ≫ r)).Cohomologous (ζ.refine (q ≫ r)) := by
    obtain ⟨f, hf⟩ := h.refine q
    exact ⟨f, fun a b => by simpa only [refine_toFun, twist, Category.assoc] using hf a b⟩
  exact (cohomologous_refine_iff ξ ζ p).mp
    ((cohomologous_refine_maps ξ p (q ≫ r)).trans
      (hq.trans (cohomologous_refine_maps ζ (q ≫ r) p)))

/-- On an fpqc cover of the base, testing cohomology after refinement is
equivalent to testing it on the original cover. -/
def FpqcBaseCoverCohomologyStatement : Prop :=
  ∀ {S : Scheme.{u}} {G : GroupScheme S} {U V : Over S}
    (ξ ζ : Cocycle G U) (r : V ⟶ U) [QuasiCompact V.hom] [Flat V.hom] [Surjective V.hom],
    (ξ.refine r).Cohomologous (ζ.refine r) ↔ ξ.Cohomologous ζ

/-- An fpqc base-cover refinement preserves and reflects cohomology. -/
theorem cohomologous_refine_fpqcCover_iff : FpqcBaseCoverCohomologyStatement.{u} :=
  fun _ _ r => ⟨fun h => h.of_refine_fpqcCover r, fun h => h.refine r⟩

end Langlands.GroupScheme.Cocycle
