/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.RationalP1.CompletedChernNormalizedUnique
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernBaseChangeChernNoneCanonical

/-! # Specialized coefficient cases for scalar Chern exchange -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

/-- The scalar exchange preserves the positive Chern generator equation in the `none`
coefficient case. -/
theorem scalar_chern_base_change_chern_none
    (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l r.tq.toPresentation a)
    (b : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧))
    (hb : CompletedChernNormalized l r.t₂.toPresentation b) :
    let Λ := (coefficient l none).X
    let cq := scalarQChern l none Y r a
    let c₂ := scalarP2Chern l none Y r b
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    F.map cq ≫ secondTraceExchange l none k p hpl Y =
        (scalarUnitPullIso Λ Y).hom ≫ c₂ := by
  dsimp only
  have hY : IsUnit (l : Γ(Y, ⊤)) := by
    have hl : IsUnit (l : k) :=
      (CharP.isUnit_natCast_iff (Fact.out : p.Prime)).2
        (fun h ↦ hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
          (Fact.out : l.Prime)).1 h))
    simpa only [map_natCast] using
      hl.map ((Y ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  obtain ⟨a₀, ha₀, b₀, hb₀, hcore⟩ :=
    scalar_chern_base_change_chern_none_canonical l k p hpl Y δ family r hY hP
  have haa : a = a₀ := completedChernNormalized_unique l r.tq.toPresentation a a₀ ha ha₀
  have hbb : b = b₀ := completedChernNormalized_unique l r.t₂.toPresentation b b₀ hb hb₀
  subst a
  subst b
  exact hcore

end AlgebraicGeometry.ProEtale.RationalP1
