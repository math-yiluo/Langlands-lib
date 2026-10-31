import Langlands.AbelianScheme.LieBaseChangeNaturalityStatement
import Langlands.AbelianScheme.CotangentBaseChangeNaturalityProof

/-! # Naturality of canonical Lie base change -/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Langlands.Scheme.Modules

namespace Langlands.AbelianScheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Dualization and cancellation reduce Lie naturality to cotangent naturality. -/
theorem lieBaseChangeNaturality_of_cotangent
    (S : AlgebraicGeometry.Scheme.{u})
    (hc : CotangentBaseChangeNaturalityStatement S) :
    LieBaseChangeNaturalityStatement S := by
  intro T b A B f ellA ellB _hIsoA hIsoB hA hB
  have := hIsoB
  have : IsIso (dualMap (GroupScheme.cotangentBaseChangeMap b B.toGrp)) :=
    inferInstanceAs
      (IsIso ((dualFunctor T).map
        (GroupScheme.cotangentBaseChangeMap b B.toGrp).op))
  have hd := congrArg (fun k => dualMap k) (hc T b A B f)
  simp only [dualMap_comp] at hd
  change
    dualMap (GroupScheme.cotangentBaseChangeMap b A.toGrp) ≫
        dualMap ((pullback b).map (GroupScheme.cotangentMap (groupHom f))) =
      lieMap ((baseChange b).map f) ≫
        dualMap (GroupScheme.cotangentBaseChangeMap b B.toGrp) at hd
  apply (cancel_mono (dualMap (GroupScheme.cotangentBaseChangeMap b B.toGrp))).mp
  simp only [Category.assoc]
  rw [hB, ← hd, ← Category.assoc, hA]
  exact dualPullbackComparison_naturality b
    (GroupScheme.cotangentMap (groupHom f))

/-- The endomorphism square is the all-homomorphism square with repeated data. -/
theorem lieBaseChangeEndomorphismNaturality_of_naturality
    (S : AlgebraicGeometry.Scheme.{u})
    (h : LieBaseChangeNaturalityStatement S) :
    LieBaseChangeEndomorphismNaturalityStatement S := by
  intro T b A f ell hiso hell
  exact h T b A A f ell ell hiso hiso hell hell

/-- Both Lie squares follow from the actual abelian cotangent square. -/
theorem lieBaseChangeNaturalityStatements_of_cotangent
    (S : AlgebraicGeometry.Scheme.{u})
    (hc : CotangentBaseChangeNaturalityStatement S) :
    LieBaseChangeNaturalityStatements S := by
  have h := lieBaseChangeNaturality_of_cotangent S hc
  exact ⟨h, lieBaseChangeEndomorphismNaturality_of_naturality S h⟩

/-- Canonical Lie base change is natural in every actual abelian homomorphism,
together with its endomorphism specialization. -/
theorem lieBaseChangeNaturalityStatements
    (S : AlgebraicGeometry.Scheme.{u}) :
    LieBaseChangeNaturalityStatements S :=
  lieBaseChangeNaturalityStatements_of_cotangent S
    (Langlands.cotangentBaseChangeNaturalityStatements S).2

end Langlands.AbelianScheme
