import Langlands.GroupScheme.AffineNormalSubgroupQuotientStatement
import Langlands.GroupScheme.NormalQuotientStatement

/-! # Equivalent formulations of affine normal-subgroup quotient existence -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Reorder the ambient hypotheses and the quotient's two geometric properties.
The actual quotient map and its all-test scheme-kernel equality are unchanged. -/
theorem NormalSubgroupQuotientExistenceStatement.toAffineNormalSubgroupQuotientStatement
    (h : NormalSubgroupQuotientExistenceStatement.{u}) :
    AffineNormalSubgroupQuotientStatement.{u} := by
  intro k _ G _ _ N i hi hn
  obtain ⟨Q, q, hQaff, hQlft, hq⟩ :=
    h k G N i inferInstance inferInstance hi hn
  exact ⟨Q, q, hQlft, hQaff, hq⟩

/-- Restore the explicitly supplied ambient geometric hypotheses and the
original order of the quotient's geometric properties. -/
theorem AffineNormalSubgroupQuotientStatement.toNormalSubgroupQuotientExistenceStatement
    (h : AffineNormalSubgroupQuotientStatement.{u}) :
    NormalSubgroupQuotientExistenceStatement.{u} := by
  intro k _ G N i hGaff hGlft hi hn
  let : IsAffineHom G.X.hom := hGaff
  let : LocallyOfFiniteType G.X.hom := hGlft
  obtain ⟨Q, q, hQlft, hQaff, hq⟩ := h k G N i hi hn
  exact ⟨Q, q, hQaff, hQlft, hq⟩

/-- The two unrestricted affine normal-subgroup quotient propositions differ
only in binder style and the order of their geometric conclusions. -/
def AffineNormalSubgroupQuotientEquivalenceStatement : Prop :=
  NormalSubgroupQuotientExistenceStatement.{u} ↔
    AffineNormalSubgroupQuotientStatement.{u}

/-- The exact quotient data can be reused in either formulation. -/
theorem affineNormalSubgroupQuotientEquivalence :
    AffineNormalSubgroupQuotientEquivalenceStatement.{u} :=
  ⟨NormalSubgroupQuotientExistenceStatement.toAffineNormalSubgroupQuotientStatement,
    AffineNormalSubgroupQuotientStatement.toNormalSubgroupQuotientExistenceStatement⟩

end Langlands.GroupScheme
