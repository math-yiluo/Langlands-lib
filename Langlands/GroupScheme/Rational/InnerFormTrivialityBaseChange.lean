import Langlands.GroupScheme.Rational.QuasiSplitInnerForm
import Langlands.GroupScheme.CocycleBaseChangeTriviality
import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Absolute.GeometricBorelBaseChange
import Langlands.GroupScheme.Reductive.FieldExtensionProof

/-! # Triviality of an inner form after scalar extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {G : GroupScheme (Spec (CommRingCat.of F))}

/-- A geometric Borel remains a geometric Borel after extending the field. -/
theorem IsQuasiSplit.fieldExtension (h : IsQuasiSplit G) :
    IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) := by
  obtain ⟨P, p, hp⟩ := h.exists_isGeometricBorelSubgroup
  exact ⟨connectedReductiveFieldExtensionStatement F K G h.isConnectedReductive, _, _,
    hp.baseChange h.isConnectedReductive (algebraBaseMap F K)⟩

section BaseChange

local notation "b" => algebraBaseMap F K
local notation "BC" => GroupScheme.baseChange b

variable {L : Type u} [Field L] [Algebra F L]
  {A H : GroupScheme (Spec (CommRingCat.of F))}

/-- A trivial discrepancy on the full scalar-extended cover gives a
ground-field isomorphism after base change. -/
theorem LocalGroupIso.HasDiscrepancy.nonempty_iso_baseChange_of_isTrivial
    {ξ : Cocycle A (GaloisCocycle.cover F L)} {e : LocalGroupIso G H (GaloisCocycle.cover F L)}
    {act : AutomorphicAction A G} (he : e.HasDiscrepancy act ξ)
    (h : (ξ.baseChangePullback b).IsTrivial) : Nonempty ((BC).obj G ≅ (BC).obj H) := by
  let U := GaloisCocycle.cover F L
  let V := (Over.pullback b).obj U
  let r := (Over.mapPullbackAdj b).counit.app U
  obtain ⟨f, hf⟩ := ξ.exists_of_baseChange_isTrivial b V r h
  let E : LocalGroupIso ((BC).obj G) ((BC).obj H) V :=
    { toFun := fun {T} a => (baseChangePointsEquiv b G T).trans
        (((act.pointAut _ ((Over.map b).map a ≫ f)).trans
          (e.toFun ((Over.map b).map a ≫ r))).trans (baseChangePointsEquiv b H T).symm)
      naturality := by
        intro T W s a x
        apply (baseChangePointsEquiv b H W).injective
        simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality,
          Functor.map_comp, Category.assoc]
        change e.toFun ((Over.map b).map s ≫ (Over.map b).map a ≫ r)
            (act.act ((Over.map b).map s ≫ (Over.map b).map a ≫ f)
              ((Over.map b).map s ≫ baseChangePointsEquiv b G T x)) =
          (Over.map b).map s ≫ e.toFun ((Over.map b).map a ≫ r)
            (act.act ((Over.map b).map a ≫ f) (baseChangePointsEquiv b G T x))
        rw [← act.naturality, e.naturality] }
  have hE : E.IsIndependent := by
    intro T x y g
    apply (baseChangePointsEquiv b H T).injective
    let u := baseChangePointsEquiv b G T g
    change (baseChangePointsEquiv b H T) ((baseChangePointsEquiv b H T).symm
        (e.toFun ((Over.map b).map x ≫ r) (act.act ((Over.map b).map x ≫ f) u))) =
      (baseChangePointsEquiv b H T) ((baseChangePointsEquiv b H T).symm
        (e.toFun ((Over.map b).map y ≫ r) (act.act ((Over.map b).map y ≫ f) u)))
    simp only [MulEquiv.apply_symm_apply]
    have hx := hf ((Over.map b).map x) ((Over.map b).map y) ((Over.w x).trans (Over.w y).symm)
    have hh := he ((Over.map b).map x ≫ r) ((Over.map b).map y ≫ r)
      (act.act ((Over.map b).map y ≫ f) u)
    change e.toFun _ (act.act (ξ.toFun _ _)
      (act.act ((Over.map b).map y ≫ f) u)) = _ at hh
    rw [hx, act.act_mul_left, act.act_inv_act] at hh
    exact hh
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc F L
  let : Surjective U.hom := hs
  let : Flat U.hom := hf
  let : QuasiCompact U.hom := hq
  let : Surjective V.hom := inferInstanceAs (Surjective (pullback.snd U.hom b))
  let : Flat V.hom := inferInstanceAs (Flat (pullback.snd U.hom b))
  let : QuasiCompact V.hom := inferInstanceAs (QuasiCompact (pullback.snd U.hom b))
  exact ⟨E.descend hE⟩

end BaseChange

namespace QuasiSplitInnerForm

variable (q : QuasiSplitInnerForm G)

local notation "b" => algebraBaseMap F K
local notation "BC" => GroupScheme.baseChange b

/-- A trivial adjoint discrepancy identifies the scalar extension of an
inner form with that of its quasi-split model. -/
theorem nonempty_iso_baseChange_of_isTrivial (h : (q.cocycle.baseChangePullback b).IsTrivial) :
    Nonempty ((BC).obj q.model ≅ (BC).obj G) :=
  LocalGroupIso.HasDiscrepancy.nonempty_iso_baseChange_of_isTrivial
    (e := q.localIso) (ξ := q.cocycle) (act := q.isAdjointQuotient.innerAction) q.hasDiscrepancy h

/-- If the adjoint discrepancy becomes trivial, the original inner form
becomes quasi-split over the new field. -/
theorem isQuasiSplit_baseChange_of_isTrivial (h : (q.cocycle.baseChangePullback b).IsTrivial) :
    IsQuasiSplit ((BC).obj G) := by
  obtain ⟨e⟩ := q.nonempty_iso_baseChange_of_isTrivial h
  exact q.isQuasiSplit.fieldExtension.of_iso e.symm

end QuasiSplitInnerForm
end Langlands.GroupScheme
