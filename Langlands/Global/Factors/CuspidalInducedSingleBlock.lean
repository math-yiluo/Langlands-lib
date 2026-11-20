import Langlands.Automorphic.AssociatedPresentationComparison
import Langlands.Global.Factors.CuspidalInducedConstituentAutomorphyStatement
import Langlands.Group.GL.OneBlockShape
import Langlands.Group.GL.RankReindex
import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Induction.SingleBlock

/-! # Finite-place constituent automorphy for one block -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1500000

universe u uQ

namespace Langlands.Global.CuspidalInducedSingleBlock

open Automorphic
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject IsSubquotientOf)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open CuspidalSupport.LeviAdmissibility (oneBlock)
open FiniteAdelicGL (localInclusion)
open scoped BigOperators

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T : CuspidalOperatorRealization F r}
  (P : CuspidalSpectralPresentation.{u, uQ} T) (h : HasIrreducibleAdmissibleComponents P)

local instance canonicalTopology (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

private abbrev factor (v : FinitePlace F) :=
  (P.localComponent v).padicObject (h v).1 (h v).2

/-- The prescribed cuspidal local component embeds into the corresponding
zero-denominator operator quotient of the original cusp realization. -/
def cuspidalLocalInclusion (v : FinitePlace F) :
    (factor P h v).obj.representation.IntertwiningMap
      (T.toIrreducibleSubquotient.subquotient.localRepresentation v) := by
  let e := T.realization.toSubquotientFiniteEquiv
  let j : (T.realization.localRepresentation v).IntertwiningMap
      (T.toIrreducibleSubquotient.subquotient.localRepresentation v) :=
    ⟨e.toLinearEquiv.toLinearMap, fun g => e.isIntertwining' (localInclusion F (r + 1) v g)⟩
  exact j.comp (T.realization.localSubspaceInclusion v (P.localComponent v)
    (P.localComponent_le_full v))

set_option synthInstance.maxHeartbeats 150000 in
theorem cuspidalLocalInclusion_injective (v : FinitePlace F) :
    Function.Injective (cuspidalLocalInclusion P h v).toLinearMap :=
  T.realization.toSubquotientFiniteEquiv.injective.comp
    (T.realization.localSubspaceInclusion_injective v _ (P.localComponent_le_full v))

/-- For the full-group parabolic, every prescribed local constituent embeds
in the quotient of the same cuspidal realization. -/
theorem singleBlockAutomorphy
    (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
    (hsub : ∀ v, IsSubquotientOf
      ((padicField v).canonicalNormalizedProductInduced (oneBlock (r + 1) (Nat.succ_pos r))
        (fun _ => (factor P h v).obj.representation))
      (A v).obj.representation) :
    ∃ Q : IrreducibleOperatorSubquotient F r, ∀ v : FinitePlace F,
      ∃ f : (A v).obj.representation.IntertwiningMap (Q.subquotient.localRepresentation v),
        Function.Injective f.toLinearMap := by
  refine ⟨T.toIrreducibleSubquotient, fun v => ?_⟩
  let B := oneBlock (r + 1) (Nat.succ_pos r)
  let ρ := (factor P h v).obj.representation
  let induced := (padicField v).canonicalNormalizedProductInduced B (fun _ => ρ)
  have he : induced.Equiv ρ := by
    let hB : B.length = 1 := rfl
    let i : Fin B.length := ⟨0, Nat.zero_lt_one⟩
    let reindex := (GeneralLinear.reindex (R := (padicField v).Carrier)
      (finCongr (B.singleBlock_size hB i))).symm.toMonoidHom
    have hid : reindex = MonoidHom.id (GeneralLinear (r + 1) (padicField v).Carrier) := by
      change (GeneralLinear.reindex (finCongr (rfl : r + 1 = r + 1))).symm.toMonoidHom = _
      rw [GeneralLinear.reindex_finCongr_rfl, MulEquiv.refl_symm]
      rfl
    have hρ : ρ.comp reindex = ρ := hid ▸ MonoidHom.comp_id ρ
    exact Eq.mp (congrArg (fun action => induced.Equiv action) hρ)
      ((padicField v).canonicalTopologicalData.singleBlockNormalizedProductEquiv B hB
        (fun _ => ρ) (fun _ => (factor P h v).property.2.1) i)
  have hsub' := WeylBranchPieces.IsSubquotient.of_equiv_left he.symm (hsub v)
  obtain ⟨q⟩ := CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient
    (factor P h v).property.1 (A v).property.1 hsub'
  exact ⟨(cuspidalLocalInclusion P h v).comp q.symm.toIntertwiningMap,
    (cuspidalLocalInclusion_injective P h v).comp q.symm.injective⟩

/-- Apply the one-block argument directly to the telescope of the target
when the number of blocks is one. -/
theorem singleBlockAutomorphy_of_card_eq_one (k : ℕ) (hk : k = 1) (m : Fin k → ℕ)
    (hm : ∑ i, (m i + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i))
    (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
    (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
    (hsub : ∀ v, IsSubquotientOf
      ((padicField v).canonicalNormalizedProductInduced
        ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
        (fun i => (((P i).localComponent v).padicObject
          (h i v).1 (h i v).2).obj.representation))
      (A v).obj.representation) :
    ∃ Q : IrreducibleOperatorSubquotient F r, ∀ v : FinitePlace F,
      ∃ f : (A v).obj.representation.IntertwiningMap (Q.subquotient.localRepresentation v),
        Function.Injective f.toLinearMap := by
  subst k
  have hsize : m (0 : Fin 1) + 1 = r + 1 := by rwa [Fin.sum_univ_one] at hm
  have heq : m = fun _ => r := by
    funext i
    rw [Fin.eq_zero i]
    exact Nat.succ.inj hsize
  subst m
  refine singleBlockAutomorphy (P 0) (h 0) A fun v => ?_
  let τ (i : Fin 1) := ((P i).localComponent v).padicObject (h i v).1 (h i v).2
  have hv : IsSubquotientOf
      ((padicField v).canonicalNormalizedProductInduced (oneBlock (r + 1) (Nat.succ_pos r))
        (fun i => (τ i).obj.representation))
      (A v).obj.representation := hsub v
  have hτ : τ = fun _ => τ 0 := funext fun i => congrArg τ (Fin.eq_zero i)
  rw [hτ] at hv
  exact hv

end Langlands.Global.CuspidalInducedSingleBlock
