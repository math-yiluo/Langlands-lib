import Langlands.Global.Factors.CuspidalInducedConstituentAutomorphyStatement
import Langlands.Global.FiniteAdelicGL.IrreducibleTensor
import Langlands.Global.FiniteAdelicGL.PadicComparison
import Langlands.Global.FiniteAdelicGL.TensorSubquotient

/-! # The finite tensor of the prescribed cuspidally induced constituents -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1500000

universe u uQ

namespace Langlands.Global.CuspidalInducedFiniteTensor

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation
  IrreducibleOperatorSubquotient)
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject IsSubquotientOf sphericalSubgroup)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open FiniteAdelicGL
open scoped BigOperators

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ}

local instance canonicalTopology (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

variable (hm : ∑ i, (m i + 1) = r + 1)
variable {T : ∀ i, CuspidalOperatorRealization F (m i)}
variable (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
variable (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
variable (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)

private abbrev blockShape : GeneralLinear.BlockShape (r + 1) :=
  ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩

private abbrev localFactors (v : FinitePlace F) (i : Fin k) :=
  (((P i).localComponent v).padicObject (h i v).1 (h i v).2).obj.representation

/-- The canonical normalized local inductions in the target proposition. -/
abbrev source (v : FinitePlace F) :=
  (padicField v).canonicalNormalizedProductInduced (blockShape hm) (localFactors P h v)

/-- The finite tensor diagram for the given local constituents. -/
def assemble (S : Finset (FinitePlace F))
    (hsub : ∀ v, IsSubquotientOf (source hm P h v) (A v).obj.representation)
    (hfixed : ∀ v ∉ S,
      fixedVectors (A v).obj.representation (sphericalSubgroup (padicField v) r) ≠ ⊥) :
    TensorSubquotient F (r + 1) (source hm P h) (fun v => (A v).obj.representation) S := by
  refine TensorSubquotient.ofLocalSubquotients F (r + 1) (source hm P h)
    (fun v => (A v).obj.representation) S ?_ ?_ hsub ?_
  · intro v
    refine Eq.mpr (congrArg (fun t =>
      @IsSmooth ℂ (FiniteLocalGL F (r + 1) v) _ _ _ _ _ t (source hm P h v))
      (localGL_topology_eq F v (r + 1))) ?_
    exact (padicField v).canonicalTopologicalData.isSmooth_normalizedProductInduced
      (blockShape hm) (localFactors P h v)
  · intro v
    refine Eq.mpr (congrArg (fun t =>
      @IsSmooth ℂ (FiniteLocalGL F (r + 1) v) _ _ _ _ _ t (A v).obj.representation)
      (localGL_topology_eq F v (r + 1))) ?_
    exact (A v).property.2.1
  · intro v hv
    rw [localIntegral_eq_sphericalSubgroup F v r]
    exact hfixed v hv

variable {U : FinitePlace F → Type u} [∀ v, AddCommGroup (U v)] [∀ v, Module ℂ (U v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (U v)}
variable {S : Finset (FinitePlace F)}
variable (D : TensorSubquotient F (r + 1) ρ (fun v => (A v).obj.representation) S)

omit [CompactSpace (AdeleQuotient F)] in
/-- The finite tensor of the prescribed constituents is irreducible. -/
theorem target_isIrreducible :
    (tensorRepresentation F (r + 1) (fun v => (A v).obj.representation) S
      D.targetReference D.target_fixed).IsIrreducible := by
  refine tensorRepresentation_isIrreducible F (r + 1) _ S _ _ D.target_nonzero
    (fun v => (A v).property.1) ?_
  intro v
  refine Eq.mpr (congrArg (fun t =>
    @IsAdmissible ℂ (FiniteLocalGL F (r + 1) v) _ _ _ _ _ t (A v).obj.representation)
    (localGL_topology_eq F v (r + 1))) ?_
  exact (A v).property.2

omit [CompactSpace (AdeleQuotient F)] in
/-- An embedding of the assembled tensor into one quotient gives every required
local embedding into that same quotient. -/
theorem localEmbeddings {Q : IrreducibleOperatorSubquotient F r}
    (f : (tensorRepresentation F (r + 1) (fun v => (A v).obj.representation) S
      D.targetReference D.target_fixed).IntertwiningMap Q.subquotient.finiteRepresentation)
    (hf : Function.Injective f.toLinearMap) :
    ∀ v : FinitePlace F,
      ∃ j : (A v).obj.representation.IntertwiningMap (Q.subquotient.localRepresentation v),
        Function.Injective j.toLinearMap := by
  let : ∀ v, (A v).obj.representation.IsIrreducible := fun v => (A v).property.1
  let : ∀ v, Nontrivial (A v).obj := fun v =>
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (r.succPNat : ℕ) (padicField v).Carrier))
      (A v).obj.representation.asModule
  intro v
  obtain ⟨j, hj⟩ := exists_injective_localTensorEmbedding F (r + 1)
    (fun w => (A w).obj.representation) S D.targetReference D.target_fixed D.target_nonzero v
  let f₀ : (tensorLocalRepresentation F (r + 1) (fun w => (A w).obj.representation) S
      D.targetReference D.target_fixed v).IntertwiningMap
        (Q.subquotient.localRepresentation v) :=
    ⟨f.toLinearMap, fun g => f.isIntertwining' (localInclusion F (r + 1) v g)⟩
  exact ⟨f₀.comp j, hf.comp hj⟩

end Langlands.Global.CuspidalInducedFiniteTensor
