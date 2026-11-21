import Langlands.Global.AdelicBlockCompactSpecialization
import Langlands.Global.AdelicFiniteInfiniteOperatorTensor
import Langlands.Global.Factors.CuspidalInducedFiniteTensor

/-! # Automorphic specialization of a finite cuspidal constituent tensor -/

noncomputable section

universe u uQ

open NumberField
open scoped MonoidAlgebra TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 150000

namespace Langlands.Global.CuspidalInducedFiniteTensor

open Langlands.Automorphic
open Langlands.GeneralLinear (BlockShape)
open AdelicBlockScalarSections AdelicFiniteInfiniteOperatorTensor FiniteAdelicGL
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ}

local instance tensorSpecializationLocalTopology (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

private abbrev inducingShape (hm : ∑ i, (m i + 1) = r + 1) : BlockShape (r + 1) :=
  ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩

private abbrev inducingRealizations (hm : ∑ i, (m i + 1) = r + 1)
    (T : ∀ i, CuspidalOperatorRealization F (m i)) :
    ∀ i : Fin (inducingShape hm).length, OperatorRealization F ((inducingShape hm).size i) :=
  fun i => (T i).realization

variable (hm : ∑ i, (m i + 1) = r + 1) {T : ∀ i, CuspidalOperatorRealization F (m i)}
  (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
  (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
  (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
  {E : Finset (FinitePlace F)}
  (D : TensorSubquotient F (r + 1) (source hm P h) (fun v => (A v).obj.representation) E)

local notation "B" => inducingShape hm
local notation "S" => inducingRealizations hm T
local notation "W" => smoothCompactFiniteSections F B S
local notation "V" => FiniteSmoothRealizedSections F B S
local notation "ρ" => tensorRepresentation F (r + 1) (source hm P h) E D.sourceReference D.source_fixed
set_option quotPrecheck false in
local notation "ξ" => tensorRepresentation F (r + 1) (fun v => (A v).obj.representation) E
  D.targetReference D.target_fixed
local notation "a₀" => blockSectionOperatorAction F r B S 0

local instance tensorSpecializationFiniteAddGroup : AddCommGroup V := Submodule.addCommGroup _
local instance tensorSpecializationSmoothAddGroup : AddCommGroup W := Submodule.addCommGroup _

/-- The original scalar block sections contain the specified finite inducing
tensor with a nonzero infinite operator carrier. -/
def HasSmoothBlockTensorSource : Prop :=
  ∃ (I : Type u) (_ : AddCommGroup I) (_ : Module ℂ I) (_ : Nontrivial I)
    (κ : Representation ℂ (standardInfiniteCompact F (r + 1)) I)
    (δ : ArchimedeanGL.EnvelopingAlgebra F (r + 1) →ₐ[ℂ] Module.End ℂ I)
    (j : Representation.IntertwiningMap (tensorOperatorAction F (r + 1) ρ κ δ).toMonoidHom
      (a₀).toMonoidHom), Function.Injective j

/-- The original inducing tensor and the two analytic inputs give one
irreducible automorphic quotient containing every prescribed finite constituent. -/
theorem exists_localEmbeddings_of_blockTensorSource
    (hcont : EisensteinMeromorphicContinuationStatement.{u})
    (hinj : BlockEisensteinInjectiveOnFiniteRanges F r B S)
    (hsource : HasSmoothBlockTensorSource hm P h A D) :
    ∃ Q : IrreducibleOperatorSubquotient F r, ∀ v : FinitePlace F,
      ∃ f : (A v).obj.representation.IntertwiningMap (Q.subquotient.localRepresentation v),
        Function.Injective f.toLinearMap := by
  let : (ξ).IsIrreducible := target_isIrreducible A D
  obtain ⟨I, _, _, _, κ, δ, j, hj⟩ := hsource
  have hsimple := hasSimpleOperatorQuotientWithFiniteType_of_tensorEmbedding F (r + 1)
    κ δ D.subquotient a₀ j hj
  obtain ⟨Y, _, _, aY, ha, σ, ν, hσ, hν, ⟨e, he⟩, U, q, hq⟩ := hsimple
  obtain ⟨U', p, hp⟩ := exists_freeOperatorQuotient_of_block_subquotient F r B S
    (fun i => (T i).isJointlyAdmissible) hcont hinj aY ha σ ν hσ hν U q hq
  obtain ⟨Q, ⟨j'⟩⟩ := exists_irreducibleOperatorSubquotient_of_freeModule F r aY ha σ hσ U' p hp
  exact ⟨Q, localEmbeddings A D (j'.symm.toIntertwiningMap.comp e) (j'.symm.injective.comp he)⟩

end Langlands.Global.CuspidalInducedFiniteTensor
