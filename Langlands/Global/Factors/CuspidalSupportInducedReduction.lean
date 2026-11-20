import Langlands.Global.Factors.CuspidalSupportFiniteRestriction
import Langlands.Global.FiniteParametrizedBlockRestriction
import Langlands.Automorphic.CuspidalPresentationLocalMultiplicity
import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Representation.TensorProduct.ExternalMultiplicitySeparation

/-! The finite normalized cuspidal section model supplies the local constituents. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.Representation
open scoped TensorProduct

universe u uV uW uM

namespace Langlands.Global

open Automorphic Correspondence CuspidalPairFunctionalEquation FiniteAdelicGL GeneralLinear

variable {F : Type u} [Field F] [NumberField F]

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup
  padicCategoryLocalSpaceAddCommGroup

namespace FiniteParametrizedBlockInduction

variable {n : ℕ} (B : BlockShape n)
  {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (σ : ∀ i, Representation ℂ (FiniteAdelicGL F (B.size i)) (V i))
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local instance : AddCommGroup (Induction.EquivariantFunctions (parabolic F B) (coefficient F B σ)) :=
  Submodule.addCommGroup _

local instance : AddCommGroup (Sections F B σ) := Submodule.addCommGroup _

/-- The target is a subquotient of the normalized parametrized induction. -/
def HasSubquotient (π : Representation ℂ (FiniteAdelicGL F n) W) : Prop :=
  IsSubquotientOf (induced F B σ) π

private theorem blockTensor_comp_localLeviInclusion (v : FinitePlace F) :
    (B.blockTensor σ).comp (localLeviInclusion F B v) =
      B.blockTensor (fun i => (σ i).comp (localInclusion F (B.size i) v).toMonoidHom) := by
  apply MonoidHom.ext
  intro g
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  exact (B.blockTensor_tprod σ (localLeviInclusion F B v g) x).trans
    (B.blockTensor_tprod (fun i => (σ i).comp (localInclusion F (B.size i) v).toMonoidHom) g x).symm

private theorem hasSeparatingIntertwiners_of_localMultiplicity (v : FinitePlace F)
    {X : Fin B.length → Type uW} {M : Fin B.length → Type uM}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (τ : ∀ i, Representation ℂ (FiniteLocalGL F (B.size i) v) (X i))
    (e : ∀ i, Representation.Equiv ((σ i).comp (localInclusion F (B.size i) v).toMonoidHom)
      ((τ i).tprod (Representation.trivial ℂ (FiniteLocalGL F (B.size i) v) (M i)))) :
    HasSeparatingIntertwiners ((B.blockTensor σ).comp (localLeviInclusion F B v))
      (B.blockTensor τ) := by
  rw [blockTensor_comp_localLeviInclusion]
  exact hasSeparatingIntertwiners_external_of_multiplicity e

end FiniteParametrizedBlockInduction

variable [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ} {T : ∀ i, CuspidalOperatorRealization F (m i)}

set_option maxHeartbeats 650000 in
/-- The actual finite normalized cuspidal realization supplies the finite-place
constituents of the given irreducible operator subquotient. -/
theorem isFiniteInducedConstituent_of_parametrizedInduction
    (hm : ∑ i, (m i + 1) = r + 1) (P : ∀ i, CuspidalSpectralPresentation.{u, u} (T i))
    (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)) (Q : IrreducibleOperatorSubquotient F r)
    (hsub : FiniteParametrizedBlockInduction.HasSubquotient
      ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
      (fun i => (T i).realization.finiteRepresentation) Q.subquotient.finiteRepresentation) :
    IsFiniteInducedConstituent hm P h Q := by
  let B : BlockShape (r + 1) := ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
  let σ := fun i => (T i).realization.finiteRepresentation
  let : AddCommGroup (Induction.EquivariantFunctions (FiniteParametrizedBlockInduction.parabolic F B)
      (FiniteParametrizedBlockInduction.coefficient F B σ)) := Submodule.addCommGroup _
  let C := FiniteParametrizedBlockInduction.Sections F B σ
  let : AddCommGroup C := Submodule.addCommGroup C
  let : Module ℂ C := Submodule.module C
  let ρ := FiniteParametrizedBlockInduction.induced F B σ
  have hρ : IsSmooth ρ := isSmooth_smoothPart _
  refine isFiniteInducedConstituent_of_separatingIntertwiners hm P h Q ρ hρ hsub ?_
  intro v
  let τ := fun i => ((P i).localComponent v).representation
  let M := fun i => (P i).localMultiplicityTail v
  let : ∀ i : Fin k, AddCommGroup (M i) := fun i =>
    inferInstanceAs (AddCommGroup ((P i).localMultiplicityTail v))
  let : ∀ i : Fin k, Module ℂ (M i) := fun i =>
    inferInstanceAs (Module ℂ ((P i).localMultiplicityTail v))
  have hsep := FiniteParametrizedBlockInduction.hasSeparatingIntertwiners_of_localMultiplicity B σ v
    (M := M) τ
    (fun i => (P i).localMultiplicityEquiv (h i) v)
  exact FiniteParametrizedBlockInduction.hasSeparatingIntertwiners_restriction F B v σ τ hsep

/-- Choose presentations in the form-space universe for the supplied actual cuspidal blocks. -/
theorem exists_finiteInducedConstituent_of_parametrizedInduction
    (hm : ∑ i, (m i + 1) = r + 1) (Q : IrreducibleOperatorSubquotient F r)
    (hsub : FiniteParametrizedBlockInduction.HasSubquotient
      ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩
      (fun i => (T i).realization.finiteRepresentation) Q.subquotient.finiteRepresentation) :
    ∃ (P : ∀ i, CuspidalSpectralPresentation.{u, u} (T i))
      (h : ∀ i, HasIrreducibleAdmissibleComponents (P i)), IsFiniteInducedConstituent hm P h Q := by
  classical
  have hP (i : Fin k) :
      ∃ P : CuspidalSpectralPresentation.{u, u} (T i), HasIrreducibleAdmissibleComponents P :=
    (cuspidalIrreducibleAdmissibleFiniteSliceExistence F (m i) (T i)).elim fun A hA =>
      (T i).exists_presentation_of_finiteSlice A hA.1 hA.2
  choose P hP using hP
  exact ⟨P, hP, isFiniteInducedConstituent_of_parametrizedInduction hm P hP Q hsub⟩

end Langlands.Global
