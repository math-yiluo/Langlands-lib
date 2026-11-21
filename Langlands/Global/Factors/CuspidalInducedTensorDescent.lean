import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Global.AdelicOperatorTensorDescent
import Langlands.Global.Factors.CuspidalInducedFiniteTensor
import Langlands.Global.FiniteAdelicGL.TensorDensity
import Langlands.Representation.Archimedean.StandardQuotientDensity

/-! # Descent for the prescribed cuspidally induced finite and infinite constituents -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct Matrix.Norms.Operator

universe u

namespace Langlands.Global.CuspidalInducedFiniteTensor

open NumberField Langlands.Archimedean Langlands.Automorphic
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)
open LocalFactor.Archimedean (RealBlock ComplexCharacterData)
open FiniteAdelicGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

local instance prescribedRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance prescribedContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance prescribedSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance prescribedFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance prescribedStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F (r + 1)) := Submodule.addCommGroup _

section Descent

local notation "Rank" => (r + 1)
local notation "RK" => Matrix.unitaryGroup (Fin Rank) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin Rank) ℂ
local notation "RL" => ℂ ⊗[ℝ] Matrix (Fin Rank) (Fin Rank) ℝ
local notation "CL" => ℂ ⊗[ℝ] Matrix (Fin Rank) (Fin Rank) ℂ

private def IsAutomorphicTensorQuotient {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    (fin : Representation ℂ (FiniteAdelicGL F Rank) Vf)
    (κr : ∀ v : RP, Representation ℂ RK (Vr v))
    (δr : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Vr v))
    (κc : ∀ v : CP, Representation ℂ CK (Vc v))
    (δc : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)) : Prop :=
  ∃ a : Representation ℂ (FreeOperatorAlgebra F Rank) (AdelicOperatorTensor.Space F Vf Vr Vc),
    AdelicOperatorTensor.HasActions F Rank fin κr δr κc δc a ∧
    ∃ S : Subrepresentation
        ((stableAutomorphicAction F Rank).comp (freeOperatorProjection F Rank).toMonoidHom),
      ∃ q : S.toRepresentation.IntertwiningMap a, Function.Surjective q

set_option maxHeartbeats 2000000 in
private theorem exists_placeEmbeddings_of_density {Vf : Type u} {Vr : RP → Type} {Vc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    {fin : Representation ℂ (FiniteAdelicGL F Rank) Vf}
    {κr : ∀ v : RP, Representation ℂ RK (Vr v)}
    {δr : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Vr v)}
    {κc : ∀ v : CP, Representation ℂ CK (Vc v)}
    {δc : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)}
    (hne : Nontrivial Vf)
    (hfin : ∀ (s : Finset Vf) (T : Module.End ℂ Vf),
      ∃ A ∈ Algebra.adjoin ℂ (Set.range fin), ∀ x ∈ s, A x = T x)
    (hr : ∀ v : RP, GKModuleDensity.Hyp (κr v) (δr v))
    (hc : ∀ v : CP, GKModuleDensity.Hyp (κc v) (δc v))
    (hgeom : IsAutomorphicTensorQuotient (r := r) fin κr δr κc δc) :
    ∃ Q : IrreducibleOperatorSubquotient F r,
      AdelicOperatorTensor.HasPlaceEmbeddings Q fin κr δr κc δc := by
  obtain ⟨a, ha, S, q, hq⟩ := hgeom
  have hirr := AdelicOperatorTensor.isIrreducible_of_density ha hne hfin hr hc
  exact AdelicOperatorTensor.exists_with_placeEmbeddings (F := F) (r := r) ha hne
    (fun v => (hr v).irreducible.1) (fun v => (hc v).irreducible.1) hirr S q hq

end Descent

local instance prescribedTensorTopology (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

variable {U : FinitePlace F → Type u} [∀ v, AddCommGroup (U v)] [∀ v, Module ℂ (U v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (U v)}
variable {E : Finset (FinitePlace F)}
variable (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
variable (D : TensorSubquotient F (r + 1) ρ (fun v => (A v).obj.representation) E)

set_option quotPrecheck false in
local notation "FinTarget" => tensorRepresentation F (r + 1)
  (fun v => (A v).obj.representation) E D.targetReference D.target_fixed

private theorem target_density
    (s : Finset (Langlands.RestrictedTensor.Space ℂ (fun v => (A v).obj) E D.targetReference))
    (T : Module.End ℂ (Langlands.RestrictedTensor.Space ℂ (fun v => (A v).obj) E D.targetReference)) :
    ∃ B ∈ Algebra.adjoin ℂ (Set.range FinTarget), ∀ x ∈ s, B x = T x := by
  refine tensorRepresentation_exists_eq_on F (r + 1) _ E _ _ D.target_nonzero
    (fun v => (A v).property.1) ?_ s T
  intro v
  refine Eq.mpr (congrArg (fun t =>
    @IsAdmissible ℂ (FiniteLocalGL F (r + 1) v) _ _ _ _ _ t (A v).obj.representation)
    (localGL_topology_eq F v (r + 1))) ?_
  exact (A v).property.2

private theorem target_nontrivial :
    Nontrivial (Langlands.RestrictedTensor.Space ℂ (fun v => (A v).obj) E D.targetReference) := by
  let fin := FinTarget
  let : fin.IsIrreducible := target_isIrreducible A D
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (FiniteAdelicGL F (r + 1))) fin.asModule

set_option quotPrecheck false in
local notation "RealCompact[" es "," R "," h "]" =>
  (fun v : RP => (realStandardRep (r + 1) (es v)).quotient (R v) (h v).1)
set_option quotPrecheck false in
local notation "RealLie[" es "," R "," h "]" =>
  (fun v : RP => RealLeviDuality.quotLie (realStandardLie (r + 1) (es v)) (R v) (h v).2)
set_option quotPrecheck false in
local notation "ComplexCompact[" es "," R "," h "]" =>
  (fun v : CP => (complexStandardRep (r + 1) (es v)).quotient (R v) (h v).1)
set_option quotPrecheck false in
local notation "ComplexLie[" es "," R "," h "]" =>
  (fun v : CP => RealLeviDuality.quotLie (complexStandardLie (r + 1) (es v)) (R v) (h v).2)

set_option maxHeartbeats 1000000 in
/-- The specified finite tensor and standard quotients have a simultaneous
operator tensor realization by a quotient of a stable automorphic subspace. -/
def HasTensorRealization
    (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
    (D : TensorSubquotient F (r + 1) ρ (fun v => (A v).obj.representation) E)
    (esr : RP → List RealBlock) (esc : CP → List ComplexCharacterData)
    (Rr : ∀ v : RP, Submodule ℂ (realStandardKFinite (r + 1) (esr v)))
    (Rc : ∀ v : CP, Submodule ℂ (complexStandardKFinite (r + 1) (esc v)))
    (hr : ∀ v : RP, IsGKSubmodule (realStandardRep (r + 1) (esr v))
      (realStandardLie (r + 1) (esr v)) (Rr v))
    (hc : ∀ v : CP, IsGKSubmodule (complexStandardRep (r + 1) (esc v))
      (complexStandardLie (r + 1) (esc v)) (Rc v)) : Prop :=
  let fin := tensorRepresentation F (r + 1) (fun v => (A v).obj.representation)
    E D.targetReference D.target_fixed
  IsAutomorphicTensorQuotient (r := r)
    (Vr := fun v : RP => realStandardKFinite (r + 1) (esr v) ⧸ Rr v)
    (Vc := fun v : CP => complexStandardKFinite (r + 1) (esc v) ⧸ Rc v)
    fin RealCompact[esr, Rr, hr] RealLie[esr, Rr, hr] ComplexCompact[esc, Rc, hc] ComplexLie[esc, Rc, hc]

set_option maxHeartbeats 3600000 in
/-- The actual irreducible standard quotients and the assembled finite tensor
embed simultaneously into one automorphic quotient when their tensor is realized. -/
theorem exists_placeEmbeddings_of_tensorRealization
    (esr : RP → List RealBlock) (esc : CP → List ComplexCharacterData)
    (Rr : ∀ v : RP, Submodule ℂ (realStandardKFinite (r + 1) (esr v)))
    (Rc : ∀ v : CP, Submodule ℂ (complexStandardKFinite (r + 1) (esc v)))
    (hr : ∀ v : RP, IsGKSubmodule (realStandardRep (r + 1) (esr v))
      (realStandardLie (r + 1) (esr v)) (Rr v))
    (hc : ∀ v : CP, IsGKSubmodule (complexStandardRep (r + 1) (esc v))
      (complexStandardLie (r + 1) (esc v)) (Rc v))
    (hR : ∀ v : RP, IsIrreducibleGKModule (RealCompact[esr, Rr, hr] v) (RealLie[esr, Rr, hr] v))
    (hC : ∀ v : CP, IsIrreducibleGKModule (ComplexCompact[esc, Rc, hc] v) (ComplexLie[esc, Rc, hc] v))
    (hgeom : HasTensorRealization A D esr esc Rr Rc hr hc) :
    ∃ Q : IrreducibleOperatorSubquotient F r,
      AdelicOperatorTensor.HasPlaceEmbeddings
        (Vr := fun v : RP => realStandardKFinite (r + 1) (esr v) ⧸ Rr v)
        (Vc := fun v : CP => complexStandardKFinite (r + 1) (esc v) ⧸ Rc v)
        Q FinTarget
        RealCompact[esr, Rr, hr] RealLie[esr, Rr, hr]
        ComplexCompact[esc, Rc, hc] ComplexLie[esc, Rc, hc] := by
  refine exists_placeEmbeddings_of_density (F := F) (r := r) ?_ ?_ ?_ ?_ ?_
  · exact target_nontrivial A D
  · exact target_density A D
  · intro v
    exact realStandardQuotient_density (r + 1) (esr v) (hr v) (hR v)
  · intro v
    exact complexStandardQuotient_density (r + 1) (esc v) (hc v) (hC v)
  · exact hgeom

end Langlands.Global.CuspidalInducedFiniteTensor
