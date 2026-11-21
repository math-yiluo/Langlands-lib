import Langlands.Global.AdelicOperatorTensorMap
import Langlands.Global.Factors.CuspidalIsobaricTensorRealization

/-! # The prescribed isobaric tensor is a subquotient of the ordered induction tensor -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct Matrix.Norms.Operator

universe u

namespace Langlands.Global.CuspidalInducedFiniteTensor

open Langlands.Archimedean Langlands.Automorphic AdelicOperatorTensor
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)
open FiniteAdelicGL

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem subquotient_of_intertwiners {M V W Y : Type*} [Monoid M]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]
    {a : Representation ℂ M V} {b : Representation ℂ M W} {c : Representation ℂ M Y}
    (i : b.IntertwiningMap a) (q : b.IntertwiningMap c)
    (hi : Function.Injective i) (hq : Function.Surjective q) :
    ∃ (S : Subrepresentation a) (p : S.toRepresentation.IntertwiningMap c), Function.Surjective p := by
  let e : b.IntertwiningMap i.range.toRepresentation :=
    { toLinearMap := i.toLinearMap.rangeRestrict
      isIntertwining' m := LinearMap.ext fun y =>
        Subtype.ext (Representation.IntertwiningMap.isIntertwining b a i m y) }
  let E := e.ofBijective
    ⟨fun x y hxy => hi (congrArg Subtype.val hxy), LinearMap.surjective_rangeRestrict _⟩
  exact ⟨i.range, q.comp E.symm.toIntertwiningMap, hq.comp E.symm.surjective⟩

section Subquotients

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ
local notation "RL" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ
local notation "CL" => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ

set_option maxHeartbeats 1700000 in
private theorem tensorSubquotient_of_placeSubquotients
    {Vf Wf : Type u} {Vr Wr : RP → Type} {Vc Wc : CP → Type}
    [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Wf] [Module ℂ Wf]
    [∀ v, AddCommGroup (Vr v)] [∀ v, Module ℂ (Vr v)]
    [∀ v, AddCommGroup (Wr v)] [∀ v, Module ℂ (Wr v)]
    [∀ v, AddCommGroup (Vc v)] [∀ v, Module ℂ (Vc v)]
    [∀ v, AddCommGroup (Wc v)] [∀ v, Module ℂ (Wc v)]
    {fin : Representation ℂ (FiniteAdelicGL F n) Vf}
    {fin' : Representation ℂ (FiniteAdelicGL F n) Wf}
    {κr : ∀ v : RP, Representation ℂ RK (Vr v)}
    {κr' : ∀ v : RP, Representation ℂ RK (Wr v)}
    {δr : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Vr v)}
    {δr' : ∀ v : RP, RL →ₗ⁅ℂ⁆ Module.End ℂ (Wr v)}
    {κc : ∀ v : CP, Representation ℂ CK (Vc v)}
    {κc' : ∀ v : CP, Representation ℂ CK (Wc v)}
    {δc : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Vc v)}
    {δc' : ∀ v : CP, CL →ₗ⁅ℂ⁆ Module.End ℂ (Wc v)}
    (hf : Correspondence.IsSubquotientOf fin fin')
    (hr : ∀ v : RP, ∃ (S : Submodule ℂ (Vr v)) (hS : IsGKSubmodule (κr v) (δr v) S)
      (q : S →ₗ[ℂ] Wr v), IsGKSubquotientMap (κr' v) (δr' v) hS q)
    (hc : ∀ v : CP, ∃ (S : Submodule ℂ (Vc v)) (hS : IsGKSubmodule (κc v) (δc v) S)
      (q : S →ₗ[ℂ] Wc v), IsGKSubquotientMap (κc' v) (δc' v) hS q) :
    ∃ (S : Subrepresentation (tensorFreeAction F n fin κr δr κc δc).toMonoidHom)
      (q : S.toRepresentation.IntertwiningMap (tensorFreeAction F n fin' κr' δr' κc' δc').toMonoidHom),
      Function.Surjective q := by
  obtain ⟨Sf, qf, hqf⟩ := hf
  choose Sr hSr qr hqr using hr
  choose Sc hSc qc hqc using hc
  let Kr (v : RP) := PlaceComponent.restrictCompact (hSr v)
  let Lr (v : RP) := PlaceComponent.restrictLie (hSr v)
  let Kc (v : CP) := PlaceComponent.restrictCompact (hSc v)
  let Lc (v : CP) := PlaceComponent.restrictLie (hSc v)
  have hir (v : RP) : (Sr v).subtype ∈ gkHoms (V := Sr v) (Kr v) (Lr v) (κr v) (δr v) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hic (v : CP) : (Sc v).subtype ∈ gkHoms (V := Sc v) (Kc v) (Lc v) (κc v) (δc v) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hpr (v : RP) : qr v ∈ gkHoms (V := Sr v) (Kr v) (Lr v) (κr' v) (δr' v) := (hqr v).2
  have hpc (v : CP) : qc v ∈ gkHoms (V := Sc v) (Kc v) (Lc v) (κc' v) (δc' v) := (hqc v).2
  let incl := tensorIntertwiningMap F n
    (Vr := fun v => ↥(Sr v)) (Vc := fun v => ↥(Sc v)) (Wr := Vr) (Wc := Vc)
    (κr := Kr) (δr := Lr) (κc := Kc) (δc := Lc)
    (κr' := κr) (δr' := δr) (κc' := κc) (δc' := δc)
    (WeylBranchPieces.subtypeMap Sf) (fun v => (Sr v).subtype) (fun v => (Sc v).subtype) hir hic
  let proj := tensorIntertwiningMap F n
    (Vr := fun v => ↥(Sr v)) (Vc := fun v => ↥(Sc v)) (Wr := Wr) (Wc := Wc)
    (κr := Kr) (δr := Lr) (κc := Kc) (δc := Lc)
    (κr' := κr') (δr' := δr') (κc' := κc') (δc' := δc') qf qr qc hpr hpc
  refine subquotient_of_intertwiners incl proj ?_ ?_
  · exact tensorMap_injective F Subtype.val_injective
      (fun _ => Subtype.val_injective) (fun _ => Subtype.val_injective)
  · exact tensorMap_surjective F hqf (fun v => (hqr v).1) (fun v => (hqc v).1)

end Subquotients

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ} {T : ∀ i, CuspidalOperatorRealization F (m i)}

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance isobaricInductionTopology (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

variable {U : FinitePlace F → Type u} [∀ v, AddCommGroup (U v)] [∀ v, Module ℂ (U v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (U v)}
variable {E : Finset (FinitePlace F)}
variable (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
variable (D : TensorSubquotient F (r + 1) ρ (fun v => (A v).obj.representation) E)

set_option quotPrecheck false in
local notation "RealBlocks(" data ", " v ")" => (List.ofFn (data v).blocks).flatten
set_option quotPrecheck false in
local notation "ComplexBlocks(" data ", " v ")" => (List.ofFn (data v).blocks).flatten

/-- The free action on the finite induction tensor and the standards in the
original cuspidal block order. -/
abbrev sourceTensorAction
    (real : ∀ v : RP, RealIsobaricPlaceData (r := r) T v)
    (complex : ∀ v : CP, ComplexIsobaricPlaceData (r := r) T v) :=
  tensorFreeAction F (r + 1)
    (tensorRepresentation F (r + 1) ρ E D.sourceReference D.source_fixed)
    (fun v => realStandardRep (r + 1) RealBlocks(real, v))
    (fun v => realStandardLie (r + 1) RealBlocks(real, v))
    (fun v => complexStandardRep (r + 1) ComplexBlocks(complex, v))
    (fun v => complexStandardLie (r + 1) ComplexBlocks(complex, v))

/-- The free action on the prescribed finite and archimedean constituents. -/
abbrev targetTensorAction
    (real : ∀ v : RP, RealIsobaricPlaceData (r := r) T v)
    (complex : ∀ v : CP, ComplexIsobaricPlaceData (r := r) T v) :=
  tensorFreeAction F (r + 1)
    (Vr := fun v : RP => realStandardKFinite (r + 1) (real v).orderedBlocks ⧸ (real v).kernel)
    (Vc := fun v : CP => complexStandardKFinite (r + 1) (complex v).orderedBlocks ⧸ (complex v).kernel)
    (tensorRepresentation F (r + 1) (fun v => (A v).obj.representation) E D.targetReference D.target_fixed)
    (fun v => (realStandardRep (r + 1) (real v).orderedBlocks).quotient (real v).kernel (real v).stable.1)
    (fun v => RealLeviDuality.quotLie (realStandardLie (r + 1) (real v).orderedBlocks)
      (real v).kernel (real v).stable.2)
    (fun v => (complexStandardRep (r + 1) (complex v).orderedBlocks).quotient
      (complex v).kernel (complex v).stable.1)
    (fun v => RealLeviDuality.quotLie (complexStandardLie (r + 1) (complex v).orderedBlocks)
      (complex v).kernel (complex v).stable.2)

set_option maxHeartbeats 3300000 in
/-- The tensor of the prescribed constituents is a quotient of an invariant
subspace of the tensor of the normalized local inductions. -/
theorem targetTensorAction_subquotient
    (real : ∀ v : RP, RealIsobaricPlaceData (r := r) T v)
    (complex : ∀ v : CP, ComplexIsobaricPlaceData (r := r) T v) :
    ∃ (S : Subrepresentation (sourceTensorAction A D real complex).toMonoidHom)
      (q : S.toRepresentation.IntertwiningMap (targetTensorAction A D real complex).toMonoidHom),
      Function.Surjective q := by
  refine tensorSubquotient_of_placeSubquotients F (r + 1) ?_ ?_ ?_
  · exact D.subquotient
  · exact fun v => (real v).isSubquotient
  · exact fun v => (complex v).isSubquotient

end Langlands.Global.CuspidalInducedFiniteTensor
