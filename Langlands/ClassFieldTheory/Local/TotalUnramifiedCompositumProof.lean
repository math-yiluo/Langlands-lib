import Langlands.ClassFieldTheory.Local.TotalUnramifiedCompositumStatement
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.Galois.Local.UnramifiedCriterionProof

noncomputable section

namespace Langlands.LocalClassField

open IntermediateField
open Langlands.Weil.Local

universe u v

private theorem ramificationIndex_le_of_extension
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] :
    F.canonicalTopologicalData.ramificationIndex ≤
      E.canonicalTopologicalData.ramificationIndex := by
  let T := F.canonicalTopologicalData
  let S := E.canonicalTopologicalData
  have h := ramificationIndex_mul_ord_relative_algebraMap F E T S T.uniformizer
  rw [T.ord_uniformizer, mul_one] at h
  have he : (0 : ℤ) < S.ramificationIndex := by exact_mod_cast S.ramificationIndex_pos
  have hf : (0 : ℤ) < T.ramificationIndex := by exact_mod_cast T.ramificationIndex_pos
  have ho : 0 < S.ord (algebraMap F.Carrier E.Carrier T.uniformizer) := by
    nlinarith
  have hle : (T.ramificationIndex : ℤ) ≤ S.ramificationIndex := by nlinarith
  exact_mod_cast hle

private theorem relative_ramification_identity
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] :
    E.canonicalTopologicalData.ramificationIndex *
        extensionResidueDegree F E (IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier) =
      Module.finrank F.Carrier E.Carrier * F.canonicalTopologicalData.ramificationIndex := by
  have h := PadicField.ramificationIndex_mul_extensionResidueDegree F E
    (IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier)
  have ha : extensionAlgebra F E (IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier) =
      (inferInstance : Algebra F.Carrier E.Carrier) := toAlgebra_algebraMap
  unfold extensionDegree at h
  rw [ha] at h
  exact h

section Restriction

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
  (E K M : IntermediateField k Ω) (hM : M = E ⊔ K) (hE : E ≤ M) (hK : K ≤ M)

include hM in
private theorem restricted_sup : E.restrict hE ⊔ K.restrict hK = ⊤ := by
  rw [← lift_inj, lift_sup, lift_top, lift_restrict, lift_restrict, hM]

private theorem restricted_disjoint [FiniteDimensional k E]
    (h : E.LinearDisjoint K) : (E.restrict hE).LinearDisjoint (K.restrict hK) := by
  exact h.algEquiv_of_isAlgebraic (E.restrict hE) (K.restrict hK)
    (restrictAlgEquiv hE) (restrictAlgEquiv hK) (Or.inl inferInstance)

include hM in
private theorem compositum_norm [FiniteDimensional k E] [FiniteDimensional k M]
    (h : E.LinearDisjoint K) :
    letI : Algebra E M := (inclusion hE).toAlgebra
    let : Algebra K M := (inclusion hK).toAlgebra
    ∀ z : E, Algebra.norm K (inclusion hE z) = algebraMap k K (Algebra.norm k z) := by
  let : Algebra E M := (inclusion hE).toAlgebra
  let : Algebra K M := (inclusion hK).toAlgebra
  dsimp only
  intro z
  let e := restrictAlgEquiv hE
  let f := restrictAlgEquiv hK
  have hd := (restricted_disjoint E K M hE hK h).symm
  have hn := hd.norm_algebraMap (by rw [sup_comm]; exact restricted_sup E K M hM hE hK) (e z)
  have hc : (algebraMap (K.restrict hK) M).comp f.toRingEquiv.toRingHom =
      algebraMap K M := by ext x; rfl
  apply f.injective
  change f.toRingEquiv (Algebra.norm K (inclusion hE z)) = _
  rw [Algebra.norm_eq_of_ringEquiv f.toRingEquiv hc]
  change Algebra.norm (K.restrict hK) (algebraMap (E.restrict hE) M (e z)) = _
  rw [hn, Algebra.norm_eq_of_algEquiv e]
  exact (f.commutes _).symm

include hM in
private theorem compositum_trace [FiniteDimensional k E] [FiniteDimensional k M]
    (h : E.LinearDisjoint K) :
    letI : Algebra E M := (inclusion hE).toAlgebra
    let : Algebra K M := (inclusion hK).toAlgebra
    ∀ z : E, Algebra.trace K M (inclusion hE z) = algebraMap k K (Algebra.trace k E z) := by
  let : Algebra E M := (inclusion hE).toAlgebra
  let : Algebra K M := (inclusion hK).toAlgebra
  dsimp only
  intro z
  let e := restrictAlgEquiv hE
  let f := restrictAlgEquiv hK
  have hd := (restricted_disjoint E K M hE hK h).symm
  have hn := hd.trace_algebraMap (by rw [sup_comm]; exact restricted_sup E K M hM hE hK) (e z)
  have hc : (algebraMap (K.restrict hK) M).comp f.toRingEquiv.toRingHom =
      algebraMap K M := by ext x; rfl
  apply f.injective
  change f.toRingEquiv (Algebra.trace K M (inclusion hE z)) = _
  rw [Algebra.trace_eq_of_ringEquiv f.toRingEquiv hc]
  change Algebra.trace (K.restrict hK) M (algebraMap (E.restrict hE) M (e z)) = _
  rw [hn, Algebra.trace_eq_of_algEquiv e]
  exact (f.commutes _).symm

include hM hE in
private theorem compositum_galois [FiniteDimensional k M] [IsGalois k E] :
    letI : Algebra K M := (inclusion hK).toAlgebra
    IsGalois K M := by
  let : Algebra K M := (inclusion hK).toAlgebra
  let f := restrictAlgEquiv hK
  let : IsGalois k (E.restrict hE) := IsGalois.of_algEquiv (restrictAlgEquiv hE)
  let : IsGalois (K.restrict hK) M :=
    IsGalois.sup_right (E.restrict hE) (K.restrict hK) (restricted_sup E K M hM hE hK)
  exact IsGalois.of_equiv_equiv (F := K.restrict hK) (E := M)
    (f := f.symm.toRingEquiv) (g := RingEquiv.refl M) (by
      apply RingHom.ext
      intro x
      change inclusion hK (f.symm x) = (x : M)
      exact congrArg Subtype.val (f.apply_symm_apply x))

end Restriction

/-- Trace commutes with the actual inclusions into any finite compositum of
linearly disjoint intermediate extensions. -/
theorem totalUnramifiedCompositum_trace
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (E K' M : FiniteIntermediateExtension F.Carrier)
    (hM : M.field = E.field ⊔ K'.field)
    (hE : E.field ≤ M.field) (hK : K'.field ≤ M.field)
    (h : E.field.LinearDisjoint K'.field) :
    letI := (E.asPadicField (p := p)).algebra
    letI := (K'.asPadicField (p := p)).algebra
    letI := (M.asPadicField (p := p)).algebra
    letI : Algebra E.field M.field := (inclusion hE).toAlgebra
    letI : Algebra K'.field M.field := (inclusion hK).toAlgebra
    letI : IsScalarTower F.Carrier E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower F.Carrier K'.field M.field := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (Padic p) E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (Padic p) K'.field M.field := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional K'.field M.field :=
      FiniteDimensional.right F.Carrier K'.field M.field
    ∀ z : E.field, Algebra.trace K'.field M.field (inclusion hE z) =
      algebraMap F.Carrier K'.field (Algebra.trace F.Carrier E.field z) := by
  exact compositum_trace E.field K'.field M.field hM hE hK h

section Arithmetic

variable {p : ℕ} [Fact p.Prime] (F E K M : PadicField.{u} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier]
  [Algebra E.Carrier M.Carrier] [IsScalarTower (Padic p) E.Carrier M.Carrier]
  [FiniteDimensional E.Carrier M.Carrier]
  [Algebra K.Carrier M.Carrier] [IsScalarTower (Padic p) K.Carrier M.Carrier]
  [FiniteDimensional K.Carrier M.Carrier]

omit [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier] in
private theorem arithmetic
    (hEram : E.canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier E.Carrier * F.canonicalTopologicalData.ramificationIndex)
    (hKram : K.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex)
    (hb : Module.finrank K.Carrier M.Carrier ≤ Module.finrank F.Carrier E.Carrier) :
    Module.finrank K.Carrier M.Carrier = Module.finrank F.Carrier E.Carrier ∧
    M.canonicalTopologicalData.ramificationIndex = E.canonicalTopologicalData.ramificationIndex ∧
    Function.Bijective (PadicField.TopologicalData.relativeResidueMap
      K.canonicalTopologicalData M.canonicalTopologicalData) ∧
    ∀ z : E.Carrier, M.canonicalTopologicalData.ord (algebraMap E.Carrier M.Carrier z) =
      E.canonicalTopologicalData.ord z := by
  let TE := E.canonicalTopologicalData
  let TK := K.canonicalTopologicalData
  let TM := M.canonicalTopologicalData
  let f := IsScalarTower.toAlgHom (Padic p) K.Carrier M.Carrier
  have hlo : TE.ramificationIndex ≤ TM.ramificationIndex :=
    ramificationIndex_le_of_extension E M
  have hef := relative_ramification_identity K M
  have hfp := extensionResidueDegree_pos K M f
  change TM.ramificationIndex * extensionResidueDegree _ _ f =
    Module.finrank K.Carrier M.Carrier * TK.ramificationIndex at hef
  have hup : TM.ramificationIndex ≤
      Module.finrank K.Carrier M.Carrier * TK.ramificationIndex := by nlinarith
  change TE.ramificationIndex = _ at hEram
  change TK.ramificationIndex = _ at hKram
  have hbase := F.canonicalTopologicalData.ramificationIndex_pos
  have hn : Module.finrank K.Carrier M.Carrier = Module.finrank F.Carrier E.Carrier := by
    rw [hKram] at hup
    rw [hEram] at hlo
    nlinarith
  have he : TM.ramificationIndex = TE.ramificationIndex := by
    rw [hn, hKram, ← hEram] at hup
    exact le_antisymm hup hlo
  have hres : extensionResidueDegree K M f = 1 := by
    have hpos := TM.ramificationIndex_pos
    rw [hn, hKram, ← hEram, ← he] at hef
    nlinarith
  refine ⟨hn, he, ?_, ?_⟩
  · let := TM.finite_residueField
    apply (Nat.bijective_iff_injective_and_card _).mpr
    refine ⟨(PadicField.TopologicalData.relativeResidueMap TK TM).injective, ?_⟩
    have hc := extensionResidueCardinality K M f
    rw [hres, pow_one] at hc
    exact hc.symm
  · intro z
    have h := ramificationIndex_mul_ord_relative_algebraMap E M TE TM z
    rw [he] at h
    exact mul_left_cancel₀ (by exact_mod_cast TE.ramificationIndex_pos.ne') h

end Arithmetic

set_option maxHeartbeats 400000 in
private theorem compositum_result
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (E K' M : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier E.field]
    (hM : M.field = E.field ⊔ K'.field)
    (hE : E.field ≤ M.field) (hK : K'.field ≤ M.field)
    (hEram : (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier E.field * F.canonicalTopologicalData.ramificationIndex)
    (hKram : (K'.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex) :
    letI := (E.asPadicField (p := p)).algebra
    letI := (K'.asPadicField (p := p)).algebra
    letI := (M.asPadicField (p := p)).algebra
    letI : Algebra E.field M.field := (inclusion hE).toAlgebra
    letI : Algebra K'.field M.field := (inclusion hK).toAlgebra
    letI : IsScalarTower F.Carrier E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower F.Carrier K'.field M.field := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (Padic p) E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (Padic p) K'.field M.field := IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional K'.field M.field :=
      FiniteDimensional.right F.Carrier K'.field M.field
    E.field.LinearDisjoint K'.field ∧
    Module.finrank K'.field M.field = Module.finrank F.Carrier E.field ∧
    (M.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ∧
    IsGalois K'.field M.field ∧
    Function.Bijective (PadicField.TopologicalData.relativeResidueMap
      (K'.asPadicField (p := p)).canonicalTopologicalData
      (M.asPadicField (p := p)).canonicalTopologicalData) ∧
    (∀ z : E.field, (M.asPadicField (p := p)).canonicalTopologicalData.ord (inclusion hE z) =
      (E.asPadicField (p := p)).canonicalTopologicalData.ord z) ∧
    ∀ z : E.field, Algebra.norm K'.field (inclusion hE z) =
      algebraMap F.Carrier K'.field (Algebra.norm F.Carrier z) := by
  let := (E.asPadicField (p := p)).algebra
  let := (K'.asPadicField (p := p)).algebra
  let := (M.asPadicField (p := p)).algebra
  let : Algebra E.field M.field := (inclusion hE).toAlgebra
  let : Algebra K'.field M.field := (inclusion hK).toAlgebra
  let : IsScalarTower F.Carrier E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F.Carrier K'.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) E.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (Padic p) K'.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional E.field M.field :=
    FiniteDimensional.right F.Carrier E.field M.field
  let : FiniteDimensional K'.field M.field :=
    FiniteDimensional.right F.Carrier K'.field M.field
  let : Module.Free K'.field M.field := Module.Free.of_divisionRing K'.field M.field
  have hb : Module.finrank K'.field M.field ≤ Module.finrank F.Carrier E.field := by
    have hs := IntermediateField.finrank_sup_le E.field K'.field
    have ht := Module.finrank_mul_finrank F.Carrier K'.field M.field
    have hp := Module.finrank_pos (R := F.Carrier) (M := K'.field)
    rw [← hM] at hs
    nlinarith
  obtain ⟨hn, he, hr, ho⟩ := arithmetic F (E.asPadicField (p := p))
    (K'.asPadicField (p := p)) (M.asPadicField (p := p)) hEram hKram hb
  have hd : E.field.LinearDisjoint K'.field := by
    apply IntermediateField.LinearDisjoint.of_finrank_sup
    rw [← hM, ← Module.finrank_mul_finrank F.Carrier K'.field M.field, hn, mul_comm]
  exact ⟨hd, hn, he, compositum_galois E.field K'.field M.field hM hE hK, hr, ho,
    compositum_norm E.field K'.field M.field hM hE hK hd⟩

/-- Finite totally ramified Galois extensions retain their arithmetic under
finite unramified base change. -/
theorem totalUnramifiedCompositum : TotalUnramifiedCompositum.{u} := by
  intro p _ F E K' _ hEram hKram
  let M : FiniteIntermediateExtension F.Carrier := ⟨E.field ⊔ K'.field, inferInstance⟩
  have hE : E.field ≤ M.field := le_sup_left
  have hK : K'.field ≤ M.field := le_sup_right
  have h := compositum_result F E K' M rfl hE hK hEram hKram
  exact ⟨h.1, M, rfl, hE, hK, h.2⟩

end Langlands.LocalClassField
