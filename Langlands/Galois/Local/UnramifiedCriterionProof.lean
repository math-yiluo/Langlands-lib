import Langlands.Galois.Local.UnramifiedCriterionStatement
import Langlands.Weil.Local.IntermediateWeil
import Langlands.LocalField.Normalization.Proof
import Langlands.Galois.Local.AbsoluteProof

/-!
# Proof of the canonical unramified criterion

For an embedding `f : F → E` of finite extensions of `Q_p`, the image `S` of `G_E` in `G_F`
has index `[E : F]`, while `S ⊔ I_F` has index equal to the relative residue degree.
Comparing indices with the identity `e_E * f(E/F) = [E : F] * e_F` gives the criterion.
-/

noncomputable section

namespace Langlands.PadicField

open Langlands.Weil.Local LocalClassField

universe u v

section Embedding

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- The image of the residue field of `E` in the algebraic closure of that of `F`. -/
def extensionResidueIntermediateField :
    IntermediateField (localResidueField F) (AlgebraicClosure (localResidueField F)) :=
  letI := extensionResidueAlgebra F E f
  (extensionResidueFieldAlgHom F E f).fieldRange

theorem mem_extensionResidueIntermediateField (y : AlgebraicClosure (localResidueField F)) :
    y ∈ extensionResidueIntermediateField F E f ↔
      ∃ x : localResidueField E, extensionResidueFieldAlgHom F E f x = y := by
  let := extensionResidueAlgebra F E f
  exact AlgHom.mem_fieldRange

/-- The image of `G_{k_E}` is the fixing subgroup of the image of `k_E`. -/
theorem extensionResidueGaloisMap_range :
    (extensionResidueGaloisMap F E f).toMonoidHom.range =
      (extensionResidueIntermediateField F E f).fixingSubgroup := by
  ext τ
  rw [MonoidHom.mem_range]
  refine Iff.trans ?_ (IntermediateField.mem_fixingSubgroup_iff
    (K := extensionResidueIntermediateField F E f) τ).symm
  constructor
  · rintro ⟨σ, rfl⟩ y hy
    obtain ⟨x, rfl⟩ := (mem_extensionResidueIntermediateField F E f y).mp hy
    exact extensionResidueGaloisMap_fixes F E f σ x
  · intro h
    let e := extensionResidueClosureEquiv F E f
    let ρ : AlgebraicClosure (localResidueField E) ≃+* AlgebraicClosure (localResidueField E) :=
      (e.symm.trans (AlgEquiv.toRingEquiv τ)).trans e
    have hρ : ∀ x : localResidueField E,
        ρ (algebraMap (localResidueField E) _ x) = algebraMap (localResidueField E) _ x := by
      intro x
      have hfix : AlgEquiv.toAlgHom τ (extensionResidueFieldAlgHom F E f x) =
          extensionResidueFieldAlgHom F E f x :=
        h _ ((mem_extensionResidueIntermediateField F E f _).mpr ⟨x, rfl⟩)
      calc ρ (algebraMap (localResidueField E) _ x)
          = e (AlgEquiv.toAlgHom τ (extensionResidueFieldAlgHom F E f x)) := rfl
        _ = e (extensionResidueFieldAlgHom F E f x) := by rw [hfix]
        _ = algebraMap (localResidueField E) _ x := e.apply_symm_apply _
    refine ⟨AlgEquiv.ofRingEquiv (f := ρ) hρ, ?_⟩
    apply AlgEquiv.ext
    intro y
    apply e.injective
    refine (extensionResidueClosureEquiv_galoisMap F E f _ y).trans ?_
    change e (AlgEquiv.toAlgHom τ (e.symm (e y))) = e (AlgEquiv.toAlgHom τ y)
    rw [RingEquiv.symm_apply_apply]

/-- The image of `G_{k_E}` has index equal to the relative residue degree. -/
theorem extensionResidueGaloisMap_range_index :
    (extensionResidueGaloisMap F E f).toMonoidHom.range.index =
      extensionResidueDegree F E f := by
  let := extensionResidueAlgebra F E f
  have : IsGalois (localResidueField F) (AlgebraicClosure (localResidueField F)) := {}
  have h : Module.finrank (localResidueField F) (extensionResidueIntermediateField F E f) =
      extensionResidueDegree F E f :=
    (AlgHom.equivFieldRange (extensionResidueFieldAlgHom F E f)).toLinearEquiv.finrank_eq.symm
  rw [extensionResidueGaloisMap_range, ← h]
  exact ((extensionResidueIntermediateField F E f).finrank_eq_fixingSubgroup_index).symm

/-- The residue action carries the image of `G_E` onto the image of `G_{k_E}`. -/
theorem map_localResidueMap_extensionGaloisMap_range :
    (extensionGaloisMap F E f).toMonoidHom.range.map (localResidueMap F).toMonoidHom =
      (extensionResidueGaloisMap F E f).toMonoidHom.range := by
  ext τ
  constructor
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    exact ⟨localResidueMap E σ, (localResidueMap_extensionGaloisMap F E f σ).symm⟩
  · rintro ⟨κ, rfl⟩
    obtain ⟨σ, rfl⟩ := E.absoluteResidueHom_surjective E.canonicalTopologicalData κ
    exact ⟨_, ⟨σ, rfl⟩, localResidueMap_extensionGaloisMap F E f σ⟩

/-- Adjoining absolute inertia to the image of `G_E` gives index `f(E/F)`. -/
theorem extensionGaloisMap_range_sup_absoluteInertia_index :
    ((extensionGaloisMap F E f).toMonoidHom.range ⊔
        F.absoluteInertia F.canonicalTopologicalData).index =
      extensionResidueDegree F E f := by
  have hker : (localResidueMap F).toMonoidHom.ker =
      F.absoluteInertia F.canonicalTopologicalData :=
    F.absoluteResidueHom_ker F.canonicalTopologicalData
  have hsurj : Function.Surjective (localResidueMap F).toMonoidHom :=
    F.absoluteResidueHom_surjective F.canonicalTopologicalData
  rw [← hker, ← Subgroup.comap_map_eq, Subgroup.index_comap_of_surjective _ hsurj,
    map_localResidueMap_extensionGaloisMap_range, extensionResidueGaloisMap_range_index]

/-- Absolute inertia lies in the image of `G_E` exactly when `f(E/F) = [E : F]`. -/
theorem absoluteInertia_le_extensionGaloisMap_range_iff :
    F.absoluteInertia F.canonicalTopologicalData ≤ (extensionGaloisMap F E f).toMonoidHom.range ↔
      extensionResidueDegree F E f = extensionDegree F E f := by
  set S := (extensionGaloisMap F E f).toMonoidHom.range
  set I := F.absoluteInertia F.canonicalTopologicalData
  have hmul := Subgroup.relIndex_mul_index (le_sup_left : S ≤ S ⊔ I)
  rw [extensionGaloisMap_range_sup_absoluteInertia_index, extensionGaloisMap_range_index] at hmul
  constructor
  · intro h
    rw [sup_eq_left.mpr h, Subgroup.relIndex_self, one_mul] at hmul
    exact hmul
  · intro h
    rw [h] at hmul
    have h1 : S.relIndex (S ⊔ I) = 1 :=
      Nat.eq_of_mul_eq_mul_right (extensionDegree_pos F E f) (hmul.trans (one_mul _).symm)
    exact le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1)

/-- The fundamental identity `e_E * f(E/F) = [E : F] * e_F` for the canonical data. -/
theorem ramificationIndex_mul_extensionResidueDegree :
    E.canonicalTopologicalData.ramificationIndex * extensionResidueDegree F E f =
      extensionDegree F E f * F.canonicalTopologicalData.ramificationIndex := by
  have hF := F.canonicalTopologicalData.ramificationIndex_mul_residueDegree
  have hE := E.canonicalTopologicalData.ramificationIndex_mul_residueDegree
  have hdeg := finrank_mul_extensionDegree F E f
  have hcard := extensionResidueCardinality F E f
  rw [TopologicalData.residueCardinality_eq_pow, TopologicalData.residueCardinality_eq_pow,
    ← pow_mul] at hcard
  have hres : E.canonicalTopologicalData.residueDegree =
      F.canonicalTopologicalData.residueDegree * extensionResidueDegree F E f :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le hcard
  apply Nat.eq_of_mul_eq_mul_right F.canonicalTopologicalData.residueDegree_pos
  calc E.canonicalTopologicalData.ramificationIndex * extensionResidueDegree F E f *
        F.canonicalTopologicalData.residueDegree
      = E.canonicalTopologicalData.ramificationIndex *
          E.canonicalTopologicalData.residueDegree := by rw [hres]; ring
    _ = Module.finrank (Padic p) F.Carrier * extensionDegree F E f := by rw [hE, hdeg]
    _ = extensionDegree F E f * F.canonicalTopologicalData.ramificationIndex *
          F.canonicalTopologicalData.residueDegree := by rw [← hF]; ring

/-- Equal canonical ramification indices are equivalent to `f(E/F) = [E : F]`. -/
theorem ramificationIndex_eq_iff_extensionResidueDegree_eq :
    F.canonicalTopologicalData.ramificationIndex = E.canonicalTopologicalData.ramificationIndex ↔
      extensionResidueDegree F E f = extensionDegree F E f := by
  have key := ramificationIndex_mul_extensionResidueDegree F E f
  constructor
  · intro h
    rw [← h, mul_comm (extensionDegree F E f)] at key
    exact Nat.eq_of_mul_eq_mul_left F.canonicalTopologicalData.ramificationIndex_pos key
  · intro h
    rw [h, mul_comm] at key
    exact (Nat.eq_of_mul_eq_mul_left (extensionDegree_pos F E f) key).symm

/-- Absolute inertia lies in the image of `G_E` exactly when the canonical ramification
indices agree. -/
theorem absoluteInertia_le_extensionGaloisMap_range_iff_ramificationIndex_eq :
    F.absoluteInertia F.canonicalTopologicalData ≤ (extensionGaloisMap F E f).toMonoidHom.range ↔
      F.canonicalTopologicalData.ramificationIndex =
        E.canonicalTopologicalData.ramificationIndex :=
  (absoluteInertia_le_extensionGaloisMap_range_iff F E f).trans
    (ramificationIndex_eq_iff_extensionResidueDegree_eq F E f).symm

end Embedding

section Intermediate

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (E : FiniteIntermediateExtension F.Carrier)

local notation "EP" => E.asPadicField (p := p)

local instance : Algebra (Padic p) E.field := (EP).algebra

/-- Absolute inertia fixes `E` exactly when it lies in the image of `G_E` under the
published embedding. -/
theorem absoluteInertia_le_fixingSubgroup_iff :
    F.absoluteInertia F.canonicalTopologicalData ≤ E.field.fixingSubgroup ↔
      F.absoluteInertia F.canonicalTopologicalData ≤
        (extensionGaloisMap F EP (intermediateEmbedding F E)).toMonoidHom.range := by
  have hI : (F.absoluteInertia F.canonicalTopologicalData).Normal := inferInstance
  rw [extensionGaloisMap_range]
  constructor
  · intro h τ hτ
    exact (intermediateClosureCorrection_conj_mem F E τ).mp
      (h (hI.conj_mem τ hτ (intermediateClosureCorrection F E)))
  · intro h τ hτ
    have hτ' := hI.conj_mem τ hτ (intermediateClosureCorrection F E)⁻¹
    have hmem := (intermediateClosureCorrection_conj_mem F E _).mpr (h hτ')
    rw [show intermediateClosureCorrection F E * ((intermediateClosureCorrection F E)⁻¹ * τ *
      (intermediateClosureCorrection F E)⁻¹⁻¹) * (intermediateClosureCorrection F E)⁻¹ = τ by
        group] at hmem
    exact hmem

end Intermediate

/-- The canonical unramified criterion. -/
theorem canonicalUnramifiedCriterion : CanonicalUnramifiedCriterion.{u} := by
  intro p _ F E _
  exact ((absoluteInertia_le_fixingSubgroup_iff F E).trans
    (absoluteInertia_le_extensionGaloisMap_range_iff_ramificationIndex_eq F
      (E.asPadicField (p := p)) (Weil.Local.intermediateEmbedding F E))).symm

section ResidueSupplement

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- The fixing subgroup of the image of `k_E` has index the relative residue degree. -/
theorem criterion_residueImage_index :
    (extensionResidueIntermediateField F E f).fixingSubgroup.index = extensionResidueDegree F E f := by
  let : Algebra (localResidueField F) (localResidueField E) := extensionResidueAlgebra F E f
  have : IsGalois (localResidueField F) (AlgebraicClosure (localResidueField F)) := ⟨⟩
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact (AlgHom.equivFieldRange (extensionResidueFieldAlgHom F E f)).toLinearEquiv.finrank_eq.symm

/-- The canonical absolute indices and the two relative degrees satisfy `e_F n = e_E r`. -/
theorem criterion_ramificationIndex_mul :
    F.canonicalTopologicalData.ramificationIndex * extensionDegree F E f =
      E.canonicalTopologicalData.ramificationIndex * extensionResidueDegree F E f := by
  have hres : E.canonicalTopologicalData.residueDegree =
      F.canonicalTopologicalData.residueDegree * extensionResidueDegree F E f := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    change p ^ E.canonicalTopologicalData.residueDegree =
      p ^ (F.canonicalTopologicalData.residueDegree * extensionResidueDegree F E f)
    rw [← TopologicalData.residueCardinality_eq_pow, pow_mul,
      ← TopologicalData.residueCardinality_eq_pow]
    exact extensionResidueCardinality F E f
  have hF := F.canonicalTopologicalData.ramificationIndex_mul_residueDegree
  have hE := E.canonicalTopologicalData.ramificationIndex_mul_residueDegree
  have hdeg := finrank_mul_extensionDegree F E f
  apply Nat.eq_of_mul_eq_mul_left F.canonicalTopologicalData.residueDegree_pos
  calc F.canonicalTopologicalData.residueDegree *
        (F.canonicalTopologicalData.ramificationIndex * extensionDegree F E f)
      = (F.canonicalTopologicalData.ramificationIndex *
          F.canonicalTopologicalData.residueDegree) * extensionDegree F E f := by ring
    _ = E.canonicalTopologicalData.ramificationIndex *
          E.canonicalTopologicalData.residueDegree := by rw [hF, hdeg, hE]
    _ = F.canonicalTopologicalData.residueDegree *
          (E.canonicalTopologicalData.ramificationIndex * extensionResidueDegree F E f) := by
      rw [hres]; ring

end ResidueSupplement

section NormalIntermediate

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (E : LocalClassField.FiniteIntermediateExtension F.Carrier)

/-- For a normal intermediate field, the closure comparison returns the same field. -/
theorem criterion_intermediateField_eq [Normal F.Carrier E.field] :
    extensionIntermediateField F (E.asPadicField (p := p)) (intermediateEmbedding F E) =
      E.field := by
  let g : E.field →ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
    { toRingHom := extensionFieldEmbedding F (E.asPadicField (p := p)) (intermediateEmbedding F E)
      commutes' := fun x =>
        extensionFieldEmbedding_comp F (E.asPadicField (p := p)) (intermediateEmbedding F E) x }
  rw [← AlgHom.fieldRange_of_normal g]
  ext y
  rw [mem_extensionIntermediateField, AlgHom.mem_fieldRange]
  rfl

/-- The image of `G_E` is the actual fixing subgroup of `E.field`. -/
theorem criterion_galoisMap_range [Normal F.Carrier E.field] :
    (extensionGaloisMap F (E.asPadicField (p := p)) (intermediateEmbedding F E)).toMonoidHom.range =
      E.field.fixingSubgroup := by
  rw [extensionGaloisMap_range, criterion_intermediateField_eq]

end NormalIntermediate

end Langlands.PadicField
