import Langlands.Galois.ClosureRestriction
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.FieldTheory.Galois.Profinite

/-!
# The image of absolute Galois restriction along a closure embedding

For an algebraic extension `E/K` and a `K`-embedding `e` of algebraic closures,
`restrictionAlongClosure e : Gal(Ē/E) → Gal(K̄/K)` is injective, and its image is the subgroup
fixing the copy `transportedEmbedding e` of `E` in `K̄`. For a finite extension of a field whose
algebraic closure is Galois, the image has index `[E : K]`; it is open when the algebraic closure
of `E` is Galois over `E`. A character of `Gal(Ē/E)` descends to the image
(`descendedCharacter`), continuously for a continuous character.
-/

noncomputable section

universe uK uE

namespace Langlands.GaloisRepresentation

variable {K : Type uK} {E : Type uE} [Field K] [Field E] [Algebra K E]

section Algebraic

variable [Algebra.IsAlgebraic K E] (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)

/-- For an algebraic extension, a closure embedding is an isomorphism. -/
theorem closureEmbedding_bijective : Function.Bijective e := by
  have : Algebra.IsAlgebraic K (AlgebraicClosure E) :=
    Algebra.IsAlgebraic.trans K E (AlgebraicClosure E)
  exact (Algebra.IsAlgebraic.algHom_bijective₂
    (IsAlgClosed.lift : AlgebraicClosure E →ₐ[K] AlgebraicClosure K) e).2

/-- The closure embedding as an isomorphism of `K`-algebras. -/
def closureEmbeddingEquiv : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure E :=
  AlgEquiv.ofBijective e (closureEmbedding_bijective e)

theorem closureEmbeddingEquiv_apply (x : AlgebraicClosure K) :
    closureEmbeddingEquiv e x = e x := rfl

/-- The copy of `E` inside the algebraic closure of `K`, transported along `e`. -/
def transportedEmbedding : E →ₐ[K] AlgebraicClosure K :=
  (closureEmbeddingEquiv e).symm.toAlgHom.comp (IsScalarTower.toAlgHom K E (AlgebraicClosure E))

theorem e_transportedEmbedding (x : E) :
    e (transportedEmbedding e x) = algebraMap E (AlgebraicClosure E) x := by
  rw [← closureEmbeddingEquiv_apply]
  exact (closureEmbeddingEquiv e).apply_symm_apply _

/-- The transported copy of `E` as an intermediate field. -/
def transportedField : IntermediateField K (AlgebraicClosure K) :=
  (transportedEmbedding e).fieldRange

theorem restrictionAlongClosure_injective : Function.Injective (restrictionAlongClosure e) := by
  intro s t hst
  apply AlgEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (closureEmbedding_bijective e).2 y
  have hs := restrictionAlongClosure_commutes e s x
  have ht := restrictionAlongClosure_commutes e t x
  rw [hst] at hs
  exact hs.symm.trans ht

theorem mem_range_restrictionAlongClosure_iff (g : Field.absoluteGaloisGroup K) :
    g ∈ (restrictionAlongClosure e).toMonoidHom.range ↔
      ∀ x : E, AlgEquiv.toRingEquiv g (transportedEmbedding e x) = transportedEmbedding e x := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨s, rfl⟩ x
    apply (closureEmbedding_bijective e).1
    have h := restrictionAlongClosure_commutes e s (transportedEmbedding e x)
    change e (AlgEquiv.toRingEquiv (restrictionAlongClosure e s) (transportedEmbedding e x)) = _
    rw [h, e_transportedEmbedding]
    exact s.commutes x
  · intro hg
    let c := closureEmbeddingEquiv e
    let t : AlgebraicClosure E ≃+* AlgebraicClosure E :=
      (c.symm.toRingEquiv.trans (AlgEquiv.toRingEquiv g)).trans c.toRingEquiv
    have ht (x : E) : t (algebraMap E (AlgebraicClosure E) x) =
        algebraMap E (AlgebraicClosure E) x := by
      have h1 : c.symm (algebraMap E (AlgebraicClosure E) x) = transportedEmbedding e x := rfl
      change c (AlgEquiv.toRingEquiv g (c.symm (algebraMap E (AlgebraicClosure E) x))) = _
      rw [h1, hg x, ← e_transportedEmbedding e x]
      rfl
    let s : Field.absoluteGaloisGroup E := AlgEquiv.ofRingEquiv (f := t) ht
    refine ⟨s, ?_⟩
    apply AlgEquiv.ext
    intro y
    apply (closureEmbedding_bijective e).1
    change e (AlgEquiv.toRingEquiv (restrictionAlongClosure e s) y) = e (AlgEquiv.toRingEquiv g y)
    rw [restrictionAlongClosure_commutes]
    change c (AlgEquiv.toRingEquiv g (c.symm (e y))) = e (AlgEquiv.toRingEquiv g y)
    rw [← closureEmbeddingEquiv_apply e y, AlgEquiv.symm_apply_apply]
    rfl

/-- The absolute Galois group, viewed as the Galois group of the algebraic closure. -/
def absoluteToGal (K : Type uK) [Field K] :
    Field.absoluteGaloisGroup K →* Gal(AlgebraicClosure K/K) where
  toFun g := g
  map_one' := rfl
  map_mul' _ _ := rfl

theorem absoluteToGal_surjective (K : Type uK) [Field K] :
    Function.Surjective (absoluteToGal K) := fun g => ⟨g, rfl⟩

theorem range_restrictionAlongClosure_eq :
    (restrictionAlongClosure e).toMonoidHom.range =
      (transportedField e).fixingSubgroup.comap (absoluteToGal K) := by
  ext g
  rw [mem_range_restrictionAlongClosure_iff, Subgroup.mem_comap,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro h _ ⟨x, rfl⟩
    exact h x
  · intro h x
    exact h _ ⟨x, rfl⟩

/-- A character of the absolute Galois group of `E`, transported to the image of
restriction along `e`. -/
def descendedCharacter {M : Type*} [Monoid M] (ψ : Field.absoluteGaloisGroup E →* M) :
    (restrictionAlongClosure e).toMonoidHom.range →* M :=
  ψ.comp (MonoidHom.ofInjective (f := (restrictionAlongClosure e).toMonoidHom)
    (restrictionAlongClosure_injective e)).symm.toMonoidHom

theorem descendedCharacter_comp_rangeRestrict {M : Type*} [Monoid M]
    (ψ : Field.absoluteGaloisGroup E →* M) :
    (descendedCharacter e ψ).comp (restrictionAlongClosure e).toMonoidHom.rangeRestrict = ψ := by
  ext s
  change ψ ((MonoidHom.ofInjective (f := (restrictionAlongClosure e).toMonoidHom)
    (restrictionAlongClosure_injective e)).symm
      ((MonoidHom.ofInjective (f := (restrictionAlongClosure e).toMonoidHom)
        (restrictionAlongClosure_injective e)) s)) = ψ s
  rw [MulEquiv.symm_apply_apply]

theorem descendedCharacter_apply {M : Type*} [Monoid M] (ψ : Field.absoluteGaloisGroup E →* M)
    (s : Field.absoluteGaloisGroup E) :
    descendedCharacter e ψ ⟨restrictionAlongClosure e s, ⟨s, rfl⟩⟩ = ψ s :=
  DFunLike.congr_fun (descendedCharacter_comp_rangeRestrict e ψ) s

end Algebraic

section Finite

variable [FiniteDimensional K E] [IsGalois K (AlgebraicClosure K)]
  (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)

omit [IsGalois K (AlgebraicClosure K)] in
theorem finrank_transportedField : Module.finrank K (transportedField e) = Module.finrank K E :=
  (AlgEquiv.ofInjectiveField (transportedEmbedding e)).toLinearEquiv.finrank_eq.symm

/-- The image of the absolute Galois group of `E` has index `[E : K]`. -/
theorem index_range_restrictionAlongClosure :
    (restrictionAlongClosure e).toMonoidHom.range.index = Module.finrank K E := by
  rw [range_restrictionAlongClosure_eq,
    Subgroup.index_comap_of_surjective _ (absoluteToGal_surjective K),
    ← IntermediateField.finrank_eq_fixingSubgroup_index, finrank_transportedField]

theorem finiteIndex_range_restrictionAlongClosure :
    (restrictionAlongClosure e).toMonoidHom.range.FiniteIndex :=
  ⟨by rw [index_range_restrictionAlongClosure]; exact Module.finrank_pos.ne'⟩

theorem isOpen_range_restrictionAlongClosure [IsGalois E (AlgebraicClosure E)] :
    IsOpen ((restrictionAlongClosure e).toMonoidHom.range : Set (Field.absoluteGaloisGroup K)) := by
  have := finiteIndex_range_restrictionAlongClosure e
  have : CompactSpace (Field.absoluteGaloisGroup E) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure E/E))
  have : T2Space (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure K/K))
  apply Subgroup.isOpen_of_isClosed_of_finiteIndex
  rw [MonoidHom.coe_range]
  exact (isCompact_range (restrictionAlongClosure e).continuous).isClosed

omit [IsGalois K (AlgebraicClosure K)] in
/-- The descended character of a continuous character is continuous on the image, with
its subspace topology: restriction is a continuous bijection from a compact group onto its
Hausdorff image. -/
theorem continuous_descendedCharacter [IsGalois E (AlgebraicClosure E)] {M : Type*} [Monoid M]
    [TopologicalSpace M] (ψ : Field.absoluteGaloisGroup E →* M) (hψ : Continuous ψ) :
    Continuous (descendedCharacter e ψ) := by
  have : CompactSpace (Field.absoluteGaloisGroup E) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure E/E))
  have : T2Space (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure K/K))
  let f := (MonoidHom.ofInjective (f := (restrictionAlongClosure e).toMonoidHom)
    (restrictionAlongClosure_injective e)).toEquiv
  have hf : Continuous f :=
    Continuous.subtype_mk (restrictionAlongClosure e).continuous _
  exact hψ.comp hf.continuous_symm_of_equiv_compact_to_t2

end Finite

end Langlands.GaloisRepresentation
