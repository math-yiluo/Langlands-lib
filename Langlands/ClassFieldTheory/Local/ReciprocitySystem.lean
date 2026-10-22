import Langlands.ClassFieldTheory.Local.ReciprocityRelations
import Langlands.LocalField.Canonical

/-!
# Reciprocity systems in a common algebraic closure

The indices are actual finite intermediate fields, including nonnormal ones.
All subgroup inclusions, transfers and conjugations below are constructed from
those fields. Candidate families, their relations and the existence and
uniqueness properties are definitions; no candidate family or reciprocity
theorem is constructed.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u

/-- Actual finite intermediate fields of the existing algebraic closure.
This packages a finiteness certificate and introduces no new field operations. -/
def FiniteIntermediateExtension (K : Type u) [Field K] :=
  {E : IntermediateField K (AlgebraicClosure K) // FiniteDimensional K E}

namespace FiniteIntermediateExtension

variable {K : Type u} [Field K]

/-- The underlying actual intermediate field. -/
abbrev field (E : FiniteIntermediateExtension K) :
    IntermediateField K (AlgebraicClosure K) := E.1

instance (E : FiniteIntermediateExtension K) : FiniteDimensional K E.field := E.2

/-- Repackage the same field as a finite extension of the specified `Q_p`.
The scalar map is the composite through `K`. -/
abbrev asPadicField {p : ℕ} [Fact p.Prime] [Algebra (Padic p) K]
    [FiniteDimensional (Padic p) K] (E : FiniteIntermediateExtension K) :
    PadicField.{u} p := by
  let alg : Algebra (Padic p) E.field :=
    ((algebraMap K E.field).comp (algebraMap (Padic p) K)).toAlgebra
  letI := alg
  letI : Module (Padic p) E.field := @Algebra.toModule _ _ _ _ alg
  letI : IsScalarTower (Padic p) K E.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hfd : FiniteDimensional (Padic p) E.field :=
    FiniteDimensional.trans (Padic p) K E.field
  exact @Langlands.PadicField.mk p inferInstance E.field inferInstance alg hfd

/-- The conjugate field `σ(E)` in the same closure. Its finite dimensionality
is Mathlib's instance for the image under an algebra homomorphism. -/
def conj (σ : Field.absoluteGaloisGroup K) (E : FiniteIntermediateExtension K) :
    FiniteIntermediateExtension K :=
  ⟨E.field.map (AlgEquiv.toAlgHom σ), inferInstance⟩

/-- The actual field isomorphism `E ≃ σ(E)` on multiplicative groups. -/
def unitsConjugation (σ : Field.absoluteGaloisGroup K) (E : FiniteIntermediateExtension K) :
    E.fieldˣ →* (E.conj σ).fieldˣ :=
  Units.map (IntermediateField.equivMap E.field (AlgEquiv.toAlgHom σ)).toRingEquiv.toMonoidHom

variable (E L : FiniteIntermediateExtension K) (h : E.field ≤ L.field)

/-- Actual field inclusion on multiplicative groups. -/
def unitsInclusion : E.fieldˣ →* L.fieldˣ :=
  Units.map (IntermediateField.inclusion h).toMonoidHom

/-- Actual field norm along an inclusion of finite intermediate fields.
The scalar structure is induced by that inclusion. -/
def unitsNorm : L.fieldˣ →* E.fieldˣ := by
  letI : Algebra E.field L.field := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower K E.field L.field := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional E.field L.field := FiniteDimensional.right K E.field L.field
  exact normUnits E.field L.field

variable [PerfectField K]

/-- Restriction of the ambient inclusion to the actual fixing subgroups,
in the direction opposite to field inclusion. -/
def galoisInclusion : L.field.fixingSubgroup →ₜ* E.field.fixingSubgroup :=
  subgroupInclusion (IntermediateField.fixingSubgroup_antitone h)

/-- The induced inclusion of the actual topological abelianizations. -/
def galoisAbelianInclusion :
    TopologicalAbelianization L.field.fixingSubgroup →ₜ*
      TopologicalAbelianization E.field.fixingSubgroup :=
  abelianizationMap (galoisInclusion E L h)

/-- The actual opposite-direction finite-index transfer between fixing
subgroups, not a supplied homomorphism. -/
def galoisAbelianTransfer :
    TopologicalAbelianization E.field.fixingSubgroup →ₜ*
      TopologicalAbelianization L.field.fixingSubgroup := by
  letI := absoluteFixingFiniteIndex K L.field
  exact subgroupAbelianTransfer
    (IntermediateField.fixingSubgroup_antitone h) L.field.fixingSubgroup_isOpen

variable (φ : Field.absoluteGaloisGroup K →ₜ* Weil.ProfiniteIntegers)

/-- Inclusion of the actual preimage subgroups in the existing Weil pullback. -/
def weilInclusion :
    pullbackFixingSubgroup K L.field φ →ₜ* pullbackFixingSubgroup K E.field φ :=
  subgroupInclusion (Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone h))

/-- Inclusion on the actual topological Weil abelianizations in the common closure. -/
def weilAbelianInclusion :
    TopologicalAbelianization (pullbackFixingSubgroup K L.field φ) →ₜ*
      TopologicalAbelianization (pullbackFixingSubgroup K E.field φ) :=
  abelianizationMap (weilInclusion E L h φ)

/-- Transfer in the opposite direction, between the same actual quotients. -/
def weilAbelianTransfer :
    TopologicalAbelianization (pullbackFixingSubgroup K E.field φ) →ₜ*
      TopologicalAbelianization (pullbackFixingSubgroup K L.field φ) := by
  letI := pullbackFixingFiniteIndex K L.field φ
  exact subgroupAbelianTransfer
    (Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone h))
    (pullbackFixingSubgroup_open K L.field φ)

omit [PerfectField K] in
/-- Conjugation by `w` maps the preimage subgroup for `E` into the one for
`σ(E)`, where `σ` is the Galois projection of `w`. This uses Mathlib's
formula for the fixing subgroup of an image field. -/
theorem conj_mem_pullbackFixingSubgroup (w : Weil.Pullback φ) {x : Weil.Pullback φ}
    (hx : x ∈ pullbackFixingSubgroup K E.field φ) :
    w * x * w⁻¹ ∈ pullbackFixingSubgroup K (E.conj (Weil.projection φ w)).field φ := by
  change Weil.projection φ (w * x * w⁻¹) ∈
    (E.field.map (AlgEquiv.toAlgHom (Weil.projection φ w))).fixingSubgroup
  rw [IsGalois.map_fixingSubgroup E.field (Weil.projection φ w), map_mul, map_mul, map_inv]
  exact Subgroup.smul_mem_pointwise_smul (G := Gal(AlgebraicClosure K/K))
    (α := MulAut Gal(AlgebraicClosure K/K)) (Weil.projection φ x)
    (MulAut.conj (G := Gal(AlgebraicClosure K/K)) (Weil.projection φ w))
    E.field.fixingSubgroup hx

/-- Conjugation by an element `w` of the existing Weil pullback, from the
preimage subgroup for `E` to the one for `σ(E)`. -/
def weilConjugation (w : Weil.Pullback φ) :
    pullbackFixingSubgroup K E.field φ →ₜ*
      pullbackFixingSubgroup K (E.conj (Weil.projection φ w)).field φ where
  toFun x := ⟨w * x * w⁻¹, E.conj_mem_pullbackFixingSubgroup φ w x.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_assoc]
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

/-- The induced conjugation on the actual topological abelianizations. -/
def weilAbelianConjugation (w : Weil.Pullback φ) :
    TopologicalAbelianization (pullbackFixingSubgroup K E.field φ) →ₜ*
      TopologicalAbelianization
        (pullbackFixingSubgroup K (E.conj (Weil.projection φ w)).field φ) :=
  abelianizationMap (E.weilConjugation φ w)

/-- The integer degree of the existing pullback, read on the abelianized
subgroup fixing `E` through the actual inclusion. It is the degree over
the base field, not a renormalized degree over `E`. -/
def weilDegree :
    TopologicalAbelianization (pullbackFixingSubgroup K E.field φ) →ₜ* Weil.Degree :=
  (WeilQuotients.degree φ).comp (pullbackFixingAbelianInclusion K E.field φ)

/-- Restriction of the existing Weil projection to the subgroup fixing `E`. -/
def weilGaloisProjection :
    pullbackFixingSubgroup K E.field φ →ₜ* E.field.fixingSubgroup where
  toFun w := ⟨Weil.projection φ w.1, w.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    ((Weil.projection φ).continuous.comp continuous_subtype_val).subtype_mk _

/-- The actual induced map to the fixing subgroup's Galois abelianization.
The Weil source is not declared compact. -/
def weilGaloisAbelianProjection :
    TopologicalAbelianization (pullbackFixingSubgroup K E.field φ) →ₜ*
      TopologicalAbelianization E.field.fixingSubgroup :=
  abelianizationMap (weilGaloisProjection E φ)

end FiniteIntermediateExtension

section Local

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
  (T : F.TopologicalData)
  (φ : Field.absoluteGaloisGroup F.Carrier →ₜ* Weil.ProfiniteIntegers)

/-- Uniqueness of a single-field candidate under the local conditions:
geometric order normalization, density, and every finite norm-residue
relation. This is a proposition definition, not a uniqueness theorem. -/
def LocalReciprocityUniqueness : Prop :=
  ∀ e₁ e₂ : WeilReciprocityCandidate T φ,
    LocalReciprocityCandidateRelation T φ e₁ →
      LocalReciprocityCandidateRelation T φ e₂ → e₁ = e₂

end Local

namespace CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (S : ∀ E : FiniteIntermediateExtension F.Carrier, (E.asPadicField (p := p)).TopologicalData)
  (φ : Field.absoluteGaloisGroup F.Carrier →ₜ* Weil.ProfiniteIntegers)

/-- A family of candidate Weil reciprocity isomorphisms on every actual
finite intermediate field, including non-Galois extensions. This type is
not asserted to be inhabited. The degree map `φ` is still explicit. -/
abbrev CandidateFamily :=
  ∀ E : FiniteIntermediateExtension F.Carrier,
    letI := (S E).topology
    TopologicalAbelianization (pullbackFixingSubgroup F.Carrier E.field φ) ≃ₜ*
      E.fieldˣ

/-- Candidate maps into the actual Galois abelianizations in this common
closure. Inverses are taken only into the abelianized Weil groups. -/
def galoisHom (e : CandidateFamily F S φ) (E : FiniteIntermediateExtension F.Carrier) :
    letI := (S E).topology
    E.fieldˣ →ₜ* TopologicalAbelianization E.field.fixingSubgroup := by
  letI := (S E).topology
  letI := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact (E.weilGaloisAbelianProjection φ).comp
    ((e E).symm : E.fieldˣ →ₜ*
      TopologicalAbelianization (pullbackFixingSubgroup F.Carrier E.field φ))

/-- The norm square for all nested finite extensions in the common closure.
Each norm and each subgroup inclusion is the actual constructed map. -/
def NormRelation (e : CandidateFamily F S φ) : Prop :=
  letI := Algebra.charZero_of_charZero (Padic p) F.Carrier
  ∀ (E L : FiniteIntermediateExtension F.Carrier) (h : E.field ≤ L.field),
    (e E).toMonoidHom.comp (E.weilAbelianInclusion L h φ).toMonoidHom =
      (E.unitsNorm L h).comp (e L).toMonoidHom

/-- The opposite field-inclusion/transfer square for all nested finite
extensions. No transfer is supplied as arbitrary data. -/
def TransferRelation (e : CandidateFamily F S φ) : Prop :=
  letI := Algebra.charZero_of_charZero (Padic p) F.Carrier
  ∀ (E L : FiniteIntermediateExtension F.Carrier) (h : E.field ≤ L.field),
    (e L).toMonoidHom.comp (E.weilAbelianTransfer L h φ).toMonoidHom =
      (E.unitsInclusion L h).comp (e E).toMonoidHom

/-- The conjugation square for every element `w` of the existing pullback
and every finite intermediate field, with `σ` the Galois projection of `w`:
the candidate for `σ(E)` after conjugation by `w` is `σ` after the
candidate for `E`. -/
def ConjugationRelation (e : CandidateFamily F S φ) : Prop :=
  letI := Algebra.charZero_of_charZero (Padic p) F.Carrier
  ∀ (w : Weil.Pullback φ) (E : FiniteIntermediateExtension F.Carrier),
    (e (E.conj (Weil.projection φ w))).toMonoidHom.comp
        (E.weilAbelianConjugation φ w).toMonoidHom =
      (E.unitsConjugation (Weil.projection φ w)).comp (e E).toMonoidHom

/-- Density of every candidate's actual map into the corresponding Galois
abelianization. This is a condition, not a consequence assumed by the constructors. -/
def DensityRelation (e : CandidateFamily F S φ) : Prop :=
  ∀ E, DenseRange (galoisHom F S φ e E)

/-- The completion comparison diagram at every finite intermediate field.
Existence of the comparison equivalences is stated explicitly as a relation. -/
def CompletionRelation (e : CandidateFamily F S φ) : Prop :=
  ∀ E, letI := (S E).topology
    ∃ c : LocalMultiplicative.profiniteCompletion (S E) ≃ₜ*
        TopologicalAbelianization E.field.fixingSubgroup,
      (c : LocalMultiplicative.profiniteCompletion (S E) →ₜ*
        TopologicalAbelianization E.field.fixingSubgroup).comp
        (LocalMultiplicative.completionMap (S E)) =
        galoisHom F S φ e E

/-- Coherence conditions before normalization: norm, transfer and
conjugation squares, density and completion comparison. This unnormalized
predicate is not the full reciprocity system. -/
def CoherentFamilyRelation (e : CandidateFamily F S φ) : Prop :=
  NormRelation F S φ e ∧ TransferRelation F S φ e ∧ ConjugationRelation F S φ e ∧
    DensityRelation F S φ e ∧ CompletionRelation F S φ e

/-- Existence of a coherent family is a proposition, not a selected family
or a class-field-theory theorem. -/
def CoherentFamilyExistence : Prop :=
  ∃ e : CandidateFamily F S φ, CoherentFamilyRelation F S φ e

variable (T : F.TopologicalData)

/-- Geometric normalization at every finite intermediate field: the
normalized absolute value of the image of `w` is `q_F` to minus the
base-field degree of `w`, with `q_F` the residue cardinality of `T`. -/
def NormalizationRelation (e : CandidateFamily F S φ) : Prop :=
  letI := Algebra.charZero_of_charZero (Padic p) F.Carrier
  ∀ (E : FiniteIntermediateExtension F.Carrier)
    (w : TopologicalAbelianization (pullbackFixingSubgroup F.Carrier E.field φ)),
    (S E).normalizedAbs ((e E w : E.fieldˣ) : E.field) =
      (T.residueCardinality : ℝ) ^ (-Multiplicative.toAdd (E.weilDegree φ w))

/-- The normalized reciprocity-system relation. -/
def NormalizedSystemRelation (e : CandidateFamily F S φ) : Prop :=
  CoherentFamilyRelation F S φ e ∧ NormalizationRelation F S φ T e

/-- Existence of a normalized reciprocity system, as a proposition only. -/
def NormalizedSystemExistence : Prop :=
  ∃ e : CandidateFamily F S φ, NormalizedSystemRelation F S φ T e

/-- Uniqueness of a normalized reciprocity system, as a proposition only. -/
def NormalizedSystemUniqueness : Prop :=
  ∀ e₁ e₂ : CandidateFamily F S φ,
    NormalizedSystemRelation F S φ T e₁ → NormalizedSystemRelation F S φ T e₂ → e₁ = e₂

/-- The constructed canonical topological data on every finite intermediate
field. It supplies `S` for the canonical formulations; `φ` stays explicit. -/
def canonicalData (E : FiniteIntermediateExtension F.Carrier) :
    (E.asPadicField (p := p)).TopologicalData :=
  (E.asPadicField (p := p)).canonicalTopologicalData

end CommonClosure

end Langlands.LocalClassField
