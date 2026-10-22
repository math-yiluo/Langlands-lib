import Langlands.Galois.CompatibleFamily

/-!
# Independence of the closure embedding for Galois representations

Restriction maps for two compatible closure embeddings are conjugate. Their
pulled-back representations are explicitly intertwined, so their polynomials
and triviality on any given subgroup agree.
-/

noncomputable section

universe uK uE uL uV

namespace Langlands.GaloisRepresentation

variable {K : Type uK} {E : Type uE} [Field K] [Field E]
variable {L : Type uL} [Field L] [TopologicalSpace L]

section Algebra

variable [Algebra K E]

/-- Continuous restriction using the supplied compatible closure embedding. -/
def restrictionAlongClosure (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) :
    Field.absoluteGaloisGroup E →ₜ* Field.absoluteGaloisGroup K := by
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure E) := ι.toAlgebra
  exact Field.absoluteGaloisGroup.mapOfAlgebra K E

theorem restrictionAlongClosure_commutes
    (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (g : Field.absoluteGaloisGroup E) (x : AlgebraicClosure K) :
    ι (AlgEquiv.toRingEquiv (restrictionAlongClosure ι g) x) =
      AlgEquiv.toRingEquiv g (ι x) := by
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure E) := ι.toAlgebra
  exact (AlgEquiv.restrictScalars K g).restrictNormal_commutes (AlgebraicClosure K) x

/-- Normality of the algebraic closure gives the unique automorphism `c`
such that `ι ∘ c = κ`. -/
def closureChange (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) :
    Field.absoluteGaloisGroup K := by
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure E) := ι.toAlgebra
  exact κ.restrictNormal' (AlgebraicClosure K)

theorem closureChange_spec (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (x : AlgebraicClosure K) :
    ι (AlgEquiv.toRingEquiv (closureChange ι κ) x) = κ x := by
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure E) := ι.toAlgebra
  exact κ.restrictNormal_commutes (AlgebraicClosure K) x

theorem closureChange_unique (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (c : Field.absoluteGaloisGroup K)
    (hc : ∀ x, ι (AlgEquiv.toRingEquiv c x) = κ x) :
    c = closureChange ι κ := by
  apply AlgEquiv.ext
  intro x
  exact ι.injective ((hc x).trans (closureChange_spec ι κ x).symm)

theorem closureChange_intertwines
    (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (g : Field.absoluteGaloisGroup E) :
    closureChange ι κ * restrictionAlongClosure κ g =
      restrictionAlongClosure ι g * closureChange ι κ := by
  apply AlgEquiv.ext
  intro x
  apply ι.injective
  change ι (AlgEquiv.toRingEquiv (closureChange ι κ)
    (AlgEquiv.toRingEquiv (restrictionAlongClosure κ g) x)) =
    ι (AlgEquiv.toRingEquiv (restrictionAlongClosure ι g)
      (AlgEquiv.toRingEquiv (closureChange ι κ) x))
  rw [closureChange_spec, restrictionAlongClosure_commutes,
    restrictionAlongClosure_commutes, closureChange_spec]

/-- Pull back the actual continuous representation along a specified closure
embedding. The carrier and coefficient topology are unchanged. -/
def pullbackAlongClosure (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (A : Objects.{uK, uL, uV} K L) : Objects.{uE, uL, uV} E L := by
  refine ⟨FiniteRepresentation.of
    (A.val.representation.comp (restrictionAlongClosure ι).toMonoidHom), ?_⟩
  let : TopologicalSpace (Module.End L A.val) := moduleTopology L (Module.End L A.val)
  exact A.property.comp (restrictionAlongClosure ι).continuous

/-- The intertwiner from the `κ` restriction to the `ι` restriction is the
action of `closureChange ι κ` on the original representation. -/
def pullbackAlongClosureEquiv
    (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (A : Objects.{uK, uL, uV} K L) :
    FiniteRepresentation.Equiv (pullbackAlongClosure κ A).val
      (pullbackAlongClosure ι A).val := by
  let r := A.val.representation
  let c := closureChange ι κ
  let e : A.val ≃ₗ[L] A.val :=
    { toLinearMap := r c
      invFun := r c⁻¹
      left_inv := fun x => by
        change (r c⁻¹ * r c) x = x
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := fun x => by
        change (r c * r c⁻¹) x = x
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl }
  refine Representation.Equiv.mk e fun g => ?_
  change r c * r (restrictionAlongClosure κ g) =
    r (restrictionAlongClosure ι g) * r c
  rw [← map_mul, ← map_mul, closureChange_intertwines]

theorem characteristicPolynomial_pullbackAlongClosure_eq
    (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (A : Objects.{uK, uL, uV} K L) (g : Field.absoluteGaloisGroup E) :
    characteristicPolynomial (pullbackAlongClosure κ A) g =
      characteristicPolynomial (pullbackAlongClosure ι A) g :=
  characteristicPolynomial_eq_of_equiv (pullbackAlongClosureEquiv ι κ A) g

theorem eulerPolynomial_pullbackAlongClosure_eq
    (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (A : Objects.{uK, uL, uV} K L) (g : Field.absoluteGaloisGroup E) :
    eulerPolynomial (pullbackAlongClosure κ A) g =
      eulerPolynomial (pullbackAlongClosure ι A) g :=
  eulerPolynomial_eq_of_equiv (pullbackAlongClosureEquiv ι κ A) g

theorem pullbackAlongClosure_action_eq_one_iff
    (ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
    (A : Objects.{uK, uL, uV} K L) (g : Field.absoluteGaloisGroup E) :
    (pullbackAlongClosure κ A).val.representation g = 1 ↔
      (pullbackAlongClosure ι A).val.representation g = 1 := by
  let e := pullbackAlongClosureEquiv ι κ A
  have h1 : e.conj (1 : Module.End L (pullbackAlongClosure κ A).val) = 1 :=
    e.toLinearEquiv.conj_id
  rw [← Representation.Equiv.conj_apply_self g e, ← h1, e.conj.injective.eq_iff]

end Algebra

/-- Mathlib's selected restriction is the explicit-closure construction for
its chosen lift. The algebra structure here comes from the same field map. -/
theorem restrictionAlongClosure_chosen_eq (f : K →+* E) :
    letI : Algebra K E := f.toAlgebra
    restrictionAlongClosure (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) =
      Field.absoluteGaloisGroup.map f := by
  rfl

/-- The originally published pullback uses precisely Mathlib's selected lift. -/
theorem pullbackAlongClosure_chosen_eq (f : K →+* E)
    (A : Objects.{uK, uL, uV} K L) :
    letI : Algebra K E := f.toAlgebra
    pullbackAlongClosure (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure E)
        A = pullback f A := by
  rfl

theorem eulerPolynomial_pullbackAlongClosure_eq_pullback (f : K →+* E)
    (A : Objects.{uK, uL, uV} K L) :
    letI : Algebra K E := f.toAlgebra
    ∀ (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E) (g : Field.absoluteGaloisGroup E),
      eulerPolynomial (pullbackAlongClosure ι A) g =
        eulerPolynomial (pullback f A) g := by
  let : Algebra K E := f.toAlgebra
  intro ι g
  rw [← pullbackAlongClosure_chosen_eq]
  exact eulerPolynomial_pullbackAlongClosure_eq _ _ _ _

/-- A closure embedding compatible with the specified field homomorphism.
The algebra structure is part of this explicit interface. -/
abbrev ClosureEmbedding (f : K →+* E) :=
  letI : Algebra K E := f.toAlgebra
  AlgebraicClosure K →ₐ[K] AlgebraicClosure E

/-- Mathlib's selected lift for the algebra structure induced by `f`. -/
def chosenClosureEmbedding (f : K →+* E) : ClosureEmbedding f := by
  letI : Algebra K E := f.toAlgebra
  exact IsAlgClosed.lift

section FinitePlace

variable [NumberField K] (v : Global.FinitePlace K)

/-- Restriction at a finite place with its closure embedding specified. -/
def atFinitePlaceAlongClosure
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
    (A : Objects.{uK, uL, uV} K L) :
    Objects.{uK, uL, uV} (Global.FiniteCompletion K v) L := by
  letI : Algebra K (Global.FiniteCompletion K v) :=
    (NumberField.FinitePlace.embedding (K := K) v).toAlgebra
  exact pullbackAlongClosure ι A

theorem atFinitePlaceAlongClosure_chosen_eq
    (A : Objects.{uK, uL, uV} K L) :
    atFinitePlaceAlongClosure v
      (chosenClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v)) A = atFinitePlace v A :=
  pullbackAlongClosure_chosen_eq (NumberField.FinitePlace.embedding (K := K) v) A

/-- The specified-closure local representation is actually isomorphic to the
published local restriction, with the comparison operator constructed above. -/
def atFinitePlaceAlongClosureEquiv
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
    (A : Objects.{uK, uL, uV} K L) :
    FiniteRepresentation.Equiv (atFinitePlaceAlongClosure v ι A).val
      (atFinitePlace v A).val := by
  letI : Algebra K (Global.FiniteCompletion K v) :=
    (NumberField.FinitePlace.embedding (K := K) v).toAlgebra
  exact pullbackAlongClosureEquiv IsAlgClosed.lift ι A

theorem eulerPolynomial_atFinitePlaceAlongClosure_eq
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
    (A : Objects.{uK, uL, uV} K L) (g : LocalGroup v) :
    eulerPolynomial (atFinitePlaceAlongClosure v ι A) g =
      eulerPolynomial (atFinitePlace v A) g := by
  let : Algebra K (Global.FiniteCompletion K v) :=
    (NumberField.FinitePlace.embedding (K := K) v).toAlgebra
  rw [← atFinitePlaceAlongClosure_chosen_eq]
  exact eulerPolynomial_pullbackAlongClosure_eq _ _ _ _

/-- Triviality on actual local inertia does not depend on the closure embedding. -/
theorem isUnramifiedAt_iff_alongClosure
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
    (A : Objects.{uK, uL, uV} K L) :
    IsUnramifiedAt A v ↔
      ∀ i : localInertia v, (atFinitePlaceAlongClosure v ι A).val.representation i.val = 1 := by
  let : Algebra K (Global.FiniteCompletion K v) :=
    (NumberField.FinitePlace.embedding (K := K) v).toAlgebra
  unfold IsUnramifiedAt
  rw [← atFinitePlaceAlongClosure_chosen_eq]
  apply forall_congr'
  intro i
  exact pullbackAlongClosure_action_eq_one_iff _ _ _ _

/-- The published existential matching predicate has the same meaning with any
compatible closure embedding; the actual geometric-lift condition is unchanged. -/
theorem hasEulerPolynomialAt_iff_alongClosure
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := K) v))
    (A : Objects.{uK, uL, uV} K L) (P : Polynomial L) :
    HasEulerPolynomialAt A v P ↔
      (∀ i : localInertia v, (atFinitePlaceAlongClosure v ι A).val.representation i.val = 1) ∧
        ∃ g : LocalGroup v, IsGeometricFrobeniusLift v g ∧
          eulerPolynomial (atFinitePlaceAlongClosure v ι A) g = P := by
  simp only [HasEulerPolynomialAt, isUnramifiedAt_iff_alongClosure v ι A,
    eulerPolynomial_atFinitePlaceAlongClosure_eq]

end FinitePlace

end Langlands.GaloisRepresentation
