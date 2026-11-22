import Langlands.Galois.AbsoluteGeometricFrobeniusDensityProof
import Langlands.Galois.FrobeniusCharacter
import Langlands.Galois.QuadraticFrobeniusPatching.CharacterRigidity
import Langlands.Galois.QuadraticFrobeniusPatching.Local
import Langlands.Representation.Category.NormalRestrictionSemisimplicity
import Langlands.Representation.Category.SubrepresentationRange

/-! # Semisimplicity and character comparison for absolute Galois representations -/

noncomputable section

namespace Langlands.GaloisRepresentation.QuadraticFrobeniusPatching

open Filter Polynomial Langlands.Global

section Restriction

variable {K E C : Type*} [Field K] [Field E] [Field C] [TopologicalSpace C]

private theorem normal_range_map [CharZero K] [Algebra K E] [IsGalois K E] :
    (Field.absoluteGaloisGroup.map (algebraMap K E)).toMonoidHom.range.Normal := by
  let f := algebraMap K E
  have hf : @Algebra.IsAlgebraic K E _ _ f.toAlgebra := by
    change @Algebra.IsAlgebraic K E _ _ (algebraMap K E).toAlgebra
    rw [toAlgebra_algebraMap]
    infer_instance
  let e : AlgebraicClosure K ≃+* AlgebraicClosure E := by
    let : Algebra K E := f.toAlgebra
    exact RingEquiv.ofBijective (chosenClosureEmbedding f).toRingHom
      (chosenClosureEmbedding_bijective f hf)
  let i : E →ₐ[K] AlgebraicClosure K :=
    { toRingHom := e.symm.toRingHom.comp (algebraMap E (AlgebraicClosure E))
      commutes' := fun x => by
        apply e.injective
        change e (e.symm (algebraMap E _ (f x))) = e (algebraMap K _ x)
        rw [e.apply_symm_apply]
        exact (chosenClosureEmbedding_commutes f x).symm }
  have hr : (Field.absoluteGaloisGroup.map f).toMonoidHom.range = i.fieldRange.fixingSubgroup := by
    apply Subgroup.ext
    intro g
    rw [mem_map_range_iff f e (fun _ => rfl)]
    let τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := g
    change (∀ y : E, τ (i y) = i y) ↔ τ ∈ i.fieldRange.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hg x hx
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
      exact hg y
    · intro hg y
      exact hg (i y) (AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩)
  change (Field.absoluteGaloisGroup.map f).toMonoidHom.range.Normal
  rw [hr]
  have : IsGalois K i.fieldRange := IsGalois.of_algEquiv i.equivFieldRange
  exact IsGalois.fixingSubgroup_normal_of_isGalois i.fieldRange

private theorem isSemisimple_pullback_of_normal_range (f : K →+* E)
    (hn : (Field.absoluteGaloisGroup.map f).toMonoidHom.range.Normal) {A : Objects K C}
    (hA : Representation.IsSemisimpleRepresentation A.val.representation) :
    Representation.IsSemisimpleRepresentation (pullback f A).val.representation := by
  let φ := (Field.absoluteGaloisGroup.map f).toMonoidHom
  let ρ := A.val.representation
  have h : Set.range (ρ.comp φ.range.subtype) = Set.range (ρ.comp φ) := by
    ext x
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hg
      exact ⟨y, congrArg ρ hy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨φ y, ⟨y, rfl⟩⟩, rfl⟩
  have : φ.range.Normal := hn
  exact (Langlands.Weil.FiniteIndexRestrictionSemisimplicity.isSemisimpleRepresentation_iff_of_range_eq
    _ _ h).mp (finiteDimensionalNormalRestrictionSemisimplicity C _ A.val φ.range ρ hA)

/-- A finite dimensional semisimple representation stays semisimple after
restriction along a Galois extension of characteristic-zero fields. -/
theorem isSemisimple_pullback_of_isGalois [CharZero K] [Algebra K E] [IsGalois K E]
    {A : Objects K C} (hA : Representation.IsSemisimpleRepresentation A.val.representation) :
    Representation.IsSemisimpleRepresentation (pullback (algebraMap K E) A).val.representation :=
  isSemisimple_pullback_of_normal_range _ normal_range_map hA

/-- Precomposing the action along a field isomorphism preserves semisimplicity. -/
theorem isSemisimple_pullback_of_surjective (f : K →+* E) (hf : Function.Surjective f)
    {A : Objects K C} (hA : Representation.IsSemisimpleRepresentation A.val.representation) :
    Representation.IsSemisimpleRepresentation (pullback f A).val.representation := by
  apply isSemisimple_pullback_of_normal_range f _ hA
  rw [MonoidHom.range_eq_top_of_surjective _ (map_surjective f hf)]
  infer_instance

end Restriction

section Comparison

variable {K C : Type*} [Field K] [NumberField K] [Field C] [CharZero C]
  [TopologicalSpace C] [IsTopologicalRing C] [T2Space C]

/-- Cofinite agreement of the Euler polynomials of actual geometric Frobenius
lifts gives an intertwiner between semisimple representations. -/
theorem equiv_of_eventually_hasEulerPolynomialAt {A B : Objects K C}
    (hA : Representation.IsSemisimpleRepresentation A.val.representation)
    (hB : Representation.IsSemisimpleRepresentation B.val.representation)
    (h : ∀ᶠ v : FinitePlace K in cofinite, ∃ Q : C[X],
      HasEulerPolynomialAt A v Q ∧ HasEulerPolynomialAt B v Q) :
    Nonempty (FiniteRepresentation.Equiv A.val B.val) := by
  classical
  let exceptions := (eventually_cofinite.mp h).toFinset
  apply equiv_of_character_eq hA hB
  apply (continuous_character A).ext_on (absoluteGeometricFrobeniusDensity K exceptions)
    (continuous_character B)
  rintro _ ⟨v, a, t, hv, ha, rfl⟩
  rw [Representation.char_conj, Representation.char_conj]
  obtain ⟨Q, hAv, hBv⟩ : ∃ Q : C[X], HasEulerPolynomialAt A v Q ∧
      HasEulerPolynomialAt B v Q := by
    by_contra hn
    exact hv ((eventually_cofinite.mp h).mem_toFinset.mpr hn)
  have he := (hAv.forall_lifts a ha).trans (hBv.forall_lifts a ha).symm
  have hc := congrArg (fun P : C[X] => P.coeff 1) he
  simpa only [atFinitePlace, eulerPolynomial_pullback, coeff_one_eulerPolynomial, neg_inj] using hc

end Comparison

end Langlands.GaloisRepresentation.QuadraticFrobeniusPatching
