import Langlands.ClassFieldTheory.Local.CommonClosureFiniteRestrictions
import Langlands.ClassFieldTheory.Local.FiniteAbelianizedArtin
import Langlands.ClassFieldTheory.Local.FiniteArtinSystemExistenceProof
import Langlands.Weil.Local.ExtensionNormReciprocity

/-! # Finite Galois restrictions of geometric profinite reciprocity -/

noncomputable section

namespace Langlands.LocalClassField.FiniteQuotientTransport

open ClassFieldTheory.Local

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (D : Type u) [Field D] [Algebra F.Carrier D]
  [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]
  [Algebra D (AlgebraicClosure F.Carrier)]
  [IsScalarTower F.Carrier D (AlgebraicClosure F.Carrier)]

local instance artinRestrictionBaseCharZero : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

omit [FiniteDimensional F.Carrier D] in
/-- The finite restriction kernel fixes the actual image of the finite field. -/
theorem closureFiniteRestriction_ker :
    (AlgEquiv.restrictNormalHom (F := F.Carrier)
      (K₁ := AlgebraicClosure F.Carrier) D).ker =
        (IsScalarTower.toAlgHom F.Carrier D (AlgebraicClosure F.Carrier)).fieldRange.fixingSubgroup := by
  ext σ
  change σ.restrictNormal D = 1 ↔ _
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    have hh := AlgEquiv.restrictNormal_commutes σ D y
    rw [h] at hh
    exact hh.symm
  · intro h
    apply AlgEquiv.ext
    intro x
    apply (algebraMap D (AlgebraicClosure F.Carrier)).injective
    rw [AlgEquiv.restrictNormal_commutes]
    exact h _ ⟨x, rfl⟩

/-- Restriction to any finite Galois field with a specified embedding in the
algebraic closure is continuous. -/
def closureFiniteRestriction :
    Field.absoluteGaloisGroup F.Carrier →ₜ* Gal(D/F.Carrier) := by
  let j := IsScalarTower.toAlgHom F.Carrier D (AlgebraicClosure F.Carrier)
  let : FiniteDimensional F.Carrier j.fieldRange :=
    Module.Finite.equiv j.equivFieldRange.toLinearEquiv
  exact
    { toMonoidHom := AlgEquiv.restrictNormalHom D
      continuous_toFun := WeilReciprocityExistence.continuous_of_isOpen_ker _ (by
        change IsOpen ((AlgEquiv.restrictNormalHom (F := F.Carrier)
          (K₁ := AlgebraicClosure F.Carrier) D).ker : Set Gal(AlgebraicClosure F.Carrier/F.Carrier))
        rw [closureFiniteRestriction_ker F D]
        exact j.fieldRange.fixingSubgroup_isOpen) }

/-- Finite restriction on the actual closed-commutator quotient, valued in
the algebraic abelianization of the finite Galois group. -/
def closureFiniteAbelianRestriction :
    Field.absoluteGaloisGroupAbelianization F.Carrier →* Abelianization Gal(D/F.Carrier) :=
  (discreteAbelianizationEquiv Gal(D/F.Carrier)).toMonoidHom.comp
    (abelianizationMap (closureFiniteRestriction F D)).toMonoidHom

@[simp] theorem closureFiniteAbelianRestriction_projection
    (σ : Field.absoluteGaloisGroup F.Carrier) :
    closureFiniteAbelianRestriction F D (absoluteAbelianizationProjection F.Carrier σ) =
      Abelianization.of (closureFiniteRestriction F D σ) :=
  discreteAbelianizationEquiv_projection _ _

/-- Every finite Galois restriction of a geometrically normalized profinite
reciprocity map is the geometric abelianized carry symbol. -/
theorem closureFiniteAbelianRestriction_geometric (T : F.TopologicalData) :
    letI := T.topology
    ∀ (ρ : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier),
      GeometricProfiniteReciprocityRelation F T ρ →
        ∀ a : F.Carrierˣ, closureFiniteAbelianRestriction F D (ρ a) =
          FiniteArtinSymbol.abelianizedArtinSymbol F D a⁻¹ := by
  let := T.topology
  intro ρ hρ a
  let : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  let j := IsScalarTower.toAlgHom F.Carrier D (AlgebraicClosure F.Carrier)
  let N := j.fieldRange
  let : FiniteDimensional F.Carrier N := Module.Finite.equiv j.equivFieldRange.toLinearEquiv
  let r : Gal(AlgebraicClosure F.Carrier/F.Carrier) →ₜ* Gal(D/F.Carrier) :=
    closureFiniteRestriction F D
  let V := (Abelianization.of.comp r.toMonoidHom).ker
  have hV : V = (commutator Gal(D/F.Carrier)).comap r.toMonoidHom := by
    ext τ
    change r τ ∈ (Abelianization.of : Gal(D/F.Carrier) →* _).ker ↔
      r τ ∈ commutator Gal(D/F.Carrier)
    rw [Abelianization.ker_of]
  have hVo : IsOpen (V : Set Gal(AlgebraicClosure F.Carrier/F.Carrier)) := by
    rw [hV]
    exact (isOpen_discrete (commutator Gal(D/F.Carrier) : Set Gal(D/F.Carrier))).preimage
      r.continuous
  have hcomm : ∀ s t : Gal(AlgebraicClosure F.Carrier/F.Carrier),
      s * t * (t * s)⁻¹ ∈ V := by
    intro s t
    change Abelianization.of (r (s * t * (t * s)⁻¹)) = 1
    simp only [map_mul, map_inv]
    rw [mul_comm (Abelianization.of (r t)) (Abelianization.of (r s)), mul_inv_cancel]
  let A := FiniteAbelianExtension.ofOpenNormal V hVo hcomm
  have hAfix : A.field.toIntermediateField.fixingSubgroup = V :=
    FiniteAbelianExtension.ofOpenNormal_fixingSubgroup V hVo hcomm
  have hrker : r.toMonoidHom.ker = N.fixingSubgroup :=
    closureFiniteRestriction_ker F D
  have hAN : A.field.toIntermediateField ≤ N := by
    change IntermediateField.fixedField V ≤ N
    rw [← InfiniteGalois.fixedField_fixingSubgroup N]
    apply IntermediateField.fixedField_le
    intro τ hτ
    have hh : r τ = 1 := by
      change τ ∈ r.toMonoidHom.ker
      rw [hrker]
      exact hτ
    change Abelianization.of (r τ) = 1
    rw [hh, map_one]
  let φ : A.field →ₐ[F.Carrier] D :=
    j.equivFieldRange.symm.toAlgHom.comp (IntermediateField.inclusion hAN)
  have hjφ (x : A.field) : j (φ x) = (x : AlgebraicClosure F.Carrier) := by
    exact congrArg (fun z : N => (z : AlgebraicClosure F.Carrier))
      (j.equivFieldRange.apply_symm_apply (IntermediateField.inclusion hAN x))
  let : Algebra A.field D := φ.toRingHom.toAlgebra
  let : IsScalarTower F.Carrier A.field D :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  let : IsScalarTower A.field D (AlgebraicClosure F.Carrier) :=
    IsScalarTower.of_algebraMap_eq (fun x => (hjφ x).symm)
  let : FiniteDimensional A.field D := FiniteDimensional.right F.Carrier A.field D
  let q : Gal(D/F.Carrier) →* Gal(A.field/F.Carrier) := AlgEquiv.restrictNormalHom A.field
  have hq (τ : Gal(AlgebraicClosure F.Carrier/F.Carrier)) :
      q (r τ) = A.restriction τ :=
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply A.field D τ).symm
  have hqi : Function.Injective (Abelianization.lift q) := by
    apply (Abelianization.lift q).ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    change x = 1
    induction x using QuotientGroup.induction_on with
    | H σ =>
      obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure F.Carrier) σ
      change r τ = σ at hτ
      have hqσ : q σ = 1 := hx
      have hAτ : A.restriction τ = 1 := by
        rw [← hq, hτ]
        exact hqσ
      have hτV : τ ∈ V := by
        have hh := (A.restriction_eq_one_iff τ).mp hAτ
        rw [hAfix] at hh
        exact hh
      have hh : Abelianization.of (r τ) = 1 := hτV
      rw [hτ] at hh
      exact hh
  have hdesc (z : Field.absoluteGaloisGroupAbelianization F.Carrier) :
      Abelianization.lift q (closureFiniteAbelianRestriction F D z) =
        A.abelianRestriction z := by
    induction z using QuotientGroup.induction_on with
    | H τ =>
      change Abelianization.lift q
        (closureFiniteAbelianRestriction F D (absoluteAbelianizationProjection F.Carrier τ)) =
          A.restriction τ
      rw [closureFiniteAbelianRestriction_projection, Abelianization.lift_apply_of]
      exact hq τ
  have hsymbol (b : F.Carrierˣ) :
      Abelianization.lift q (FiniteArtinSymbol.abelianizedArtinSymbol F D b) =
        FiniteArtinSymbol.artinSymbol F A.field b := by
    have ht := FiniteArtinSymbol.restrictNormalHom_abelianizedArtinSymbol F D A.field b
    rw [FiniteArtinSymbol.abelianizedArtinSymbol_eq_of_comm F A.field] at ht
    have hh := congrArg (Abelianization.lift (MonoidHom.id Gal(A.field/F.Carrier))) ht
    have hl : (Abelianization.lift (MonoidHom.id Gal(A.field/F.Carrier))).comp
        (Abelianization.map q) = Abelianization.lift q := by
      apply Abelianization.hom_ext
      ext σ
      rfl
    change (Abelianization.lift (MonoidHom.id Gal(A.field/F.Carrier))).comp
      (Abelianization.map q) (FiniteArtinSymbol.abelianizedArtinSymbol F D b) = _ at hh
    rw [hl] at hh
    exact hh
  apply hqi
  rw [hdesc, hsymbol]
  have hfamily := geometricFiniteArtinSystemUniqueness p F T
    (finiteFamilyOfHom ρ) (FiniteArtinSystemExistence.geometricFamily F T)
    ⟨hρ.1.2, hρ.2⟩ (FiniteArtinSystemExistence.geometricFamily_relation F T)
  exact DFunLike.congr_fun (congrFun hfamily A) a

end Langlands.LocalClassField.FiniteQuotientTransport
