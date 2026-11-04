import Langlands.Representation.Plancherel.ProductInducedOrbitSections
import Langlands.Representation.Plancherel.FiniteSmoothFamilyTransport
import Langlands.Representation.Plancherel.ProductCompactBaseChange

/-! # Base-object independence of actual smooth orbit sections -/

noncomputable section

open CategoryTheory Langlands.Aubert.General Langlands.Induction
open scoped NNReal

namespace Langlands.Plancherel

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (A : UnitaryOrbitRepresentative ν π)

/-- Moving the base within its unitary orbit leaves exactly the same actual
irreducible admissible objects in that orbit. -/
theorem unitaryOrbitRepresentative_mem_iff
    (B : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M)) :
    B ∈ {B | ∃ χ : unitaryUnramifiedCharacters ν,
      SmoothDualClass.twist (unitaryUnramifiedInclusion ν χ).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (unitaryUnramifiedInclusion ν χ))
        (Quotient.mk _ A.val : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) =
      (Quotient.mk _ B : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M))} ↔
    B ∈ {B | ∃ χ : unitaryUnramifiedCharacters ν,
      SmoothDualClass.twist (unitaryUnramifiedInclusion ν χ).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (unitaryUnramifiedInclusion ν χ))
        (Quotient.mk _ π : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) =
      (Quotient.mk _ B : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M))} := by
  let ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M) := Quotient.mk _ π
  let ωA : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M) := Quotient.mk _ A.val
  let ωB : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M) := Quotient.mk _ B
  obtain ⟨χ, hχ⟩ := A.property
  change unitaryUnramifiedInclusion ν χ • ω = ωA at hχ
  change (∃ η, unitaryUnramifiedInclusion ν η • ωA = ωB) ↔
    (∃ η, unitaryUnramifiedInclusion ν η • ω = ωB)
  constructor
  · rintro ⟨η, hη⟩
    exact ⟨η * χ, by rw [map_mul, mul_smul, hχ]; exact hη⟩
  · rintro ⟨η, hη⟩
    refine ⟨η * χ⁻¹, ?_⟩
    rw [map_mul, map_inv, mul_smul, ← hχ, inv_smul_smul]
    exact hη

/-- Recenter the orbit by retaining every actual representative object. -/
def unitaryOrbitRepresentativeBaseEquiv :
    UnitaryOrbitRepresentative ν π ≃ UnitaryOrbitRepresentative ν A.val where
  toFun B := ⟨B.val, (unitaryOrbitRepresentative_mem_iff ν π A B.val).mpr B.property⟩
  invFun B := ⟨B.val, (unitaryOrbitRepresentative_mem_iff ν π A B.val).mp B.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

variable [LocallyCompactSpace G]
  {P U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))

/-- Reindex actual sections without changing any value in an actual fiber. -/
def productInducedOrbitBaseEquiv :
    ProductInducedOrbitSections ν π h hU ≃ₗ[ℂ]
      ProductInducedOrbitSections ν A.val h hU where
  toFun q B := q ((unitaryOrbitRepresentativeBaseEquiv ν π A).symm B)
  invFun q B := q (unitaryOrbitRepresentativeBaseEquiv ν π A B)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reindexing preserves and reflects coherence under all actual inducing
equivalences. -/
theorem productInducedOrbitBaseEquiv_coherent_iff
    (q : ProductInducedOrbitSections ν π h hU) :
    productInducedOrbitBaseEquiv ν π A h hU q ∈
        coherentProductInducedOrbitSections ν A.val h hU ↔
      q ∈ coherentProductInducedOrbitSections ν π h hU := by
  constructor
  · intro hq B C a
    exact hq (unitaryOrbitRepresentativeBaseEquiv ν π A B)
      (unitaryOrbitRepresentativeBaseEquiv ν π A C) a
  · intro hq B C a
    exact hq ((unitaryOrbitRepresentativeBaseEquiv ν π A).symm B)
      ((unitaryOrbitRepresentativeBaseEquiv ν π A).symm C) a

variable {J : Type uJ} (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

omit [NonarchimedeanGroup G] [LocallyCompactSpace G] in
/-- Multiplication in the coordinate torus is multiplication of the actual
unitary unramified characters. -/
theorem unitaryTorusParameter_mul (z w : J → Circle) :
    unitaryTorusParameter ν e (z * w) =
      unitaryTorusParameter ν e z * unitaryTorusParameter ν e w := by
  change unitaryUnramifiedInclusion ν (e.symm (z * w)) = _
  rw [map_mul, map_mul]
  rfl

variable (K : OpenSubgroup G)
  (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

/-- On coherent actual sections, recentering the base translates the torus
parameter and applies one fixed compact coefficient map. -/
theorem productInducedOrbitCompactPullback_baseChange
    (q : ProductInducedOrbitSections ν π h hU)
    (hq : q ∈ coherentProductInducedOrbitSections ν π h hU)
    (z₀ : J → Circle)
    (a : (π.obj.twist (unitaryTorusParameter ν e z₀).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z₀))).representation.Equiv
        A.val.obj.representation) (z : J → Circle) :
    productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK A.val.obj
        (productInducedOrbitPullback ν A.val e h hU
          (productInducedOrbitBaseEquiv ν π A h hU q)) z =
      productCompactBaseChangeEquiv ν h K hP hK hν hr
        (unitaryTorusParameter ν e z₀) a
        (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
          (productInducedOrbitPullback ν π e h hU q) (z * z₀)) := by
  let R (χ : unitaryUnramifiedCharacters ν) : ProductInducedCompactPicture h K π.obj :=
    productInducedCompactEquiv ν h K hP hK hν hr hU hPK
      (unitaryUnramifiedInclusion ν χ) π.obj
      (q ⟨IrreducibleAdmissibleRep.twist
        (unitaryUnramifiedInclusion ν χ).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (unitaryUnramifiedInclusion ν χ)) π,
        χ, rfl⟩)
  change productInducedCompactEquiv ν h K hP hK hν hr hU hPK
      (unitaryTorusParameter ν e z) A.val.obj
      (q ((unitaryOrbitRepresentativeBaseEquiv ν π A).symm
        (unitaryOrbitParameterRepresentative ν A.val e z))) =
    productCompactBaseChangeEquiv ν h K hP hK hν hr
      (unitaryTorusParameter ν e z₀) a (R (e.symm (z * z₀)))
  rw [map_mul]
  let C : UnitaryOrbitRepresentative ν π :=
    ⟨IrreducibleAdmissibleRep.twist
      (unitaryUnramifiedInclusion ν (e.symm z * e.symm z₀)).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν
        (unitaryUnramifiedInclusion ν (e.symm z * e.symm z₀))) π,
      e.symm z * e.symm z₀, rfl⟩
  let B := (unitaryOrbitRepresentativeBaseEquiv ν π A).symm
    (unitaryOrbitParameterRepresentative ν A.val e z)
  change productInducedCompactEquiv ν h K hP hK hν hr hU hPK
      (unitaryTorusParameter ν e z) A.val.obj (q B) =
    productCompactBaseChangeEquiv ν h K hP hK hν hr
      (unitaryTorusParameter ν e z₀) a
      (productInducedCompactEquiv ν h K hP hK hν hr hU hPK
        (unitaryTorusParameter ν e z * unitaryTorusParameter ν e z₀) π.obj (q C))
  rw [hq C B (productBaseTwistEquiv ν
    (unitaryTorusParameter ν e z₀) (unitaryTorusParameter ν e z) a)]
  exact productInducedCompactBaseChange ν h K hP hK hν hr hU hPK
    (unitaryTorusParameter ν e z₀) (unitaryTorusParameter ν e z) a _

variable [Fintype J]

/-- Coherence and finite scalar-smooth compact pullback are preserved and
reflected by the actual-object reindexing. -/
theorem productInducedOrbitBaseEquiv_smooth_iff
    (q : ProductInducedOrbitSections ν π h hU) :
    productInducedOrbitBaseEquiv ν π A h hU q ∈
        productInducedSmoothOrbitSections ν A.val e h hU K hP hK hν hr hPK ↔
      q ∈ productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK := by
  change ((_ ∈ coherentProductInducedOrbitSections ν A.val h hU) ∧
      productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK A.val.obj
        (productInducedOrbitPullback ν A.val e h hU
          (productInducedOrbitBaseEquiv ν π A h hU q)) ∈
        finiteSmoothFamilies J (ProductInducedCompactPicture h K A.val.obj)) ↔
    ((q ∈ coherentProductInducedOrbitSections ν π h hU) ∧
      productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
        (productInducedOrbitPullback ν π e h hU q) ∈
        finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj))
  rw [productInducedOrbitBaseEquiv_coherent_iff ν π A h hU q]
  apply and_congr_right
  intro hq
  let z₀ := unitaryOrbitRepresentativeParameter ν π e A
  let a := unitaryOrbitRepresentativeEquiv ν π e A
  have hsquare :
      productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK A.val.obj
        (productInducedOrbitPullback ν A.val e h hU
          (productInducedOrbitBaseEquiv ν π A h hU q)) =
      fun z => productCompactBaseChangeEquiv ν h K hP hK hν hr
        (unitaryTorusParameter ν e z₀) a
        (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
          (productInducedOrbitPullback ν π e h hU q) (z * z₀)) :=
    funext (productInducedOrbitCompactPullback_baseChange ν π A h hU e
      K hP hK hν hr hPK q hq z₀ a)
  rw [hsquare]
  exact (mem_finiteSmoothFamilies_linearEquiv_iff _
    (productCompactBaseChangeEquiv ν h K hP hK hν hr
      (unitaryTorusParameter ν e z₀) a).toLinearEquiv).trans
    (mem_finiteSmoothFamilies_mul_const_iff _ z₀)

/-- The comparison of smooth orbit sections changes only orbit-membership
witnesses. It preserves every value in every actual inducing fiber. -/
def productInducedSmoothOrbitBaseEquiv :
    productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK ≃ₗ[ℂ]
      productInducedSmoothOrbitSections ν A.val e h hU K hP hK hν hr hPK where
  toFun q := ⟨productInducedOrbitBaseEquiv ν π A h hU q.val,
    (productInducedOrbitBaseEquiv_smooth_iff ν π A h hU e K hP hK hν hr hPK _).mpr
      q.property⟩
  invFun q := ⟨(productInducedOrbitBaseEquiv ν π A h hU).symm q.val,
    (productInducedOrbitBaseEquiv_smooth_iff ν π A h hU e K hP hK hν hr hPK _).mp
      (by simpa only [LinearEquiv.apply_symm_apply] using q.property)⟩
  left_inv q := Subtype.ext
    ((productInducedOrbitBaseEquiv ν π A h hU).symm_apply_apply q.val)
  right_inv q := Subtype.ext
    ((productInducedOrbitBaseEquiv ν π A h hU).apply_symm_apply q.val)
  map_add' q r := Subtype.ext
    ((productInducedOrbitBaseEquiv ν π A h hU).map_add q.val r.val)
  map_smul' c q := Subtype.ext
    ((productInducedOrbitBaseEquiv ν π A h hU).map_smul c q.val)

@[simp]
theorem productInducedSmoothOrbitBaseEquiv_apply
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (B : UnitaryOrbitRepresentative ν A.val) :
    (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK q).val B =
      q.val ((unitaryOrbitRepresentativeBaseEquiv ν π A).symm B) := rfl

@[simp]
theorem productInducedSmoothOrbitBaseEquiv_apply_representative
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (B : UnitaryOrbitRepresentative ν π) :
    (productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK q).val
        (unitaryOrbitRepresentativeBaseEquiv ν π A B) = q.val B := rfl

@[simp]
theorem productInducedSmoothOrbitBaseEquiv_symm_apply
    (q : productInducedSmoothOrbitSections ν A.val e h hU K hP hK hν hr hPK)
    (B : UnitaryOrbitRepresentative ν π) :
    ((productInducedSmoothOrbitBaseEquiv ν π A h hU e K hP hK hν hr hPK).symm q).val B =
      q.val (unitaryOrbitRepresentativeBaseEquiv ν π A B) := rfl

end Langlands.Plancherel
