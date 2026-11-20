import Langlands.Representation.Plancherel.SmoothFamilyFiniteValues

/-! # Prescribed values at actual representatives of finitely many orbit classes -/

noncomputable section

open CategoryTheory Langlands.Aubert.General Langlands.Induction
open scoped NNReal

namespace Langlands.Plancherel

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  {J : Type uJ} (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

/-- The chosen parameter of an actual representative has that same smooth
representation class. -/
theorem unitaryOrbitRepresentativeParameter_class (A : UnitaryOrbitRepresentative ν π) :
    (Quotient.mk _ (unitaryOrbitParameterRepresentative ν π e
      (unitaryOrbitRepresentativeParameter ν π e A)).val :
        SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) = Quotient.mk _ A.val :=
  Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk
    (SmoothRep.mkIso (unitaryOrbitRepresentativeEquiv ν π e A))⟩

/-- Stabilizer translation preserves the actual class of a parameter
representative. -/
theorem unitaryOrbitParameterRepresentative_class_stabilizer
    (z : J → Circle) (s : unitaryClassTwistStabilizer ν (Quotient.mk _ π)) :
    (Quotient.mk _ (unitaryOrbitParameterRepresentative ν π e
      (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s)).val :
        SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) =
      Quotient.mk _ (unitaryOrbitParameterRepresentative ν π e z).val := by
  symm
  exact Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk
    (SmoothRep.mkIso (unitaryTorusFiberEquiv ν e π s z))⟩

variable [LocallyCompactSpace G] {P U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  [Fintype J]

/-- Evaluation on an actual inducing representative, using the existing
coherent smooth orbit-section space. -/
def productInducedSmoothOrbitEvaluation (A : UnitaryOrbitRepresentative ν π) :
    productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK →ₗ[ℂ]
      productInducedCoefficientObject h hU A.val.obj where
  toFun q := q.val A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Finite (unitaryClassTwistStabilizer ν (Quotient.mk _ π))]

/-- At an arbitrary actual representative, any actual product-induced value
can be prescribed while forcing zero at finitely many representatives in
other smooth isomorphism classes. No torus parameters are supplied by the
caller, and the output lies in the existing coherent smooth section space. -/
theorem exists_productInducedSmoothOrbitSection_finiteClasses
    (A₀ : UnitaryOrbitRepresentative ν π)
    (Φ : Set (UnitaryOrbitRepresentative ν π)) (hΦ : Φ.Finite)
    (hclasses : ∀ A ∈ Φ,
      (Quotient.mk _ A.val : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) ≠
        Quotient.mk _ A₀.val)
    (w : productInducedCoefficientObject h hU A₀.val.obj) :
    ∃ q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK,
      productInducedSmoothOrbitEvaluation ν π e h hU K hP hK hν hr hPK A₀ q = w ∧
        ∀ A ∈ Φ, productInducedSmoothOrbitEvaluation ν π e h hU K hP hK hν hr hPK A q = 0 := by
  let z := unitaryOrbitRepresentativeParameter ν π e
  let Z := z '' Φ
  have hZ : Z.Finite := hΦ.image z
  have hsep : ∀ y ∈ Z, ∀ s : unitaryClassTwistStabilizer ν (Quotient.mk _ π),
      y * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s ≠ z A₀ := by
    rintro _ ⟨A, hA, rfl⟩ s he
    have hc := unitaryOrbitParameterRepresentative_class_stabilizer ν π e (z A) s
    rw [he] at hc
    apply hclasses A hA
    exact (unitaryOrbitRepresentativeParameter_class ν π e A).symm.trans
      (hc.symm.trans (unitaryOrbitRepresentativeParameter_class ν π e A₀))
  let E := productInducedCoefficientTransport h hU (unitaryOrbitRepresentativeEquiv ν π e A₀)
  obtain ⟨q, hq, hq0, hqZ⟩ :=
    exists_mem_productInducedSmoothOrbitSections_finiteValues ν π e h hU K hP hK hν hr hPK
      Z hZ (z A₀) hsep (E.symm w)
  refine ⟨⟨q, hq⟩, ?_, ?_⟩
  · change q A₀ = w
    rw [hq.1 _ A₀ (unitaryOrbitRepresentativeEquiv ν π e A₀), hq0]
    exact E.apply_symm_apply w
  · intro A hA
    change q A = 0
    rw [hq.1 _ A (unitaryOrbitRepresentativeEquiv ν π e A),
      hqZ (z A) ⟨A, hA, rfl⟩, map_zero]

end Langlands.Plancherel
