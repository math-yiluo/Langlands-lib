import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Filtration.MultiplicityAdditivityProof

/-! Canonical composition-factor sums and their descent through exact K0. -/

noncomputable section

open CategoryTheory
open Langlands.VirtualRepresentation
open scoped BigOperators

universe uR uG uV

namespace Langlands.SmoothRep.IrreducibleGrothendieckProof

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  {A B : SmoothRep.{uR, uG, uV} k G} {n m : ℕ}

/-- Bundle the existing actual graded representation with inherited smoothness. -/
def gradedSmooth (s : ObjectRepFiltration A.obj n) (i : Fin n) :
    SmoothRep.{uR, uG, uV} k G :=
  ⟨s.gradedRepresentation i,
    Langlands.isSmooth_of_surjective (s.gradedProjection i).hom
      (s.gradedProjection_surjective i)
      (subrepresentation A (s.subrepresentation i.succ)).isSmooth⟩

/-- The finite integral sum of genuine labels of a supplied composition series. -/
def seriesClass (s : ObjectRepFiltration A.obj n) (hs : s.HasSimpleFactors) :
    IrreducibleLattice.{uR, uG, uV} k G :=
  ∑ i, generator (irreducibleIsoClass (gradedSmooth s i) (hs i))

/-- A coordinate of this finite sum is the existing actual factor count. -/
theorem seriesClass_apply (s : ObjectRepFiltration A.obj n) (hs : s.HasSimpleFactors)
    (τ : SmoothRep.{uR, uG, uV} k G) (hτ : τ.IsIrreducible) :
    seriesClass s hs (irreducibleIsoClass τ hτ) = (s.factorMultiplicity τ.obj : ℤ) := by
  classical
  simp only [seriesClass, Finsupp.finsetSum_apply, generator, Finsupp.single_apply]
  rw [ObjectRepFiltration.factorMultiplicity, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi :
      irreducibleIsoClass (gradedSmooth s i) (hs i) = irreducibleIsoClass τ hτ ↔
        Nonempty ((s.gradedRepresentation i).ρ.Equiv τ.obj.ρ) :=
    irreducibleIsoClass_eq_iff_nonempty_equiv (hs i) hτ
  rw [hi]
  split_ifs <;> rfl

/-- Jordan–Hölder independence identifies the whole finite label sum. -/
theorem seriesClass_eq (s : ObjectRepFiltration A.obj n)
    (t : ObjectRepFiltration A.obj m) (hs : s.HasSimpleFactors) (ht : t.HasSimpleFactors) :
    seriesClass s hs = seriesClass t ht := by
  apply Finsupp.ext
  intro c
  obtain ⟨τ, hτ, rfl⟩ := IrreducibleIsoClass.exists_eq c
  rw [seriesClass_apply s hs τ hτ, seriesClass_apply t ht τ hτ]
  exact congrArg (fun x : ℕ => (x : ℤ))
    (jordanHolderMultiplicityIndependence k G A.obj τ.obj n m s t hs ht)

/-- Equivariant isomorphisms identify the whole finite label sum. -/
theorem seriesClass_eq_of_equiv (s : ObjectRepFiltration A.obj n)
    (t : ObjectRepFiltration B.obj m) (hs : s.HasSimpleFactors) (ht : t.HasSimpleFactors)
    (e : A.representation.Equiv B.representation) :
    seriesClass s hs = seriesClass t ht := by
  apply Finsupp.ext
  intro c
  obtain ⟨τ, hτ, rfl⟩ := IrreducibleIsoClass.exists_eq c
  rw [seriesClass_apply s hs τ hτ, seriesClass_apply t ht τ hτ]
  apply congrArg (fun x : ℕ => (x : ℤ))
  have hs' : HasJordanHolderMultiplicity B.obj τ.obj (s.factorMultiplicity τ.obj) :=
    (equivJordanHolderMultiplicityTransport k G A.obj B.obj τ.obj τ.obj e
      (Representation.Equiv.refl _) _).mp ⟨n, s, hs, rfl⟩
  exact HasJordanHolderMultiplicity.unique hs' ⟨m, t, ht, rfl⟩

/-- Choose an actual finite composition series, keeping its original carrier universe. -/
def chosenSeries (A : FiniteLengthObject.{uR, uG, uV} k G) :
    Σ n, {s : ObjectRepFiltration A.val.obj n // s.HasSimpleFactors} :=
  Classical.choice (by
    obtain ⟨n, s, hs⟩ := MultiplicityAdditivityProof.exists_series A.property
    exact ⟨⟨n, s, hs⟩⟩)

/-- The finite sum of irreducible labels of an actual finite-length object. -/
def compositionFactors (A : FiniteLengthObject.{uR, uG, uV} k G) :
    IrreducibleLattice.{uR, uG, uV} k G :=
  seriesClass (chosenSeries A).2.val (chosenSeries A).2.property

/-- Its defining choice agrees with every actual composition series. -/
theorem compositionFactors_eq_series (A : FiniteLengthObject.{uR, uG, uV} k G)
    (s : ObjectRepFiltration A.val.obj n) (hs : s.HasSimpleFactors) :
    compositionFactors A = seriesClass s hs :=
  seriesClass_eq _ _ _ hs

/-- The natural-valued multiplicity attached to the chosen actual series. -/
def compositionMultiplicity (A : FiniteLengthObject.{uR, uG, uV} k G)
    (τ : SmoothRep.{uR, uG, uV} k G) : ℕ :=
  (chosenSeries A).2.val.factorMultiplicity τ.obj

/-- The chosen count has the published actual Jordan–Hölder witness. -/
theorem compositionMultiplicity_witness (A : FiniteLengthObject.{uR, uG, uV} k G)
    (τ : SmoothRep.{uR, uG, uV} k G) :
    HasJordanHolderMultiplicity A.val.obj τ.obj (compositionMultiplicity A τ) :=
  ⟨(chosenSeries A).1, (chosenSeries A).2.val, (chosenSeries A).2.property, rfl⟩

/-- The integral coordinate is the chosen natural count. -/
theorem compositionFactors_apply (A : FiniteLengthObject.{uR, uG, uV} k G)
    (τ : SmoothRep.{uR, uG, uV} k G) (hτ : τ.IsIrreducible) :
    compositionFactors A (irreducibleIsoClass τ hτ) = (compositionMultiplicity A τ : ℤ) :=
  seriesClass_apply _ _ τ hτ

/-- Actual representation isomorphisms preserve the canonical finite factor sum. -/
theorem compositionFactors_eq_of_equiv
    (A B : FiniteLengthObject.{uR, uG, uV} k G)
    (e : A.val.representation.Equiv B.val.representation) :
    compositionFactors A = compositionFactors B :=
  seriesClass_eq_of_equiv _ _ _ _ e

/-- Every actual short exact sequence gives additive canonical factor sums. -/
theorem compositionFactors_shortExact
    (A B C : FiniteLengthObject.{uR, uG, uV} k G)
    (f : A.val.representation.IntertwiningMap B.val.representation)
    (g : B.val.representation.IntertwiningMap C.val.representation)
    (h : IsShortExact f g) :
    compositionFactors B = compositionFactors A + compositionFactors C := by
  apply Finsupp.ext
  intro c
  obtain ⟨τ, hτ, rfl⟩ := IrreducibleIsoClass.exists_eq c
  rw [Finsupp.add_apply, compositionFactors_apply B τ hτ,
    compositionFactors_apply A τ hτ, compositionFactors_apply C τ hτ, ← Nat.cast_add]
  apply congrArg (fun x : ℕ => (x : ℤ))
  have hadd : HasJordanHolderMultiplicity B.val.obj τ.obj
      (compositionMultiplicity A τ + compositionMultiplicity C τ) :=
    jordanHolderShortExactAdditivity k G A.val.obj B.val.obj C.val.obj τ.obj
      f g h.1 h.2.1 h.2.2 _ _
      (compositionMultiplicity_witness A τ) (compositionMultiplicity_witness C τ)
  exact HasJordanHolderMultiplicity.unique (compositionMultiplicity_witness B τ) hadd

/-- The only graded piece of the one-step filtration is the original representation. -/
theorem oneStep_graded_equiv (A : SmoothRep.{uR, uG, uV} k G) :
    Nonempty (((LengthTwo.oneStep A.representation).gradedRepresentation 0).ρ.Equiv
      A.representation) := by
  let f : (⊤ : Subrepresentation A.representation).toRepresentation.IntertwiningMap
      A.representation :=
    { toLinearMap := (⊤ : Subrepresentation A.representation).toSubmodule.subtype
      isIntertwining' _ := rfl }
  apply MultiplicityAdditivityProof.quotient_equiv_of_surjective ⊥ ⊤ f
  · intro x
    change (x : A.obj) = 0 ↔ (x : A.obj) = 0
    rfl
  · intro a
    exact ⟨⟨a, Submodule.mem_top⟩, rfl⟩

/-- An actual irreducible object has the single expected irreducible label. -/
theorem compositionFactors_irreducible (A : SmoothRep.{uR, uG, uV} k G)
    (hA : A.IsIrreducible) (hLength : A.HasFiniteLength) :
    compositionFactors ⟨A, hLength⟩ = generator (irreducibleIsoClass A hA) := by
  obtain ⟨e⟩ := oneStep_graded_equiv A
  have hs : (LengthTwo.oneStep A.representation).HasSimpleFactors := by
    intro i
    fin_cases i
    exact LengthTwo.isIrreducible_of_equiv e.symm hA
  rw [compositionFactors_eq_series ⟨A, hLength⟩ _ hs]
  simp only [seriesClass, Fin.sum_univ_one]
  congr 1
  exact irreducibleIsoClass_eq_of_equiv (hs 0) hA e

/-- The same finite factor sum on genuine finite-length isomorphism classes. -/
def classFactors :
    FiniteLengthIsoClass.{uR, uG, uV} k G → IrreducibleLattice.{uR, uG, uV} k G :=
  Quotient.lift compositionFactors (by
    intro A B h
    obtain ⟨e⟩ := h
    exact compositionFactors_eq_of_equiv A B (equivOfIso e))

@[simp] theorem classFactors_finiteLengthIsoClass
    (A : FiniteLengthObject.{uR, uG, uV} k G) :
    classFactors (finiteLengthIsoClass A) = compositionFactors A := rfl

/-- The class function annihilates every defining exact-K0 relation. -/
theorem classFactors_isExactAdditive :
    FiniteLengthGrothendieckGroup.IsExactAdditive k G
      (classFactors : FiniteLengthIsoClass.{uR, uG, uV} k G →
        IrreducibleLattice.{uR, uG, uV} k G) :=
  fun A B C f g h => compositionFactors_shortExact A B C f g h

/-- The canonical integer-linear factor-count map from the exact quotient. -/
def factorMap :
    FiniteLengthGrothendieckGroup.{uR, uG, uV} k G →ₗ[ℤ]
      IrreducibleLattice.{uR, uG, uV} k G :=
  FiniteLengthGrothendieckGroup.lift k G classFactors classFactors_isExactAdditive

@[simp] theorem factorMap_ofRepresentation (A : SmoothRep.{uR, uG, uV} k G)
    (hA : A.HasFiniteLength) :
    factorMap (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      compositionFactors ⟨A, hA⟩ :=
  FiniteLengthGrothendieckGroup.lift_ofRepresentation k G
    classFactors classFactors_isExactAdditive A hA

end Langlands.SmoothRep.IrreducibleGrothendieckProof
