import Langlands.Representation.Aubert.General.JacquetCokernelTransport
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! Actual ambient and Levi cokernel functors on full smooth subcategories. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

section ConjugationExactness

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Actual conjugation retains the underlying linear maps of every short exact sequence. -/
theorem conjugationFunctor_mapsShortExactIntertwiners (g : G) {L N : Subgroup G}
    (hLN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ L) :
    Derivative.Mirabolic.MapsShortExactIntertwiners (conjugationFunctor.{uG, uV} g hLN) := by
  intro A B C i q hi hq hex
  exact ⟨hi, hex, hq⟩

end ConjugationExactness

namespace StandardComplex

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (h : ∀ s, IsSemidirectDecomposition (P s) (M s) (U s))
variable (hclosed : ∀ s, IsClosed (U s : Set G))
variable (hδ : ∀ s, IsUnimodularModulus (U s) (hclosed s))
variable (hP : Monotone P) (hU : Antitone U)

/-- The ambient side of the associated-Levi comparison, in its literal
full-subcategory functor form, is naturally the mapped differential cokernel. -/
def jacquetSharpCokernelIsoOn
    (C : ObjectProperty (SmoothRep.{0, uG, max uI uG uV} ℂ G))
    (I : Finset ι) (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (U I)) :
    (C.ι ⋙ sharpFunctor.{uI, uG, max uI uV} P M U h hclosed hδ hP hU I ⋙
      jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I)) ≅
    (C.ι ⋙ SmoothNatCokernel.functor (Functor.whiskerRight
      (incomingDifferentialNat.{uI, uG, max uI uV} P M U h hclosed hδ hP hU
        (Complex.terminalDegree I))
      (jacquetFunctor.{uG, max uI uG uV} (h I) (hclosed I)))) :=
  Functor.isoWhiskerLeft C.ι (jacquetSharpCokernelIso.{uI, uG, max uI uV}
    P M U h hclosed hδ hP hU I hUc).symm

end StandardComplex

namespace LeviComplex

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (hclosed : ∀ K, IsClosed (U K : Set G))
variable (hP : Monotone P) (hU : Antitone U)
variable (J : Finset ι) (hM : IsClosed (M J : Set G))
variable (hJ : ∀ K : Finset J,
  IsSemidirectDecomposition (family (M J) P J K)
    (family (M J) M J K) (family (M J) U J K))
variable (hJδ : letI := hM.locallyCompactSpace
  ∀ K : Finset J, IsUnimodularModulus (family (M J) U J K)
    ((hclosed (leviIndex J K)).preimage continuous_subtype_val))

/-- The actual incoming natural differential for the standard complex inside `M J`. -/
abbrev incomingDifferentialNat (K : Finset J) :=
  letI := hM.locallyCompactSpace
  StandardComplex.incomingDifferentialNat.{uI, uG, max uI uV}
    (family (M J) P J) (family (M J) M J) (family (M J) U J) hJ
    (fun L => (hclosed (leviIndex J L)).preimage continuous_subtype_val) hJδ
    (family_monotone (M J) hP J) (family_antitone (M J) hU J)
    (Complex.terminalDegree K)

/-- The original natural retained quotient projection inside `M J`. -/
abbrev sharpProjectionNat (K : Finset J) :=
  letI := hM.locallyCompactSpace
  StandardComplex.sharpProjectionNat.{uI, uG, max uI uV}
    (family (M J) P J) (family (M J) M J) (family (M J) U J) hJ
    (fun L => (hclosed (leviIndex J L)).preimage continuous_subtype_val) hJδ
    (family_monotone (M J) hP J) (family_antitone (M J) hU J) K

variable (g : G) {N : Subgroup G}
variable (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M J)

/-- The actual Levi sharp functor followed by the specified conjugation is
the natural cokernel of its conjugated incoming differential. -/
def conjugationSharpCokernelIso (K : Finset J) :
    SmoothNatCokernel.functor (Functor.whiskerRight
      (incomingDifferentialNat.{uI, uG, uV} P M U hclosed hP hU J hM hJ hJδ K)
      (conjugationFunctor.{uG, max uI uG uV} g hMN)) ≅
    (sharpFunctor.{uI, uG, uV} P M U hclosed hP hU J hM hJ hJδ K ⋙
      conjugationFunctor.{uG, max uI uG uV} g hMN) := by
  letI := hM.locallyCompactSpace
  exact StandardComplex.sharpCokernelIso
    (family (M J) P J) (family (M J) M J) (family (M J) U J) hJ
    (fun L => (hclosed (leviIndex J L)).preimage continuous_subtype_val) hJδ
    (family_monotone (M J) hP J) (family_antitone (M J) hU J)
    (conjugationFunctor g hMN) (conjugationFunctor_mapsShortExactIntertwiners g hMN) K

omit [Fintype ι] in
/-- This comparison preserves the actual conjugated Levi quotient projection. -/
theorem conjugationSharpCokernelIso_projection_nat (K : Finset J) :
    SmoothNatCokernel.projection (Functor.whiskerRight
      (incomingDifferentialNat.{uI, uG, uV} P M U hclosed hP hU J hM hJ hJδ K)
      (conjugationFunctor.{uG, max uI uG uV} g hMN)) ≫
      (conjugationSharpCokernelIso P M U hclosed hP hU J hM hJ hJδ g hMN K).hom =
    Functor.whiskerRight
      (sharpProjectionNat.{uI, uG, uV} P M U hclosed hP hU J hM hJ hJδ K)
      (conjugationFunctor.{uG, max uI uG uV} g hMN) := by
  let := hM.locallyCompactSpace
  exact StandardComplex.sharpCokernelIso_projection_nat
    (family (M J) P J) (family (M J) M J) (family (M J) U J) hJ
    (fun L => (hclosed (leviIndex J L)).preimage continuous_subtype_val) hJδ
    (family_monotone (M J) hP J) (family_antitone (M J) hU J)
    (conjugationFunctor g hMN) (conjugationFunctor_mapsShortExactIntertwiners g hMN) K

/-- The associated-Levi side in the literal full-subcategory functor form.
Every smooth full subcategory is allowed, including the published support one. -/
def jacquetConjugationSharpCokernelIsoOn
    (C : ObjectProperty (SmoothRep.{0, uG, max uI uG uV} ℂ G))
    (h : IsSemidirectDecomposition (P J) (M J) (U J)) :
    (C.ι ⋙ jacquetFunctor.{uG, max uI uG uV} h (hclosed J) ⋙
      sharpFunctor.{uI, uG, uV} P M U hclosed hP hU J hM hJ hJδ Finset.univ ⋙
      conjugationFunctor.{uG, max uI uG uV} g hMN) ≅
    (C.ι ⋙ jacquetFunctor.{uG, max uI uG uV} h (hclosed J) ⋙
      SmoothNatCokernel.functor (Functor.whiskerRight
        (incomingDifferentialNat.{uI, uG, uV} P M U hclosed hP hU J hM hJ hJδ Finset.univ)
        (conjugationFunctor.{uG, max uI uG uV} g hMN))) :=
  Functor.isoWhiskerLeft C.ι
    (Functor.isoWhiskerLeft (jacquetFunctor.{uG, max uI uG uV} h (hclosed J))
      (conjugationSharpCokernelIso P M U hclosed hP hU J hM hJ hJδ g hMN Finset.univ).symm)

end LeviComplex

end Langlands.Aubert.General
