import Langlands.Representation.Classification.PositiveTotalHeadCriterionStatement
import Langlands.Representation.Classification.MultiplicityOneConstituentProof
import Langlands.Representation.Classification.HeadQuotientCriterionProof
import Langlands.Representation.Filtration.MultiplicityAdditivityProof
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Basic.Complex.Basic

/-!
# Strong irreducible heads from a positive total count

The proof reuses the actual product construction and split image maps from the
published multiplicity-one argument of Workers 495 and 502 for any positive total.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory

universe uG uH uV uW uT

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Monoid H]

/-- A positive total count and quotient-image counts at least that total
force equality of all actual irreducible quotient kernels. -/
theorem positiveTotalHeadCore
    (F : SmoothRep.{0, uG, uV} ℂ G ⥤ Rep.{uW} ℂ H)
    [F.Additive] [F.PreservesEpimorphisms]
    (A : SmoothRep.{0, uG, uV} ℂ G) (τ : Rep.{uT} ℂ H) (m : ℕ)
    (hm : 0 < m) (hA : HasJordanHolderMultiplicity (F.obj A) τ m)
    (hex : ∃ (P : SmoothRep.{0, uG, uV} ℂ G), P.IsIrreducible ∧
      ∃ q : A ⟶ P, Function.Surjective (SmoothRep.hom q))
    (hpos : ∀ (P : SmoothRep.{0, uG, uV} ℂ G), P.IsIrreducible →
      ∀ q : A ⟶ P, Function.Surjective (SmoothRep.hom q) →
        ∃ c : ℕ, HasJordanHolderMultiplicity (F.obj P) τ c ∧ m ≤ c) :
    HasIrreducibleHead A.representation := by
  obtain ⟨P, hP, q, hq⟩ := hex
  obtain ⟨mP, hmP, hPpos⟩ := hpos P hP q hq
  refine ⟨P, inferInstance, inferInstance, P.representation,
    hP, SmoothRep.hom q, hq, ?_⟩
  intro W _ _ π hπ q' hq'
  by_contra hne
  let Q : SmoothRep.{0, uG, uV} ℂ G :=
    SmoothRep.of π (isSmooth_of_surjective q' hq' A.isSmooth)
  let qQ : A ⟶ Q := SmoothRep.ofHom q'
  obtain ⟨mQ, hmQ, hQpos⟩ := hpos Q hπ qQ hq'
  let r : A ⟶ smoothProduct Q P :=
    SmoothRep.ofHom (q'.prod (SmoothRep.hom q))
  have hr : Function.Surjective (SmoothRep.hom r) :=
    unequalIrreducibleQuotientKernels G A W P A.representation π P.representation
      hπ hP q' (SmoothRep.hom q) hq' hq hne
  let : Epi r := (SmoothRep.epi_iff_surjective r).mpr hr
  have hFr : Function.Surjective (F.map r).hom :=
    (Rep.epi_iff_surjective (F.map r)).mp inferInstance
  obtain ⟨u, -, hu, -⟩ := mappedProductSplitting F Q P
  let f := u.comp (F.map r).hom
  have hf : Function.Surjective f := hu.comp hFr
  have hprod := jordanHolderProductAdditivity ℂ H (F.obj Q) (F.obj P) τ
    mQ mP hmQ hmP
  have hle := jordanHolderSurjectiveMonotonicity ℂ H (F.obj A)
    (Rep.of ((F.obj Q).ρ.prod (F.obj P).ρ)) τ f hf m (mQ + mP) hA hprod
  omega

/-- The positive-total head criterion with the exact published statement
as its target. -/
theorem positiveTotalHeadCriterion :
    PositiveTotalHeadCriterionStatement.{uG, uH, uV, uW, uT} := by
  intro G _ _ H _ F _ _ A τ m hm hA hex hpos
  exact positiveTotalHeadCore F A τ m hm hA hex hpos

end Langlands.Classification
