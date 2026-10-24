import Langlands.ClassField.Global.TotalIdeleInvariantFamily
import Langlands.Global.AdelicFunctoriality.FinitePlaceDegreeTransfer

/-! # Finite local degree transfer and conditional total invariant tower laws -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)

/-- The remaining finite-place choice law, expressed on actual idele cohomology. -/
def FiniteIdeleInvariantPlaceIndependent : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E] [IsGalois F E] (v : HeightOneSpectrum (𝓞 F))
    (w z : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    [z.asIdeal.LiesOver v.asIdeal] (c : relativeIdeleCohomology F E 2),
    finiteIdeleInvariant I v w c = finiteIdeleInvariant I v z c

/-- The remaining finite local restriction law uses the same upper place on both sides. -/
def FiniteIdeleInvariantRestriction : Prop :=
  ∀ (F K E : Type u) [Field F] [Field K] [Field E]
    [NumberField F] [NumberField K] [NumberField E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
    [IsGalois F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    [q.asIdeal.LiesOver w.asIdeal] [q.asIdeal.LiesOver v.asIdeal],
    let := IsGalois.tower_top_of_isGalois F K E
    ∀ c : relativeIdeleCohomology F E 2,
      finiteIdeleInvariant I w q (relativeIdeleRestriction F K E 2 c) =
        Module.finrank (v.adicCompletion F) (w.adicCompletion K) • finiteIdeleInvariant I v q c

variable (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)

section Sum

variable {F E : Type u} [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- The existing finite sum is the sum of the existing finite-support vector. -/
theorem finiteIdeleInvariantSum_eq_finitePlaceSum
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (c : relativeIdeleCohomology F E 2) :
    finiteIdeleInvariantSum I hI wf c =
      finitePlaceSum (finiteIdeleInvariantVector I hI wf c) := by
  rw [finitePlaceSum_eq_finsum]
  rfl

/-- Finite-place independence gives equality of the entire finite-support vectors. -/
theorem finiteIdeleInvariantVector_eq_of_placeIndependent
    (hchoice : FiniteIdeleInvariantPlaceIndependent I)
    (wf wf' : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (c : relativeIdeleCohomology F E 2) :
    finiteIdeleInvariantVector I hI wf c = finiteIdeleInvariantVector I hI wf' c := by
  ext v
  have := (wf v).2
  have := (wf' v).2
  exact hchoice F E v (wf v).1 (wf' v).1 c

/-- The finite sum is independent of choices when the coordinate choice law is supplied. -/
theorem finiteIdeleInvariantSum_eq_of_placeIndependent
    (hchoice : FiniteIdeleInvariantPlaceIndependent I)
    (wf wf' : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (c : relativeIdeleCohomology F E 2) :
    finiteIdeleInvariantSum I hI wf c = finiteIdeleInvariantSum I hI wf' c := by
  rw [finiteIdeleInvariantSum_eq_finitePlaceSum, finiteIdeleInvariantSum_eq_finitePlaceSum,
    finiteIdeleInvariantVector_eq_of_placeIndependent I hI hchoice wf wf']

/-- The total family agrees with every explicit total sum under finite-place independence. -/
theorem totalIdeleInvariantMaps_eq_of_placeIndependent
    (hchoice : FiniteIdeleInvariantPlaceIndependent I)
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v) :
    totalIdeleInvariantMaps I hI F E = totalIdeleInvariant I hI wf wi := by
  ext c
  change finiteIdeleInvariantSum I hI (placeAbove E) c +
      canonicalArchimedeanIdeleInvariantSum c =
    finiteIdeleInvariantSum I hI wf c + archimedeanIdeleInvariantSum wi c
  rw [finiteIdeleInvariantSum_eq_of_placeIndependent I hI hchoice (placeAbove E) wf,
    canonicalArchimedeanIdeleInvariantSum_eq wi]

end Sum

section Transfer

variable {F K E : Type u} [Field F] [Field K] [Field E]
  [NumberField F] [NumberField K] [NumberField E]
  [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E] [IsGalois F E]

/-- Transfer the finite invariant vector from `F` to `K`, weighted by actual completed degrees. -/
def finiteIdeleInvariantBaseTransfer
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v) :
    relativeIdeleCohomology F E 2 →+ (HeightOneSpectrum (𝓞 K) →₀ RationalModIntegers) :=
  (finitePlaceDegreeTransfer (L := K)).comp (finiteIdeleInvariantVector I hI wf)

omit [Algebra K E] [IsScalarTower F K E] in
/-- The transferred vector has total sum equal to the global degree times the original sum. -/
theorem finitePlaceSum_finiteIdeleInvariantBaseTransfer
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (c : relativeIdeleCohomology F E 2) :
    finitePlaceSum (finiteIdeleInvariantBaseTransfer I hI (K := K) wf c) =
      Module.finrank F K • finiteIdeleInvariantSum I hI wf c := by
  change finitePlaceSum (finitePlaceDegreeTransfer (L := K)
    (finiteIdeleInvariantVector I hI wf c)) = _
  rw [finitePlaceSum_degreeTransfer, finiteIdeleInvariantSum_eq_finitePlaceSum]

/-- With the two local coordinate laws, restriction is exactly degree-weighted transfer. -/
theorem finiteIdeleInvariantVector_restriction_eq_transfer
    (hchoice : FiniteIdeleInvariantPlaceIndependent I)
    (hres : FiniteIdeleInvariantRestriction I)
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wk : ∀ w : HeightOneSpectrum (𝓞 K), FinitePlacesAbove E w)
    (c : relativeIdeleCohomology F E 2) :
    let := IsGalois.tower_top_of_isGalois F K E
    finiteIdeleInvariantVector I hI wk (relativeIdeleRestriction F K E 2 c) =
      finiteIdeleInvariantBaseTransfer I hI (K := K) wf c := by
  have := IsGalois.tower_top_of_isGalois F K E
  ext w
  have := (wk w).2
  have : (wk w).1.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal :=
    Ideal.LiesOver.trans (wk w).1.asIdeal w.asIdeal (w.under (𝓞 F)).asIdeal
  have := (wf (w.under (𝓞 F))).2
  change finiteIdeleInvariant I w (wk w).1 (relativeIdeleRestriction F K E 2 c) =
    finitePlaceDegreeTransfer (L := K) (finiteIdeleInvariantVector I hI wf c) w
  rw [finitePlaceDegreeTransfer_apply]
  change _ = Module.finrank ((w.under (𝓞 F)).adicCompletion F) (w.adicCompletion K) •
    finiteIdeleInvariant I (w.under (𝓞 F)) (wf (w.under (𝓞 F))).1 c
  rw [hres F K E (w.under (𝓞 F)) w (wk w).1 c,
    hchoice F E (w.under (𝓞 F)) (wk w).1 (wf (w.under (𝓞 F))).1 c]

/-- The finite restriction sum law follows from local restriction and place independence. -/
theorem finiteIdeleInvariantSum_relativeIdeleRestriction
    (hchoice : FiniteIdeleInvariantPlaceIndependent I)
    (hres : FiniteIdeleInvariantRestriction I)
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wk : ∀ w : HeightOneSpectrum (𝓞 K), FinitePlacesAbove E w)
    (c : relativeIdeleCohomology F E 2) :
    let := IsGalois.tower_top_of_isGalois F K E
    finiteIdeleInvariantSum I hI wk (relativeIdeleRestriction F K E 2 c) =
      Module.finrank F K • finiteIdeleInvariantSum I hI wf c := by
  have := IsGalois.tower_top_of_isGalois F K E
  dsimp only
  rw [finiteIdeleInvariantSum_eq_finitePlaceSum I hI wk,
    finiteIdeleInvariantVector_restriction_eq_transfer I hI hchoice hres wf wk,
    finitePlaceSum_finiteIdeleInvariantBaseTransfer]

end Transfer

/-- Arbitrary finite upper-place choices are allowed in inflation once place independence holds. -/
theorem finiteIdeleInvariantSum_inflation_of_placeIndependent
    (hchoice : FiniteIdeleInvariantPlaceIndependent I)
    (hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility)
    {F E L : Type u} [Field F] [Field E] [Field L]
    [NumberField F] [NumberField E] [NumberField L]
    [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [IsGalois F E] [IsGalois F L]
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wl : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove L v)
    (c : relativeIdeleCohomology F E 2) :
    finiteIdeleInvariantSum I hI wl (relativeIdeleInflation F E L 2 c) =
      finiteIdeleInvariantSum I hI wf c := by
  rw [finiteIdeleInvariantSum_eq_of_placeIndependent I hI hchoice wl
    (Reciprocity.liftFinitePlaces L wf)]
  exact finiteIdeleInvariantSum_relativeIdeleInflation I hI hInf wf
    (Reciprocity.liftFinitePlaces L wf) (fun v => (placeAbove L (wf v).1).2) c

/-- Finite-place independence and local inflation imply the total-family inflation law. -/
theorem totalIdeleInvariantMaps_inflation
    (hchoice : FiniteIdeleInvariantPlaceIndependent I)
    (hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility) :
    (totalIdeleInvariantMaps I hI).InflationCompatible := by
  intro F E L _ _ _ _ _ _ _ _ _ _ _ _ c
  change finiteIdeleInvariantSum I hI (placeAbove L) (relativeIdeleInflation F E L 2 c) +
      canonicalArchimedeanIdeleInvariantSum (relativeIdeleInflation F E L 2 c) =
    finiteIdeleInvariantSum I hI (placeAbove E) c + canonicalArchimedeanIdeleInvariantSum c
  rw [finiteIdeleInvariantSum_inflation_of_placeIndependent I hI hchoice hInf,
    canonicalArchimedeanIdeleInvariantSum_relativeIdeleInflation]

/-- The two finite local coordinate laws imply the total-family restriction law. -/
theorem totalIdeleInvariantMaps_restriction
    (hchoice : FiniteIdeleInvariantPlaceIndependent I)
    (hres : FiniteIdeleInvariantRestriction I) :
    (totalIdeleInvariantMaps I hI).RestrictionCompatible := by
  intro F K E _ _ _ _ _ _ _ _ _ _ _
  dsimp only
  have := IsGalois.tower_top_of_isGalois F K E
  intro c
  change finiteIdeleInvariantSum I hI (placeAbove E) (relativeIdeleRestriction F K E 2 c) +
      canonicalArchimedeanIdeleInvariantSum (relativeIdeleRestriction F K E 2 c) =
    Module.finrank F K • (finiteIdeleInvariantSum I hI (placeAbove E) c +
      canonicalArchimedeanIdeleInvariantSum c)
  rw [finiteIdeleInvariantSum_relativeIdeleRestriction I hI hchoice hres,
    canonicalArchimedeanIdeleInvariantSum_relativeIdeleRestriction, smul_add]

end Langlands.ClassField.Global
