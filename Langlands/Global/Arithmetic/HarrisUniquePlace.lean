import Langlands.Global.Arithmetic.HarrisSetup
import Langlands.Global.AdelicFunctoriality.LocalDegree

/-!
# The unique place of an intermediate field above a place with one place above it

If a finite place `v` of `E` has exactly one place of `L` above it, and `E ⊆ E' ⊆ L`,
then `v` also has exactly one place of `E'` above it. In a place datum `P` this place
is `P.v'`.
-/

noncomputable section

namespace Langlands.Global.Harris

open NumberField IsDedekindDomain AdelicFunctoriality LocalFactor.CommonClosure

variable {E E' L : Type*} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]
  [IsScalarTower E E' L]

/-- One place of `L` above `v` forces one place of `E'` above `v`: two places of `E'`
above `v` lie under places of `L` above `v`, which coincide, and each place of `E'`
is the place below any place of `L` over it. -/
theorem finitePlacesAbove_subsingleton (v : FinitePlace E) (h : HasUniquePlaceAbove L v) :
    Subsingleton (FinitePlacesAbove E' v) := by
  constructor
  rintro ⟨u, hu⟩ ⟨u', hu'⟩
  obtain ⟨w, hw⟩ := exists_place_above (L := L) u
  obtain ⟨w', hw'⟩ := exists_place_above (L := L) u'
  have hwv : w.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans w.asIdeal u.asIdeal v.asIdeal
  have hwv' : w'.asIdeal.LiesOver v.asIdeal :=
    Ideal.LiesOver.trans w'.asIdeal u'.asIdeal v.asIdeal
  obtain rfl := h w w' hwv hwv'
  exact Subtype.ext (HeightOneSpectrum.ext ((Ideal.LiesOver.over (P := w.asIdeal)
    (p := u.asIdeal)).trans (Ideal.LiesOver.over (P := w.asIdeal) (p := u'.asIdeal)).symm))

variable {p : ℕ} [Fact p.Prime] {F : PadicField p} {F' : Extension F}

/-- For a place datum `P` with one place of `L` above `P.v`, the place `P.v'` is the
only place of `E'` above `P.v`. -/
abbrev PlaceDatum.uniquePlaceAbove (P : PlaceDatum F F' E E' L) (h : HasUniquePlaceAbove L P.v) :
    Unique (FinitePlacesAbove E' P.v) :=
  @Unique.mk' _ ⟨⟨P.v', P.liesOver_v'⟩⟩ (finitePlacesAbove_subsingleton P.v h)

theorem PlaceDatum.uniquePlaceAbove_default (P : PlaceDatum F F' E E' L)
    (h : HasUniquePlaceAbove L P.v) :
    (P.uniquePlaceAbove h).default = ⟨P.v', P.liesOver_v'⟩ :=
  rfl

end Langlands.Global.Harris
