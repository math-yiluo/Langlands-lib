import Langlands.Global.Arithmetic.HarrisSetup

/-!
# Henniart's global characters as data for Harris's Proposition 4.8

Proposition definitions for the global construction of Henniart (2000),
Sections 3.3–3.6, read in the hypotheses of Harris (1998), Proposition 4.8.
A paired-place configuration names the field-and-place data of
`HarrisPairedPlaceRealizationStatement`. One target builds the characters
of the datum on any such configuration, one builds the configurations over
a common base field for all intermediate fields of a finite extension, and
the last combines the two. None of them is proved here.
-/

noncomputable section

universe uF uE uE' uL

namespace Langlands.Global

open NumberField LocalFactor.CommonClosure GeneralPosition Harris
open AdelicFunctoriality

namespace Harris

/-- The field-and-place data in the conclusion of
`HarrisPairedPlaceRealizationStatement`: CM fields `E ⊆ E' ⊆ L` with `L` the
normal closure of `E'/E`, an imaginary quadratic `K₀ ⊆ E` in which `p`
splits, exact degrees `[E' : E] = [F' : F]` and `[L : E] = [F̃ : F]`, four
distinct places `P.v, c(P.v), Ps.v, c(Ps.v)` above `p` each with one place of
`L` above it, compatible continuous completion isomorphisms for `P` and `Ps`
commuting with one Galois comparison `θ`, and continuous isomorphisms
`φ, φs` of the completions of `E'` with `F'` that extend the base
isomorphisms and agree with `L_ṽ ≅ F̃`. -/
def IsPairedPlaceConfiguration {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    {F' : Extension F} {E : Type uE} {E' : Type uE'} {L : Type uL}
    [Field E] [Field E'] [Field L] [NumberField E] [NumberField E'] [NumberField L]
    [IsCMField E] [IsCMField E'] [IsCMField L]
    [Algebra E E'] [Algebra E L] [Algebra E' L]
    (K₀ : IntermediateField ℚ E) (P Ps : PlaceDatum F F' E E' L)
    (φ : FiniteCompletion E' P.v' ≃+* F'.field)
    (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
    (θ : (L ≃ₐ[E] L) ≃*
      ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field)) : Prop :=
  letI := F.canonicalTopology
  letI := (fieldData F F').topology
  letI := (fieldData F (galoisClosure F F')).topology
  IsScalarTower E E' L ∧ IsNormalClosure E E' L ∧
  IsSplitImaginaryQuadratic p K₀ ∧
  maximalRealSubfield E ⊔ K₀.toSubfield = ⊤ ∧
  maximalRealSubfield E' ⊔ K₀.toSubfield.map (algebraMap E E') = ⊤ ∧
  maximalRealSubfield L ⊔ K₀.toSubfield.map (algebraMap E L) = ⊤ ∧
  Module.finrank E E' = Module.finrank F.Carrier F'.field ∧
  Module.finrank E L = Module.finrank F.Carrier (galoisClosure F F').field ∧
  List.Pairwise (· ≠ ·) [P.v, conjPlace E P.v, Ps.v, conjPlace E Ps.v] ∧
  (∀ v ∈ [P.v, conjPlace E P.v, Ps.v, conjPlace E Ps.v],
    (p : 𝓞 E) ∈ v.asIdeal ∧ HasUniquePlaceAbove L v) ∧
  (∀ Q ∈ [P, Ps],
    Q.IsCompatible ∧
    Continuous Q.iso ∧ Continuous Q.iso.symm ∧
    Continuous Q.isoTilde ∧ Continuous Q.isoTilde.symm ∧
    ∀ (σ : L ≃ₐ[E] L) (x : L),
      θ σ (Q.isoTilde (algebraMap L (FiniteCompletion L Q.vTilde) x)) =
        Q.isoTilde (algebraMap L (FiniteCompletion L Q.vTilde) (σ x))) ∧
  Continuous φ ∧ Continuous φ.symm ∧
  Continuous φs ∧ Continuous φs.symm ∧
  (∀ x : FiniteCompletion E P.v,
    φ (FiniteExtension.completionMap P.v P.v' x) =
      algebraMap F.Carrier F'.field (P.iso x)) ∧
  (∀ y : FiniteCompletion E' P.v',
    ((φ y : F'.field) : AlgebraicClosure F.Carrier) =
      ((P.isoTilde (FiniteExtension.completionMap P.v' P.vTilde y) :
        (galoisClosure F F').field) : AlgebraicClosure F.Carrier)) ∧
  (∀ x : FiniteCompletion E Ps.v,
    φs (FiniteExtension.completionMap Ps.v Ps.v' x) =
      algebraMap F.Carrier F'.field (Ps.iso x)) ∧
  (∀ y : FiniteCompletion E' Ps.v',
    ((φs y : F'.field) : AlgebraicClosure F.Carrier) =
      ((Ps.isoTilde (FiniteExtension.completionMap Ps.v' Ps.vTilde y) :
        (galoisClosure F F').field) : AlgebraicClosure F.Carrier))

end Harris

/-- Henniart 2000, Lemma 3 of Section 3.6, in the hypotheses of Harris 1998,
Proposition 4.8. On every paired-place configuration, for every normalized
reciprocity family `e` and every continuous character `χ₀` of `F'ˣ`, there
are characters `χ, χs` of `F'ˣ` and a Hecke character `ξ` of `E'` satisfying
`IsProposition48Datum e χ χs K₀ P Ps ξ`, with `χ` equal to `χ₀` on the units
of the valuation ring of `F'` (so `χ / χ₀` is unramified). -/
def HarrisDatumCharacterRealizationStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
    (E : Type uE) (E' : Type uE') (L : Type uL)
    [Field E] [Field E'] [Field L] [NumberField E] [NumberField E'] [NumberField L]
    [IsCMField E] [IsCMField E'] [IsCMField L]
    [Algebra E E'] [Algebra E L] [Algebra E' L]
    (K₀ : IntermediateField ℚ E) (P Ps : PlaceDatum F F' E E' L)
    (φ : FiniteCompletion E' P.v' ≃+* F'.field)
    (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
    (θ : (L ≃ₐ[E] L) ≃*
      ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field)),
    IsPairedPlaceConfiguration K₀ P Ps φ φs θ →
    ∀ (e : ReciprocityFamily F), NormalizedReciprocity F e →
    ∀ χ₀ : FieldCharacter F F',
      ∃ (χ χs : FieldCharacter F F') (ξ : HeckeCharacter E'),
        IsProposition48Datum e χ χs K₀ P Ps ξ ∧
        ∀ u : F'.fieldˣ, (fieldData F F').discreteValuation (u : F'.field) = 1 →
          χ u = χ₀ u

/-- Henniart 2000, Section 3.3, with the place pairs of Harris 1998,
Section 4: for every finite extension `M` of a p-adic field `F` there is one
CM number field `E` with a place `v₀` and a continuous isomorphism
`ι₀ : E_{v₀} ≅ F` such that every intermediate field `F'` of `M/F` has a
paired-place configuration whose place `P.v` is `v₀` and whose isomorphism
`P.iso` agrees with `ι₀` on `E`. -/
def HenniartCommonBaseRealizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (M : Extension F),
    letI := F.canonicalTopology
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E)
      (v₀ : FinitePlace E) (ι₀ : FiniteCompletion E v₀ ≃+* F.Carrier),
      Continuous ι₀ ∧ Continuous ι₀.symm ∧
      ∀ F' : Extension F, F'.field ≤ M.field →
        ∃ (E' L : Type) (_ : Field E') (_ : Field L)
          (_ : NumberField E') (_ : NumberField L)
          (_ : IsCMField E') (_ : IsCMField L)
          (_ : Algebra E E') (_ : Algebra E L) (_ : Algebra E' L)
          (K₀ : IntermediateField ℚ E) (P Ps : PlaceDatum F F' E E' L)
          (φ : FiniteCompletion E' P.v' ≃+* F'.field)
          (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
          (θ : (L ≃ₐ[E] L) ≃*
            ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field)),
          IsPairedPlaceConfiguration K₀ P Ps φ φs θ ∧
          P.v = v₀ ∧
          ∀ x : E, P.iso (algebraMap E (FiniteCompletion E P.v) x) =
            ι₀ (algebraMap E (FiniteCompletion E v₀) x)

/-- The combination used by Henniart 2000, Sections 3.3–3.7: one CM field `E`
with `ι₀ : E_{v₀} ≅ F` serves every intermediate field `F'` of `M/F`; for
every normalized reciprocity family and every continuous character `χ₀` of
`F'ˣ` there is a paired-place configuration over `E` at `v₀` and data of
Harris's Proposition 4.8 on it whose character `χ` at `P` equals `χ₀` on the
units of `F'`. -/
def HenniartHarrisDatumStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (M : Extension F),
    letI := F.canonicalTopology
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E)
      (v₀ : FinitePlace E) (ι₀ : FiniteCompletion E v₀ ≃+* F.Carrier),
      Continuous ι₀ ∧ Continuous ι₀.symm ∧
      ∀ F' : Extension F, F'.field ≤ M.field →
      ∀ (e : ReciprocityFamily F), NormalizedReciprocity F e →
      ∀ χ₀ : FieldCharacter F F',
        ∃ (E' L : Type) (_ : Field E') (_ : Field L)
          (_ : NumberField E') (_ : NumberField L)
          (_ : IsCMField E') (_ : IsCMField L)
          (_ : Algebra E E') (_ : Algebra E L) (_ : Algebra E' L)
          (K₀ : IntermediateField ℚ E) (P Ps : PlaceDatum F F' E E' L)
          (φ : FiniteCompletion E' P.v' ≃+* F'.field)
          (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
          (θ : (L ≃ₐ[E] L) ≃*
            ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field))
          (χ χs : FieldCharacter F F') (ξ : HeckeCharacter E'),
          IsPairedPlaceConfiguration K₀ P Ps φ φs θ ∧
          P.v = v₀ ∧
          (∀ x : E, P.iso (algebraMap E (FiniteCompletion E P.v) x) =
            ι₀ (algebraMap E (FiniteCompletion E v₀) x)) ∧
          IsProposition48Datum e χ χs K₀ P Ps ξ ∧
          ∀ u : F'.fieldˣ, (fieldData F F').discreteValuation (u : F'.field) = 1 →
            χ u = χ₀ u

end Langlands.Global
