import Langlands.Global.HeckeCharacter
import Langlands.Global.InfinityType
import Langlands.Global.AdelicFunctoriality.Extension
import Langlands.Global.AdelicFunctoriality.Isomorphism
import Langlands.Global.Arithmetic.GeneralPositionStatement
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances

/-!
# The arithmetic hypotheses of Harris's Proposition 4.8

Harris (1998), Section 4, pages 200--201: a CM extension `E'/E` with an
imaginary quadratic field `K₀ ⊆ E` in which `p` splits, the Galois closure
`L = Ẽ` of `E'/E`, two designated places of `E` matched with the local fields
`F ⊆ F' ⊆ F̃`, and an `E'/E`-regular (Definition 2.3) algebraic Hecke character
`ξ = ξ⁻¹ ∘ c` of `E'` with prescribed components at the two places above them.
Only the hypotheses are defined here; the automorphic conclusion is separate.
-/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open NumberField IsDedekindDomain
open LocalFactor.CommonClosure GeneralPosition AdelicFunctoriality

section HeckeCharacters

variable {K : Type*} [Field K] [NumberField K]

/-- An algebraic Hecke character of a totally complex field: its archimedean
component is the character of an integral infinity type. -/
def IsAlgebraic [IsTotallyComplex K] (χ : HeckeCharacter K) : Prop :=
  ∃ a : InfinityType K, χ.HasPrescribedInfinityComponent (InfinityType.toCharacter a)

/-- Harris's `χ = χ⁻¹ ∘ c` on a CM field, with the actual arithmetic complex
conjugation of the idele-class group. -/
def IsConjugateInverse [IsCMField K] (χ : HeckeCharacter K) : Prop :=
  ∀ x, χ (ideleClassComplexConj x) = (χ x)⁻¹

/-- Harris 1998 Definition 2.3 for a totally complex base: for every archimedean
place `τ` of `E`, the components of `χ` at distinct places of `E'` above `τ`
are distinct. They are compared on `E_τˣ` through the completion maps
`E_τ → E'_w`, which are isomorphisms because `τ` is complex. -/
def IsRelativelyRegular (E : Type*) {E' : Type*} [Field E] [NumberField E]
    [IsTotallyComplex E] [Field E'] [NumberField E'] [Algebra E E']
    (χ : HeckeCharacter E') : Prop :=
  ∀ (τ : InfinitePlace E) (w w' : InfinitePlace E') [w.LiesOver τ] [w'.LiesOver τ],
    w ≠ w' →
      ∃ x : (InfiniteCompletion E τ)ˣ,
        χ.infiniteComponent w
            (Units.map (LiesOver.completionMap (v := τ) (w := w)).toMonoidHom x) ≠
          χ.infiniteComponent w'
            (Units.map (LiesOver.completionMap (v := τ) (w := w')).toMonoidHom x)

end HeckeCharacters

/-- `K₀` is an imaginary quadratic field in which the rational prime `p`
splits: two distinct primes of `𝓞 K₀` contain `p`. -/
def IsSplitImaginaryQuadratic (p : ℕ) (K₀ : Type*) [Field K₀] [NumberField K₀] : Prop :=
  Module.finrank ℚ K₀ = 2 ∧ IsTotallyComplex K₀ ∧
    ∃ P Q : FinitePlace K₀, P ≠ Q ∧ (p : 𝓞 K₀) ∈ P.asIdeal ∧ (p : 𝓞 K₀) ∈ Q.asIdeal

/-- Exactly one place of `L` lies above the finite place `v` of `E`. -/
def HasUniquePlaceAbove (L : Type*) {E : Type*} [Field E] [NumberField E] [Field L]
    [NumberField L] [Algebra E L] (v : FinitePlace E) : Prop :=
  ∀ w w' : FinitePlace L, w.asIdeal.LiesOver v.asIdeal → w'.asIdeal.LiesOver v.asIdeal → w = w'

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
variable (E E' L : Type*) [Field E] [NumberField E] [Field E'] [NumberField E']
  [Field L] [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L]

/-- A place `v` of `E` with places `v' | v` of `E'` and `ṽ | v'` of `L`, an
isomorphism `E_v ≅ F` and an isomorphism `L_ṽ ≅ F̃` with Harris's
`F̃ = galoisClosure F F'`. -/
structure PlaceDatum where
  /-- The place of `E`. -/
  v : FinitePlace E
  /-- The place of `E'` below `vTilde`. -/
  v' : FinitePlace E'
  /-- The place of `L` above `v`. -/
  vTilde : FinitePlace L
  [liesOver_v' : v'.asIdeal.LiesOver v.asIdeal]
  [liesOver_vTilde' : vTilde.asIdeal.LiesOver v'.asIdeal]
  [liesOver_vTilde : vTilde.asIdeal.LiesOver v.asIdeal]
  /-- The isomorphism `E_v ≅ F`. -/
  iso : FiniteCompletion E v ≃+* F.Carrier
  /-- The isomorphism `L_ṽ ≅ F̃`. -/
  isoTilde : FiniteCompletion L vTilde ≃+* (galoisClosure F F').field

attribute [instance] PlaceDatum.liesOver_v' PlaceDatum.liesOver_vTilde'
  PlaceDatum.liesOver_vTilde

namespace PlaceDatum

variable {F F' E E' L}

/-- `L_ṽ ≅ F̃` extends `E_v ≅ F`, and it carries `E'_{v'}` onto `F'`. -/
def IsCompatible (P : PlaceDatum F F' E E' L) : Prop :=
  (∀ x : FiniteCompletion E P.v,
    P.isoTilde (FiniteExtension.completionMap P.v P.vTilde x) =
      algebraMap F.Carrier (galoisClosure F F').field (P.iso x)) ∧
  Set.range (fun y : FiniteCompletion E' P.v' ↦
      ((P.isoTilde (FiniteExtension.completionMap P.v' P.vTilde y) :
        (galoisClosure F F').field) : AlgebraicClosure F.Carrier)) =
    (F'.field : Set (AlgebraicClosure F.Carrier))

/-- The component of `χ` at `v'` is `η` under the isomorphism `E'_{v'} ≅ F'`
induced by `L_ṽ ≅ F̃`. -/
def HasComponent (P : PlaceDatum F F' E E' L) (χ : HeckeCharacter E')
    (η : FieldCharacter F F') : Prop :=
  ∀ (x : (FiniteCompletion E' P.v')ˣ) (y : F'.fieldˣ),
    ((y : F'.field) : AlgebraicClosure F.Carrier) =
        P.isoTilde (FiniteExtension.completionMap P.v' P.vTilde (x : FiniteCompletion E' P.v')) →
      χ.finiteComponent P.v' x = η y

end PlaceDatum

variable [IsCMField E] [IsCMField E']

/-- The complex-conjugate place `c(v)` of a finite place of the CM field `E`. -/
def conjPlace (v : FinitePlace E) : FinitePlace E :=
  finitePlaceEquiv (IsCMField.complexConj E).toRingEquiv v

variable {F F' E E' L}

/-- The hypotheses of Harris 1998, Proposition 4.8, with the setup of
Section 4 (pages 200--201). `K₀ ⊆ E` is imaginary quadratic and `p` splits in
it; `L` is the Galois closure of the CM extension `E'/E`; `P` gives `v₁` and
`Ps` gives `v(*)₁`, both above `p`; each of `v₁, c(v₁), v(*)₁, c(v(*)₁)` has
exactly one place of `L` above it; the two pairs differ; `χs` is in general
position relative to `F` through the reciprocity family `e`; and `ξ` is an
`E'/E`-regular algebraic Hecke character with `ξ = ξ⁻¹ ∘ c` and components `χ`
at `v₁'` and `χs` at `v(*)₁'`. -/
def IsProposition48Datum (e : ReciprocityFamily F) (χ χs : FieldCharacter F F')
    (K₀ : IntermediateField ℚ E) (P Ps : PlaceDatum F F' E E' L)
    (ξ : HeckeCharacter E') : Prop :=
  IsSplitImaginaryQuadratic p K₀ ∧
  IsScalarTower E E' L ∧ IsNormalClosure E E' L ∧
  (p : 𝓞 E) ∈ P.v.asIdeal ∧ P.IsCompatible ∧
  HasUniquePlaceAbove L P.v ∧ HasUniquePlaceAbove L (conjPlace E P.v) ∧
  (p : 𝓞 E) ∈ Ps.v.asIdeal ∧ Ps.IsCompatible ∧
  HasUniquePlaceAbove L Ps.v ∧ HasUniquePlaceAbove L (conjPlace E Ps.v) ∧
  Ps.v ≠ P.v ∧ Ps.v ≠ conjPlace E P.v ∧
  IsInGeneralPosition F F' (weilCharacter F e F' χs) ∧
  IsAlgebraic ξ ∧ IsRelativelyRegular E ξ ∧ IsConjugateInverse ξ ∧
  P.HasComponent ξ χ ∧ Ps.HasComponent ξ χs

end Langlands.Global.Harris
