import Langlands.ClassField.Global.Cohomology
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.Global.CompletionPadic
import Langlands.ClassFieldTheory.Local.ClassFormation

/-! # The global fundamental classes of idele-class cohomology

A family of classes `u_{E/F}` in the actual relative second cohomology of the idele
class group `C_E`, one for each finite Galois extension `E / F` of number fields.
Restriction, inflation and local compatibility are stated by explicit cochains in
the convention of `RelativeIdeleCocycle.cohomologyClass_eq_of_cochain`. Local
compatibility is stated at the finite places, against a supplied family of local
relative invariant maps.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

namespace FundamentalClass

/-- A choice of one actual class in `H²(Gal(E/F), C_E)` for every finite Galois
extension `E / F` of number fields. -/
abbrev ClassFamily : Type (u + 1) :=
  ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E], (relativeIdeleClassCohomology F E 2 : Type u)

/-- The first cohomology of the idele class group vanishes in every finite Galois
extension of number fields. -/
def IdeleClassH1Vanishing : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E],
    Subsingleton (relativeIdeleClassCohomology F E 1 : Type u)

/-- Each class has exact additive order `[E : F]` and generates the actual group
`H²(Gal(E/F), C_E)`. -/
def Generates (c : ClassFamily.{u}) : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E],
    addOrderOf (c F E) = Module.finrank F E ∧ AddSubgroup.zmultiples (c F E) = ⊤

/-- Restriction to `Gal(E/F')` for an intermediate field `F ⊆ F' ⊆ E` sends `u_{E/F}`
to `u_{E/F'}`: the restricted cocycle and a representative of `u_{E/F'}` differ by
the coboundary of an explicit idele-class cochain. -/
def Restriction (c : ClassFamily.{u}) : Prop :=
  ∀ (F F' E : Type u) [Field F] [Field F'] [Field E]
    [NumberField F] [NumberField F'] [NumberField E]
    [Algebra F F'] [Algebra F E] [Algebra F' E] [IsScalarTower F F' E] [IsGalois F E],
    haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    ∀ (x : RelativeIdeleCocycle F E) (y : RelativeIdeleCocycle F' E),
      x.cohomologyClass = c F E → y.cohomologyClass = c F' E →
      ∃ b : (E ≃ₐ[F'] E) → IdeleClassGroup (𝓞 E) E, ∀ σ τ : E ≃ₐ[F'] E,
        x (σ.restrictScalars F, τ.restrictScalars F) * b (σ * τ) =
          b σ * relativeIdeleClassAut F' E σ (b τ) * y (σ, τ)

/-- Inflation along `Gal(L/F) → Gal(E/F)`, with coefficients pushed forward by the
idele-class inclusion `C_E → C_L`, sends `u_{E/F}` to `[L : E] • u_{L/F}`. -/
def Inflation (c : ClassFamily.{u}) : Prop :=
  ∀ (F E L : Type u) [Field F] [Field E] [Field L]
    [NumberField F] [NumberField E] [NumberField L]
    [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [IsGalois F E] [IsGalois F L]
    (x : RelativeIdeleCocycle F E) (y : RelativeIdeleCocycle F L),
    x.cohomologyClass = c F E → y.cohomologyClass = c F L →
    ∃ b : (L ≃ₐ[F] L) → IdeleClassGroup (𝓞 L) L, ∀ σ τ : L ≃ₐ[F] L,
      ideleClassInclusion
          (x (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ)) *
          b (σ * τ) =
        b σ * relativeIdeleClassAut F L σ (b τ) * y (σ, τ) ^ Module.finrank E L

section Decomposition

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- The homomorphism `Gal(E_w/F_v) → Gal(E/F)`: forget `F_v`-linearity down to
`F`-linearity, then restrict to `E`. -/
def decompositionHom [Normal F E] :
    (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) →* (E ≃ₐ[F] E) :=
  (AlgEquiv.restrictNormalHom E).comp (AlgEquiv.restrictScalarsHom F)

end Decomposition

/-- At every finite place `w | v`, the image of a local fundamental class of
`E_w / F_v` under `E_wˣ → C_E` (the `w`-coordinate) is the restriction of `u_{E/F}`
along `Gal(E_w/F_v) → Gal(E/F)`. Local fundamental classes have invariant
`1 / [E_w : F_v]` for the supplied relative invariant maps at the residue prime of `v`. -/
def LocalCompatibility (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (c : ClassFamily.{u}) : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal]
    [IsGalois (padicField v).Carrier (w.adicCompletion E)],
    haveI : FiniteDimensional (padicField v).Carrier (w.adicCompletion E) :=
      FiniteExtension.local_finite v w
    ∀ (z : groupCohomology.cocycles₂
        (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)))
      (y : RelativeIdeleCocycle F E),
      IsFundamentalClass (padicField v).Carrier (w.adicCompletion E)
          ((I (residuePrime v)).relative (padicField v) (w.adicCompletion E))
          (groupCohomology.H2π _ z) →
      y.cohomologyClass = c F E →
      ∃ b : (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) →
          IdeleClassGroup (𝓞 E) E,
        ∀ σ τ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E,
          IdeleClassGroup.ofAdicCompletion (𝓞 E) E w
              (@Additive.toMul (w.adicCompletion E)ˣ (z (σ, τ))) * b (σ * τ) =
            b σ * relativeIdeleClassAut F E (decompositionHom v w σ) (b τ) *
              y (decompositionHom v w σ, decompositionHom v w τ)

end FundamentalClass

open FundamentalClass in
/-- Global class field theory in fundamental-class form (Artin–Tate VI Theorem 1 and
VII Theorems 7–8; Tate, Cassels–Fröhlich VII §11). `H¹(Gal(E/F), C_E) = 0`, and for
every family of local relative invariant maps forming a class formation with the
arithmetic normalization there is exactly one family of global classes which
generate, and are compatible with restriction, inflation and the local fundamental
classes at all finite places. -/
def GlobalFundamentalClassStatement : Prop :=
  IdeleClassH1Vanishing.{u} ∧
    ∀ I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p,
      (∀ (p : ℕ) [Fact p.Prime],
        (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) →
      ∃! c : ClassFamily.{u},
        Generates c ∧ Restriction c ∧ Inflation c ∧ LocalCompatibility I c

end Langlands.ClassField.Global
