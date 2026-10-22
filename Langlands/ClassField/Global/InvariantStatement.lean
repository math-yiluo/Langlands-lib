import Langlands.ClassField.Global.FundamentalClassStatement

/-! # The global invariant maps of idele-class cohomology

A family of homomorphisms `inv_{E/F} : H²(Gal(E/F), C_E) → ℚ/ℤ`, one for every finite
Galois extension `E / F` of number fields, together with the properties that characterize
the global invariant of class field theory: it is injective with image `(1/[E:F])ℤ/ℤ`,
restriction multiplies it by the base-extension degree, inflation preserves it, and the
image of a local class at a finite place `w | v` has the local invariant after
multiplication by `[E : F] / [E_w : F_v]`. Each compatibility is an equivalence between an
explicit cochain relation, in the convention of the published
`FundamentalClass.Restriction`, `FundamentalClass.Inflation` and
`FundamentalClass.LocalCompatibility`, and an equation of invariants.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

universe u

namespace FundamentalClass

/-- A candidate global invariant map on the actual `H²(Gal(E/F), C_E)` for every finite
Galois extension `E / F` of number fields; no law is assumed. -/
abbrev GlobalInvariantMaps : Type (u + 1) :=
  ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E],
    (relativeIdeleClassCohomology F E 2 : Type u) →+ RationalModIntegers

/-- Each invariant map is injective with image the subgroup `(1/[E:F])ℤ/ℤ`. -/
def InvariantImages (inv : GlobalInvariantMaps.{u}) : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E],
    Function.Injective (inv F E) ∧
      (inv F E).range = denominatorSubgroup (Module.finrank F E)

/-- Restriction to `Gal(E/F')` multiplies invariants by `[F' : F]`: a cocycle `x` of
`E / F`, restricted along `E ≃ₐ[F'] E → E ≃ₐ[F] E`, is related to a cocycle `y` of
`E / F'` by an explicit cochain exactly when `inv_{E/F'}[y] = [F' : F] • inv_{E/F}[x]`. -/
def InvariantRestriction (inv : GlobalInvariantMaps.{u}) : Prop :=
  ∀ (F F' E : Type u) [Field F] [Field F'] [Field E]
    [NumberField F] [NumberField F'] [NumberField E]
    [Algebra F F'] [Algebra F E] [Algebra F' E] [IsScalarTower F F' E] [IsGalois F E],
    haveI : IsGalois F' E := IsGalois.tower_top_of_isGalois F F' E
    ∀ (x : RelativeIdeleCocycle F E) (y : RelativeIdeleCocycle F' E),
      (∃ b : (E ≃ₐ[F'] E) → IdeleClassGroup (𝓞 E) E, ∀ σ τ : E ≃ₐ[F'] E,
          x (σ.restrictScalars F, τ.restrictScalars F) * b (σ * τ) =
            b σ * relativeIdeleClassAut F' E σ (b τ) * y (σ, τ)) ↔
        inv F' E y.cohomologyClass = Module.finrank F F' • inv F E x.cohomologyClass

/-- Inflation along `Gal(L/F) → Gal(E/F)`, with coefficients pushed into `C_L` by the
idele-class inclusion, preserves invariants: for every `m : ℕ`, the inflated cocycle of
`x` is related to the pointwise `m`-th power of a cocycle `y` of `L / F` by an explicit
cochain exactly when `m • inv_{L/F}[y] = inv_{E/F}[x]`. -/
def InvariantInflation (inv : GlobalInvariantMaps.{u}) : Prop :=
  ∀ (F E L : Type u) [Field F] [Field E] [Field L]
    [NumberField F] [NumberField E] [NumberField L]
    [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [IsGalois F E] [IsGalois F L]
    (x : RelativeIdeleCocycle F E) (y : RelativeIdeleCocycle F L) (m : ℕ),
    (∃ b : (L ≃ₐ[F] L) → IdeleClassGroup (𝓞 L) L, ∀ σ τ : L ≃ₐ[F] L,
        ideleClassInclusion
            (x (AlgEquiv.restrictNormalHom E σ, AlgEquiv.restrictNormalHom E τ)) *
            b (σ * τ) =
          b σ * relativeIdeleClassAut F L σ (b τ) * y (σ, τ) ^ m) ↔
      m • inv F L y.cohomologyClass = inv F E x.cohomologyClass

/-- At a finite place `w | v` with `E_w / F_v` Galois, the image in `C_E` of a local
cocycle `z` (through the `w`-coordinate) is related to a global cocycle `y` pulled back
along `decompositionHom v w` by an explicit cochain exactly when
`([E : F] / [E_w : F_v]) • inv_{E/F}[y]` is the local invariant of `z` for the supplied
relative invariant maps at the residue prime of `v`. The quotient is natural-number
division; the local degree divides the global degree. -/
def InvariantLocal (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (inv : GlobalInvariantMaps.{u}) : Prop :=
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
      (∃ b : (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) →
          IdeleClassGroup (𝓞 E) E,
        ∀ σ τ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E,
          IdeleClassGroup.ofAdicCompletion (𝓞 E) E w
              (@Additive.toMul (w.adicCompletion E)ˣ (z (σ, τ))) * b (σ * τ) =
            b σ * relativeIdeleClassAut F E (decompositionHom v w σ) (b τ) *
              y (decompositionHom v w σ, decompositionHom v w τ)) ↔
        (Module.finrank F E /
            Module.finrank (padicField v).Carrier (w.adicCompletion E)) •
            inv F E y.cohomologyClass =
          (I (residuePrime v)).relative (padicField v) (w.adicCompletion E)
            (groupCohomology.H2π _ z)

/-- The global invariant maps of class field theory relative to the local family `I`. -/
def IsGlobalInvariant (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (inv : GlobalInvariantMaps.{u}) : Prop :=
  InvariantImages inv ∧ InvariantRestriction inv ∧ InvariantInflation inv ∧
    InvariantLocal I inv

end FundamentalClass

open FundamentalClass in
/-- Existence of the global invariant maps (Artin–Tate VII §3, Theorems 7–8, and XIV §3):
for every family of local relative invariant maps forming a class formation with the
arithmetic normalization, there are global invariant maps on the actual idele-class
cohomology which are isomorphisms onto `(1/[E:F])ℤ/ℤ` and are compatible with
restriction, inflation and the local invariants at all finite places. -/
def GlobalInvariantStatement : Prop :=
  ∀ I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p,
    (∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) →
    ∃ inv : GlobalInvariantMaps.{u}, IsGlobalInvariant I inv

end Langlands.ClassField.Global
