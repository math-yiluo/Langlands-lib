import Langlands.Global.CMReflexField
import Langlands.Galois.CompatibleFamily
import Langlands.Galois.UnitaryNormalization
import Langlands.Automorphic.SquareIntegrableComponent
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.RegularAlgebraic
import Langlands.Automorphic.ConjugateContragredient
import Langlands.Global.Arithmetic.HarrisSetup

/-!
# Clozel's compatible systems for conjugate self-dual representations of `GL(n)`

Clozel, *Représentations galoisiennes associées aux représentations
automorphes autoduales de GL(n)*, Publ. Math. IHÉS 73 (1991), Théorème 5.7
with the conclusions (i)-(iv) of Théorème 5.3, and Clozel, *On the cohomology
of Kottwitz's arithmetic varieties*, Duke Math. J. 72 (1993), Theorem 2.6.

For a CM field `F_c = K`, a cuspidal regular algebraic `π_c` with
`π_c ≅ σ(π̃_c)`, a CM type `Σ` and `ι₀ ∈ Σ`, these give a number field `L ⊂ ℂ`,
a finite set `S` of primes, an integer `a > 0` and a compatible system of
`λ`-adic representations of `Gal(Ē/E)`, `E = F_c R` Clozel's reflex field, whose
Frobenius characteristic polynomials at the places of `E` above `p ∉ S` are
those of `a` copies of the representation attached to `π_c`. The multiplicity
`a` is not removed here.

The statements are unproved `Prop` definitions.
-/

noncomputable section

open Polynomial
open scoped NumberField
open NumberField (IsCMField)

universe uK uL uV uW

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Unramified Langlands.Automorphic

variable {K : Type uK} [Field K] [NumberField K] [IsCMField K]

/-- `∏_{α} (1 - q^{(n-1)/2} α^f X)` for `n` Hecke eigenvalues `α`: the reversed
characteristic polynomial of `r^T(Φ_w) q_w^{n-1}` in Clozel's normalization (5.3),
at a place `w` of residue degree `f` over the place of the eigenvalues, with
`q = q_w`. -/
def clozelEulerPolynomial {n : ℕ} (α : Eigenvalues n) (f q : ℕ) : ℂ[X] :=
  (α.power f).eulerPolynomial.comp
    (C (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * X)

variable [CompactSpace (AdeleQuotient K)]

/-- Clozel's conclusions (i)-(iv) of Théorème 5.3 for a cuspidal class `c` of
`GL_{r+1}(𝔸_K)`: `a > 0`; `W` is a compatible system over all finite places of `L`,
of rank `a (r + 1)` and pure of weight `n - 1 = r`; and there are polynomials
`P_w ∈ L[X]` and a spectral system `s` of `c` such that, at every place `w` of
`E` whose residue characteristic is not in `S`, `W_λ` (for `λ ∤ p`) is unramified
with Euler polynomial `P_w`, and `ι(P_w)` is the `a`-th power of
`clozelEulerPolynomial` of the eigenvalues of `s` at the place `v` of `K` below `w`,
with `f = f(w | v)` and `q = q_w`. -/
def IsClozelSystem (Φ : CMType K) (ι₀ : K →+* ℂ) {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass K r) {L : Type uL} [Field L] [NumberField L]
    (ι : L →+* ℂ) (S : Finset ℕ) (a : ℕ)
    (W : Collection.{0, uL, uV} (Φ.clozelReflexField ι₀) L ∅) : Prop :=
  letI : Algebra K (Φ.clozelReflexField ι₀) := (Φ.toClozelReflexField ι₀).toAlgebra
  0 < a ∧ HasRank ∅ W (a * (r + 1)) ∧ IsPureCompatible ∅ W r ∧
  ∃ P : FinitePlace (Φ.clozelReflexField ι₀) → L[X],
    (∀ (lam : {lam : FinitePlace L // lam ∉ (∅ : Finset (FinitePlace L))})
        (w : FinitePlace (Φ.clozelReflexField ι₀)),
      residueCharacteristic w ∉ S → residueCharacteristic w ≠ residueCharacteristic lam.val →
        HasEulerPolynomialAt (W lam) w ((P w).map (NumberField.FinitePlace.embedding lam.val))) ∧
    ∃ s : SpectralSystem (FinitePlace K) (r + 1),
      CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uK, uW} c s ∧
      ∀ (w : FinitePlace (Φ.clozelReflexField ι₀)) (v : FinitePlace K),
        w.asIdeal.LiesOver v.asIdeal → residueCharacteristic w ∉ S →
          ∃ hv : v ∉ s.exceptional,
            (P w).map ι =
              clozelEulerPolynomial (s.eigenvalues v hv) (w.asIdeal.inertiaDeg (𝓞 K))
                (residueCardinality w) ^ a

/-- The weaker association used for Clozel (1993), Theorem 2.6: as `IsClozelSystem`,
but with purity of some weight `m` and with the comparison made after Harris's
unitary normalization, `β ↦ β / |β|` on the reciprocal roots of `ι(P_w)`. -/
def IsClozelUnitarySystem (Φ : CMType K) (ι₀ : K →+* ℂ) {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass K r) {L : Type uL} [Field L] [NumberField L]
    (ι : L →+* ℂ) (S : Finset ℕ) (a : ℕ) (m : ℤ)
    (W : Collection.{0, uL, uV} (Φ.clozelReflexField ι₀) L ∅) : Prop :=
  letI : Algebra K (Φ.clozelReflexField ι₀) := (Φ.toClozelReflexField ι₀).toAlgebra
  0 < a ∧ HasRank ∅ W (a * (r + 1)) ∧ IsPureCompatible ∅ W m ∧
  ∃ P : FinitePlace (Φ.clozelReflexField ι₀) → L[X],
    (∀ (lam : {lam : FinitePlace L // lam ∉ (∅ : Finset (FinitePlace L))})
        (w : FinitePlace (Φ.clozelReflexField ι₀)),
      residueCharacteristic w ∉ S → residueCharacteristic w ≠ residueCharacteristic lam.val →
        HasEulerPolynomialAt (W lam) w ((P w).map (NumberField.FinitePlace.embedding lam.val))) ∧
    ∃ s : SpectralSystem (FinitePlace K) (r + 1),
      CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uK, uW} c s ∧
      ∀ (w : FinitePlace (Φ.clozelReflexField ι₀)) (v : FinitePlace K),
        w.asIdeal.LiesOver v.asIdeal → residueCharacteristic w ∉ S →
          ∃ hv : v ∉ s.exceptional,
            unitaryEulerPolynomial ((P w).map ι) =
              ((s.eigenvalues v hv).power (w.asIdeal.inertiaDeg (𝓞 K))).eulerPolynomial ^ a

/-- Clozel (1991), Théorème 5.7, with the conclusions (i)-(iv) of Théorème 5.3.

`K = F_c` is a CM field of degree `2d`, `c = π_c` a cuspidal class of `GL_n(𝔸_K)`,
`n = r + 1 > 2` (Clozel's standing assumption in §5), which is regular algebraic and satisfies `π_c ≅ σ(π̃_c)` (i). For (ii):
at a place `v₀` of `K` with `c(v₀) ≠ v₀` (the place of `F` below splits in `K`),
both components of `(π_c)_{v₀}` are square-integrable; if `2 ∣ n`, `4 ∤ n` and `d`
is odd, the same holds at a second such place `v₁` above a different place of `F`.
Then for every CM type `Σ` and `ι₀ ∈ Σ` there are `L`, `ι : L → ℂ`, `S`, `a` and a
compatible system `W` of `λ`-adic representations of `Gal(Ē/E)`,
`E = Σ.clozelReflexField ι₀`, satisfying `IsClozelSystem`. -/
def Clozel1991Theorem57Statement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] [IsCMField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ), 2 ≤ r → ∀ c : CuspidalOperatorRealization.IsoClass K r,
    c.IsRegularAlgebraic → c.IsConjugateSelfDual →
    ∀ v₀ : FinitePlace K, Harris.conjPlace K v₀ ≠ v₀ →
    CuspidalOperatorRealization.IsoClass.HasSquareIntegrableComponent.{uK, uW} c v₀ →
    CuspidalOperatorRealization.IsoClass.HasSquareIntegrableComponent.{uK, uW} c
      (Harris.conjPlace K v₀) →
    (2 ∣ r + 1 → ¬ 4 ∣ r + 1 → Odd (Module.finrank ℚ K / 2) →
      ∃ v₁ : FinitePlace K, Harris.conjPlace K v₁ ≠ v₁ ∧ v₁ ≠ v₀ ∧
        v₁ ≠ Harris.conjPlace K v₀ ∧
        CuspidalOperatorRealization.IsoClass.HasSquareIntegrableComponent.{uK, uW} c v₁ ∧
        CuspidalOperatorRealization.IsoClass.HasSquareIntegrableComponent.{uK, uW} c
          (Harris.conjPlace K v₁)) →
    ∀ (Φ : CMType K) (ι₀ : K →+* ℂ), ι₀ ∈ Φ →
      ∃ (L : Type uL) (fieldL : Field L),
        letI : Field L := fieldL
        ∃ (numberFieldL : NumberField L),
          letI : NumberField L := numberFieldL
          ∃ (ι : L →+* ℂ) (S : Finset ℕ) (a : ℕ)
            (W : Collection.{0, uL, uV} (Φ.clozelReflexField ι₀) L ∅),
            IsClozelSystem.{uK, uL, uV, uW} Φ ι₀ c ι S a W

/-- Clozel (1993), Theorem 2.6: parity removal under a supercuspidal hypothesis.

Same data as `Clozel1991Theorem57Statement`, with `n = r + 1 ≥ 2`, but the hypothesis (ii) and the
parity condition are replaced by: at a place `v₀` of `K` with `c(v₀) ≠ v₀`, both
components of `(π_c)_{v₀}` are supercuspidal. The conclusion is a compatible system
of `λ`-adic representations of `Gal(Ē/E)` associated to `π_c`, here in the form
`IsClozelUnitarySystem` (unitary normalization, some weight `m`, multiplicity `a`). -/
def Clozel1993Theorem26Statement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] [IsCMField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ), 1 ≤ r → ∀ c : CuspidalOperatorRealization.IsoClass K r,
    c.IsRegularAlgebraic → c.IsConjugateSelfDual →
    ∀ v₀ : FinitePlace K, Harris.conjPlace K v₀ ≠ v₀ →
    CuspidalOperatorRealization.IsoClass.HasSupercuspidalComponent.{uK, uW} c v₀ →
    CuspidalOperatorRealization.IsoClass.HasSupercuspidalComponent.{uK, uW} c
      (Harris.conjPlace K v₀) →
    ∀ (Φ : CMType K) (ι₀ : K →+* ℂ), ι₀ ∈ Φ →
      ∃ (L : Type uL) (fieldL : Field L),
        letI : Field L := fieldL
        ∃ (numberFieldL : NumberField L),
          letI : NumberField L := numberFieldL
          ∃ (ι : L →+* ℂ) (S : Finset ℕ) (a : ℕ) (m : ℤ)
            (W : Collection.{0, uL, uV} (Φ.clozelReflexField ι₀) L ∅),
            IsClozelUnitarySystem.{uK, uL, uV, uW} Φ ι₀ c ι S a m W

end Langlands.GaloisRepresentation
