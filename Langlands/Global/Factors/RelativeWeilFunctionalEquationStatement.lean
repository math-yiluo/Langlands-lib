import Langlands.Global.Factors.HeckeTwistComparisonStatement
import Langlands.Automorphic.AssociatedDeterminantTwistStatement

/-!
# The global functional equation for twisted pairs of relative Weil representations

Tate (1979), Theorem 3.5.3 with (3.5.1)-(3.5.4), for the tensor product of two
continuous representations of the relative Weil group `W_{E/F}` of an arithmetic
class family, twisted by `χ ∘ τ_F` for a finite-order Hecke character `χ` trivial
on the archimedean ideles; compare Henniart (2000), §2.3. Every finite factor is
the actual arithmetic pair factor along a local map `W_{F_v} → W_{E/F}`. The
archimedean factors are existential and independent of the twist. Proposition
definitions only.
-/

noncomputable section

set_option autoImplicit false

universe u uV uE

namespace Langlands.Global.FunctionalEquationComparison

open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassField.Global Langlands.ClassField.Global.RelativeWeilGroup

section Local

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

/-- `f` is the factor triple of the pair `(X, Y)` with dual pair `(Xd, Yd)` for the
supplied local-constant system and additive character: `f.lFactor` and
`f.dualLFactor` are the arithmetic pair L-factors evaluated at `q^(-s)`, and
`f.epsilonFactor` is a monomial `c q^(-ms)` that is the arithmetic pair epsilon
factor. Values at poles are those of totalized rational-function evaluation. -/
def IsArithmeticPairLocalFactors (eC : LocalFactor.CommonClosure.ReciprocityFamily K)
    (ε : LocalFactor.NonabelianSystem.Assignment.{u, uE} K)
    (hε : LocalFactor.NonabelianSystem.IsSystem K eC ε)
    (ψ : Correspondence.NontrivialAdditiveCharacter K)
    (X Y Xd Yd : Correspondence.LocalPairClass.{u, uV} K) (f : LocalFactors) : Prop :=
  (∀ s : ℂ, f.lFactor s = RatFunc.eval (RingHom.id ℂ)
      (RankinSelberg.spectralPoint K.canonicalTopologicalData.residueCardinality s)
      (Correspondence.arithmeticPairLFactor K X Y)) ∧
  (∀ s : ℂ, f.dualLFactor s = RatFunc.eval (RingHom.id ℂ)
      (RankinSelberg.spectralPoint K.canonicalTopologicalData.residueCardinality s)
      (Correspondence.arithmeticPairLFactor K Xd Yd)) ∧
  ∃ (c : ℂˣ) (m : ℤ), Correspondence.IsArithmeticPairEpsilonFactor K eC ε hε ψ X Y c m ∧
    ∀ s : ℂ, f.epsilonFactor s =
      RankinSelberg.epsilonMonomial K.canonicalTopologicalData.residueCardinality c m s

end Local

variable {F : Type u} [Field F] [NumberField F]
  (c : FundamentalClass.ClassFamily.{u})
  (E : Type u) [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- At the finite place `z`, `f` is the factor triple of the twisted pair
`((χ ∘ τ_F) ⊗ S) ⊗ S'` along some local map `ι : W_{F_z} → W_{E/F}` for some place
of `E` above `z`, at the canonical component of `ψ` and for some local-constant
system. The dual pair consists of the duals of the twisted `S` and of `S'`. -/
def IsTwistedRelativePairFactorsAt
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (χ : HeckeCharacter F) (z : FinitePlace F) (f : LocalFactors) : Prop :=
  ∃ (w : FinitePlacesAbove E z)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w.1))
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E),
    IsLocalRelativeWeilMap z w.1 e ι ∧
  ∃ (ψz : Correspondence.NontrivialAdditiveCharacter (padicField z))
    (eCz : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (εz : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField z))
    (hεz : LocalFactor.NonabelianSystem.IsSystem (padicField z) eCz εz),
    IsCanonicalFiniteAdditiveComponent ψ z ψz ∧
    IsArithmeticPairLocalFactors.{u, uV, uE} (padicField z) eCz εz hεz ψz
      (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) ι)
      (localPairClass S' ι)
      (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S).dual ι)
      (localPairClass S'.dual ι) f

variable {c E}

/-- The Euler data with the archimedean block `arch`, the finite factors `f`, and the
partial L-functions `Lp`, `Lpd`. No analytic assertion is part of these data. -/
def assembledEulerData (arch : InfinitePlace F → LocalFactors)
    (f : FinitePlace F → LocalFactors) (Lp Lpd : ℂ → ℂ) : FiniteEulerData (AllPlaces F) where
  localFactors := Sum.elim arch f
  partialL := Lp
  partialDualL := Lpd

/-- Tate (1979), Theorem 3.5.3, for `((χ ∘ τ_F) ⊗ S) ⊗ S'` on the relative Weil group
of an arithmetic class family. For continuous `S`, `S'` and a nontrivial adelic
character `ψ` trivial on `F`, there are a finite set `T₀` of finite places and an
archimedean block `arch`, independent of the twist, such that for every
finite-order Hecke character `χ` trivial on the archimedean ideles, every finite
`B ⊇ T₀` outside which `χ` is unramified, and every family `f` of actual twisted
arithmetic factors at all finite places: the partial L-functions outside
`B` and the infinite places converge as Euler products on a right half-plane, all
these functions and every exceptional local factor are nonzero meromorphic, and
the completed functional equation holds with every epsilon factor in the
exceptional set. -/
def RelativeWeilTwistFunctionalEquationStatement : Prop := by
  classical
  exact
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∃ x : Adeles F, ψ x ≠ 1) → (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E),
    S.IsContinuous → S'.IsContinuous →
  ∃ (T₀ : Finset (FinitePlace F)) (arch : InfinitePlace F → LocalFactors),
  ∀ χ : HeckeCharacter F, χ.HasFiniteOrder → χ.HasPrescribedInfinityComponent 1 →
  ∀ B : Finset (FinitePlace F), T₀ ⊆ B → (∀ z ∉ B, χ.IsUnramifiedAt z) →
  ∀ f : FinitePlace F → LocalFactors,
    (∀ z : FinitePlace F, IsTwistedRelativePairFactorsAt.{u, uV, uE} c E ψ S S' χ z (f z)) →
  ∃ (σ : ℝ) (Lp Lpd : ℂ → ℂ),
    Admissible (assembledEulerData arch f Lp Lpd) (exceptionalPlaces F B) ∧
    HasEulerProductsOutside (assembledEulerData arch f Lp Lpd) (exceptionalPlaces F B) σ ∧
    FunctionalEquation (assembledEulerData arch f Lp Lpd) (exceptionalPlaces F B)

end Langlands.Global.FunctionalEquationComparison
