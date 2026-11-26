import Langlands.Global.Factors.RelativePairLFactorReduction
import Langlands.Representation.RankinSelberg.TemperedLFactorGamma
import Langlands.Correspondence.SupercuspidalEpsilonComparison
import Langlands.Correspondence.RankOneArithmeticEpsilonData
import Langlands.Correspondence.ArithmeticEpsilonBilinear

/-!
# Reduction of the pair epsilon-factor clause to witnessed generators

A virtual epsilon relation built from a basis relation with unique values is the
graph of an integer-bilinear map with values in `Additive ℂˣ × ℤ`. On the side of
`GL_n` the JPSS epsilon certificate `c q^(-ms)` of two unitary supercuspidal basis
classes exists for a self-dual measure and is unique. On the Weil side arithmetic
epsilon certificates are unique; their existence for all pairs of unitary basis
classes is kept as an explicit hypothesis. Under it, the epsilon clause of
`RelativeIsometryFactorStatement` reduces to witnessed generators, through the
same span argument as the L-factor clause.
-/

noncomputable section

set_option autoImplicit false

universe uF uV uW uP uE

namespace Langlands.VirtualRepresentation

variable {ι κ : Type*}

/-- An integer-bilinear map on integral lattices is the multiplicity-weighted sum of
its values on pairs of basis classes. -/
theorem bilinear_eq_sum {N : Type*} [AddCommGroup N]
    (Φ : IntegralLattice ι →ₗ[ℤ] IntegralLattice κ →ₗ[ℤ] N)
    (x : IntegralLattice ι) (y : IntegralLattice κ) :
    Φ x y = x.sum fun a m => y.sum fun b n => (m * n) • Φ (generator a) (generator b) := by
  have hx : x = x.sum fun a m => m • generator a := by
    simp [generator]
  have hy : y = y.sum fun b n => n • generator b := by
    simp [generator]
  have h1 : Φ x = x.sum fun a m => m • Φ (generator a) := by
    conv_lhs => rw [hx]
    rw [map_finsuppSum]
    simp only [map_zsmul]
  have h2 : ∀ a, Φ (generator a) y = y.sum fun b n => n • Φ (generator a) (generator b) := by
    intro a
    conv_lhs => rw [hy]
    rw [map_finsuppSum]
    simp only [map_zsmul]
  rw [h1, LinearMap.finsupp_sum_apply]
  simp only [LinearMap.smul_apply, h2, Finsupp.sum, Finset.smul_sum, mul_smul]

/-- The bilinear epsilon map with values `(c, m)` on basis pairs, written additively
in `Additive ℂˣ × ℤ`. -/
def epsilonHom (g : ι → κ → ℂˣ × ℤ) :
    IntegralLattice ι →ₗ[ℤ] IntegralLattice κ →ₗ[ℤ] Additive ℂˣ × ℤ :=
  extendBilinear fun a b => (Additive.ofMul (g a b).1, (g a b).2)

/-- Read an element of `Additive ℂˣ × ℤ` as a pair `(c, m)`. -/
def epsilonPair (z : Additive ℂˣ × ℤ) : ℂˣ × ℤ :=
  (Additive.toMul z.1, z.2)

theorem epsilonPair_injective : Function.Injective epsilonPair := by
  rintro ⟨a, m⟩ ⟨b, n⟩ h
  simp only [epsilonPair, Prod.mk.injEq] at h
  exact Prod.ext (Additive.toMul.injective h.1) h.2

theorem epsilonHom_generator (g : ι → κ → ℂˣ × ℤ) (a : ι) (b : κ) :
    epsilonHom g (generator a) (generator b) = (Additive.ofMul (g a b).1, (g a b).2) := by
  simp [epsilonHom, extendBilinear, extend, generator]

theorem epsilonPair_epsilonHom (g : ι → κ → ℂˣ × ℤ) (x : IntegralLattice ι)
    (y : IntegralLattice κ) :
    epsilonPair (epsilonHom g x y) =
      (x.prod fun a m => y.prod fun b n => (g a b).1 ^ (m * n),
        x.sum fun a m => y.sum fun b n => m * n * (g a b).2) := by
  have h1 := toMul_bilinear_eq_prod ((epsilonHom g).compr₂ (LinearMap.fst ℤ _ ℤ)) x y
  have h2 := bilinear_eq_sum ((epsilonHom g).compr₂ (LinearMap.snd ℤ (Additive ℂˣ) ℤ)) x y
  simp only [LinearMap.compr₂_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    epsilonHom_generator, toMul_ofMul, smul_eq_mul] at h1 h2
  exact Prod.ext h1 h2

/-- A virtual epsilon relation built from a basis relation `R` with unique values
`g a b` is the graph of the bilinear map `epsilonHom g`. -/
theorem virtualEpsilon_iff (R : ι → κ → ℂˣ × ℤ → Prop) (g : ι → κ → ℂˣ × ℤ)
    (hg : ∀ a b, R a b (g a b)) (huniq : ∀ a b e, R a b e → e = g a b)
    (x : IntegralLattice ι) (y : IntegralLattice κ) (e : ℂˣ × ℤ) :
    (∃ f : ι → κ → ℂˣ × ℤ,
      (∀ a ∈ x.support, ∀ b ∈ y.support, R a b (f a b)) ∧
      e = (x.prod fun a m => y.prod fun b n => (f a b).1 ^ (m * n),
        x.sum fun a m => y.sum fun b n => m * n * (f a b).2)) ↔
      e = epsilonPair (epsilonHom g x y) := by
  rw [epsilonPair_epsilonHom]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine Prod.ext ?_ ?_
    · refine Finset.prod_congr rfl fun a ha => Finset.prod_congr rfl fun b hb => ?_
      dsimp only
      rw [huniq a b _ (hf a ha b hb)]
    · refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
      dsimp only
      rw [huniq a b _ (hf a ha b hb)]
  · rintro rfl
    exact ⟨g, fun a _ b _ => hg a b, rfl⟩

end Langlands.VirtualRepresentation

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

open Langlands.RankinSelberg

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : Correspondence.NontrivialAdditiveCharacter F)
  (ν : Correspondence.LocalAdditiveHaarMeasure F)

/-- For a self-dual measure, every pair of unitary supercuspidal basis classes has a
JPSS epsilon certificate. -/
theorem exists_isUnitaryBasisPairEpsilonFactor
    (hν : Correspondence.IsSelfDualMeasure F ψ ν) (a b : UnitaryBasis.{uF, uV} F) :
    ∃ e : ℂˣ × ℤ, IsUnitaryBasisPairEpsilonFactor F ψ ν a b e := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨⟨⟨_ | r, hr⟩, π⟩, ha⟩ := a
  · exact absurd hr (lt_irrefl 0)
  obtain ⟨⟨⟨_ | n, hn⟩, τ⟩, hb⟩ := b
  · exact absurd hn (lt_irrefl 0)
  induction π using Quotient.inductionOn with
  | h A =>
    induction τ using Quotient.inductionOn with
    | h B =>
      exact TemperedLFactorGamma.epsilon_exists_of_whittakerType F ψ ⟨ν, hν⟩
        A.obj.representation B.obj.representation
        (supercuspidalRep_isOfWhittakerType F ψ A) (supercuspidalRep_isOfWhittakerType F ψ B)

variable {F ψ ν}

/-- The JPSS epsilon certificate of two unitary supercuspidal basis classes is unique. -/
theorem IsUnitaryBasisPairEpsilonFactor.unique {a b : UnitaryBasis.{uF, uV} F}
    {e e' : ℂˣ × ℤ} (h : IsUnitaryBasisPairEpsilonFactor F ψ ν a b e)
    (h' : IsUnitaryBasisPairEpsilonFactor F ψ ν a b e') : e = e' := by
  obtain ⟨⟨⟨_ | r, hr⟩, π⟩, ha⟩ := a
  · exact absurd hr (lt_irrefl 0)
  obtain ⟨⟨⟨_ | n, hn⟩, τ⟩, hb⟩ := b
  · exact absurd hn (lt_irrefl 0)
  induction π using Quotient.inductionOn with
  | h A =>
    induction τ using Quotient.inductionOn with
    | h B => exact IsPadicSymmetricEpsilonFactor.unique h h'

variable (F ψ ν)

/-- The chosen JPSS epsilon certificate of two unitary supercuspidal basis classes,
for a self-dual measure. -/
def unitaryBasisPairEpsilon (hν : Correspondence.IsSelfDualMeasure F ψ ν)
    (a b : UnitaryBasis.{uF, uV} F) : ℂˣ × ℤ :=
  (exists_isUnitaryBasisPairEpsilonFactor F ψ ν hν a b).choose

/-- For a self-dual measure, the virtual pair epsilon relation on unitary
supercuspidal classes is the graph of a bilinear map. -/
theorem isUnitaryPairEpsilonFactor_iff (hν : Correspondence.IsSelfDualMeasure F ψ ν)
    (x y : UnitaryLattice.{uF, uV} F) (e : ℂˣ × ℤ) :
    IsUnitaryPairEpsilonFactor F ψ ν x y e ↔
      e = epsilonPair (epsilonHom (unitaryBasisPairEpsilon F ψ ν hν) x y) :=
  virtualEpsilon_iff (IsUnitaryBasisPairEpsilonFactor F ψ ν) _
    (fun a b => (exists_isUnitaryBasisPairEpsilonFactor F ψ ν hν a b).choose_spec)
    (fun a b _ he => he.unique (exists_isUnitaryBasisPairEpsilonFactor F ψ ν hν a b).choose_spec)
    x y e

end Langlands.VirtualRepresentation.PadicSupercuspidal

namespace Langlands.VirtualRepresentation.LocalWeil

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (eC : LocalFactor.CommonClosure.ReciprocityFamily F)
  (ε : LocalFactor.NonabelianSystem.Assignment.{uF, uE} F)
  (hε : LocalFactor.NonabelianSystem.IsSystem F eC ε)
  (ψ : Correspondence.NontrivialAdditiveCharacter F)

/-- Every pair of unitary Weil basis classes has an arithmetic epsilon certificate
`c q^(-ms)` for the supplied local-constant system and additive character. -/
def HasUnitaryBasisPairEpsilonFactors : Prop :=
  ∀ a b : UnitaryBasis.{uF, uV} F, ∃ e : ℂˣ × ℤ,
    Correspondence.IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (unitaryBasisPairClass F a) (unitaryBasisPairClass F b) e.1 e.2

/-- Every pair of unitary Weil basis classes has an arithmetic epsilon certificate:
the basis pair classes are the zero-monodromy classes of continuous representatives
(`exists_unitaryRealize_generator`), and the exact bilinear epsilon map gives the
certificate on continuous representations. -/
theorem hasUnitaryBasisPairEpsilonFactors :
    HasUnitaryBasisPairEpsilonFactors.{uF, uV, uE} F eC ε hε ψ := by
  intro a b
  obtain ⟨A, -, hpA⟩ := exists_unitaryRealize_generator F a
  obtain ⟨B, -, hpB⟩ := exists_unitaryRealize_generator F b
  let e := Correspondence.pairEpsilonHom F eC ε hε ψ
    (ExactGrothendieckGroup.ofRepresentation _ A) (ExactGrothendieckGroup.ofRepresentation _ B)
  refine ⟨epsilonPair e, ?_⟩
  rw [hpA, hpB]
  exact Correspondence.isArithmeticPairEpsilonFactor_pairEpsilonHom F eC ε hε ψ A B

/-- The chosen arithmetic epsilon certificate of two unitary Weil basis classes. -/
def unitaryBasisPairEpsilon (hW : HasUnitaryBasisPairEpsilonFactors.{uF, uV, uE} F eC ε hε ψ)
    (a b : UnitaryBasis.{uF, uV} F) : ℂˣ × ℤ :=
  (hW a b).choose

/-- When all basis certificates exist, the virtual arithmetic pair epsilon relation on
unitary Weil classes is the graph of a bilinear map. -/
theorem isUnitaryPairEpsilonFactor_iff
    (hW : HasUnitaryBasisPairEpsilonFactors.{uF, uV, uE} F eC ε hε ψ)
    (x y : UnitaryLattice.{uF, uV} F) (e : ℂˣ × ℤ) :
    IsUnitaryPairEpsilonFactor F eC ε hε ψ x y e ↔
      e = epsilonPair (epsilonHom (unitaryBasisPairEpsilon F eC ε hε ψ hW) x y) :=
  virtualEpsilon_iff
    (fun a b e => Correspondence.IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (unitaryBasisPairClass F a) (unitaryBasisPairClass F b) e.1 e.2) _
    (fun a b => (hW a b).choose_spec)
    (fun a b e he => by
      obtain ⟨h1, h2⟩ := Correspondence.IsArithmeticPairEpsilonFactor.unique F he
        (hW a b).choose_spec
      exact Prod.ext h1 h2)
    x y e

end Langlands.VirtualRepresentation.LocalWeil

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)
  (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ]
    automorphicImage.{uF, uW, uP} F E c v)
  (hT : RelativeGeneratedPositiveIsometry F E c v T)

include hT in
/-- The pair epsilon clause for one self-dual measure and one local-constant system
reduces to witnessed generators, given arithmetic epsilon certificates for all pairs
of unitary Weil basis classes: if some `c q^(-ms)` is both epsilon factors for every
pair of witnessed generators, then the same holds on the whole generated span. -/
theorem relativePairEpsilonFactor_of_witnessed
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ν : Correspondence.LocalAdditiveHaarMeasure (padicField v))
    (hν : Correspondence.IsSelfDualMeasure (padicField v) ψ ν)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
    (ε : LocalFactor.NonabelianSystem.Assignment.{uF, uE} (padicField v))
    (hε : LocalFactor.NonabelianSystem.IsSystem (padicField v) eC ε)
    (hW : LocalWeil.HasUnitaryBasisPairEpsilonFactors.{uF, uW, uE} (padicField v) eC ε hε ψ)
    (hgen : ∀ d e : WitnessedGenerator.{uF, uW, uP} F E c v, ∃ e' : ℂˣ × ℤ,
      LocalWeil.IsUnitaryPairEpsilonFactor (padicField v) eC ε hε ψ
        d.weilElement e.weilElement e' ∧
      PadicSupercuspidal.IsUnitaryPairEpsilonFactor (padicField v) ψ ν
        d.automorphicElement e.automorphicElement e')
    (x y : weilImage.{uF, uW, uP} F E c v) :
    ∃ e' : ℂˣ × ℤ,
      LocalWeil.IsUnitaryPairEpsilonFactor (padicField v) eC ε hε ψ x.1 y.1 e' ∧
        PadicSupercuspidal.IsUnitaryPairEpsilonFactor (padicField v) ψ ν (T x).1 (T y).1 e' := by
  let Φ := epsilonHom (LocalWeil.unitaryBasisPairEpsilon (padicField v) eC ε hε ψ hW)
  let Θ := epsilonHom (PadicSupercuspidal.unitaryBasisPairEpsilon.{uF, uF} (padicField v) ψ ν hν)
  have hgen' : ∀ d e : WitnessedGenerator.{uF, uW, uP} F E c v,
      Φ d.weilElement e.weilElement = Θ d.automorphicElement e.automorphicElement := by
    intro d e
    obtain ⟨e', hw, ha⟩ := hgen d e
    rw [LocalWeil.isUnitaryPairEpsilonFactor_iff (padicField v) eC ε hε ψ hW] at hw
    rw [PadicSupercuspidal.isUnitaryPairEpsilonFactor_iff (padicField v) ψ ν hν] at ha
    exact epsilonPair_injective (hw.symm.trans ha)
  refine ⟨epsilonPair (Φ x.1 y.1), ?_, ?_⟩
  · exact (LocalWeil.isUnitaryPairEpsilonFactor_iff (padicField v) eC ε hε ψ hW _ _ _).mpr rfl
  · rw [PadicSupercuspidal.isUnitaryPairEpsilonFactor_iff (padicField v) ψ ν hν,
      relative_bilinear_graph F E c v T hT Φ Θ hgen' x y]

end Langlands.Global.PoleComparison
