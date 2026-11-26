import Langlands.Global.Factors.RelativePairLFactorExact
import Langlands.Global.Factors.RelativeIsometryOperationReduction
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
import Langlands.Representation.RankinSelberg.PadicPairLPolynomialNormalization
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.Whittaker.SupercuspidalKirillovProof

/-!
# Reduction of the pair L-factor clause to witnessed generators

On the side of `GL_n`, every pair of unitary supercuspidal basis classes has a unique
JPSS pair L-polynomial for a self-dual measure, with constant term `1`. The virtual
relation `IsUnitaryPairLFactor` is therefore the graph of a multiplicatively
bilinear function. On the Weil side `unitaryPairLFactor` is multiplicatively
bilinear by definition. Two bilinear functions that agree on all pairs of witnessed
generators agree on the graph of a generated positive isometry, so the pair
L-factor clause of `RelativeIsometryFactorStatement` reduces to witnessed
generators.
-/

noncomputable section

set_option autoImplicit false

universe uF uV uW uP

open Polynomial

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

open Langlands.RankinSelberg Langlands.Whittaker

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- An irreducible supercuspidal representation of `GL_(r+1)` over a p-adic field is
of Whittaker type: it is generic (Gelfand–Kazhdan, via the Kirillov model). -/
theorem supercuspidalRep_isOfWhittakerType
    (ψ : Correspondence.NontrivialAdditiveCharacter F) {r : ℕ}
    (A : letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1)) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType r (standardCharacter ψ r) A.obj.representation := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨ℓ, hℓ⟩ := Whittaker.SupercuspidalKirillovProof.exists_functional
    F.canonicalTopologicalData ψ r A.obj A.property.1 A.property.2
  exact isOfWhittakerType_of_isGeneric F ⟨A.property.1, A.property.2.1, ℓ, hℓ⟩

variable (ψ : Correspondence.NontrivialAdditiveCharacter F)
  (ν : Correspondence.LocalAdditiveHaarMeasure F)

/-- For a self-dual measure, every pair of unitary supercuspidal basis classes has a
JPSS pair L-polynomial. -/
theorem exists_isUnitaryBasisPairLPolynomial
    (hν : Correspondence.IsSelfDualMeasure F ψ ν) (a b : UnitaryBasis.{uF, uV} F) :
    ∃ P : ℂ[X], IsUnitaryBasisPairLPolynomial F ψ ν a b P := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨⟨⟨_ | r, hr⟩, π⟩, ha⟩ := a
  · exact absurd hr (lt_irrefl 0)
  obtain ⟨⟨⟨_ | n, hn⟩, τ⟩, hb⟩ := b
  · exact absurd hn (lt_irrefl 0)
  induction π using Quotient.inductionOn with
  | h A =>
    induction τ using Quotient.inductionOn with
    | h B =>
      exact symmetricLPolynomialExists.{uF, uV, uV} p F ψ ⟨ν, hν⟩ r n _ _
        A.obj.representation B.obj.representation
        (supercuspidalRep_isOfWhittakerType F ψ A) (supercuspidalRep_isOfWhittakerType F ψ B)

variable {F ψ ν}

/-- The JPSS pair L-polynomial of two unitary supercuspidal basis classes is unique. -/
theorem IsUnitaryBasisPairLPolynomial.unique {a b : UnitaryBasis.{uF, uV} F} {P P' : ℂ[X]}
    (h : IsUnitaryBasisPairLPolynomial F ψ ν a b P)
    (h' : IsUnitaryBasisPairLPolynomial F ψ ν a b P') : P = P' := by
  obtain ⟨⟨⟨_ | r, hr⟩, π⟩, ha⟩ := a
  · exact absurd hr (lt_irrefl 0)
  obtain ⟨⟨⟨_ | n, hn⟩, τ⟩, hb⟩ := b
  · exact absurd hn (lt_irrefl 0)
  induction π using Quotient.inductionOn with
  | h A =>
    induction τ using Quotient.inductionOn with
    | h B => exact IsPadicSymmetricLPolynomial.unique h h'

/-- The JPSS pair L-polynomial of two unitary supercuspidal basis classes has
constant term `1`. -/
theorem IsUnitaryBasisPairLPolynomial.coeff_zero {a b : UnitaryBasis.{uF, uV} F} {P : ℂ[X]}
    (h : IsUnitaryBasisPairLPolynomial F ψ ν a b P) : P.coeff 0 = 1 := by
  obtain ⟨⟨⟨_ | r, hr⟩, π⟩, ha⟩ := a
  · exact absurd hr (lt_irrefl 0)
  obtain ⟨⟨⟨_ | n, hn⟩, τ⟩, hb⟩ := b
  · exact absurd hn (lt_irrefl 0)
  induction π using Quotient.inductionOn with
  | h A =>
    induction τ using Quotient.inductionOn with
    | h B => exact IsPadicSymmetricLPolynomial.coeff_zero h

theorem IsUnitaryBasisPairLPolynomial.ne_zero {a b : UnitaryBasis.{uF, uV} F} {P : ℂ[X]}
    (h : IsUnitaryBasisPairLPolynomial F ψ ν a b P) : P ≠ 0 := by
  intro h0
  have h1 := h.coeff_zero
  rw [h0, Polynomial.coeff_zero] at h1
  exact zero_ne_one h1

variable (F ψ ν)

/-- The pair L-factor `1 / P(q^(-s))` of two unitary supercuspidal basis classes, as a
unit of `ℂ(X)`, when a JPSS polynomial exists; `1` otherwise. -/
def unitaryBasisPairLUnit (a b : UnitaryBasis.{uF, uV} F) : (RatFunc ℂ)ˣ := by
  classical
  exact if h : ∃ P : ℂ[X], IsUnitaryBasisPairLPolynomial F ψ ν a b P ∧ P ≠ 0 then
    (Units.mk0 (algebraMap ℂ[X] (RatFunc ℂ) h.choose)
      (RatFunc.algebraMap_ne_zero h.choose_spec.2))⁻¹
  else 1

variable {F ψ ν}

theorem coe_unitaryBasisPairLUnit {a b : UnitaryBasis.{uF, uV} F} {P : ℂ[X]}
    (h : IsUnitaryBasisPairLPolynomial F ψ ν a b P) :
    (unitaryBasisPairLUnit F ψ ν a b : RatFunc ℂ) = (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹ := by
  have hex : ∃ P : ℂ[X], IsUnitaryBasisPairLPolynomial F ψ ν a b P ∧ P ≠ 0 :=
    ⟨P, h, h.ne_zero⟩
  unfold unitaryBasisPairLUnit
  split_ifs
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, hex.choose_spec.1.unique h]

variable (F ψ ν)

/-- The pair L-factor of unitary virtual supercuspidal classes, as a multiplicatively
bilinear map: the basis factors `1 / P(q^(-s))` extended by integral bilinearity. -/
def unitaryPairLHom :
    UnitaryLattice.{uF, uV} F →ₗ[ℤ] UnitaryLattice.{uF, uV} F →ₗ[ℤ] Additive (RatFunc ℂ)ˣ :=
  extendBilinear fun a b => Additive.ofMul (unitaryBasisPairLUnit F ψ ν a b)

theorem unitaryPairLHom_generator (a b : UnitaryBasis.{uF, uV} F) :
    unitaryPairLHom F ψ ν (generator a) (generator b) =
      Additive.ofMul (unitaryBasisPairLUnit F ψ ν a b) := by
  simp [unitaryPairLHom, extendBilinear, extend, generator]

/-- For a self-dual measure, the virtual pair L-factor relation on unitary
supercuspidal classes is the graph of the bilinear map `unitaryPairLHom`. -/
theorem isUnitaryPairLFactor_iff (hν : Correspondence.IsSelfDualMeasure F ψ ν)
    (x y : UnitaryLattice.{uF, uV} F) (L : RatFunc ℂ) :
    IsUnitaryPairLFactor F ψ ν x y L ↔
      L = ((Additive.toMul (unitaryPairLHom F ψ ν x y) : (RatFunc ℂ)ˣ) : RatFunc ℂ) := by
  have hval : ((Additive.toMul (unitaryPairLHom F ψ ν x y) : (RatFunc ℂ)ˣ) : RatFunc ℂ) =
      x.prod fun a m => y.prod fun b n =>
        (unitaryBasisPairLUnit F ψ ν a b : RatFunc ℂ) ^ (m * n) := by
    rw [toMul_bilinear_eq_prod]
    simp only [unitaryPairLHom_generator, toMul_ofMul, Finsupp.prod, Units.coe_prod,
      Units.val_zpow_eq_zpow_val]
  rw [hval]
  constructor
  · rintro ⟨P, hP, rfl⟩
    refine Finset.prod_congr rfl fun a ha => Finset.prod_congr rfl fun b hb => ?_
    dsimp only
    rw [coe_unitaryBasisPairLUnit (hP a ha b hb)]
  · rintro rfl
    classical
    refine ⟨fun a b => (exists_isUnitaryBasisPairLPolynomial F ψ ν hν a b).choose,
      fun a _ b _ => (exists_isUnitaryBasisPairLPolynomial F ψ ν hν a b).choose_spec, ?_⟩
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
    dsimp only
    rw [coe_unitaryBasisPairLUnit
      (exists_isUnitaryBasisPairLPolynomial F ψ ν hν a b).choose_spec]

end Langlands.VirtualRepresentation.PadicSupercuspidal

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- Two integer-bilinear maps, on the Weil side and on the side of `GL_n`, that
agree on all pairs of witnessed generators agree on all pairs of elements of the
generated paired span. -/
theorem pairedLattice_bilinear_eq {M : Type*} [AddCommGroup M]
    (Φ : LocalWeil.UnitaryLattice.{uF, uW} (padicField v) →ₗ[ℤ]
      LocalWeil.UnitaryLattice.{uF, uW} (padicField v) →ₗ[ℤ] M)
    (Θ : PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v) →ₗ[ℤ]
      PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v) →ₗ[ℤ] M)
    (h : ∀ d e : WitnessedGenerator.{uF, uW, uP} F E c v,
      Φ d.weilElement e.weilElement = Θ d.automorphicElement e.automorphicElement)
    {z z' : LocalWeil.UnitaryLattice.{uF, uW} (padicField v) ×
      PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v)}
    (hz : z ∈ pairedLattice.{uF, uW, uP} F E c v)
    (hz' : z' ∈ pairedLattice.{uF, uW, uP} F E c v) :
    Φ z.1 z'.1 = Θ z.2 z'.2 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, rfl⟩ := hz
    induction hz' using Submodule.span_induction with
    | mem z' hz' =>
      obtain ⟨e, rfl⟩ := hz'
      exact h d e
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Prod.fst_add, Prod.snd_add, map_add, hx, hy]
    | smul k x _ hx =>
      simp only [Prod.smul_fst, Prod.smul_snd, map_zsmul, hx]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply, hx, hy]
  | smul k x _ hx =>
    simp only [Prod.smul_fst, Prod.smul_snd, map_zsmul, LinearMap.smul_apply, hx]

variable
  (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ]
    automorphicImage.{uF, uW, uP} F E c v)
  (hT : RelativeGeneratedPositiveIsometry F E c v T)

include hT in
/-- Two integer-bilinear maps that agree on all pairs of witnessed generators agree
on the graph of a generated positive isometry. -/
theorem relative_bilinear_graph {M : Type*} [AddCommGroup M]
    (Φ : LocalWeil.UnitaryLattice.{uF, uW} (padicField v) →ₗ[ℤ]
      LocalWeil.UnitaryLattice.{uF, uW} (padicField v) →ₗ[ℤ] M)
    (Θ : PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v) →ₗ[ℤ]
      PadicSupercuspidal.UnitaryLattice.{uF, uF} (padicField v) →ₗ[ℤ] M)
    (h : ∀ d e : WitnessedGenerator.{uF, uW, uP} F E c v,
      Φ d.weilElement e.weilElement = Θ d.automorphicElement e.automorphicElement)
    (x y : weilImage.{uF, uW, uP} F E c v) :
    Φ x.1 y.1 = Θ (T x).1 (T y).1 :=
  pairedLattice_bilinear_eq F E c v Φ Θ h (relative_graph_mem_pair F E c v T hT x)
    (relative_graph_mem_pair F E c v T hT y)

/-- The virtual pair L-factor of two witnessed Weil elements is the arithmetic pair
L-factor of the zero-monodromy pairs of the two actual local components. -/
theorem witnessed_unitaryPairLFactor (d e : WitnessedGenerator.{uF, uW, uP} F E c v) :
    LocalWeil.unitaryPairLFactor (padicField v) d.weilElement e.weilElement =
      Correspondence.arithmeticPairLFactor (padicField v)
        (RelativeWeilGroup.localPairClass d.weil d.localMap)
        (RelativeWeilGroup.localPairClass e.weil e.localMap) :=
  LocalWeil.unitaryPairLFactor_eq_of_expansion (padicField v) d.weilElement e.weilElement
    ⟨RelativeWeilGroup.localComponent d.weil d.localMap,
      RelativeWeilGroup.localComponent_isContinuous d.localMap d.associated.1⟩
    ⟨RelativeWeilGroup.localComponent e.weil e.localMap,
      RelativeWeilGroup.localComponent_isContinuous e.localMap e.associated.1⟩
    d.weil_expansion e.weil_expansion

include hT in
/-- The pair L-factor clause for one self-dual measure reduces to witnessed
generators: if `L(s, a_d × a_e) = L(s, w_d ⊗ w_e)` for all witnessed generators
`d`, `e`, then `L(s, T x × T y) = L(s, x ⊗ y)` on the whole generated span. -/
theorem relativePairLFactor_of_witnessed
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (ν : Correspondence.LocalAdditiveHaarMeasure (padicField v))
    (hν : Correspondence.IsSelfDualMeasure (padicField v) ψ ν)
    (hgen : ∀ d e : WitnessedGenerator.{uF, uW, uP} F E c v,
      PadicSupercuspidal.IsUnitaryPairLFactor (padicField v) ψ ν
        d.automorphicElement e.automorphicElement
        (LocalWeil.unitaryPairLFactor (padicField v) d.weilElement e.weilElement))
    (x y : weilImage.{uF, uW, uP} F E c v) :
    PadicSupercuspidal.IsUnitaryPairLFactor (padicField v) ψ ν (T x).1 (T y).1
      (LocalWeil.unitaryPairLFactor (padicField v) x.1 y.1) := by
  let Φ := (LocalWeil.exactPairLFactorHom.{uF, uW} (padicField v)).compl₁₂
    (LocalWeil.unitaryRealize (padicField v)) (LocalWeil.unitaryRealize (padicField v))
  let Θ := PadicSupercuspidal.unitaryPairLHom.{uF, uF} (padicField v) ψ ν
  have hΦ : ∀ x y, LocalWeil.unitaryPairLFactor (padicField v) x y =
      ((Additive.toMul (Φ x y) : (RatFunc ℂ)ˣ) : RatFunc ℂ) :=
    fun x y => LocalWeil.unitaryPairLFactor_eq_exact (padicField v) x y
  have hgen' : ∀ d e : WitnessedGenerator.{uF, uW, uP} F E c v,
      Φ d.weilElement e.weilElement = Θ d.automorphicElement e.automorphicElement := by
    intro d e
    have h := (PadicSupercuspidal.isUnitaryPairLFactor_iff (padicField v) ψ ν hν _ _ _).mp (hgen d e)
    rw [hΦ] at h
    exact Additive.toMul.injective (Units.val_injective h)
  rw [PadicSupercuspidal.isUnitaryPairLFactor_iff (padicField v) ψ ν hν, hΦ,
    relative_bilinear_graph F E c v T hT Φ Θ hgen' x y]

end Langlands.Global.PoleComparison
