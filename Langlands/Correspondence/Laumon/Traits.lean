import Langlands.MathlibBase
import WeilConjectures.AlgebraicGeometry.AffineSpace.PolynomialMap
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts

/-!
# End traits of the affine line and its dual, and the Fourier character

Laumon's local Fourier transforms (Laumon 1987, (2.4.1)) are defined on henselian traits of equal
characteristic `p` with residue field `k`, which arise as the henselizations of the projective
line `D` and its dual `D'` at the rational ends `0, ∞` and `0', ∞'`. This module constructs one
model of these traits, their maps to the global lines, their generic, strictly henselian and
geometric points, and the nontrivial additive character `ψ` used by the Fourier transform.

The henselization `k{x}` of `k[x]_(x)` sits between `k[x]_(x)` and `k[[x]]` (Laumon (2.1.1)).
The model used here is the ring `endRing k` of power series in `t` whose image in `k((t))` lies in
the separable closure `endField k` of `k(t)` in `k((t))`. All four ends use this ring; they differ
by the coordinate of the global line pulled back to `t` (`x`, `1/x`, `x'`, `1/x'`). The statement
`EndTraitHenselizationStatement` asserts that this ring is the henselization of `k[x]` at `x = 0`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace Langlands.Henniart.Laumon

variable (k : Type u) [Field k]

/-- The coordinate `x` of the affine line over `k`. -/
abbrev lineCoordinate : Γ(affineLine k, ⊤) := AffineSpace.coord (Spec (.of k)) PUnit.unit

attribute [local instance] RatFunc.liftAlgebra in
/-- Rational functions embedded in Laurent series by expansion at `t = 0`: Mathlib's scoped
`RatFunc.liftAlgebra`, specialized to the field of Laurent series. -/
instance laurentSeriesRatFuncAlgebra : Algebra (RatFunc k) (LaurentSeries k) :=
  RatFunc.liftAlgebra k (LaurentSeries k)

/-- A constant rational function expands to the constant power series. -/
theorem algebraMap_ratFunc_algebraMap (c : k) :
    algebraMap (RatFunc k) (LaurentSeries k) (algebraMap k (RatFunc k) c) =
      HahnSeries.ofPowerSeries ℤ k (PowerSeries.C c) := by
  rw [← Polynomial.coe_C, RatFunc.coe_coe, RatFunc.algebraMap_eq_C, ← RatFunc.algebraMap_C]
  rfl

/-- The variable of `k(t)` expands to the power series `t`. -/
theorem algebraMap_ratFunc_X :
    algebraMap (RatFunc k) (LaurentSeries k) RatFunc.X =
      HahnSeries.ofPowerSeries ℤ k PowerSeries.X := by
  rw [HahnSeries.ofPowerSeries_X]
  exact RatFunc.coe_X

/-- The fraction field of the end trait: the separable closure of `k(t)` in `k((t))`. -/
def endField : IntermediateField (RatFunc k) (LaurentSeries k) :=
  separableClosure (RatFunc k) (LaurentSeries k)

/-- The ring of the end trait: the elements of `endField k` that are power series. -/
def endRing : Subring (endField k) :=
  (HahnSeries.ofPowerSeries ℤ k).range.comap (endField k).val.toRingHom

/-- The constants `k → endRing k`. -/
def endConstantHom : k →+* endRing k where
  toFun c := ⟨algebraMap (RatFunc k) (endField k) (algebraMap k (RatFunc k) c),
    PowerSeries.C c, (algebraMap_ratFunc_algebraMap k c).symm⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

/-- Power series of the end ring, by the injectivity of `PowerSeries k → LaurentSeries k`. -/
def endPowerSeriesHom : endRing k →+* PowerSeries k :=
  (RingEquiv.ofBijective (HahnSeries.ofPowerSeries ℤ k).rangeRestrict
      ⟨fun _ _ h => HahnSeries.ofPowerSeries_injective (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩).symm.toRingHom.comp
    ((endField k).val.toRingHom.restrict (endRing k) _ fun _ h => h)

/-- The residue map of the end trait: the constant coefficient. -/
def endResidue : endRing k →+* k :=
  PowerSeries.constantCoeff.comp (endPowerSeriesHom k)

/-- The four rational ends: `0` and `∞` of the line `A` with coordinate `x`, and `0'` and `∞'`
of the dual line `A'` with coordinate `x'` (Laumon (2.4.1)–(2.4.2.1)). -/
inductive FourierEnd
  | zero
  | infinity
  | dualZero
  | dualInfinity
  deriving DecidableEq

/-- The exponent `ε` with `coordinate = t ^ ε` on the punctured end: `1` at `0, 0'`, where the
coordinate `x` or `x'` is the uniformizer, and `-1` at `∞, ∞'`, where `1/x` or `1/x'` is. -/
def FourierEnd.coordinateExponent : FourierEnd → ℤ
  | .zero => 1
  | .infinity => -1
  | .dualZero => 1
  | .dualInfinity => -1

/-- The end trait at `e`, the spectrum of `endRing k`. -/
abbrev endTrait (_e : FourierEnd) : Scheme.{u} := Spec (.of (endRing k))

/-- The punctured end trait at `e`, the spectrum of its fraction field `endField k`. -/
abbrev puncturedEnd (_e : FourierEnd) : Scheme.{u} := Spec (.of (endField k))

/-- The uniformizer `t` of the end trait at `e`, the pullback of `x`, `1/x`, `x'` or `1/x'`. -/
def endUniformizer (_e : FourierEnd) : endRing k :=
  ⟨algebraMap (RatFunc k) (endField k) RatFunc.X, PowerSeries.X, (algebraMap_ratFunc_X k).symm⟩

/-- The inclusion of the generic point of the end trait. -/
def puncturedEndToTrait (e : FourierEnd) : puncturedEnd k e ⟶ endTrait k e :=
  Spec.map (CommRingCat.ofHom (endRing k).subtype)

/-- The coordinate of the affine chart containing the end, sent to the uniformizer. -/
def endChartCoordinate (e : FourierEnd) : k[X] →+* endRing k :=
  Polynomial.eval₂RingHom (endConstantHom k) (endUniformizer k e)

/-- The map of the end trait to the affine chart of `D` or `D'` containing the end: the line
`A` or `A'` itself at `0` and `0'`, and the chart with coordinate `1/x` or `1/x'` at `∞` and
`∞'`. -/
def endTraitToChart (e : FourierEnd) : endTrait k e ⟶ affineLine k :=
  Spec.map (CommRingCat.ofHom (endChartCoordinate k e)) ≫ (affineLine.isoSpecPolynomial k).inv

/-- The standard affine chart of the projective line at infinity: the open immersion
`𝔸¹_S → ℙ¹_S`, `y ↦ [1 : y]`, onto the standard open `D₊(T₀)`. Its coordinate `T₁/T₀` is the
inverse of the coordinate `T₀/T₁` of weil-conjectures's `ProjectiveLine.affineChart`. -/
def infinityChart (S : Scheme.{u}) : 𝔸(PUnit.{u + 1}; S) ⟶ ProjectiveLine S :=
  AffineSpace.reindex (fun _ : {j : ULift.{u} (Fin 2) // j ≠ ⟨0⟩} ↦ PUnit.unit) S ≫
    (ProjectiveSpace.standardOpenIso (ULift.{u} (Fin 2)) S ⟨0⟩).inv ≫
      (ProjectiveSpace.standardOpen (ULift.{u} (Fin 2)) S ⟨0⟩).ι

/-- The map of the end trait to the projective line `D` or `D'` over `k`: the chart map
`endTraitToChart` followed by the standard chart `x ↦ [x : 1]` at `0` and `0'`, and by the chart
`y ↦ [1 : y]` at `∞` and `∞'`. -/
def endTraitToProjectiveLine : (e : FourierEnd) →
    endTrait k e ⟶ ProjectiveLine (Spec (.of k))
  | .zero => endTraitToChart k .zero ≫ ProjectiveLine.affineChart (Spec (.of k))
  | .infinity => endTraitToChart k .infinity ≫ infinityChart (Spec (.of k))
  | .dualZero => endTraitToChart k .dualZero ≫ ProjectiveLine.affineChart (Spec (.of k))
  | .dualInfinity => endTraitToChart k .dualInfinity ≫ infinityChart (Spec (.of k))

/-- The coordinate `x` (or `x'`) of the global line on the punctured end: `t ^ ε`. -/
def endLineCoordinate (e : FourierEnd) : endField k :=
  ((endUniformizer k e : endRing k) : endField k) ^ e.coordinateExponent

/-- The map of the punctured end trait to the global affine line `A` or `A'`. -/
def puncturedEndToLine (e : FourierEnd) : puncturedEnd k e ⟶ affineLine k :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom
      ((endRing k).subtype.comp (endConstantHom k)) (endLineCoordinate k e))) ≫
    (affineLine.isoSpecPolynomial k).inv

/-- The separable generic closure of the end trait: the separable closure of `endField k` in the
separable closure of `k((t))`. -/
abbrev endGenericClosure : IntermediateField (endField k) (SeparableClosure (LaurentSeries k)) :=
  separableClosure (endField k) (SeparableClosure (LaurentSeries k))

/-- The geometric generic point `Spec Ω̄ → Spec Ω → η` of the end trait, where `Ω` is
`endGenericClosure k` and `Ω̄` its algebraic closure. -/
def endGeometricGenericPoint (e : FourierEnd) :
    Spec (.of (AlgebraicClosure (endGenericClosure k))) ⟶ puncturedEnd k e :=
  Scheme.FiniteEtale.pointOfAlgebra (AlgebraicClosure (endGenericClosure k))
    (𝟙 (Spec (.of (endField k))))

/-- The constants of the separable generic closure as a `k`-algebra. -/
@[reducible] def endClosureConstantAlgebra : Algebra k (endGenericClosure k) :=
  ((algebraMap (endField k) (endGenericClosure k)).comp
    ((endRing k).subtype.comp (endConstantHom k))).toAlgebra

/-- The algebraic closure of `k` in the separable generic closure. As the separable generic
closure is separable over `k(t)`, these constants form a separable closure of `k`. -/
def endConstants : Subfield (endGenericClosure k) :=
  letI := endClosureConstantAlgebra k
  (algebraicClosure k (endGenericClosure k)).toSubfield

/-- The constants `k → endConstants k`. -/
def endConstantsHom : k →+* endConstants k :=
  letI := endClosureConstantAlgebra k
  (algebraMap k (endGenericClosure k)).codRestrict (endConstants k)
    fun c => (algebraicClosure k (endGenericClosure k)).algebraMap_mem c

/-- The maximal unramified subextension of the separable generic closure: the field generated
over `endField k` by the algebraic closure of `k`. -/
def endUnramifiedField : IntermediateField (endField k) (endGenericClosure k) :=
  IntermediateField.adjoin (endField k) (endConstants k : Set (endGenericClosure k))

/-- The inclusion `endField k → endUnramifiedField k`. -/
def endUnramifiedInclusion : endField k →+* endUnramifiedField k :=
  (algebraMap (endField k) (endGenericClosure k)).codRestrict (endUnramifiedField k)
    fun a => (endUnramifiedField k).algebraMap_mem a

/-- The end ring as an algebra over which the strict ring is integral. -/
@[reducible] def endStrictAlgebra : Algebra (endRing k) (endUnramifiedField k) :=
  ((endUnramifiedInclusion k).comp (endRing k).subtype).toAlgebra

/-- The ring of the strict target trait: the integral closure of `endRing k` in the maximal
unramified subextension. -/
def endStrictRing : Subring (endUnramifiedField k) :=
  letI := endStrictAlgebra k
  (integralClosure (endRing k) (endUnramifiedField k)).toSubring

/-- The inclusion `endRing k → endStrictRing k`. -/
def endStrictRingHom : endRing k →+* endStrictRing k :=
  letI := endStrictAlgebra k
  (algebraMap (endRing k) (endUnramifiedField k)).codRestrict (endStrictRing k)
    fun _ => isIntegral_algebraMap

/-- The strict target trait, the spectrum of `endStrictRing k`. -/
abbrev endStrictTrait : Scheme.{u} := Spec (.of (endStrictRing k))

/-- The strict target trait over the end trait at `e`. -/
def endStrictTraitToTrait (e : FourierEnd) : endStrictTrait k ⟶ endTrait k e :=
  Spec.map (CommRingCat.ofHom (endStrictRingHom k))

/-- The generic point of the strict target trait over the punctured end at `e`; the geometric
generic point `endGeometricGenericPoint k e` factors through it. -/
def endStrictGenericPoint (e : FourierEnd) :
    Spec (.of (endUnramifiedField k)) ⟶ puncturedEnd k e :=
  Spec.map (CommRingCat.ofHom (endUnramifiedInclusion k))

/-- The geometric special point `Spec k̄ → Spec k → T` of the end trait at `e`, through the
residue map. -/
def endGeometricSpecialPoint (e : FourierEnd) :
    Spec (.of (AlgebraicClosure k)) ⟶ endTrait k e :=
  Spec.map (CommRingCat.ofHom ((algebraMap k (AlgebraicClosure k)).comp (endResidue k)))

/-- The end ring is the henselization of `k[x]` at `x = 0`, with uniformizer the coordinate: it
is a henselian discrete valuation ring with uniformizer `endUniformizer k .zero`, and every ring
map `φ : k[x] → B` to a henselian local ring with `φ⁻¹(𝔪_B) = (x)` extends uniquely to a local
map along `endChartCoordinate k .zero`. -/
def EndTraitHenselizationStatement : Prop :=
  ∀ (k : Type u) [Field k],
    HenselianLocalRing (endRing k) ∧ IsDiscreteValuationRing (endRing k) ∧
      Irreducible (endUniformizer k .zero) ∧
      ∀ (B : Type u) [CommRing B] [HenselianLocalRing B] (φ : k[X] →+* B),
        Ideal.comap φ (IsLocalRing.maximalIdeal B) = Ideal.span {X} →
        ∃! ψ : endRing k →+* B, IsLocalHom ψ ∧ ψ.comp (endChartCoordinate k .zero) = φ

section Character

variable (ℓ : ℕ) [Fact ℓ.Prime] [Finite k]

local notation "E" => PadicAlgCl ℓ

/-- The characteristic of a finite field is prime. -/
instance fact_ringChar_prime : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩

/-- A chosen primitive `p`-th root of unity in `E = PadicAlgCl ℓ`, where `p = ringChar k`. -/
def fourierRoot : E :=
  (HasEnoughRootsOfUnity.exists_isPrimitiveRoot E (ringChar k)).choose

/-- The chosen root is a primitive `p`-th root of unity. -/
theorem fourierRoot_isPrimitiveRoot : IsPrimitiveRoot (fourierRoot k ℓ) (ringChar k) :=
  (HasEnoughRootsOfUnity.exists_isPrimitiveRoot E (ringChar k)).choose_spec

/-- The additive character `ψ(a) = ζ ^ Tr_{k/𝔽_p}(a)` of `k` with values in `E`, for the chosen
primitive `p`-th root of unity `ζ`. -/
def fourierCharacter : AddChar k E :=
  letI : Algebra (ZMod (ringChar k)) k := ZMod.algebra k (ringChar k)
  (AddChar.zmodChar (ringChar k) (fourierRoot_isPrimitiveRoot k ℓ).pow_eq_one).compAddMonoidHom
    (Algebra.trace (ZMod (ringChar k)) k).toAddMonoidHom

/-- The character `ψ` is nontrivial. -/
theorem fourierCharacter_ne_one : fourierCharacter k ℓ ≠ 1 := by
  let : Algebra (ZMod (ringChar k)) k := ZMod.algebra k (ringChar k)
  obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate k (one_ne_zero (α := k))
  rw [one_mul] at ha
  refine AddChar.ne_one_iff.2 ⟨a, fun hf => ha ?_⟩
  exact ((AddChar.zmodChar_primitive_of_primitive_root (ringChar k)
    (fourierRoot_isPrimitiveRoot k ℓ)).zmod_char_eq_one_iff (ringChar k) _).mp hf

end Character

end Langlands.Henniart.Laumon
