import Langlands.Global.AdelicEisensteinCompactBounds
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicIwasawaHeight
import Langlands.Global.EisensteinConstantTerm.Points
import Mathlib.MeasureTheory.Function.L2Space

/-! # Weighted Hilbert spaces from an adelic Siegel domain

Bernstein–Lapid §§7.3–7.4, on an actual closed subgroup (intended as the minimal
parabolic) with supplied Iwasawa compact and supplied domain. The automorphic
measure is defined by pushing forward the weighted domain measure, so that
restriction-pullback is isometric by construction.
-/

noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Set MeasureTheory
open scoped CategoryTheory.MonObj Pointwise ENNReal

namespace Langlands.Global.WeightedSiegel

open AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  (p : P ⟶ G)

/-- The actual image of `P(F)` in `G(𝔸)`. -/
def parabolicPrincipalSubgroup : Subgroup (AdelicGroupPoints F G) :=
  (rationalSubgroup F P).map (map F P G p).toMonoidHom

omit [IsAffine G.X.left] [IsAffine P.X.left] in
theorem parabolicPrincipalSubgroup_le : parabolicPrincipalSubgroup F p ≤ rationalSubgroup F G := by
  rintro _ ⟨y, ⟨q, rfl⟩, rfl⟩
  change map F P G p (rational F P q) ∈ rationalSubgroup F G
  rw [map_rational]
  exact ⟨_, rfl⟩

/-- The actual left quotient `P(F) \ G(𝔸)`, called `Z` in BL for `P = P₀`. -/
abbrev DomainQuotient := LeftCosetSpace (parabolicPrincipalSubgroup F p)

/-- The quotient projection from the rational-parabolic quotient to the
rational quotient of the full adelic group. -/
def toAutomorphic : DomainQuotient F p → RationalQuotient F G :=
  LeftCosetSpace.lift (parabolicPrincipalSubgroup F p) (LeftCosetSpace.mk (rationalSubgroup F G))
    fun dlt g => LeftCosetSpace.mk_subgroup_mul (rationalSubgroup F G)
      ⟨(dlt : AdelicGroupPoints F G), parabolicPrincipalSubgroup_le F p dlt.2⟩ g

omit [IsAffine G.X.left] [IsAffine P.X.left] in
@[simp]
theorem toAutomorphic_mk (g : AdelicGroupPoints F G) :
    toAutomorphic F p (LeftCosetSpace.mk (parabolicPrincipalSubgroup F p) g) =
      LeftCosetSpace.mk (rationalSubgroup F G) g := rfl

omit [IsAffine G.X.left] [IsAffine P.X.left] in
theorem continuous_toAutomorphic : Continuous (toAutomorphic F p) :=
  LeftCosetSpace.continuous_lift _ _ _ (LeftCosetSpace.continuous_mk _)

variable [LocallyOfFiniteType G.X.hom]

omit [IsAffine P.X.left] in
theorem isDiscrete_parabolicPrincipalSubgroup :
    IsDiscrete (parabolicPrincipalSubgroup F p : Set (AdelicGroupPoints F G)) :=
  (isDiscrete_rationalSubgroup F G).mono (parabolicPrincipalSubgroup_le F p)

instance : BorelSpace (DomainQuotient F p) :=
  LeftCosetSpace.discreteQuotientBorelSpace _ (isDiscrete_parabolicPrincipalSubgroup F p)

/-- Haar quotient measure on the rational-parabolic quotient, obtained by
counting measure on the discrete subgroup `P(F)`. -/
def domainHaarMeasure : Measure (DomainQuotient F p) :=
  LeftCosetSpace.haarQuotientMeasure _ (isDiscrete_parabolicPrincipalSubgroup F p)

variable [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K)

omit [LocallyOfFiniteType G.X.hom] in
private theorem height_left_principal (dlt : parabolicPrincipalSubgroup F p) (g : AdelicGroupPoints F G) :
    hK.height ((dlt : AdelicGroupPoints F G) * g) = hK.height g := by
  obtain ⟨y, ⟨q, rfl⟩, hy⟩ := dlt.2
  rw [← hy]
  exact hK.height_rational_mul q g

/-- Iwasawa height on the rational-parabolic left quotient. -/
def domainHeight : DomainQuotient F p → RealCharacterDual F P :=
  LeftCosetSpace.lift _ hK.height (height_left_principal F p hK)

omit [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem domainHeight_mk (g : AdelicGroupPoints F G) :
    domainHeight F p hK (LeftCosetSpace.mk (parabolicPrincipalSubgroup F p) g) = hK.height g := rfl

omit [LocallyOfFiniteType G.X.hom] in
theorem continuous_domainHeight : Continuous (domainHeight F p hK) :=
  LeftCosetSpace.continuous_lift _ _ _ hK.continuous_height

/-- The `w⁻²` density for `w = exp(ell(H_P))`, with a general supplied scalar
function of height (which may be piecewise linear in central orthants). -/
def domainDensity (ell : RealCharacterDual F P → ℝ) (z : DomainQuotient F p) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-2 * ell (domainHeight F p hK z)))

theorem measurable_domainDensity {ell : RealCharacterDual F P → ℝ} (hell : Continuous ell) :
    Measurable (domainDensity F p hK ell) :=
  (ENNReal.continuous_ofReal.comp ((continuous_const.mul
    (hell.comp (continuous_domainHeight F p hK))).rexp)).measurable

/-- The weighted measure on a supplied domain, realized as a restricted measure
on the ambient rational-parabolic quotient. -/
def domainMeasure (ell : RealCharacterDual F P → ℝ) (S : Set (DomainQuotient F p)) :
    Measure (DomainQuotient F p) :=
  ((domainHaarMeasure F p).restrict S).withDensity (domainDensity F p hK ell)

/-- The automorphic measure giving the norm pulled back from the weighted domain.
No choice of a measurable section or fibre-counting estimate is needed for
this construction on a fixed domain. -/
def automorphicMeasure (ell : RealCharacterDual F P → ℝ) (S : Set (DomainQuotient F p)) :
    Measure (RationalQuotient F G) :=
  Measure.map (toAutomorphic F p) (domainMeasure F p hK ell S)

/-- The actual weighted domain and automorphic norms are related by a
measure-preserving projection for the pushforward realization. -/
theorem measurePreserving_toAutomorphic (ell : RealCharacterDual F P → ℝ) (S : Set (DomainQuotient F p)) :
    MeasurePreserving (toAutomorphic F p) (domainMeasure F p hK ell S)
      (automorphicMeasure F p hK ell S) :=
  ⟨(continuous_toAutomorphic F p).measurable, rfl⟩

/-- The weighted Hilbert space on the automorphic quotient attached to a fixed
supplied domain. -/
abbrev HilbertSpace (ell : RealCharacterDual F P → ℝ) (S : Set (DomainQuotient F p)) :=
  Lp ℂ 2 (automorphicMeasure F p hK ell S)

/-- Pullback from the automorphic stage to the weighted rational-parabolic
stage is isometric. -/
def pullback (ell : RealCharacterDual F P → ℝ) (S : Set (DomainQuotient F p)) :
    HilbertSpace F p hK ell S →ₗᵢ[ℂ] Lp ℂ 2 (domainMeasure F p hK ell S) :=
  Lp.compMeasurePreservingₗᵢ ℂ (toAutomorphic F p) (measurePreserving_toAutomorphic F p hK ell S)

/-- The pullback is composition with the quotient projection on representatives. -/
theorem pullback_ae (ell : RealCharacterDual F P → ℝ) (S : Set (DomainQuotient F p))
    (f : HilbertSpace F p hK ell S) :
    pullback F p hK ell S f =ᵐ[domainMeasure F p hK ell S] f ∘ toAutomorphic F p :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_toAutomorphic F p hK ell S)

/-- Membership of a strongly measurable automorphic function is exactly
membership of its pullback on the weighted domain. -/
theorem memLp_iff_pullback (ell : RealCharacterDual F P → ℝ) (S : Set (DomainQuotient F p))
    {f : RationalQuotient F G → ℂ} (hf : StronglyMeasurable f) :
    MemLp f 2 (automorphicMeasure F p hK ell S) ↔
      MemLp (f ∘ toAutomorphic F p) 2 (domainMeasure F p hK ell S) :=
  memLp_map_measure_iff hf.aestronglyMeasurable ((continuous_toAutomorphic F p).measurable.aemeasurable)

end Langlands.Global.WeightedSiegel
