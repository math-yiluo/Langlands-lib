import Langlands.Geometry.FormalGroup.SpecialKernelRank
import Langlands.Geometry.FormalGroup.AtlasQuasiIsogenyHeight
import Langlands.Geometry.FormalGroup.AtlasOrderRationalMorphism
import Langlands.Geometry.FormalGroup.GlobalRationalHeight
import Mathlib.FieldTheory.AlgebraicClosure

/-! # Pointwise height divisibility for special quasi-isogenies -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

universe u s

namespace Langlands.FormalGroup.LocalDivision.SpecialModule

open CategoryTheory TopologicalSpace ValuativeRel ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {π : 𝒪[K]}

local notation "d" => CentralSimple.reducedDegree K D
set_option quotPrecheck false in
local notation "q" => Nat.card 𝓀[K]

section Field

variable {k : Type u} [Field k] [Algebra 𝒪[K] k] {X Y : SpecialModule K D ι k}
variable (z : ModuleLaw.OrderAction.QuasiIsogeny K X.order Y.order)
variable (hX : X.HasHeightSquared π) (hY : Y.HasHeightSquared π)

/-- The actual numerator of a field-valued special quasi-isogeny carries an integral
rank exponent in the central residue normalization. -/
def fieldHeightPresentation : RationalHom.GlobalHeightPresentation π q z.hom.val := by
  let P := z.toModuleQuasiIsogeny.scalarIsogenyPresentationOverRing hX.1
    hX.2.piDivisible hY.2.piDivisible
  let Pker := Classical.choice P.isIsogeny.2
  let h := Hom.finrank_finiteKernel_eq_pow_residueCard hX.1 hX.2 hY.2.piDivisible P.isIsogeny Pker
  exact ⟨P, h.choose, h.choose_spec ▸ P.isIsogeny.hasKernelRank_fieldDegree⟩

/-- The numerator of the actual clearing remains linear for the full division order. -/
def fieldHeightNumerator : ModuleLaw.OrderAction.Hom X.order Y.order := by
  let P := fieldHeightPresentation z hX hY
  refine ⟨P.representative, fun a => ?_⟩
  apply RationalHom.ofHom_injective_of_piDivisible (F := K) hX.1 hX.2.piDivisible
  rw [RationalHom.ofHom_comp, RationalHom.ofHom_comp, ← P.represents,
    RationalHom.smul_comp, RationalHom.comp_smul, z.hom.commutes]

theorem dvd_heightFunction_overField [Algebra 𝓀[K] k] [IsScalarTower 𝒪[K] 𝓀[K] k]
    [IsAlgClosed k] (x : (⊤ : Opens (PrimeSpectrum k))) :
    (d : ℤ) ∣ z.toModuleQuasiIsogeny.heightFunction hX.1 hX.2 hY.2 x := by
  let P := fieldHeightPresentation z hX hY
  let f := fieldHeightNumerator z hX hY
  have hf : f.val.HasHeight q P.numeratorHeight := ⟨P.isIsogeny, P.numeratorRank⟩
  have hn : d ∣ P.numeratorHeight := dvd_integralHeight (X := X) (Y := Y) f hf
  have hh := congrFun (z.toModuleQuasiIsogeny.heightFunction_eq hX.1 hX.2 hY.2
    (P.hasHeightFunction hX.2)) x
  rw [hh]
  change (d : ℤ) ∣ (P.numeratorHeight : ℤ) - (P.exponent : ℤ) * ((d ^ 2 : ℕ) : ℤ)
  refine dvd_sub (Int.natCast_dvd_natCast.mpr hn) ?_
  refine ⟨(P.exponent : ℤ) * (d : ℤ), ?_⟩
  push_cast
  ring

end Field

/-- A central uniformizer killed in a coefficient field forces its structural map to descend to
the central residue field. -/
private def residueFieldMap {k : Type u} [Field k] [Algebra 𝒪[K] k]
    (hπ : Irreducible π) (hπk : algebraMap 𝒪[K] k π = 0) : 𝓀[K] →+* k :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[K]) (algebraMap 𝒪[K] k) fun a ha => by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, hπk, zero_mul]

section Affine

variable {R : Type u} [CommRing R] [Algebra 𝒪[K] R] {X Y : SpecialModule K D ι R}
variable (z : ModuleLaw.OrderAction.QuasiIsogeny K X.order Y.order)
variable (hX : X.HasHeightSquared π) (hY : Y.HasHeightSquared π)

private theorem dvd_heightFunction_atGeometric {k : Type u} [Field k] [IsAlgClosed k]
    (x : (⊤ : Opens (PrimeSpectrum R))) (φ : R →+* k) (y : PrimeSpectrum k)
    (hxy : y.comap φ = x.val) :
    (d : ℤ) ∣ z.toModuleQuasiIsogeny.heightFunction hX.1 hX.2 hY.2 x := by
  let : Algebra R k := φ.toAlgebra
  let : Algebra 𝒪[K] k := Algebra.compHom k (algebraMap 𝒪[K] R)
  let : IsScalarTower 𝒪[K] R k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let θ := IsScalarTower.toAlgHom 𝒪[K] R k
  have hπk : algebraMap 𝒪[K] k π = 0 := by
    rw [IsScalarTower.algebraMap_apply 𝒪[K] R k]
    exact (hX.2.1.base_nilpotent.map (algebraMap R k)).eq_zero
  let j := residueFieldMap hX.1 hπk
  let : Algebra 𝓀[K] k := j.toAlgebra
  let : IsScalarTower 𝒪[K] 𝓀[K] k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let y' : (⊤ : Opens (PrimeSpectrum k)) := ⟨y, by trivial⟩
  have hx : coefficientOpenPoint θ ⊤ y' = x := Subtype.ext hxy
  let w := ModuleLaw.OrderAction.QuasiIsogeny.map θ z
  have hw := dvd_heightFunction_overField (X := X.mapSameUniverse θ) (Y := Y.mapSameUniverse θ)
    w (hX.map θ) (hY.map θ) y'
  have hval := congrFun (z.toModuleQuasiIsogeny.heightFunction_eq_of_map hX.1 hX.2 hY.2 θ
    w.toModuleQuasiIsogeny rfl) y'
  change _ = z.toModuleQuasiIsogeny.heightFunction hX.1 hX.2 hY.2 (coefficientOpenPoint θ ⊤ y') at hval
  rw [hx] at hval
  exact hval ▸ hw

/-- Each signed height of an actual special quasi-isogeny is divisible by the division degree.
The geometric point lies over the chosen prime, so the field calculation reads the height there. -/
theorem dvd_heightFunction (x : (⊤ : Opens (PrimeSpectrum R))) :
    (d : ℤ) ∣ z.toModuleQuasiIsogeny.heightFunction hX.1 hX.2 hY.2 x := by
  let I := x.val.asIdeal
  let : I.IsPrime := x.val.isPrime
  let E := I.ResidueField
  let k := AlgebraicClosure E
  let φ := (algebraMap E k).comp (algebraMap R E)
  let y : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
  apply dvd_heightFunction_atGeometric z hX hY x φ y
  dsimp only [φ]
  rw [PrimeSpectrum.comap_comp_apply]
  have hmem : (y.comap (algebraMap E k)).comap (algebraMap R E) ∈ ({x.val} : Set (PrimeSpectrum R)) := by
    rw [← x.val.residueField_comap]
    exact ⟨y.comap (algebraMap E k), rfl⟩
  exact hmem

end Affine

end Langlands.FormalGroup.LocalDivision.SpecialModule

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory TopologicalSpace ValuativeRel ModuleLaw

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {π : 𝒪[K]} {R : Type u} [CommRing R] [Algebra 𝒪[K] R]
variable {X Y : SpecialAtlas K D ι R} {h : X.atlas.opens = Y.atlas.opens}
variable (z : BasicAtlas.OrderAction.QuasiIsogeny K X.order Y.order h)
variable (hX : X.HasHeightSquared π) (hY : Y.HasHeightSquared π)

/-- The actual global signed height on a special atlas is pointwise divisible by the
reduced division degree. -/
theorem dvd_heightFunction (x : PrimeSpectrum R) :
    (CentralSimple.reducedDegree K D : ℤ) ∣ z.toAtlasQuasiIsogeny.heightFunction hX.1 hX.2.2 hY.2.2 x := by
  have he : ∃ b : Y.atlas.opens, b.val ∉ x.asIdeal := by
    by_contra! hx
    have hh : Ideal.span Y.atlas.opens ≤ x.asIdeal := Ideal.span_le.mpr (fun a ha => hx ⟨a, ha⟩)
    rw [Y.atlas.covers] at hh
    exact x.isPrime.ne_top (top_unique hh)
  obtain ⟨b, hb⟩ := he
  have hpoint : x ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away b.val))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away b.val) b.val]
    exact (PrimeSpectrum.mem_basicOpen b.val x).mpr hb
  obtain ⟨y, hy⟩ := hpoint
  let A := CommAlgCat.of R (Localization.Away b.val)
  let : Algebra 𝒪[K] A := coefficientAlgebra A
  let hA : IsUnit (algebraMap R A b.val) := IsLocalization.Away.algebraMap_isUnit b.val
  let a := BasicAtlas.sourceChart h b
  let w := z.onChart A b hA
  let y' : (⊤ : Opens (PrimeSpectrum A)) := ⟨y, by trivial⟩
  have hd := SpecialModule.dvd_heightFunction
    (X := X.chartTestModule A a hA) (Y := Y.chartTestModule A b hA) w
    (X.chartTest_height hX A a hA) (Y.chartTest_height hY A b hA) y'
  change (CentralSimple.reducedDegree K D : ℤ) ∣
    z.toAtlasQuasiIsogeny.heightOnChart hX.1 hX.2.2 hY.2.2 A b hA y' at hd
  rw [z.toAtlasQuasiIsogeny.heightOnChart_eq_heightFunction hX.1 hX.2.2 hY.2.2 A b hA,
    show y'.val.comap (algebraMap R A) = x from hy] at hd
  exact hd

end Langlands.FormalGroup.LocalDivision.SpecialAtlas
