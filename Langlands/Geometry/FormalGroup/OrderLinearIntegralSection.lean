import Langlands.Geometry.FormalGroup.DivisibleHomFaithfulness
import Langlands.Geometry.FormalGroup.PolarizedRationalSectionIso

/-! # Integral order linearity from a rational Hom section -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.RationalSection

open CategoryTheory Opposite TopologicalSpace _root_.AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {A : Type w} [Ring A] [Algebra O A]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : OrderAction A M} {G : OrderAction A N}
variable {U V : Opens (PrimeSpectrum R)} {π : O}

/-- The structure sections and their actual coefficient restrictions detect integral
formal maps locally, coefficient by coefficient. -/
theorem integral_eq_of_local_eq (f g : OpenIntegralHom M N U)
    (he : ∀ x : U, ∃ (V : Opens (PrimeSpectrum R)) (_ : x.val ∈ V) (i : V ⟶ U),
      Hom.algebraMapLinear ((coefficientStructurePresheaf R).map i.op) f =
        Hom.algebraMapLinear ((coefficientStructurePresheaf R).map i.op) g) : f = g := by
  apply Hom.ext
  apply CommLaw.Hom.ext
  apply CoordinateMap.ext
  funext j
  ext μ
  change (MvPowerSeries.coeff μ (f.toHom.toCoordinateMap.series j) :
    StructureSheaf.sectionsSubalgebra R U) = MvPowerSeries.coeff μ (g.toHom.toCoordinateMap.series j)
  apply Subtype.ext
  funext x
  obtain ⟨V, hxV, i, hi⟩ := he x
  have hc := congrArg (fun a : OpenIntegralHom M N V =>
    MvPowerSeries.coeff μ (a.toHom.toCoordinateMap.series j)) hi
  simp only [Hom.algebraMapLinear_coordinates, CoordinateMap.map_series, MvPowerSeries.coeff_map] at hc
  exact congrArg (fun s : StructureSheaf.sectionsSubalgebra R V => s.val ⟨x.val, hxV⟩) hc

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]

/-- Rationalization into the sheaf is faithful on each open for a scalar-divisible source. -/
theorem ofIntegral_injective_of_isPiDivisible (hπ : Irreducible π) (hM : M.IsPiDivisible π) :
    Function.Injective (ofIntegral (F := F) (M := M) (N := N) U) := by
  intro f g hf
  apply integral_eq_of_local_eq f g
  intro x
  exact exists_restrict_integral_eq hπ hM f g hf x.val x.property

/-- A cleared numerator of an order-linear rational section is itself order-linear
on the entire open where that numerator is defined. -/
def integralOrderHomOfScalar (hπ : Irreducible π) (hM : M.IsPiDivisible π)
    {z : RationalSection F M N U} (hz : IsOrderLinear E G z) (i : V ⟶ U)
    (c : F) (f : OpenIntegralHom M N V) (hf : c • restrict i z = ofIntegral V f) :
    OrderAction.Hom
      (E.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op V))))
      (G.map (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op V)))) :=
  ⟨f, fun b => by
    apply ofIntegral_injective_of_isPiDivisible (F := F) hπ hM
    rw [← comp_ofIntegral, ← comp_ofIntegral, ← hf]
    change comp (c • restrict i z) (ofHom (E.action b) V) =
      comp (ofHom (G.action b) V) (c • restrict i z)
    rw [smul_comp, comp_smul]
    apply congrArg (c • ·)
    exact (by simpa only [restrict_comp_hom, restrict_ofHom] using congrArg (restrict i) (hz b))⟩

@[simp]
theorem integralOrderHomOfScalar_val (hπ : Irreducible π) (hM : M.IsPiDivisible π)
    {z : RationalSection F M N U} (hz : IsOrderLinear E G z) (i : V ⟶ U)
    (c : F) (f : OpenIntegralHom M N V) (hf : c • restrict i z = ofIntegral V f) :
    (integralOrderHomOfScalar hπ hM hz i c f hf).val = f := rfl

end Langlands.FormalGroup.ModuleLaw.RationalSection
