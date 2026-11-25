import Langlands.ClassFieldTheory.Local.Artin.FiniteArtin
import Langlands.ClassFieldTheory.Local.FiniteArtinSystemExistenceProof
import Langlands.ClassFieldTheory.Local.General.SuppliedUnramifiedProof
import Langlands.ClassFieldTheory.Local.General.SuppliedValuationSignProof
import Langlands.ClassFieldTheory.Local.Supplied.SuppliedValuationProof
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseFrobenius

/-!
# On `p`-adic fields the general Artin map is the Library's geometric symbol

This file belongs to the Library. For a `p`-adic field `F` (`PadicField p`) with a supplied
topological datum `T` and a finite abelian extension `D` of `F.Carrier`, the Library's geometric
finite Artin symbol `FiniteArtinSystemExistence.geometricSymbol F D` (built from its cohomological
local class field theory) is the general geometric Artin map `geometricFiniteArtin F.Carrier D` of
`FiniteArtin.lean` (NYLL's map), for the local-field structure given by `T`
(`geometricSymbol_eq_geometricFiniteArtin`); in the arithmetic normalization,
`artinSymbol_eq_arithmeticFiniteArtin`.

## Proof

NYLL's maps form a continuous finite Artin family on the Library's finite abelian extensions
(`nyllGeometricFamily F T`) which satisfies the Library's geometric system relation
`GeometricFiniteArtinSystemRelation F T` (`nyllGeometricFamily_relation`): onto, kernel the norm
group, compatible with restriction (from `FiniteArtin.lean`), and on every finite abelian level the
inverse of the symbol of an element of order one induces `x ↦ x ^ q` on residues. The last property
is the Library's ramified transfer `UniverseZero.ramifiedGeometricNormalizationTransfer` applied to
the unramified case (`padicGeometricArtin_unramified`), which is NYLL's residue normalization
`abelianLocalArtinMap_inverseUniformizer_residue_pow` read in the supplied data through the
Library's comparisons `suppliedRelativeValuationExtension`, `suppliedUnramifiedValuedExtension`,
`suppliedValuationSign` and `suppliedResidueCongruence`. The Library's uniqueness theorem
`geometricFiniteArtinSystemUniqueness` then identifies NYLL's family with the Library's
`geometricFamily F T`, and compatibility with restriction carries the identity from subfields of
`AlgebraicClosure F.Carrier` to every finite abelian `D`.
-/

noncomputable section

universe u

namespace Langlands.ClassFieldTheory.Local.Artin

open LocalClassField
open scoped ValuativeRel

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)

section Unramified

/-- NYLL's geometric Artin maps over `p`-adic field data, in the shape of the Artin argument of the
Library's ramified transfer. The local-field structure of `F.Carrier` is the one of `T`; the datum of
the extension is not used. -/
def padicGeometricArtin (D : PadicField.{u} p) [Algebra F.Carrier D.Carrier]
    [IsScalarTower (Padic p) F.Carrier D.Carrier] [IsAbelianGalois F.Carrier D.Carrier]
    (_ : D.TopologicalData) : F.Carrierˣ →* Gal(D.Carrier/F.Carrier) :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := FiniteDimensional.right (Padic p) F.Carrier D.Carrier
  (geometricFiniteArtin F.Carrier D.Carrier).toMonoidHom

/-- Unramified normalization of NYLL's geometric map in the supplied data: on a relatively
unramified level, the inverse of the symbol of an element of order one induces `x ↦ x ^ q` on
residues. -/
theorem padicGeometricArtin_unramified (D : PadicField.{u} p) [Algebra F.Carrier D.Carrier]
    [IsScalarTower (Padic p) F.Carrier D.Carrier] [IsAbelianGalois F.Carrier D.Carrier]
    (TD : D.TopologicalData)
    (h : letI := PadicField.TopologicalData.relativeIntegerAlgebra T TD
      (IsLocalRing.maximalIdeal TD.Integers).ramificationIdx T.Integers = 1)
    (a : F.Carrierˣ) (ha : T.ord (a : F.Carrier) = 1) (x : D.Carrier)
    (hx : TD.discreteValuation x ≤ 1) :
    TD.discreteValuation ((padicGeometricArtin F T D TD a).symm x - x ^ T.residueCardinality) < 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := TD.topology
  let := TD.valuativeRel
  let := TD.localField
  have := FiniteDimensional.right (Padic p) F.Carrier D.Carrier
  have hext : (ValuativeRel.valuation F.Carrier).HasExtension (ValuativeRel.valuation D.Carrier) :=
    UniverseZero.suppliedRelativeValuationExtension p F D T TD
  obtain ⟨hfin, hunr⟩ := UniverseZero.suppliedUnramifiedValuedExtension p F D T TD
  have : Module.Finite 𝒪[F.Carrier] 𝒪[D.Carrier] := hfin
  have : LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension F.Carrier
      D.Carrier := hunr.2 h
  have hxI : ValuativeRel.valuation D.Carrier x ≤ 1 := by
    let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt D.Carrier
    have h1 : e (ValuativeRel.valuation D.Carrier x) ≤ e 1 := by
      rw [map_one]
      exact hx
    exact (map_le_map_iff e).mp h1
  have hval : LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap F.Carrier
      (Additive.ofMul a⁻¹) = 1 := by
    rw [ofMul_inv, map_neg, UniverseZero.suppliedValuationSign p F T a, ha, neg_neg]
  obtain ⟨z, hz, hres⟩ :=
    LocalClassFieldTheory.Universe.abelianLocalArtinMap_inverseUniformizer_residue_pow F.Carrier
      D.Carrier a⁻¹ hval ⟨x, hxI⟩
  have hsymm : (padicGeometricArtin F T D TD a).symm x = (z : D.Carrier) := by
    rw [hz]
    change (geometricFiniteArtin F.Carrier D.Carrier a).symm x =
      geometricFiniteArtin F.Carrier D.Carrier a⁻¹ x
    rw [map_inv]
    rfl
  rw [hsymm]
  have hcong := (UniverseZero.suppliedResidueCongruence D TD z
    (⟨x, hxI⟩ ^ T.residueCardinality)).mp (by
      rw [map_pow]
      exact hres)
  exact hcong

end Unramified

section Family

/-- NYLL's geometric Artin maps of the Library's finite abelian extensions of a `p`-adic field, for
the local-field structure of `T`. -/
def nyllGeometricFamily : letI := T.topology; FiniteArtinFamily F.Carrier :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  fun L => geometricFiniteArtin F.Carrier L.field

/-- NYLL's family satisfies the Library's geometric finite Artin-system relation. -/
theorem nyllGeometricFamily_relation :
    GeometricFiniteArtinSystemRelation F T (nyllGeometricFamily F T) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  refine ⟨⟨fun L => ⟨geometricFiniteArtin_ker F.Carrier L.field,
    geometricFiniteArtin_surjective F.Carrier L.field⟩, fun L M h => ?_⟩, ?_⟩
  · let : Algebra L.field M.field := (Subsemiring.inclusion h).toAlgebra
    have : IsScalarTower F.Carrier L.field M.field := IsScalarTower.of_algebraMap_eq' rfl
    apply ContinuousMonoidHom.ext
    intro a
    exact restrictNormalHom_geometricFiniteArtin F.Carrier L.field M.field a
  · intro L S b hb x hx
    let := FiniteArtinSystemExistence.fieldAlgebra F L
    have := FiniteArtinSystemExistence.fieldTower F L
    have := FiniteArtinSystemExistence.fieldAbelian F L
    let := UniverseZero.finiteInertiaField_isAbelianGalois F (L.asPadicField (p := p)) T
    refine UniverseZero.ramifiedGeometricNormalizationTransfer.{u, u} F (L.asPadicField (p := p)) T
      (UniverseZero.finiteInertiaPadicField F (L.asPadicField (p := p)) T).canonicalTopologicalData S
      (padicGeometricArtin F T)
      (fun D _ _ _ TD hD => padicGeometricArtin_unramified F T D TD hD) ?_ b hb x hx
    refine MonoidHom.ext fun c => ?_
    have := FiniteDimensional.right (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier
    exact restrictNormalHom_geometricFiniteArtin F.Carrier
      (UniverseZero.finiteInertiaField F (L.asPadicField (p := p)) T)
      (L.asPadicField (p := p)).Carrier c

/-- NYLL's family is the Library's geometric family (uniqueness of normalized coherent systems). -/
theorem nyllGeometricFamily_eq_geometricFamily :
    nyllGeometricFamily F T = FiniteArtinSystemExistence.geometricFamily F T :=
  geometricFiniteArtinSystemUniqueness p F T _ _ (nyllGeometricFamily_relation F T)
    (FiniteArtinSystemExistence.geometricFamily_relation F T)

end Family

section Comparison

/-- **Comparison on `p`-adic fields.** For every finite abelian extension `D` of a `p`-adic field
`F`, the Library's geometric finite Artin symbol is the general geometric Artin map (NYLL's) for the
local-field structure of any supplied topological datum `T`. -/
theorem geometricSymbol_eq_geometricFiniteArtin (D : Type u) [Field D] [Algebra F.Carrier D]
    [FiniteDimensional F.Carrier D] [IsAbelianGalois F.Carrier D] (a : F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    FiniteArtinSystemExistence.geometricSymbol F D a = geometricFiniteArtin F.Carrier D a := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let f : D →ₐ[F.Carrier] AlgebraicClosure F.Carrier := IsAlgClosed.lift
  let e : D ≃ₐ[F.Carrier] f.fieldRange := AlgEquiv.ofInjectiveField f
  have hfin : FiniteDimensional F.Carrier f.fieldRange := e.toLinearEquiv.finiteDimensional
  have hab : IsAbelianGalois F.Carrier f.fieldRange := IsAbelianGalois.of_algHom e.symm.toAlgHom
  let L : FiniteAbelianExtension F.Carrier :=
    ⟨{ toIntermediateField := f.fieldRange, finiteDimensional := hfin, isGalois := hab.toIsGalois },
      hab.toIsMulCommutative⟩
  let e' : D ≃ₐ[F.Carrier] L.field := e
  let : Algebra D L.field := e'.toRingHom.toAlgebra
  have : IsScalarTower F.Carrier D L.field := IsScalarTower.of_algHom e'.toAlgHom
  have hL : FiniteArtinSystemExistence.geometricSymbol F L.field a =
      geometricFiniteArtin F.Carrier L.field a := by
    have h := DFunLike.congr_fun (congrArg (fun φ => φ L) (nyllGeometricFamily_eq_geometricFamily F T)) a
    exact h.symm
  rw [← FiniteArtinSystemExistence.restrictNormalHom_geometricSymbol F L.field D a, hL,
    restrictNormalHom_geometricFiniteArtin F.Carrier D L.field a]

/-- The same comparison in the arithmetic normalization: the Library's arithmetic finite Artin
symbol is `arithmeticFiniteArtin`. -/
theorem artinSymbol_eq_arithmeticFiniteArtin (D : Type u) [Field D] [Algebra F.Carrier D]
    [FiniteDimensional F.Carrier D] [IsAbelianGalois F.Carrier D] (a : F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    FiniteArtinSymbol.artinSymbol F D a = arithmeticFiniteArtin F.Carrier D a := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [← FiniteArtinSystemExistence.geometricSymbol_symm, geometricSymbol_eq_geometricFiniteArtin,
    geometricFiniteArtin_eq_inv]
  rfl

end Comparison

end Langlands.ClassFieldTheory.Local.Artin
