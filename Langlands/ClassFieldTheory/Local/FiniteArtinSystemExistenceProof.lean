import Langlands.ClassFieldTheory.Local.FiniteArtinSymbol
import Langlands.ClassFieldTheory.Local.FiniteArtinSystemStatement
import Langlands.ClassFieldTheory.Local.FiniteArtinSystemUniquenessProof
import Langlands.ClassFieldTheory.Local.NYLL.RamifiedGeometricNormalizationTransferProof
import Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof
import Langlands.ClassFieldTheory.Local.NYLL.UniverseZeroModel
import Langlands.ClassFieldTheory.Local.NormExistenceClosedSupport

/-! # Existence of the coherent geometric finite Artin system

The geometric family sends a unit `a` to the finite Artin symbol of `a⁻¹` on every
actual finite abelian extension. Kernel, surjectivity and restriction come from
`FiniteArtinSymbol`. The geometric residue normalization holds on unramified levels
by the arithmetic coordinate law, and on all levels by the published ramified
transfer. Uniqueness is the published `geometricFiniteArtinSystemUniqueness`.
-/

noncomputable section

namespace Langlands.LocalClassField

open IsLocalRing
open Langlands.ClassFieldTheory.Local

universe u

namespace FiniteArtinSystemExistence

variable {p : ℕ} [Fact p.Prime]

section Unramified

variable (F : PadicField.{u} p) (D : PadicField.{u} p)
    [Algebra F.Carrier D.Carrier] [IsScalarTower (Padic p) F.Carrier D.Carrier]
    [FiniteDimensional F.Carrier D.Carrier]

/-- The absolute ramification index does not depend on the supplied topological datum. -/
theorem ramificationIndex_eq_canonical (T : F.TopologicalData) :
    T.ramificationIndex = F.canonicalTopologicalData.ramificationIndex :=
  congrArg Int.toNat
    (NYLL.ord_eq_of_algEquiv AlgEquiv.refl F.canonicalTopologicalData T (p : F.Carrier))

/-- Relative ramification index one for supplied data gives equal canonical
absolute ramification indices. -/
theorem canonical_ramificationIndex_eq (TF : F.TopologicalData) (TD : D.TopologicalData)
    (h : letI := PadicField.TopologicalData.relativeIntegerAlgebra TF TD
      (maximalIdeal TD.Integers).ramificationIdx TF.Integers = 1) :
    F.canonicalTopologicalData.ramificationIndex =
      D.canonicalTopologicalData.ramificationIndex := by
  rw [← ramificationIndex_eq_canonical F TF, ← ramificationIndex_eq_canonical D TD]
  let := TF.topology
  let := TF.valuativeRel
  let := TF.localField
  let := TD.topology
  let := TD.valuativeRel
  let := TD.localField
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := TF.integerAlgebra
  let := TD.integerAlgebra
  let := PadicField.TopologicalData.relativeIntegerAlgebra TF TD
  let := PadicField.TopologicalData.relativeBaseIntegerTower TF TD
  let := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := D) TF
  let := PadicField.TopologicalData.relativeIntegerFieldTower (E := D) TF
  let := PadicField.TopologicalData.relativeIntegerTower TF TD
  let := (NYLL.relativeIntegerStructure p F D TF TD).1
  let := (NYLL.relativeIntegerStructure p F D TF TD).2
  let : Module TF.Integers D.Carrier := Algebra.toModule
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  let : Module.IsTorsionFree TF.Integers D.Carrier :=
    Module.IsTorsionFree.trans_faithfulSMul TF.Integers F.Carrier D.Carrier
  let : Module.Free TF.Integers TD.Integers :=
    IsIntegralClosure.module_free TF.Integers F.Carrier D.Carrier TD.Integers
  have : IsLocalHom (algebraMap TF.Integers TD.Integers) :=
    PadicField.TopologicalData.relativeIntegerMap_isLocalHom TF TD
  have htower := Ideal.ramificationIdx_tower (R := A)
    (maximalIdeal TF.Integers) (maximalIdeal TD.Integers)
  rw [h, mul_one, TF.ramificationIdx_eq, TD.ramificationIdx_eq] at htower
  exact htower.symm

local instance finiteArtinSystemExistenceProofInstance1 : NontriviallyNormedField F.Carrier := F.canonicalNormedField
local instance finiteArtinSystemExistenceProofInstance2 : NormedAlgebra (Padic p) F.Carrier := F.canonicalNormedAlgebra
local instance finiteArtinSystemExistenceProofInstance3 : IsUltrametricDist F.Carrier :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
local instance finiteArtinSystemExistenceProofInstance4 : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier

/-- The arithmetic generator of an unramified coordinate satisfies the residue
power congruence for every supplied topological datum on the extension. -/
theorem supplied_congruence_of_arithmetic {n : ℕ} [NeZero n]
    (χ : Gal(D.Carrier/F.Carrier) ≃* Multiplicative (ZMod n))
    (hχ : IsArithmeticUnramifiedCoordinate F D.Carrier χ)
    (TF : F.TopologicalData) (TD : D.TopologicalData) (x : D.Carrier)
    (hx : TD.discreteValuation x ≤ 1) :
    TD.discreteValuation
      (χ.symm (Multiplicative.ofAdd 1) x - x ^ TF.residueCardinality) < 1 := by
  have hint : (LocalGalois.extensionIntegers F.Carrier D.Carrier).toSubring = TD.Integers := by
    ext y
    change spectralNorm F.Carrier D.Carrier y ≤ 1 ↔ _
    rw [ArithmeticCoordinate.spectralNorm_eq_canonicalNorm F D]
    exact TD.canonicalNorm_le_one_iff_mem_integers y
  let e : LocalGalois.extensionIntegers F.Carrier D.Carrier ≃+* TD.Integers :=
    RingEquiv.subringCongr hint
  have hxmem : x ∈ TD.Integers := by
    let := TD.topology
    let := TD.valuativeRel
    let := TD.localField
    let i := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt D.Carrier
    change i (ValuativeRel.valuation D.Carrier x) ≤ 1 at hx
    rw [← map_one i] at hx
    exact i.strictMono.le_iff_le.mp hx
  have hq : TF.residueCardinality =
      Nat.card (ResidueField (LocalGalois.baseIntegers F.Carrier)) :=
    (FiniteArtinSystemUniqueness.residueCardinality_eq_canonical F TF).trans
      (Nat.card_congr (ArithmeticCoordinate.baseResidueEquiv F).toEquiv).symm
  let z : LocalGalois.extensionIntegers F.Carrier D.Carrier := e.symm ⟨x, hxmem⟩
  have hres := hχ.2 (residue _ z)
  change residue _ (LocalGalois.integerAut F.Carrier D.Carrier
    (χ.symm (Multiplicative.ofAdd 1)) z) = (residue _ z) ^ _ at hres
  rw [← map_pow] at hres
  have h2 := congrArg (ResidueField.mapEquiv e) hres
  change TD.residue (e (LocalGalois.integerAut F.Carrier D.Carrier
    (χ.symm (Multiplicative.ofAdd 1)) z)) = TD.residue (e (z ^ _)) at h2
  rw [hq]
  exact (NYLL.suppliedResidueCongruence D TD _ _).mp h2

end Unramified

section Geometric

open FiniteArtinSymbol

variable (F : PadicField.{u} p) (D : Type u) [Field D] [Algebra F.Carrier D]
    [FiniteDimensional F.Carrier D] [IsAbelianGalois F.Carrier D]

/-- The geometric finite Artin symbol: the arithmetic symbol of the inverse unit. -/
def geometricSymbol : F.Carrierˣ →* Gal(D/F.Carrier) :=
  (artinSymbol F D).comp invMonoidHom

theorem geometricSymbol_apply (a : F.Carrierˣ) :
    geometricSymbol F D a = artinSymbol F D a⁻¹ :=
  rfl

/-- The inverse of the geometric symbol is the arithmetic symbol. -/
theorem geometricSymbol_symm (a : F.Carrierˣ) :
    (geometricSymbol F D a).symm = artinSymbol F D a := by
  rw [geometricSymbol_apply, map_inv]
  exact AlgEquiv.symm_symm _

theorem ker_geometricSymbol : (geometricSymbol F D).ker = normSubgroup F.Carrier D := by
  ext a
  rw [MonoidHom.mem_ker, geometricSymbol_apply, ← MonoidHom.mem_ker, ker_artinSymbol,
    inv_mem_iff]

theorem geometricSymbol_surjective : Function.Surjective (geometricSymbol F D) := by
  intro σ
  obtain ⟨a, rfl⟩ := artinSymbol_surjective (F := F) (D := D) σ
  exact ⟨a⁻¹, by rw [geometricSymbol_apply, inv_inv]⟩

/-- The geometric symbols of a tower are compatible with restriction. -/
theorem restrictNormalHom_geometricSymbol (E : Type u) [Field E] [Algebra F.Carrier E]
    [FiniteDimensional F.Carrier E] [IsAbelianGalois F.Carrier E] [Algebra E D]
    [IsScalarTower F.Carrier E D] (a : F.Carrierˣ) :
    AlgEquiv.restrictNormalHom E (geometricSymbol F D a) = geometricSymbol F E a := by
  rw [geometricSymbol_apply, geometricSymbol_apply]
  exact restrictNormalHom_artinSymbol E a⁻¹

end Geometric

section Normalization

variable (F : PadicField.{u} p)

/-- The geometric symbol of a finite abelian p-adic extension, in the shape of the
Artin argument of the ramified transfer theorem. The supplied datum is not used. -/
def geometricArtin (D : PadicField.{u} p) [Algebra F.Carrier D.Carrier]
    [IsScalarTower (Padic p) F.Carrier D.Carrier] [IsAbelianGalois F.Carrier D.Carrier]
    (_ : D.TopologicalData) : F.Carrierˣ →* Gal(D.Carrier/F.Carrier) :=
  letI := FiniteDimensional.right (Padic p) F.Carrier D.Carrier
  geometricSymbol F D.Carrier

/-- Geometric normalization on relatively unramified levels. -/
theorem unramified_normalization (TF : F.TopologicalData) (D : PadicField.{u} p)
    [Algebra F.Carrier D.Carrier] [IsScalarTower (Padic p) F.Carrier D.Carrier]
    [IsAbelianGalois F.Carrier D.Carrier] (TD : D.TopologicalData)
    (h : letI := PadicField.TopologicalData.relativeIntegerAlgebra TF TD
      (maximalIdeal TD.Integers).ramificationIdx TF.Integers = 1)
    (a : F.Carrierˣ) (ha : TF.ord (a : F.Carrier) = 1)
    (x : D.Carrier) (hx : TD.discreteValuation x ≤ 1) :
    TD.discreteValuation
      ((geometricArtin F D TD a).symm x - x ^ TF.residueCardinality) < 1 := by
  let := FiniteDimensional.right (Padic p) F.Carrier D.Carrier
  have : NeZero (Module.finrank F.Carrier D.Carrier) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨χ, hχ⟩ := ArithmeticCoordinate.coordinate_exists F D
    (canonical_ramificationIndex_eq F D TF TD h)
  have ha' : F.canonicalTopologicalData.ord (a : F.Carrier) = 1 :=
    (NYLL.ord_eq_of_algEquiv AlgEquiv.refl TF F.canonicalTopologicalData (a : F.Carrier)).trans
      ha
  change TD.discreteValuation
    ((geometricSymbol F D.Carrier a).symm x - x ^ TF.residueCardinality) < 1
  rw [geometricSymbol_symm, FiniteArtinSymbol.artinSymbol_eq_of_arithmeticCoordinate F D.Carrier χ
    hχ a ha']
  exact supplied_congruence_of_arithmetic F D χ hχ TF TD x hx

/-- Geometric normalization at every finite abelian level, by the ramified transfer. -/
theorem ramified_normalization (TF : F.TopologicalData) (E : PadicField.{u} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [IsAbelianGalois F.Carrier E.Carrier] (TE : E.TopologicalData)
    (a : F.Carrierˣ) (ha : TF.ord (a : F.Carrier) = 1)
    (x : E.Carrier) (hx : TE.discreteValuation x ≤ 1) :
    TE.discreteValuation
      ((geometricArtin F E TE a).symm x - x ^ TF.residueCardinality) < 1 := by
  let := FiniteDimensional.right (Padic p) F.Carrier E.Carrier
  let := NYLL.finiteInertiaField_isAbelianGalois F E TF
  refine NYLL.ramifiedGeometricNormalizationTransfer.{u, u} F E TF
    (NYLL.finiteInertiaPadicField F E TF).canonicalTopologicalData TE (geometricArtin F)
    (fun D _ _ _ TD h => unramified_normalization F TF D TD h) ?_ a ha x hx
  refine MonoidHom.ext fun b => ?_
  exact restrictNormalHom_geometricSymbol F E.Carrier (NYLL.finiteInertiaField F E TF) b

/-- The geometric symbol is continuous: its kernel, the norm subgroup, is closed of
finite index, hence open. -/
theorem continuous_geometricArtin (T : F.TopologicalData) (D : PadicField.{u} p)
    [Algebra F.Carrier D.Carrier] [IsScalarTower (Padic p) F.Carrier D.Carrier]
    [IsAbelianGalois F.Carrier D.Carrier] (TD : D.TopologicalData) :
    letI := T.topology
    Continuous (geometricArtin F D TD) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := FiniteDimensional.right (Padic p) F.Carrier D.Carrier
  have hopen : IsOpen ((geometricArtin F D TD).ker : Set F.Carrierˣ) := by
    have := finiteIndex_normSubgroup F D.Carrier
    have hker : (geometricArtin F D TD).ker = normSubgroup F.Carrier D.Carrier :=
      ker_geometricSymbol F D.Carrier
    rw [hker]
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ (isClosed_normSubgroup F D T TD)
  apply continuous_of_continuousAt_one
  refine Filter.Tendsto.mono_right (Filter.tendsto_pure.mpr ?_) (pure_le_nhds _)
  filter_upwards [hopen.mem_nhds (one_mem _)] with x hx
  rw [map_one]
  exact hx

end Normalization

section Family

variable (F : PadicField.{u} p) (T : F.TopologicalData)

/-- The abelian Galois structure of a finite abelian extension. -/
theorem isAbelianGalois_field (L : FiniteAbelianExtension F.Carrier) :
    IsAbelianGalois F.Carrier L.field :=
  ⟨⟩

attribute [local instance] isAbelianGalois_field

/-- The algebra structure over `F` of a finite abelian extension viewed as a p-adic field. -/
abbrev fieldAlgebra (L : FiniteAbelianExtension F.Carrier) :
    Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
  show Algebra F.Carrier L.field from inferInstance

theorem fieldTower (L : FiniteAbelianExtension F.Carrier) :
    letI := fieldAlgebra F L
    IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
  letI := fieldAlgebra F L
  IsScalarTower.of_algebraMap_eq' rfl

theorem fieldAbelian (L : FiniteAbelianExtension F.Carrier) :
    letI := fieldAlgebra F L
    IsAbelianGalois F.Carrier (L.asPadicField (p := p)).Carrier :=
  isAbelianGalois_field F L

theorem continuous_geometricSymbol_field (L : FiniteAbelianExtension F.Carrier) :
    letI := T.topology
    Continuous (geometricSymbol F L.field) := by
  let := fieldAlgebra F L
  have := fieldTower F L
  have := fieldAbelian F L
  exact continuous_geometricArtin F T (L.asPadicField (p := p))
    (L.asPadicField (p := p)).canonicalTopologicalData

/-- The coherent geometric finite Artin family. -/
def geometricFamily : letI := T.topology; FiniteArtinFamily F.Carrier :=
  letI := T.topology
  fun L =>
    { toMonoidHom := geometricSymbol F L.field
      continuous_toFun := continuous_geometricSymbol_field F T L }

theorem geometricFamily_apply (L : FiniteAbelianExtension F.Carrier) (a : F.Carrierˣ) :
    letI := T.topology
    geometricFamily F T L a = geometricSymbol F L.field a :=
  rfl

theorem geometricFamily_relation :
    GeometricFiniteArtinSystemRelation F T (geometricFamily F T) := by
  let := T.topology
  refine ⟨⟨fun L => ⟨ker_geometricSymbol F L.field, geometricSymbol_surjective F L.field⟩,
    fun L M h => ?_⟩, ?_⟩
  · refine ContinuousMonoidHom.ext fun a => ?_
    let : Algebra L.field M.field := (Subsemiring.inclusion h).toAlgebra
    have : IsScalarTower F.Carrier L.field M.field := IsScalarTower.of_algebraMap_eq' rfl
    exact restrictNormalHom_geometricSymbol F M.field L.field a
  · intro L S b hb x hx
    let := fieldAlgebra F L
    have := fieldTower F L
    have := fieldAbelian F L
    exact ramified_normalization F T (L.asPadicField (p := p)) S b hb x hx

end Family

end FiniteArtinSystemExistence

/-- Every p-adic field with a supplied topological datum has exactly one continuous
finite Artin family satisfying the geometric finite Artin-system relation. -/
theorem geometricFiniteArtinSystemExistenceUniqueness :
    GeometricFiniteArtinSystemExistenceUniqueness.{u} := by
  intro p _ F T
  let := T.topology
  exact ⟨FiniteArtinSystemExistence.geometricFamily F T,
    FiniteArtinSystemExistence.geometricFamily_relation F T,
    fun a ha => geometricFiniteArtinSystemUniqueness p F T a _ ha
      (FiniteArtinSystemExistence.geometricFamily_relation F T)⟩

end Langlands.LocalClassField
