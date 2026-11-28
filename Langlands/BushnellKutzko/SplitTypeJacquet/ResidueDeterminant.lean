import Langlands.BushnellKutzko.BetaExtension
import Langlands.BushnellKutzko.SubfieldLatticeChain

/-! # Residue determinants of relative units and simple-stratum groups -/

noncomputable section

open ValuativeRel IsLocalRing

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF uV uD

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {D : Type uD} [Group D]
  {V : Type uV} [AddCommGroup V] [Module F V]

/-- A residue determinant on the relative units reduces the integral determinant,
with its codomain identified with the residue units. -/
def IsRelativeResidueDeterminant (L : LatticeChain 𝒪[F] F V) (b : Module.End F V)
    (hf : IsField (elementAlgebra b)) (δ : relativeUnitFiltration L b 0 →* D) : Prop :=
  let E := elementAlgebra b
  letI : Field E := hf.toField
  letI : FiniteDimensional F E := L.finiteDimensional_subfield E
  letI := subfieldIntegers_isDiscreteValuationRing F E
  ∃ e : (ResidueField (subfieldIntegers F E))ˣ ≃* D,
    ∀ (x : (Module.End E V)ˣ) (hx : relativeEndUnits E x ∈ relativeUnitFiltration L b 0),
      ∃ a : (subfieldIntegers F E)ˣ,
        ((a : subfieldIntegers F E) : E) = LinearMap.det (x : Module.End E V) ∧
        δ ⟨relativeEndUnits E x, hx⟩ = e (Units.map (residue (subfieldIntegers F E)) a)

/-- The residue determinant restricts along an inclusion of relative unit groups. -/
theorem IsRelativeResidueDeterminant.comp_inclusion
    {L M : LatticeChain 𝒪[F] F V} {b : Module.End F V}
    {hf : IsField (elementAlgebra b)} {δ : relativeUnitFiltration M b 0 →* D}
    (hδ : IsRelativeResidueDeterminant M b hf δ)
    (hle : relativeUnitFiltration L b 0 ≤ relativeUnitFiltration M b 0) :
    IsRelativeResidueDeterminant L b hf (δ.comp (Subgroup.inclusion hle)) := by
  obtain ⟨e, he⟩ := hδ
  exact ⟨e, fun x hx => he x (hle hx)⟩

/-- Equality of the parameters identifies their residue determinant conditions. -/
theorem IsRelativeResidueDeterminant.comp_parameterCongr
    {L : LatticeChain 𝒪[F] F V} {b b' : Module.End F V}
    {hf : IsField (elementAlgebra b)} {hf' : IsField (elementAlgebra b')}
    {δ : relativeUnitFiltration L b 0 →* D}
    (hδ : IsRelativeResidueDeterminant L b hf δ) (hb : b' = b) :
    IsRelativeResidueDeterminant L b' hf'
      (δ.comp (MulEquiv.subgroupCongr (congrArg (fun x => relativeUnitFiltration L x 0) hb)).toMonoidHom) := by
  subst b'
  exact hδ

/-- A residue determinant on `J` kills `J¹` and is the residue determinant on
the relative units. -/
def IsSimpleJResidueDeterminant (S : Stratum 𝒪[F] F V) (hs : S.IsSimple)
    (q : S.DefiningSequenceChoice) (δ : simpleJ S.chain S.n S.b q.tail →* D) : Prop :=
  (∀ j : simpleJ S.chain S.n S.b q.tail,
    j.val ∈ simpleJGroup S.chain S.n S.b q.tail 1 → δ j = 1) ∧
    IsRelativeResidueDeterminant S.chain S.b hs.1.1.fst
      (δ.comp (Subgroup.inclusion (relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail)))

end Langlands.BushnellKutzko.SplitTypeJacquet
