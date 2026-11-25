import Langlands.Galois.Local.ResidueProjectionStatement
import Langlands.Galois.Local.ResidueProjectionIntegers
import Langlands.Galois.Local.ResidueProjectionResidueField
import Langlands.Galois.Local.ResidueProjectionQuotient

/-!
# The residue projection of a separable closure: proof of the statement

`residueProjectionProperties K Ω` proves `ResidueProjectionProperties K Ω`
(`Galois/Local/ResidueProjectionStatement.lean`) for a nonarchimedean local field `K` of
either characteristic and a separable closure `Ω` of `K`, by assembling one theorem per
clause, and `residueProjectionExactness` proves `ResidueProjectionExactness`.
-/

open ValuativeRel IsLocalRing

namespace Langlands.LocalGalois

universe uK uΩ

/-- The residue projection of a separable closure `Ω` of a nonarchimedean local field `K` of
either characteristic has all the properties of `ResidueProjectionProperties K Ω`. -/
theorem residueProjectionProperties (K : Type uK) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] :
    ResidueProjectionProperties K Ω := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : Algebra.IsAlgebraic K Ω := Algebra.IsSeparable.isAlgebraic K Ω
  refine ⟨localNormedField_topology K, ?_⟩
  let := localNormedField K
  let := localNormedField_ultrametric K
  let := localNormedField_complete K
  -- `Finite 𝓀[K]` is the anonymous Mathlib instance of
  -- `Mathlib/NumberTheory/LocalField/Basic.lean` for nonarchimedean local fields.
  exact ⟨inferInstance,
    SepClosed.closureValuation_extends K Ω, localNormedField_integer K,
    SepClosed.isIntegral_iff_mem_closureIntegers K Ω,
    SepClosed.closureValuation_algEquiv_apply K Ω,
    SepClosed.residueAlgebra_isAlgClosure K Ω,
    SepClosed.residueClosureEquiv_residue_integerMap K Ω,
    SepClosed.absoluteResidueHom_residue K Ω,
    SepClosed.absoluteResidueHom_continuous K Ω,
    SepClosed.absoluteResidueHom_surjective K Ω,
    SepClosed.isOpenMap_absoluteResidueHom K Ω,
    SepClosed.absoluteResidueHom_ker K Ω,
    SepClosed.mem_absoluteInertia_iff K Ω,
    SepClosed.absoluteInertia_eq_comap_decompositionHom K Ω,
    SepClosed.absoluteInertia_normal K Ω,
    SepClosed.isClosed_absoluteInertia K Ω,
    SepClosed.compactSpace_absoluteInertia K Ω,
    SepClosed.totallyDisconnectedSpace_absoluteInertia K Ω,
    SepClosed.t2Space_absoluteInertia K Ω,
    ⟨SepClosed.absoluteResidueQuotientEquiv K Ω,
      SepClosed.absoluteResidueQuotientEquiv_apply K Ω⟩,
    fun E _ σ y => SepClosed.absoluteResidueHom_restrictNormal K Ω E σ y⟩

/-- `ResidueProjectionExactness`: the residue projection properties hold for every
nonarchimedean local field `K` and every separable closure `Ω` of `K`. -/
theorem residueProjectionExactness : ResidueProjectionExactness.{uK, uΩ} :=
  fun K _ _ _ _ Ω _ _ _ => residueProjectionProperties K Ω

end Langlands.LocalGalois
