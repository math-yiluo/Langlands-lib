import Langlands.GroupScheme.QuasiFiniteCommutativeUniformExponentStatement
import Langlands.GroupScheme.FiniteFibreQuasiFiniteNeighbourhood
import Langlands.GroupScheme.FiniteUnitFibreSpreading
import Langlands.GroupScheme.Torus.BoundedExponentSubgroup
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeClosedSubgroupGeometry
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteSubgroupSpreadingStatement

/-! # Reduction of finite-subgroup spreading to a uniform exponent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.FiniteSubgroupSpreadingReduction

variable {S : Scheme.{u}} {H K : GroupScheme S}

/-- Local quasi-finiteness and the uniform-exponent theorem give finite
spreading for a closed subgroup of a multiplicative-type group. -/
theorem finite_neighbourhood_of_uniformExponent
    (hexp : QuasiFiniteCommutativeUniformExponentStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (i : K ⟶ H) (hi : IsClosedSubgroup i)
    [LocallyOfFinitePresentation K.X.hom] [QuasiCompact K.X.hom]
    [QuasiSeparated K.X.hom] (s : S)
    (hs : IsFinite ((baseChange (S.fromSpecResidueField s)).obj K).X.hom) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ n : ℕ, 0 < n ∧
      (∀ (T : Over U.toScheme) (x : T ⟶ ((baseChange U.ι).obj K).X), x ^ n = 1) ∧
      IsFinite ((baseChange U.ι).obj K).X.hom := by
  have : IsAffineHom K.X.hom := hH.closedSubgroup_isAffineHom i hi
  have : IsCommMonObj K.X := hH.closedSubgroup_isCommMonObj i hi
  obtain ⟨Q, hsQ, hQ⟩ :=
    FiniteFibreQuasiFiniteNeighbourhood.exists_locallyQuasiFinite_neighbourhood_of_isFinite_fibre K s hs
  obtain ⟨U, hU, hsU, hUQ⟩ := exists_isAffineOpen_mem_and_subset hsQ
  let j : U.toScheme ⟶ Q.toScheme := S.homOfLE hUQ
  have hj : j ≫ Q.ι = U.ι := S.homOfLE_ι hUQ
  let KU := (baseChange U.ι).obj K
  have : IsAffine U.toScheme := hU
  have : LocallyOfFinitePresentation KU.X.hom := by
    change LocallyOfFinitePresentation (pullback.snd K.X.hom U.ι)
    infer_instance
  have : QuasiCompact KU.X.hom := by
    change QuasiCompact (pullback.snd K.X.hom U.ι)
    infer_instance
  have : QuasiSeparated KU.X.hom := by
    change QuasiSeparated (pullback.snd K.X.hom U.ι)
    infer_instance
  have : IsCommMonObj KU.X :=
    Functor.isCommMonObj_obj (F := Over.pullback U.ι) (M := K.X)
  have : LocallyQuasiFinite KU.X.hom := by
    have : LocallyQuasiFinite ((baseChange Q.ι).obj K).X.hom := hQ
    have : LocallyQuasiFinite ((baseChange j).obj ((baseChange Q.ι).obj K)).X.hom := by
      change LocallyQuasiFinite (pullback.snd _ _)
      infer_instance
    change LocallyQuasiFinite ((baseChange U.ι).obj K).X.hom
    rw [← hj, ← Over.w (baseChangeCompIso Q.ι j K).hom.hom.hom]
    infer_instance
  obtain ⟨n, hn, hpow⟩ :=
    hexp U.toScheme KU inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
  refine ⟨U, hsU, n, hn, hpow, ?_⟩
  exact (hH.baseChange U.ι).isFinite_closedSubgroup_of_uniformPower
    ((baseChange U.ι).map i) (hi.baseChange U.ι) n hn hpow

/-- The finite-neighbourhood conclusion suffices for unit-fibre spreading. -/
theorem unit_neighbourhood_of_uniformExponent
    (hexp : QuasiFiniteCommutativeUniformExponentStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (i : K ⟶ H) (hi : IsClosedSubgroup i)
    [LocallyOfFinitePresentation K.X.hom] [QuasiCompact K.X.hom]
    [QuasiSeparated K.X.hom] (s : S)
    (hs : IsIso ((baseChange (S.fromSpecResidueField s)).obj K).X.hom) :
    ∃ U : S.Opens, s ∈ U ∧ IsIso ((baseChange U.ι).obj K).X.hom := by
  have : IsIso ((baseChange (S.fromSpecResidueField s)).obj K).X.hom := hs
  obtain ⟨U, hsU, n, hn, hpow, hfin⟩ :=
    finite_neighbourhood_of_uniformExponent hexp hH i hi s inferInstance
  exact FiniteUnitFibreSpreading.exists_isIso_neighbourhood_of_finite_neighbourhood
    K s ⟨U, hsU, hfin⟩ hs

/-- A specified finite neighbourhood with a positive exponent on every test point. -/
structure FiniteNeighbourhood (K : GroupScheme S) (s : S) where
  neighbourhood : S.Opens
  point_mem : s ∈ neighbourhood
  exponent : ℕ
  exponent_pos : 0 < exponent
  power_eq_one : ∀ (T : Over neighbourhood.toScheme)
    (x : T ⟶ ((baseChange neighbourhood.ι).obj K).X), x ^ exponent = 1
  finite : IsFinite ((baseChange neighbourhood.ι).obj K).X.hom

/-- Construct a specific finite neighbourhood and exponent from the supplied
uniform-exponent theorem. -/
def finiteNeighbourhood_of_uniformExponent
    (hexp : QuasiFiniteCommutativeUniformExponentStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (i : K ⟶ H) (hi : IsClosedSubgroup i)
    [LocallyOfFinitePresentation K.X.hom] [QuasiCompact K.X.hom]
    [QuasiSeparated K.X.hom] (s : S)
    (hs : IsFinite ((baseChange (S.fromSpecResidueField s)).obj K).X.hom) :
    FiniteNeighbourhood K s := by
  let h := finite_neighbourhood_of_uniformExponent hexp hH i hi s hs
  let he := h.choose_spec.2
  exact {
    neighbourhood := h.choose
    point_mem := h.choose_spec.1
    exponent := he.choose
    exponent_pos := he.choose_spec.1
    power_eq_one := he.choose_spec.2.1
    finite := he.choose_spec.2.2 }

/-- Construct both neighbourhood operations: a finite fibre yields a specified
finite neighbourhood and exponent, and a trivial fibre a specified trivialization. -/
def spreadingNeighbourhoods_of_uniformExponent
    (hexp : QuasiFiniteCommutativeUniformExponentStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (i : K ⟶ H) (hi : IsClosedSubgroup i)
    [LocallyOfFinitePresentation K.X.hom] [QuasiCompact K.X.hom]
    [QuasiSeparated K.X.hom] (s : S) :
    (IsFinite ((baseChange (S.fromSpecResidueField s)).obj K).X.hom →
      FiniteNeighbourhood K s) ×
    (IsIso ((baseChange (S.fromSpecResidueField s)).obj K).X.hom →
      FiniteUnitFibreSpreading.TrivialNeighbourhood K s) :=
  ⟨finiteNeighbourhood_of_uniformExponent hexp hH i hi s,
    fun hs => FiniteUnitFibreSpreading.trivialNeighbourhoodOfExists K s
      (unit_neighbourhood_of_uniformExponent hexp hH i hi s hs)⟩

/-- The unchanged finite-subgroup spreading target follows from the
quasi-finite commutative uniform-exponent theorem. -/
theorem finiteSubgroupSpreading_of_uniformExponent
    (hexp : QuasiFiniteCommutativeUniformExponentStatement.{u}) :
    MultiplicativeTypeFiniteSubgroupSpreadingStatement.{u} := by
  intro S H K i hH hi hlfp hqc hqs s
  have : LocallyOfFinitePresentation K.X.hom := hlfp
  have : QuasiCompact K.X.hom := hqc
  have : QuasiSeparated K.X.hom := hqs
  let D := spreadingNeighbourhoods_of_uniformExponent hexp hH i hi s
  constructor
  · intro hs
    let N := D.1 hs
    exact ⟨N.neighbourhood, N.point_mem, N.exponent, N.exponent_pos,
      N.power_eq_one, N.finite⟩
  · intro hs
    let N := D.2 hs
    refine ⟨N.neighbourhood, N.point_mem, ?_⟩
    rw [← N.structure_eq]
    infer_instance

end Langlands.GroupScheme.FiniteSubgroupSpreadingReduction
