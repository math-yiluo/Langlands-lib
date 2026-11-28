import Langlands.JacquetLanglands.DivisionUnits
import Langlands.BaseChange.RegularCoefficientSlice
import Langlands.Galois.Local.AbsoluteDefinitions

/-! # Continuous local choices of regular elliptic correspondents -/

noncomputable section

open scoped TensorProduct

universe u

namespace Langlands.CentralSimple

/-- Each coefficient of the reduced characteristic polynomial is continuous on the units
of a central simple algebra with its module topology. -/
theorem continuous_reducedCharpoly_coeff_units
    (K A : Type u) [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [TopologicalSpace K] [IsTopologicalRing K] [TopologicalSpace A]
    [IsModuleTopology K A] (k : ℕ) :
    Continuous (fun a : Aˣ => (reducedCharpoly K A (a : A)).coeff k) := by
  let L := finiteGaloisSplittingField K A
  let : TopologicalSpace L := moduleTopology K L
  let : IsTopologicalRing L := IsModuleTopology.isTopologicalRing K L
  let e := finiteGaloisSplittingChart K A
  let M : A →ₐ[K] Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L :=
    (e.toAlgHom.restrictScalars K).comp Algebra.TensorProduct.includeRight
  obtain ⟨r, hr⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective K L))
  have hM : Continuous M := IsModuleTopology.continuous_of_linearMap M.toLinearMap
  have hc := (BaseChange.SigmaLiftCharacterIdentity.continuous_charpoly_coefficient
    (R := L) (n := reducedDegree K A) k).comp (hM.units_map M.toMonoidHom)
  refine ((IsModuleTopology.continuous_of_linearMap r).comp hc).congr ?_
  intro a
  change r ((e (1 ⊗ₜ[K] (a : A))).charpoly.coeff k) = _
  rw [← reducedCharpoly_map_chart K A e, Polynomial.coeff_map]
  exact LinearMap.congr_fun hr _

end Langlands.CentralSimple

namespace Langlands.JacquetLanglands

open Langlands.BaseChange Langlands.CentralSimple _root_.Polynomial
open SigmaLiftCharacterIdentity (coefficients)

variable (F D : Type u) [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]

private def reducedCoefficients (n : ℕ) (g' : Dˣ) : Fin n → F :=
  fun i => (reducedCharpoly F D (g' : D)).coeff i

private theorem polynomialOfCoefficients_reducedCoefficients {n : ℕ}
    (hn : reducedDegree F D = n) (g' : Dˣ) :
    polynomialOfCoefficients (reducedCoefficients F D n g') = reducedCharpoly F D (g' : D) := by
  conv_rhs =>
    rw [(reducedCharpoly_monic F D (g' : D)).as_sum, reducedCharpoly_natDegree, hn]
  unfold polynomialOfCoefficients reducedCoefficients
  exact congrArg (X ^ n + ·) (Fin.sum_univ_eq_sum_range
    (fun i : ℕ => C ((reducedCharpoly F D (g' : D)).coeff i) * X ^ i) n)

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
  [TopologicalSpace D] [IsModuleTopology F D]

/-- The regular units form an open subset of the division unit group. -/
theorem isOpen_regularDivisionUnits : IsOpen {g' : Dˣ | IsRegular F D g'} := by
  have : T2Space F := BruhatTits.localField_t2Space F
  let n := reducedDegree F D
  have hcont : Continuous (reducedCoefficients F D n) :=
    continuous_pi fun i => continuous_reducedCharpoly_coeff_units F D i
  convert (isOpen_separable_polynomialOfCoefficients (F := F) n).preimage hcont using 1
  ext g'
  change (reducedCharpoly F D (g' : D)).Separable ↔
    (polynomialOfCoefficients (reducedCoefficients F D n g')).Separable
  rw [polynomialOfCoefficients_reducedCoefficients F D rfl]

/-- A split correspondent of a regular division unit extends to a continuous choice of
split correspondents in a neighborhood of that division unit. -/
theorem exists_local_regularCorrespondent {n : ℕ} {γ : GeneralLinear n F} {g' : Dˣ}
    (hg : Corresponds F D γ g') :
    ∃ (U : Set Dˣ) (h : g' ∈ U) (s : U → GeneralLinear n F),
      IsOpen U ∧ Continuous s ∧ s ⟨g', h⟩ = γ ∧ ∀ a : U, Corresponds F D (s a) a.val := by
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_complete F
  have hn : reducedDegree F D = n := hg.eq_reducedDegree.symm
  obtain ⟨V, hγV, t, hV, ht, ht₀, -, hcoeff⟩ :=
    regularCoefficientSlice F n 1 γ Nat.one_pos hg.1.1
  let b := reducedCoefficients F D n
  have hb : Continuous b := continuous_pi fun i => continuous_reducedCharpoly_coeff_units F D i
  have hbγ : b g' = coefficients γ := by
    funext i
    exact congrArg (fun p : F[X] => p.coeff i) hg.2.2.symm
  let U := b ⁻¹' V ∩ {a : Dˣ | IsRegular F D a}
  have hU : IsOpen U := (hV.preimage hb).inter (isOpen_regularDivisionUnits F D)
  have hgU : g' ∈ U := by
    refine ⟨?_, hg.2.1⟩
    change b g' ∈ V
    rwa [hbγ]
  let j : U → V := fun a => ⟨b a.val, a.property.1⟩
  have hj : Continuous j := (hb.comp continuous_subtype_val).subtype_mk _
  let s : U → GeneralLinear n F := fun a => γ * t (j a)
  refine ⟨U, hgU, s, hU, continuous_const.mul (ht.comp hj), ?_, ?_⟩
  · have h : j ⟨g', hgU⟩ = ⟨coefficients γ, hγV⟩ := Subtype.ext hbγ
    change γ * t (j ⟨g', hgU⟩) = γ
    rw [h, ht₀, mul_one]
  · intro a
    have hc : coefficients (s a) = b a.val := by simpa only [pow_one] using hcoeff (j a)
    have hp : (s a).val.charpoly = reducedCharpoly F D (a.val : D) := by
      rw [← polynomialOfCoefficients_coefficients (s a), hc,
        polynomialOfCoefficients_reducedCoefficients F D hn]
    have hreg : IsRegularSemisimple (s a) := by
      change (s a).val.charpoly.Separable
      rw [hp]
      exact a.property.2
    exact (corresponds_iff F D (s a) a.val).mpr ⟨hreg, a.property.2, hp⟩

end Langlands.JacquetLanglands
