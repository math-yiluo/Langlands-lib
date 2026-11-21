import Langlands.Algebra.LocalDivisionFullResidueSubfieldEtaleStatement
import Langlands.Algebra.LocalDivisionReducedDegree
import Langlands.Algebra.LocalDivisionUnitMovement
import Mathlib.RingTheory.Etale.StandardEtale

/-! Integral étaleness for the original full-residue subfield. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel _root_.Polynomial

universe u uL

section

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  {L : Type uL} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local notation "w" => localDivisionSubfieldValuation K D ι
local notation "B" => Valuation.integer (localDivisionSubfieldValuation K D ι)
local notation "kD" => DivisionValuation.Residue (localReducedNormValuation K D)

local instance : Field kD := localDivisionResidueField K D
local instance : Algebra 𝓀[K] kD := localDivisionResidueAlgebra K D
local instance : Algebra 𝒪[K] B := localDivisionSubfieldIntegerAlgebra K D ι

private def subfieldReduction : B →+* kD :=
  (localDivisionSubfieldResidueMap K D ι).comp (DivisionValuation.reduction w)

local notation "ρ" => subfieldReduction K D ι

private theorem subfieldReduction_algebraMap (a : 𝒪[K]) :
    ρ (algebraMap 𝒪[K] B a) = algebraMap 𝓀[K] kD (IsLocalRing.residue 𝒪[K] a) :=
  localDivisionSubfieldBaseIntegerMap_reduction K D ι a

private theorem coe_sum_integer_smul {I : Type*} [Fintype I]
    (a : I → 𝒪[K]) (s : I → B) :
    ((∑ i, a i • s i : B) : L) = ∑ i, (a i : K) • (s i : L) := by
  change (Valuation.integer (localDivisionSubfieldValuation K D ι)).subtype _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def (a i : K)]
  rfl

/-- If the reductions are independent, an integral vector has integral coordinates. -/
private theorem integer_coefficients {I : Type*} [Fintype I] (s : I → B)
    (hind : LinearIndependent 𝓀[K] (fun i => ρ (s i))) (x : B) (c : I → K)
    (hc : ∑ i, c i • (s i : L) = (x : L)) : ∀ i, valuation K (c i) ≤ 1 := by
  classical
  intro i
  by_contra! hi
  obtain ⟨j, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun k => valuation K (c k))
    ⟨i, Finset.mem_univ _⟩
  have hj : 1 < valuation K (c j) := hi.trans_le (hmax i (Finset.mem_univ _))
  have hj₀ : c j ≠ 0 := (valuation K).ne_zero_iff.mp ((zero_lt_one.trans hj).ne')
  let d : I → 𝒪[K] := fun k => ⟨(c j)⁻¹ * c k, by
    change valuation K ((c j)⁻¹ * c k) ≤ 1
    rw [map_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_one.trans hj)]
    exact hmax k (Finset.mem_univ _)⟩
  have hdj : d j = 1 := Subtype.ext (inv_mul_cancel₀ hj₀)
  let y : B := ∑ k, d k • s k
  have hy : (y : L) = (c j)⁻¹ • (x : L) := by
    rw [← hc, Finset.smul_sum]
    simp only [y, coe_sum_integer_smul, smul_smul]
    rfl
  have hscalar (a : K) : w (algebraMap K L a) =
      valuation K a ^ CentralSimple.reducedDegree K D := by
    rw [localDivisionSubfieldValuation_apply, ι.commutes, localReducedNormValuation_algebraMap]
  have hsmall : w (y : L) < 1 := by
    rw [hy, Algebra.smul_def, map_mul, hscalar, map_inv₀]
    exact (mul_le_of_le_one_right zero_le x.prop).trans_lt
      (pow_lt_one₀ zero_le ((inv_lt_one₀ (zero_lt_one.trans hj)).mpr hj)
        (CentralSimple.reducedDegree_pos K D).ne')
  have hzero : ρ y = 0 := by
    change localDivisionSubfieldResidueMap K D ι (DivisionValuation.reduction w y) = 0
    rw [(DivisionValuation.reduction_eq_zero_iff w y).mpr hsmall, map_zero]
  have hrel : ∑ k, IsLocalRing.residue 𝒪[K] (d k) • ρ (s k) = 0 := by
    simpa only [y, map_sum, Algebra.smul_def, map_mul, subfieldReduction_algebraMap] using hzero
  have hj' := Fintype.linearIndependent_iff.mp hind _ hrel j
  rw [hdj, map_one] at hj'
  exact one_ne_zero hj'

/-- A monic lift of the full residue generator presents the original integer ring. -/
private theorem bijective_adjoinRoot_to_integers [FiniteDimensional K L]
    (f : 𝒪[K][X]) (hf : f.Monic) (b : B) (hb : f.eval₂ (algebraMap 𝒪[K] B) b = 0)
    (hindK : LinearIndependent K (fun i : Fin f.natDegree => (b : L) ^ (i : ℕ)))
    (hindk : LinearIndependent 𝓀[K] (fun i : Fin f.natDegree => ρ (b ^ (i : ℕ))))
    (hdeg : f.natDegree = Module.finrank K L) :
    Function.Bijective (AdjoinRoot.liftAlgHom f (Algebra.ofId 𝒪[K] B) b hb) := by
  classical
  let ψ := AdjoinRoot.liftAlgHom f (Algebra.ofId 𝒪[K] B) b hb
  let pb : Module.Basis (Fin f.natDegree) 𝒪[K] (AdjoinRoot f) := AdjoinRoot.powerBasisAux' hf
  have hψpow (i : Fin f.natDegree) : ψ (pb i) = b ^ (i : ℕ) := by
    have h : pb i = AdjoinRoot.root f ^ (i : ℕ) := (AdjoinRoot.powerBasis' hf).basis_eq_pow i
    have hroot : ψ (AdjoinRoot.root f) = b :=
      AdjoinRoot.liftAlgHom_root f (Algebra.ofId 𝒪[K] B) b hb
    rw [h, map_pow, hroot]
  have hψsum (a : Fin f.natDegree → 𝒪[K]) :
      (↑(ψ (∑ i, a i • pb i)) : L) = ∑ i, (a i : K) • (b : L) ^ (i : ℕ) := by
    rw [map_sum]
    simp_rw [map_smul, hψpow, coe_sum_integer_smul, Subring.coe_pow]
  constructor
  · refine (injective_iff_map_eq_zero ψ).mpr fun a ha => ?_
    have hs : ∑ i : Fin f.natDegree, (pb.repr a i : K) • (b : L) ^ (i : ℕ) = 0 := by
      have h := hψsum (fun i => pb.repr a i)
      rw [pb.sum_repr, ha] at h
      exact h.symm
    have hzero := Fintype.linearIndependent_iff.mp hindK _ hs
    rw [← pb.sum_repr a]
    exact Finset.sum_eq_zero (fun i _ => by
      rw [show pb.repr a i = 0 from Subtype.ext (hzero i), zero_smul])
  · let β := basisOfLinearIndependentOfCardEqFinrank' _ hindK (by simpa using hdeg)
    intro x
    have hx : ∑ i, β.repr (x : L) i • ((b ^ (i : ℕ) : B) : L) = (x : L) := by
      simpa only [Subring.coe_pow, β, coe_basisOfLinearIndependentOfCardEqFinrank'] using
        β.sum_repr (x : L)
    have ha := integer_coefficients K D ι _ hindk x _ hx
    let a : Fin f.natDegree → 𝒪[K] := fun i => ⟨β.repr (x : L) i, ha i⟩
    refine ⟨∑ i, a i • pb i, Subtype.ext ?_⟩
    change (↑(ψ (∑ i, a i • pb i)) : L) = _
    rw [hψsum]
    simpa only [Subring.coe_pow] using hx

end

/-- The integer algebra of the given full-residue subfield of reduced degree is étale. -/
theorem localDivisionFullResidueSubfieldEtale : LocalDivisionFullResidueSubfieldEtaleStatement.{u, uL} := by
  intro K D _ _ _ _ _ _ _ _ L _ _ _ ι hsurj hdim
  classical
  let := localDivisionResidueField K D
  let := localDivisionResidueAlgebra K D
  let := localDivisionSubfieldIntegerAlgebra K D ι
  let B := (localDivisionSubfieldValuation K D ι).integer
  let kD := DivisionValuation.Residue (localReducedNormValuation K D)
  obtain ⟨g, hg⟩ := exists_localDivisionResidue_generator K D
  let z : kD := DivisionValuation.reduction _ g.val
  have hgen (y : kD) : y = 0 ∨ ∃ n : ℕ, y = z ^ n := by
    rcases hg y with hy | ⟨n, hn⟩
    · exact Or.inl hy
    · exact Or.inr ⟨n, hn.trans (map_pow _ _ _)⟩
  obtain ⟨f, hmon, hmap, hdeg, hirr⟩ := exists_localDivision_residue_minpoly_polynomial K D z
  have heval (q : 𝒪[K][X]) : aeval z (q.map (IsLocalRing.residue 𝒪[K])) =
      q.eval₂ (localDivisionBaseReduction K D) z := by
    rw [aeval_def, eval₂_map]
    rfl
  have hroot : f.eval₂ (localDivisionBaseReduction K D) z = 0 := by
    rw [← heval, hmap]
    exact minpoly.aeval 𝓀[K] z
  have hz : IsIntegral 𝓀[K] z := Algebra.IsIntegral.isIntegral z
  have hder : f.derivative.eval₂ (localDivisionBaseReduction K D) z ≠ 0 := by
    rw [← heval, ← derivative_map, hmap]
    exact (PerfectField.separable_of_irreducible (minpoly.irreducible hz)).aeval_derivative_ne_zero
      (minpoly.aeval 𝓀[K] z)
  obtain ⟨b, hb, hredb⟩ := localDivisionSubfield_lift_base_polynomial K D ι hsurj f hmon z hroot hder
  have hmin : f.map (algebraMap 𝒪[K] K) = minpoly K (b : L) :=
    minpoly.eq_of_irreducible_of_monic hirr
      (localDivisionSubfield_aeval_base_polynomial K D ι f b hb) (hmon.map _)
  have hdK : (minpoly K (b : L)).natDegree = f.natDegree := by
    rw [← hmin, hmon.natDegree_map]
  have hfdeg : f.natDegree = Module.finrank K L := calc
    f.natDegree = (minpoly 𝓀[K] z).natDegree := hdeg
    _ = Module.finrank 𝓀[K] kD :=
      (PowerBasis.ofAdjoinEqTop hz (localDivisionResidue_adjoin_eq_top K D z hgen)).finrank.symm
    _ = CentralSimple.reducedDegree K D := localDivisionResidue_finrank_eq_reducedDegree K D
    _ = Module.finrank K L := hdim.symm
  have hindK : LinearIndependent K (fun i : Fin f.natDegree => (b : L) ^ (i : ℕ)) := by
    rw [← hdK]
    exact linearIndependent_pow (b : L)
  let ρ := subfieldReduction K D ι
  have hρb : ρ b = z := hredb
  have hindk : LinearIndependent 𝓀[K] (fun i : Fin f.natDegree => ρ (b ^ (i : ℕ))) := by
    simp only [map_pow, hρb]
    rw [hdeg]
    exact linearIndependent_pow z
  let ψ := AdjoinRoot.liftAlgHom f (Algebra.ofId 𝒪[K] B) b hb
  let e := AlgEquiv.ofBijective ψ
    (bijective_adjoinRoot_to_integers K D ι f hmon b hb hindK hindk hfdeg)
  have hcoeff : ρ.comp (algebraMap 𝒪[K] B) = localDivisionBaseReduction K D :=
    RingHom.ext (fun c => localDivisionSubfieldBaseIntegerMap_reduction K D ι c)
  have hder' : ρ (aeval b f.derivative) ≠ 0 := by
    rw [aeval_def, hom_eval₂, hcoeff, hρb]
    exact hder
  have hu : IsUnit (aeval b f.derivative) := by
    apply (DivisionValuation.isUnit_iff_value_eq_one _ _).mpr
    apply (DivisionValuation.reduction_ne_zero_iff _ _).mp
    intro h
    refine hder' ?_
    rw [show ρ (aeval b f.derivative) = localDivisionSubfieldResidueMap K D ι
      (DivisionValuation.reduction _ (aeval b f.derivative)) from rfl, h, map_zero]
  let P : StandardEtalePair 𝒪[K] := ⟨f, hmon, f.derivative, 1, 0, 1, by simp⟩
  let t := AdjoinRoot.mk f f.derivative
  have het : e t = aeval b f.derivative :=
    (AdjoinRoot.liftAlgHom_mk f (Algebra.ofId 𝒪[K] B) b hb f.derivative).trans
      (aeval_def b f.derivative).symm
  have ht : IsUnit t := (isUnit_map_iff e t).mp (by rw [het]; exact hu)
  let eLoc := IsLocalization.atUnit (AdjoinRoot f) (Localization.Away t) t ht
  exact Algebra.Etale.of_equiv
    (P.equivAwayAdjoinRoot.trans ((eLoc.restrictScalars 𝒪[K]).symm.trans e))

end Langlands.CentralDivision
