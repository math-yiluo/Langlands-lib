import Langlands.Algebra.DivisionReducedCharpoly
import Langlands.Algebra.DivisionFieldEmbeddingsProof
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Embedding an original singleton field by a root of maximal possible degree. -/

noncomputable section

namespace Langlands.CentralDivision

universe u uL

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- A root of reduced degree identifies the root field with the original singleton field. -/
def divisionMaximalRootEquiv (a : D) (f : Polynomial K)
    (hf : f.Monic) (hirr : Irreducible f)
    (hdeg : f.natDegree = CentralSimple.reducedDegree K D)
    (b : residueGeneratorSubalgebra K D a)
    (hb : Polynomial.aeval b f = 0) :
    letI := residueGeneratorField K D a
    AdjoinRoot f ≃ₐ[K] residueGeneratorSubalgebra K D a := by
  let := residueGeneratorField K D a
  let : Fact (Irreducible f) := ⟨hirr⟩
  let : FiniteDimensional K (AdjoinRoot f) := hf.finite_adjoinRoot
  let E := residueGeneratorSubalgebra K D a
  let φ : AdjoinRoot f →ₐ[K] E :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId K E) b hb
  have hdim : Module.finrank K (AdjoinRoot f) = Module.finrank K E := by
    apply le_antisymm
    · exact LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) φ.injective
    · calc
        Module.finrank K E ≤ CentralSimple.reducedDegree K D :=
          residueGeneratorSubalgebra_finrank_le_reducedDegree K D a
        _ = Module.finrank K (AdjoinRoot f) := by
          rw [← hdeg, (AdjoinRoot.powerBasis' hf).finrank]
          rfl
  exact AlgEquiv.ofBijective φ ⟨φ.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := φ.toLinearMap) hdim).mp φ.injective⟩

/-- A common root of reduced degree conjugates the original unit into the supplied field. -/
theorem exists_unit_conj_into_field_of_maximal_root
    {L : Type uL} [Field L] [Algebra K L] (ι : L →ₐ[K] D)
    (a : Dˣ) (f : Polynomial K) (hf : f.Monic) (hirr : Irreducible f)
    (hdeg : f.natDegree = CentralSimple.reducedDegree K D)
    (b : L) (hb : Polynomial.aeval b f = 0)
    (c : residueGeneratorSubalgebra K D (a : D))
    (hc : Polynomial.aeval c f = 0) :
    ∃ u : Dˣ, ∃ y : Lˣ,
      a = u * Units.map ι.toMonoidHom y * u⁻¹ := by
  let := residueGeneratorField K D (a : D)
  let E := residueGeneratorSubalgebra K D (a : D)
  let e := divisionMaximalRootEquiv K D (a : D) f hf hirr hdeg c hc
  let ψ : AdjoinRoot f →ₐ[K] L :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId K L) b hb
  let δ : E →ₐ[K] L := ψ.comp e.symm.toAlgHom
  obtain ⟨u, hu⟩ := exists_unit_conj K D E E.val (ι.comp δ)
  let aE : Eˣ := Units.mk0 ⟨(a : D), residueGenerator_mem K D (a : D)⟩
    (fun h => a.ne_zero (congrArg Subtype.val h))
  refine ⟨u, Units.map δ.toMonoidHom aE, ?_⟩
  apply Units.ext
  exact hu aE.val

end Langlands.CentralDivision
