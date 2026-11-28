import Langlands.Shimura.Unitary.EvenUnitaryProfileReduction
import Langlands.Shimura.Unitary.NonsplitDiscriminant
import Langlands.Shimura.Unitary.RealDiscriminant

/-! # The local discriminant values of an even unitary profile -/

noncomputable section

universe u v

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Local Langlands.GaloisCohomology Langlands.Galois

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  {n : ℕ} (hn : 1 < n)
  {s : Finset (Langlands.Global.FinitePlace E)} (positive : ∀ p : s, FinitePlacesAbove K p.val)
  (a : s → ZMod n) (r : (E →+* ℝ) → ℕ)

set_option maxRecDepth 8192 in
/-- The discriminant of the initial even-degree algebra supplies all localization data
needed by the global norm correction. -/
def unitaryProfileDiscriminantValues (he : 2 ∣ n) (hs : ∀ p : s, IsSplitPlace E K p.val)
    (P : InitialUnitaryProfile hn positive a r) :
    UnitaryProfileDiscriminantValues hn positive a r P := by
  classical
  apply Classical.choice
  obtain ⟨m, rfl⟩ := he
  let A := P.carrier
  let : Algebra E A := Algebra.compHom A (algebraMap E K)
  let : IsScalarTower E K A := IsScalarTower.of_algebraMap_eq' rfl
  let D := P.data
  let hn₀ := lt_trans Nat.zero_lt_one hn
  let : Nonempty (Fin (2 * m)) := Fin.pos_iff_nonempty.mp hn₀
  let C := EvenDiscriminantPresentation.fromDimension (E := E) D.dimension
  let ι := PlaceEmbeddings.standard E
  have hm : 2 * m / 2 = m := by omega
  refine ⟨⟨ι, brauerEquiv E (AlgebraicClosure E) (C.brauerClass D.toSecondKindInvolution),
    ?_, ?_, ?_, ?_⟩⟩
  · intro p
    let x : RationalModIntegers := denominatorEquiv (2 * m) hn₀ (a p)
    have h : HasCompletedBrauerInvariant K A (positive p).val x := by
      simpa only [ite_eq_left (rfl : positive p = positive p), ite_true, A, x] using P.signed p (positive p)
    simpa only [hm] using localInvariant_discriminant_at_split C D.toSecondKindInvolution ι p.val
      (hs p).some (positive p) x h
  · intro p hps hp
    simpa only [nsmul_zero] using localInvariant_discriminant_at_split C D.toSecondKindInvolution ι p
      hp.some (placeAbove K p) 0 (P.outside p hps (placeAbove K p))
  · intro p hps hp
    exact localInvariant_discriminant_at_nonsplit C D hn₀ ι p hp (P.outside p hps)
  · intro w
    simpa only [hm] using realLocalInvariant_discriminant C D ι w
      (r (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))) (P.signatures _)

end Langlands.Shimura.FiniteUnitary
