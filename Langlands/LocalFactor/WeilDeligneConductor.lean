import Langlands.LocalFactor.WeilDeligne
import Langlands.LocalFactor.Ramification.Descent

/-!
# Weil–Deligne conductors at a supplied finite inertia quotient

The ramification expression uses the actual finite extension and quotient map.
The monodromy correction is the dimension of the actual invariant quotient.
-/

noncomputable section

namespace Langlands.LocalFactor.WeilDeligne

universe uk uG uV uW uF uL

variable {k : Type uk} [Field k] {G : Type uG} [Group G] {ν : G →* kˣ}
    (I : Subgroup G) [I.Normal]

/-- Restrict a genuine pair equivalence to the specified inertia subgroup. -/
def inertiaRestrictionEquiv
    {A : WeilDeligneRepresentation.{uk, uG, uV} k G ν}
    {B : WeilDeligneRepresentation.{uk, uG, uW} k G ν}
    (e : WeilDeligneRepresentation.Equiv A B) :
    Representation.Equiv (A.representation.comp I.subtype)
      (B.representation.comp I.subtype) where
  toLinearEquiv := e.representationEquiv.toLinearEquiv
  isIntertwining' i := e.representationEquiv.isIntertwining' i.val

variable {p : ℕ} [Fact p.Prime] {L : PadicField.{uL} p}
    (T : L.TopologicalData) (F : Type uF) [Field F] [Algebra (Padic p) F]
    [Algebra F L.Carrier] [IsScalarTower (Padic p) F L.Carrier]
    (π : I →* Ramification.Padic.inertia T F) (hπ : Function.Surjective π)

/-- The actual finite-quotient Artin expression plus the actual monodromy
quotient dimension. The input quotient is not selected implicitly. -/
def artinConductorOfInertiaQuotient
    (A : WeilDeligneRepresentation.{uk, uG, uV} k G ν)
    (hker : π.ker ≤ (A.representation.comp I.subtype).ker) : ℚ :=
  Ramification.Padic.artinConductorOfQuotient T F π hπ
    (A.representation.comp I.subtype) hker + conductorCorrection A I

/-- The Swan expression uses the underlying representation and the supplied
finite quotient; it adds no monodromy term. -/
def swanConductorOfInertiaQuotient
    (A : WeilDeligneRepresentation.{uk, uG, uV} k G ν)
    (hker : π.ker ≤ (A.representation.comp I.subtype).ker) : ℚ :=
  Ramification.Padic.swanConductorOfQuotient T F π hπ
    (A.representation.comp I.subtype) hker

/-- The correction converts the tame term into the codimension of
the inertia-fixed monodromy kernel in the original representation. -/
theorem artinConductorOfInertiaQuotient_eq_codim_add_swan
    (A : WeilDeligneRepresentation.{uk, uG, uV} k G ν)
    (hker : π.ker ≤ (A.representation.comp I.subtype).ker) :
    artinConductorOfInertiaQuotient I T F π hπ A hker =
      ((A.rank - (A.inertiaKernelRepresentation I).rank : ℕ) : ℚ) +
        swanConductorOfInertiaQuotient I T F π hπ A hker := by
  have hI : (inertiaRepresentation A I).rank ≤ A.rank :=
    Submodule.finrank_le (FiniteRepresentation.invariantSubspace A.toFiniteRepresentation I)
  have hdim := conductorCorrection_add_kernelRank A I
  have harith : A.rank - (inertiaRepresentation A I).rank + conductorCorrection A I =
      A.rank - (A.inertiaKernelRepresentation I).rank := by omega
  unfold artinConductorOfInertiaQuotient swanConductorOfInertiaQuotient
  rw [Ramification.Padic.artinConductorOfQuotient_eq_tame_add_swan]
  change ((A.rank - (inertiaRepresentation A I).rank : ℕ) : ℚ) +
      Ramification.Padic.swanConductorOfQuotient T F π hπ
        (A.representation.comp I.subtype) hker + (conductorCorrection A I : ℚ) =
    ((A.rank - (A.inertiaKernelRepresentation I).rank : ℕ) : ℚ) +
      Ramification.Padic.swanConductorOfQuotient T F π hπ
        (A.representation.comp I.subtype) hker
  rw [← harith, Nat.cast_add]
  ring

omit [I.Normal] in
/-- The required finite-quotient kernel condition transports through a pair
equivalence, so it is not an additional condition on the new representative. -/
theorem inertiaQuotient_kernel_le_of_equiv
    {A : WeilDeligneRepresentation.{uk, uG, uV} k G ν}
    {B : WeilDeligneRepresentation.{uk, uG, uW} k G ν}
    (hker : π.ker ≤ (A.representation.comp I.subtype).ker)
    (e : WeilDeligneRepresentation.Equiv A B) :
    π.ker ≤ (B.representation.comp I.subtype).ker :=
  Ramification.Padic.kernel_le_of_equiv T F π hker (inertiaRestrictionEquiv I e)

/-- The actual corrected Artin expression is invariant under pair equivalence
at the supplied finite quotient. -/
theorem artinConductorOfInertiaQuotient_eq_of_equiv
    {A : WeilDeligneRepresentation.{uk, uG, uV} k G ν}
    {B : WeilDeligneRepresentation.{uk, uG, uW} k G ν}
    (hA : π.ker ≤ (A.representation.comp I.subtype).ker)
    (hB : π.ker ≤ (B.representation.comp I.subtype).ker)
    (e : WeilDeligneRepresentation.Equiv A B) :
    artinConductorOfInertiaQuotient I T F π hπ A hA =
      artinConductorOfInertiaQuotient I T F π hπ B hB := by
  unfold artinConductorOfInertiaQuotient
  rw [Ramification.Padic.artinConductorOfQuotient_equiv T F π hπ hA hB
    (inertiaRestrictionEquiv I e), conductorCorrection_eq_of_equiv I e]

omit [I.Normal] in
theorem swanConductorOfInertiaQuotient_eq_of_equiv
    {A : WeilDeligneRepresentation.{uk, uG, uV} k G ν}
    {B : WeilDeligneRepresentation.{uk, uG, uW} k G ν}
    (hA : π.ker ≤ (A.representation.comp I.subtype).ker)
    (hB : π.ker ≤ (B.representation.comp I.subtype).ker)
    (e : WeilDeligneRepresentation.Equiv A B) :
    swanConductorOfInertiaQuotient I T F π hπ A hA =
      swanConductorOfInertiaQuotient I T F π hπ B hB :=
  Ramification.Padic.swanConductorOfQuotient_equiv T F π hπ hA hB
    (inertiaRestrictionEquiv I e)

/-- With zero monodromy, the corrected expression is the original actual
finite-quotient Artin expression. -/
theorem artinConductorOfInertiaQuotient_of_monodromy_zero
    (A : WeilDeligneRepresentation.{uk, uG, uV} k G ν)
    (hker : π.ker ≤ (A.representation.comp I.subtype).ker)
    (hN : A.monodromy = 0) :
    artinConductorOfInertiaQuotient I T F π hπ A hker =
      Ramification.Padic.artinConductorOfQuotient T F π hπ
        (A.representation.comp I.subtype) hker := by
  simp only [artinConductorOfInertiaQuotient,
    conductorCorrection_eq_zero_of_monodromy_zero A I hN, Nat.cast_zero, add_zero]

end Langlands.LocalFactor.WeilDeligne
