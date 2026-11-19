import Langlands.BaseChange.SplitPlace
import Langlands.BaseChange.TwistedCharacter
import Langlands.Group.GL.LocalFieldTopology
import Langlands.Representation.Smooth.Definitions
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Irreducible

/-!
# Statement: `π ⊗ ⋯ ⊗ π` is a σ-lift of `π` at a split place

For a nonarchimedean local field `F` of characteristic zero and `F^{l+1}` with the cyclic shift
`σ = splitCyclicShift F (l + 1)`: (a) for an irreducible admissible `π` of `GL_n(F)`, the
representation `splitTensorRep π` (`π ⊗ ⋯ ⊗ π`) of `GL_n(F^{l+1})` is irreducible admissible
and, with the intertwiner `splitTensorShift`, a σ-lift of `π` with constant `1`
(Henniart–Lemaire 2011, II.2.8 and II.2.15, printed pp. 67–69 and 76–77, and II.6.15);
(b) every irreducible admissible σ-stable representation of `GL_n(F^{l+1})` is isomorphic to
such a `splitTensorRep π` (Flath 1979, Theorem 1, printed p. 179; Henniart–Lemaire 2011,
II.2.8, printed pp. 67–68). The statement is not proved here.
See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

universe u uV uW

/-- The split σ-lift (Henniart–Lemaire, II.2.8, II.2.15 and II.6.15; Flath 1979, Theorem 1), with
`σ = splitCyclicShift F (l + 1)`: (a) for every irreducible admissible `π` of `GL_n(F)`,
`splitTensorRep π` is irreducible admissible and there is a σ-intertwiner `A` with underlying
linear equivalence `splitTensorShift V (l + 1)` such that `splitTensorRep π` is a σ-lift of `π`
with constant `1`; (b) every irreducible admissible σ-stable representation `ρ` of
`GL_n(F^{l+1})` is isomorphic to `splitTensorRep π` for an irreducible admissible `π` of
`GL_n(F)`. The topological instances that `IsSigmaLift` takes are supplied by the Library's
`LocalFieldTopology` and by the topology lemmas of `Langlands.BaseChange.TwistedCharacter`. -/
def SplitSigmaLiftStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n l : ℕ),
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F (Fin (l + 1) → F) n
    haveI := generalLinear_locallyCompactSpace_of_finite F (Fin (l + 1) → F) n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F (Fin (l + 1) → F) n
    (∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π), π.IsIrreducible →
      ∃ hP : IsAdmissible (splitTensorRep (l := l + 1) π),
        (splitTensorRep (l := l + 1) π).IsIrreducible ∧
        ∃ A : SigmaIntertwiner (splitCyclicShift F (l + 1)) n (splitTensorRep (l := l + 1) π),
          A.toLinearEquiv = splitTensorShift V (l + 1) ∧
          IsSigmaLift (splitCyclicShift F (l + 1)) (l + 1) π hπ
            (splitTensorRep (l := l + 1) π) hP A 1) ∧
    (∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (GeneralLinear n (Fin (l + 1) → F)) W),
      IsAdmissible ρ → ρ.IsIrreducible → IsSigmaStable (splitCyclicShift F (l + 1)) n ρ →
      ∃ (V : Type uW) (_ : AddCommGroup V) (_ : Module ℂ V)
        (π : Representation ℂ (GeneralLinear n F) V),
        IsAdmissible π ∧ π.IsIrreducible ∧
          Nonempty (Representation.Equiv ρ (splitTensorRep (l := l + 1) π)))

end Langlands.BaseChange
