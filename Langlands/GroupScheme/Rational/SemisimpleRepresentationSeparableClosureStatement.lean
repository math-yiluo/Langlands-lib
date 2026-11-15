import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.Lie.RepresentationSubquotient
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.FieldTheory.IsSepClosed

/-! # Semisimple representations of a reductive group over `kᵃ` are defined over `kˢ` -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Semisimple representations of a connected reductive group over an algebraic closure are
defined over the separable closure (Milne, *Algebraic Groups* (2017), 22.7). Let `G` be a
connected reductive group over a field `k`, let `Ks` be a separable closure of `k` and `Ka` an
algebraic closure of `Ks` (so an algebraic closure of `k` in which `Ks` is the separable closure
of `k`). Every semisimple representation of `(G_{Ks})_{Ka}` on `Kaᵐ` is isomorphic to the
extension of scalars of a semisimple representation of `G_{Ks}` on `Ksᵐ`. -/
def ReductiveSemisimpleRepresentationSeparableClosureStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (Ks : Type u) [Field Ks] [Algebra k Ks] [IsSepClosure k Ks]
      (Ka : Type u) [Field Ka] [Algebra Ks Ka] [IsAlgClosure Ks Ka],
      let IsSemisimpleRep : {F : Type u} → [Field F] →
          {H : GroupScheme (Spec (CommRingCat.of F))} → {m : ℕ} →
          MatrixRepresentation H (Fin m) → Prop :=
        fun {F} _ {_} {m} σ => sSup {W : Submodule F (Fin m → F) | σ.IsStableSubspace W ∧
          W ≠ ⊥ ∧ ∀ U : Submodule F (Fin m → F), σ.IsStableSubspace U → U ≤ W →
            U = ⊥ ∨ U = W} = ⊤
      ∀ (m : ℕ) (ρ' : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap Ks Ka)).obj
          ((GroupScheme.baseChange (algebraBaseMap k Ks)).obj G)) (Fin m)),
        IsSemisimpleRep ρ' →
          ∃ ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k Ks)).obj G)
              (Fin m),
            IsSemisimpleRep ρ ∧
              ∃ C : Matrix (Fin m) (Fin m) Ka,
                (ρ.baseChange (algebraBaseMap Ks Ka)).Intertwines ρ' C ∧
                  Function.Bijective C.mulVecLin

end Langlands.GroupScheme
