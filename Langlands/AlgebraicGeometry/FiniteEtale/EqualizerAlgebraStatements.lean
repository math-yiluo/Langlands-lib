import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Etale.Basic

/-!
# Finite étale closure of algebra equalizers

This proposition is derived from `Algebra.Etale.equalizer` in the pinned NYLL
adaptation of Christian Merten's pi1 work. See the paired Markdown for provenance.
-/

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

/-- The equalizer subalgebra of two maps between finite étale `R`-algebras
is finite as an `R`-module and étale over `R`. -/
def EqualizerAlgebraFiniteEtale (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [Module.Finite R A] [Module.Finite R B]
    [Algebra.Etale R A] [Algebra.Etale R B]
    (f g : A →ₐ[R] B) : Prop :=
  Module.Finite R (AlgHom.equalizer f g) ∧
    Algebra.Etale R (AlgHom.equalizer f g)

end Langlands.AlgebraicGeometry.FiniteEtale
