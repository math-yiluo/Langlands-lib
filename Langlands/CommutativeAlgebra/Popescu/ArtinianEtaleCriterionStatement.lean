import Langlands.CommutativeAlgebra.Popescu.EssentiallySmooth
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.FieldTheory.Separable

/-! # Unramified flat maps of Artinian local rings are essentially smooth -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open IsLocalRing

/-- The case of Artinian local rings of Stacks Algebra, Lemma 10.143.7 (00U6), combined with
Lemma 10.54.4 (07DT): let `P → D` be a flat local homomorphism of Artinian local rings, with `D`
essentially of finite type over `P`, such that `𝔪_P D = 𝔪_D` and the residue field extension
`κ_D / κ_P` is separable. Then `D` is essentially smooth over `P` (in fact, essentially étale). -/
def ArtinianEtaleCriterionStatement : Prop :=
  ∀ (P D : Type u) [CommRing P] [CommRing D] [IsLocalRing P] [IsLocalRing D]
    [IsArtinianRing P] [IsArtinianRing D] [Algebra P D] [IsLocalHom (algebraMap P D)]
    [Algebra.EssFiniteType P D] [Module.Flat P D],
    (maximalIdeal P).map (algebraMap P D) = maximalIdeal D →
    Algebra.IsSeparable (ResidueField P) (ResidueField D) →
    EssentiallySmooth P D

end Langlands.CommutativeAlgebra.Popescu
