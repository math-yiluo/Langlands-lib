import Langlands.GroupScheme.SimplyConnected.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Statement: reflection of the central-cover universal property from a tensor decomposition -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

/-- **Reflection of the central-cover universal property through a supplied finite tensor
decomposition.** Let `k K : Type u` be arbitrary fields with `Algebra k K`, let `C G` be actual
group schemes over `Spec k` and `π : C ⟶ G` an actual homomorphism. Suppose given a finite
index type `I`, a `K`-algebra equivalence `e : K ⊗[k] K ≃ₐ[K] (I → K)` (the source is a
`K`-algebra through its first factor) and `k`-automorphisms `s : I → (K ≃ₐ[k] K)` with
`e (a ⊗ₜ b) i = a * s i b`. If the base change of `π` along
`Spec.map (CommRingCat.ofHom (algebraMap k K))` has the central-cover universal property, then
so does `π`: every central isogeny `q : H ⟶ G` from a semisimple `H` over `Spec k` receives
exactly one factorization `a : C ⟶ H` with `a ≫ q = π`. -/
def CentralCoverUniversalPropertyTensorReflectionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (C G : GroupScheme (Spec (CommRingCat.of k))) (π : C ⟶ G)
    (I : Type) [Finite I] (e : (K ⊗[k] K) ≃ₐ[K] (I → K)) (s : I → K ≃ₐ[k] K),
    (∀ (a b : K) (i : I), e (a ⊗ₜ[k] b) i = a * s i b) →
    HasCentralCoverUniversalProperty
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map π) →
      HasCentralCoverUniversalProperty π

end Langlands.GroupScheme
