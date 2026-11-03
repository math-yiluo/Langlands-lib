import Langlands.GroupScheme.SimplyConnected.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Pi

/-! # Full cover descent for an explicit finite tensor decomposition -/

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

/-- A supplied full simply connected cover descends along a field extension
with an explicit finite tensor decomposition and its automorphism formula. -/
def SimplyConnectedCoverTensorDescentStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L]
    (J : Type v) [Fintype J]
    (e : (L ⊗[k] L) ≃ₐ[L] (J → L)) (s : J → L ≃ₐ[k] L)
    (_he : ∀ a b i, e (a ⊗ₜ[k] b) i = a * s i b)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (C : GroupScheme (Spec (CommRingCat.of L)))
    (π : C ⟶
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj G),
    IsSimplyConnectedCover π →
      ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (a : D ⟶ G)
        (j : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj D ≅ C),
        IsSimplyConnectedCover a ∧
          (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map a =
            j.hom ≫ π

end Langlands.GroupScheme
