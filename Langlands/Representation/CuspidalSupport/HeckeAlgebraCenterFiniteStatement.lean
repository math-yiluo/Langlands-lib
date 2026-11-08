import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Reductive.Basic
import Langlands.Representation.Induction.PermutationModule
import Langlands.Shimura.LevelHeckeAlgebra
import Mathlib.CategoryTheory.Center.Basic

/-! # The Hecke algebra of a compact open subgroup is finite over the Bernstein centre
(Renard VI.10.7, Corollary)

For a compact open subgroup `K` of `G(F)`, the Hecke algebra `H(G, K)`, realized as the
`K`-fixed vectors of the smooth permutation representation `𝒟(G/K)`, is a finitely generated
module over the centre `ℨ(G)` of the category of smooth representations. Each element of
`ℨ(G)` acts on `H(G, K)` as multiplication by a central element, and `H(G, K)` is a finitely
generated module over its own centre.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.10.7, Corollary: let `K` be a compact open subgroup of `G(F)`, and let
`𝒟(G/K)` be the smooth permutation representation of `G(F)` on finitely supported functions
on `G(F)/K`, whose `K`-fixed vectors form the Hecke algebra `H(G, K)` (the published
`LevelHeckeAlgebra ℂ K`). Let `ℨ(G) = CatCenter` be the centre of the category of smooth
representations, acting on `𝒟(G/K)` through `z.app 𝒟(G/K)`. Then

* `H(G, K)` is a finitely generated `ℨ(G)`-module: for some `s₁, …, s_n ∈ H(G, K)`, every
  `h ∈ H(G, K)` is `∑ zᵢ · sᵢ` with `zᵢ ∈ ℨ(G)`;
* every `z ∈ ℨ(G)` acts on `H(G, K)` as left multiplication by an element of the centre of
  `H(G, K)` (the element `e_K ∗ z ∗ e_K`);
* `H(G, K)` is a finitely generated module over its centre. -/
def HeckeAlgebraCenterFiniteStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (K : OpenSubgroup (rationalPoints G)), IsCompact (K : Set (rationalPoints G)) →
      let D : SmoothRep.{0, u, u} ℂ (rationalPoints G) :=
        Induction.smoothPermutation ℂ ℂ K.toSubgroup K.isOpen
      let H := Shimura.LevelHecke.LevelHeckeAlgebra ℂ K.toSubgroup
      let emb : H → (rationalPoints G ⧸ K.toSubgroup →₀ ℂ) := fun h =>
        ((Shimura.LevelHecke.LevelHeckeAlgebra.ofHeckeSpace (R := ℂ) K.toSubgroup).symm h :
          rationalPoints G ⧸ K.toSubgroup →₀ ℂ)
      (∃ (n : ℕ) (s : Fin n → H), ∀ h : H,
        ∃ z : Fin n → CatCenter (SmoothRep.{0, u, u} ℂ (rationalPoints G)),
          emb h = ∑ i, SmoothRep.hom ((z i).app D) (emb (s i))) ∧
      (∀ z : CatCenter (SmoothRep.{0, u, u} ℂ (rationalPoints G)),
        ∃ c ∈ Subring.center H, ∀ h : H, SmoothRep.hom (z.app D) (emb h) = emb (c * h)) ∧
      Module.Finite (Subring.center H) H

end Langlands.Aubert.General.RepresentedParabolic
