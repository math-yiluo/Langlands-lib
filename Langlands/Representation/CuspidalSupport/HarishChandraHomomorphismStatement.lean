import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.CategoryTheory.Center.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! # Harish-Chandra homomorphisms (Renard VI.10.5)

For a parabolic `P = MN` of `G`, the Harish-Chandra homomorphism `i*_{MG} : ℨ(G) → ℨ(M)`
between the centres of the categories of smooth representations is compatible with normalized
parabolic induction and with the normalized Jacquet functor, and makes `ℨ(M)` a finitely
generated `ℨ(G)`-module.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.10.5, in derived form: for an actual rational parabolic `P = MN` of `G`, there
is a ring homomorphism `z ↦ z_M` from the centre `ℨ(G)` of the category of smooth
representations of `G(F)` to the centre `ℨ(M)` of that of `M(F)` (carriers in the common
universe `max u v`) such that

* for every smooth `σ` of `M(F)`, `i_P^G(z_M)` is the endomorphism of `i_P^G(σ)` defined by `z`;
* for every smooth `π` of `G(F)`, `r_P^G(z)` is the endomorphism of `r_P^G(π)` defined by `z_M`;
* `ℨ(M)` is a finitely generated `ℨ(G)`-module through this homomorphism. -/
def HarishChandraHomomorphismStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      let I := leviInductionFunctor.{u, max u v} p l r hp hr hl hmul
      let R := leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul
      ∃ φ : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) →+*
          CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)),
        (∀ (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
            (σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)),
          I.map ((φ z).app σ) = z.app (I.obj σ)) ∧
        (∀ (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
            (π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)),
          R.map (z.app π) = (φ z).app (R.obj π)) ∧
        letI : Module (CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
            (CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints M))) :=
          Module.compHom _ φ
        Module.Finite (CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
          (CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)))

end Langlands.Aubert.General.RepresentedParabolic
