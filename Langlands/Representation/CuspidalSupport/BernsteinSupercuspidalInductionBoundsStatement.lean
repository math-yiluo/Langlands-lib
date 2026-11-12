import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.Filtration.ObjectDefinitions

/-! # Numerical bounds for induction from supercuspidal representations (Renard VI.5.4)

For standard cuspidal data `(M, ρ)` and `(M', ρ')` of a standard family, with standard
parabolics `P` and `P'`: the length of `i_P^G(ρ)` is at most `l(M) = |W(M, ∗)/W_M|`, and
`dim Hom_G(i_P^G(ρ), i_{P'}^G(ρ'))` is at most the number of `W_M`-orbits in
`W(ρ, ρ') = {w ∈ W_G | w · M = M', ρ' ∘ Ad(w) ≃ ρ}`. Here `W_G = N_G(A_∅)/Z_G(A_∅)` and
`W_M = N_M(A_∅)/Z_M(A_∅)` are the published Weyl quotients of the maximal split torus.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.5.4, Theorem, the two numerical bounds, for the actual standard cuspidal data
of a standard family. Let `W_G` be the quotient of the normalizer of the torus image `A_∅(F)`
in `G(F)` by its centralizer, and `W_M ⊆ W_G` the image of the corresponding quotient for a
standard Levi `M`. For `w ∈ W_G` and standard Levis `M`, `L`, write `w · M = L` when some
representative `n` of `w` satisfies `n M n⁻¹ = L`.

* For a cuspidal datum `a = (M, ρ)`, `i_P^G(ρ)` has a composition series of length at most
  `l(M)`, the number of left cosets `w W_M` with `w · M` a standard Levi.
* For cuspidal data `a = (M, ρ)` and `a' = (M', ρ')`, the dimension of the space of
  intertwiners `i_P^G(ρ) → i_{P'}^G(ρ')` is at most the number of left cosets `w W_M` of
  elements `w` having a representative `n` with `n M n⁻¹ = M'` and `ρ' ∘ Ad(n) ≃ ρ` as
  representations of `M(F)`. -/
def BernsteinSupercuspidalInductionBoundsStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν),
      let WL : Finset (SimpleRoot i ν) → Subgroup (Weyl i) := fun I =>
        (Group.RelativeWeyl.inclusion (torusPoints i) (levi i ν I)).range
      (∀ a : BernsteinCuspidalDatum.{uF, uV} i ν family,
        HasCompositionLengthAtMost (SmoothRep.toRep.obj (bernsteinInduction i ν family a))
          (Nat.card ((QuotientGroup.mk : Weyl i → Weyl i ⧸ WL a.roots) ''
            {w : Weyl i | ∃ (K : Finset (SimpleRoot i ν))
                (n : Group.RelativeWeyl.normalizer (torusPoints i)),
              (QuotientGroup.mk n : Weyl i) = w ∧
                (levi i ν a.roots).map
                  (MulAut.conj (n : rationalPoints G) : rationalPoints G →* rationalPoints G) =
                  levi i ν K}))) ∧
      ∀ a a' : BernsteinCuspidalDatum.{uF, uV} i ν family,
        Module.rank ℂ ((bernsteinInduction i ν family a).representation.IntertwiningMap
            (bernsteinInduction i ν family a').representation) ≤
          Nat.card ((QuotientGroup.mk : Weyl i → Weyl i ⧸ WL a.roots) ''
            {w : Weyl i | ∃ (n : Group.RelativeWeyl.normalizer (torusPoints i))
                (h : (levi i ν a.roots).map
                  (MulAut.conj (n : rationalPoints G) : rationalPoints G →* rationalPoints G) =
                  levi i ν a'.roots),
              (QuotientGroup.mk n : Weyl i) = w ∧
                ∃ e : bernsteinLiteralLeviRep i ν a.roots a.representation ≃ₗ[ℂ]
                    bernsteinLiteralLeviRep i ν a'.roots a'.representation,
                  ∀ (m : levi i ν a.roots) (x : bernsteinLiteralLeviRep i ν a.roots a.representation),
                    e ((bernsteinLiteralLeviRep i ν a.roots a.representation).representation m x) =
                      (bernsteinLiteralLeviRep i ν a'.roots a'.representation).representation
                        (Group.RelativeWeyl.conjugationEquiv (n : rationalPoints G)
                          (levi i ν a.roots) (levi i ν a'.roots) h m) (e x)})

end Langlands.CuspidalSupport
