import Langlands.Representation.CuspidalSupport.BernsteinSupportComparison
import Langlands.Representation.Plancherel.UnramifiedOperatorFamilies

/-! # The cuspidal support map and the variety of cuspidal data (Renard VI.7.1)

For the actual standard cuspidal data of a standard family: the cuspidal support map
`Sc : Irr(G) → Ω(G)` is surjective with finite fibres (Proposition), and each inertial component
of `Ω(G)` is an irreducible affine variety, the quotient of the complex torus `X(M)` of
unramified characters of a Levi by a finite group of algebraic automorphisms, independently of
the chosen representative (Theorem).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.7.1, Proposition, for the actual standard cuspidal data of a standard family, at
the saturated carrier universe `max uF uV`, with the published induction-occurrence support
relation `IsBernsteinCuspidalSupport`. For every cuspidal datum `a = (M, ρ)`:

* (surjectivity) some irreducible `π` has cuspidal support `a`;
* (finite fibres) there are finitely many representations `π₀ k` such that every irreducible
  `π` whose cuspidal support is a datum `b` associated to `a` is isomorphic to one of them. -/
def BernsteinCuspidalSupportFiniteFibreStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family),
      (∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
        IsBernsteinCuspidalSupport i ν family a π) ∧
      ∃ (n : ℕ) (π₀ : Fin n → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
        ∀ (b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
          (π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
          AreBernsteinCuspidalDataAssociated i ν family a b →
          IsBernsteinCuspidalSupport i ν family b π →
            ∃ k, Nonempty (π ≅ π₀ k)

/-- Renard VI.7.1, Theorem, for the actual standard cuspidal data of a standard family. Fix a
cuspidal datum `a = (M, ρ)`, write `X = X(M)` for the unramified characters of `M(F)`,
`ℂ[X]` for the published algebra `unramifiedRegularFunctions` of polynomial functions on `X`,
and `ω ~ ω'` when the data `(M, ρ ⊗ ω)` and `(M, ρ ⊗ ω')` are associated (an actual
`RationalLeviConjugacy` of `M` with itself and an isomorphism `ρ ⊗ ω ≅ (ρ ⊗ ω')^c`). The
component of `Ω(G)` containing `a` is the image of `ω ↦ (M, ρ ⊗ ω)`, and its functions are the
elements of `ℂ[X]` constant on the classes of `~`. Then:

* (finite group) there is a finite group `W` of permutations of `X`, each preserving `ℂ[X]`
  under composition, whose orbits are exactly the classes of `~`;
* (variety) the functions constant on the classes form a finitely generated `ℂ`-subalgebra of
  `ℂ[X]` that is a domain, every `ℂ`-algebra homomorphism from it to `ℂ` is evaluation at some
  `ω`, and these functions separate the classes;
* (components) for every other datum `a' = (M', ρ')`, with `X'` and `ℂ[X']`, some twist of `a`
  is associated to some twist of `a'` exactly when `a` and `a'` are inertially equivalent; in
  that case every twist of `a'` is associated to a twist of `a`, and every function on the
  component, read through `a`, is also read through `a'` by an element of `ℂ[X']`. -/
def BernsteinComponentVarietyStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      (a : BernsteinCuspidalDatum.{uF, uV} i ν family),
      haveI : IsClosedImmersion (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left :=
        Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots)
      haveI : IsAffine (bernsteinLeviScheme i ν a.roots).X.left :=
        isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left
      haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν a.roots).X.hom := by
        rw [← (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.w]
        infer_instance
      letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
        rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X
      let X := unramifiedCharacters
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
      let twist : X → SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
        fun ω => rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation
      let Assoc : X → X → Prop := fun ω ω' =>
        ∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
            (Standard.leviHom i ν (rootSet i ν a.roots)),
          Nonempty (twist ω ≅ rationalIsoPullback c.iso (twist ω'))
      let regular := unramifiedRegularFunctions
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
      let invariant : Set (X → ℂ) :=
        {f | f ∈ regular ∧ ∀ ω ω', Assoc ω ω' → f ω = f ω'}
      (∃ W : Subgroup (Equiv.Perm X), Finite W ∧
        (∀ w ∈ W, ∀ f ∈ regular, (fun ω => f (w ω)) ∈ regular) ∧
        ∀ ω ω', Assoc ω ω' ↔ ∃ w ∈ W, w ω' = ω) ∧
      (∃ O : Subalgebra ℂ (X → ℂ), (O : Set (X → ℂ)) = invariant ∧
        Algebra.FiniteType ℂ O ∧ IsDomain O ∧
        (∀ φ : O →ₐ[ℂ] ℂ, ∃ ω : X, ∀ f : O, φ f = (f : X → ℂ) ω) ∧
        ∀ ω ω', Assoc ω ω' ↔ ∀ f ∈ O, f ω = f ω') ∧
      ∀ a' : BernsteinCuspidalDatum.{uF, uV} i ν family,
        haveI : IsClosedImmersion (Standard.leviHom i ν (rootSet i ν a'.roots)).hom.hom.left :=
          Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a'.roots)
        haveI : IsAffine (bernsteinLeviScheme i ν a'.roots).X.left :=
          isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a'.roots)).hom.hom.left
        haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν a'.roots).X.hom := by
          rw [← (Standard.leviHom i ν (rootSet i ν a'.roots)).hom.hom.w]
          infer_instance
        letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a'.roots)) :=
          rationalPointTopology F (bernsteinLeviScheme i ν a'.roots).X
        let X' := unramifiedCharacters
          (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a'.roots) χ).toMul)
        let twist' : X' →
            SmoothRep.{0, uF, uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a'.roots)) :=
          fun ω' => rationalUnramifiedTwist (bernsteinLeviScheme i ν a'.roots) ω' a'.representation
        let Assoc' : X → X' → Prop := fun ω ω' =>
          ∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
              (Standard.leviHom i ν (rootSet i ν a'.roots)),
            Nonempty (twist ω ≅ rationalIsoPullback c.iso (twist' ω'))
        ((∃ ω ω', Assoc' ω ω') ↔ IsBernsteinInertiaRelated i ν family a a') ∧
        (IsBernsteinInertiaRelated i ν family a a' →
          (∀ ω' : X', ∃ ω : X, Assoc' ω ω') ∧
          ∀ f ∈ invariant, ∃ f' ∈ unramifiedRegularFunctions
              (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a'.roots) χ).toMul),
            ∀ ω ω', Assoc' ω ω' → f' ω' = f ω)

/-- Renard VI.7.1, Proposition and Theorem, for the actual standard cuspidal data of a
standard family. -/
def BernsteinCuspidalDataVarietyStatements : Prop :=
  BernsteinCuspidalSupportFiniteFibreStatement.{uF, uV} ∧
    BernsteinComponentVarietyStatement.{uF, uV}

end Langlands.CuspidalSupport
