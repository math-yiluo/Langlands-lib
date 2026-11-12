import Langlands.Representation.CuspidalSupport.BernsteinSupportComparison
import Langlands.Representation.Plancherel.UnramifiedOperatorFamilies
import Mathlib.CategoryTheory.Center.Basic

/-! # The centre of a Bernstein block is the algebra of functions on its component (Renard VI.10.4)

For the actual standard cuspidal data of a standard family: the centre of the Bernstein block
`M(G)_Ω` is isomorphic to the algebra of polynomial functions on the component `Ω` of `Ω(G)`,
the value of `z` at `(M, ρ ⊗ ω)_G` being the scalar by which `z` acts on `i_P^G(ρ ⊗ ω)`; the
centre of `M(G)` is the algebra of functions on `Ω(G)` that are polynomial on every component;
and the central idempotent of a block is the characteristic function of its component.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.10.4, Theorem, first sentence, with Remark 1, for the actual standard cuspidal
data of a standard family. Fix a cuspidal datum `a = (M, ρ)` (carriers in `Type (max uF uV)`),
the standard parabolic `P = MN` of `a`, `X = X(M)`, `ℂ[X]` the published
`unramifiedRegularFunctions`, `ind ω = i_P^G(ρ ⊗ ω)`, and `ω ~ ω'` when `(M, ρ ⊗ ω)` and
`(M, ρ ⊗ ω')` are associated. Then every `ind ω` lies in the Bernstein block `M(G)_Ω` of `a`,
the elements of `ℂ[X]` constant on the classes of `~` (the polynomial functions on `Ω`) form
a subalgebra `O`, and there is a ring isomorphism `e` from the centre of `M(G)_Ω` onto `O` such
that every central `z` acts on every `ind ω` by the scalar `e z ω`. -/
def BernsteinBlockCenterFunctionsStatement : Prop :=
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
      let twist : X →
          SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
        fun ω => rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation
      let ind : X → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) := fun ω =>
        (normalizedInductionFunctor (family.decomposition a.roots)
          (family.closedUnipotent a.roots)).obj
            (bernsteinLiteralLeviRep i ν a.roots (twist ω))
      let Assoc : X → X → Prop := fun ω ω' =>
        ∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
            (Standard.leviHom i ν (rootSet i ν a.roots)),
          Nonempty (twist ω ≅ rationalIsoPullback c.iso (twist ω'))
      let regular := unramifiedRegularFunctions
        (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
      let invariant : Set (X → ℂ) :=
        {f | f ∈ regular ∧ ∀ ω ω', Assoc ω ω' → f ω = f ω'}
      (∀ ω, bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
        (ind ω)) ∧
      ∃ O : Subalgebra ℂ (X → ℂ), (O : Set (X → ℂ)) = invariant ∧
        ∃ e : CatCenter (BernsteinSaturatedBlock i ν family
            (bernsteinInertialClass i ν family a)) ≃+* O,
          ∀ (z : CatCenter (BernsteinSaturatedBlock i ν family
              (bernsteinInertialClass i ν family a))) (ω : X)
            (hω : bernsteinSaturatedBlockProperty i ν family
              (bernsteinInertialClass i ν family a) (ind ω)),
            ∀ x : ind ω, SmoothRep.hom (z.app ⟨ind ω, hω⟩).hom x = (e z : X → ℂ) ω • x

/-- Renard VI.10.4, Theorem, second sentence, with Remark 1, for the actual standard cuspidal
data of a standard family, at carriers in `Type (max uF uV)`. A function on `Ω(G)` that is
polynomial on every component is encoded by a family `f a`, indexed by the cuspidal data `a`,
of functions on the characters of `M_a(F)`, read on `X(M_a)`: `ω ↦ f a ω` lies in
`ℂ[X(M_a)]`, and `f a ω = f b ω'` whenever `(M_a, ρ_a ⊗ ω)` and `(M_b, ρ_b ⊗ ω')` are
associated (values off `X(M_a)` are irrelevant). With `ind_a ω = i_{P_a}^G(ρ_a ⊗ ω)`:

* every element `z` of the centre of the category of smooth representations acts on every
  `ind_a ω` by a scalar, and these scalars form such a function;
* `z` is determined by its action on the `ind_a ω`;
* every such function is the family of scalars of some `z`.

Since `z ↦ (scalars)` is a ring homomorphism, this is a ring isomorphism from the centre
`ℨ(G)` onto the algebra of such functions. -/
def BernsteinCenterFunctionsStatement : Prop :=
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
      (∀ z : CatCenter (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
        ∃ f : (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) →
          (rationalPoints (bernsteinLeviScheme i ν a.roots) →* ℂˣ) → ℂ,
          (∀ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
            haveI : IsClosedImmersion
                (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left :=
              Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots)
            haveI : IsAffine (bernsteinLeviScheme i ν a.roots).X.left :=
              isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left
            haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν a.roots).X.hom := by
              rw [← (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.w]
              infer_instance
            letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
              rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X
            let Xa := unramifiedCharacters
              (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
            let twista : Xa → SmoothRep.{0, uF, max uF uV} ℂ
                (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
              fun ω => rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation
            let inda : Xa → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) := fun ω =>
              (normalizedInductionFunctor (family.decomposition a.roots)
                (family.closedUnipotent a.roots)).obj
                  (bernsteinLiteralLeviRep i ν a.roots (twista ω))
            (fun ω : Xa => f a ω.val.toMonoidHom) ∈ unramifiedRegularFunctions
              (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) ∧
            ∀ b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
              haveI : IsClosedImmersion
                  (Standard.leviHom i ν (rootSet i ν b.roots)).hom.hom.left :=
                Standard.isClosedSubgroup_leviHom i ν (rootSet i ν b.roots)
              haveI : IsAffine (bernsteinLeviScheme i ν b.roots).X.left :=
                isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν b.roots)).hom.hom.left
              haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν b.roots).X.hom := by
                rw [← (Standard.leviHom i ν (rootSet i ν b.roots)).hom.hom.w]
                infer_instance
              letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν b.roots)) :=
                rationalPointTopology F (bernsteinLeviScheme i ν b.roots).X
              let Xb := unramifiedCharacters
                (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν b.roots) χ).toMul)
              let twistb : Xb → SmoothRep.{0, uF, max uF uV} ℂ
                  (rationalPoints (bernsteinLeviScheme i ν b.roots)) :=
                fun ω => rationalUnramifiedTwist (bernsteinLeviScheme i ν b.roots) ω
                  b.representation
              let indb : Xb → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) := fun ω =>
                (normalizedInductionFunctor (family.decomposition b.roots)
                  (family.closedUnipotent b.roots)).obj
                    (bernsteinLiteralLeviRep i ν b.roots (twistb ω))
              ∀ (ω : Xa) (ω' : Xb),
                (∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
                    (Standard.leviHom i ν (rootSet i ν b.roots)),
                  Nonempty (twista ω ≅ rationalIsoPullback c.iso (twistb ω'))) →
                f a ω.val.toMonoidHom = f b ω'.val.toMonoidHom) ∧
          (∀ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
            haveI : IsClosedImmersion
                (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left :=
              Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots)
            haveI : IsAffine (bernsteinLeviScheme i ν a.roots).X.left :=
              isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left
            haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν a.roots).X.hom := by
              rw [← (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.w]
              infer_instance
            letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
              rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X
            let Xa := unramifiedCharacters
              (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
            let twista : Xa → SmoothRep.{0, uF, max uF uV} ℂ
                (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
              fun ω => rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation
            let inda : Xa → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) := fun ω =>
              (normalizedInductionFunctor (family.decomposition a.roots)
                (family.closedUnipotent a.roots)).obj
                  (bernsteinLiteralLeviRep i ν a.roots (twista ω))
            ∀ (ω : Xa) (x : inda ω),
              SmoothRep.hom (z.app (inda ω)) x = f a ω.val.toMonoidHom • x)) ∧
      (∀ z z' : CatCenter (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
        (∀ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
          haveI : IsClosedImmersion
              (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left :=
            Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots)
          haveI : IsAffine (bernsteinLeviScheme i ν a.roots).X.left :=
            isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left
          haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν a.roots).X.hom := by
            rw [← (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.w]
            infer_instance
          letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
            rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X
          let Xa := unramifiedCharacters
            (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
          let twista : Xa → SmoothRep.{0, uF, max uF uV} ℂ
              (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
            fun ω => rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation
          let inda : Xa → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) := fun ω =>
            (normalizedInductionFunctor (family.decomposition a.roots)
              (family.closedUnipotent a.roots)).obj
                (bernsteinLiteralLeviRep i ν a.roots (twista ω))
          ∀ ω : Xa, z.app (inda ω) = z'.app (inda ω)) → z = z') ∧
      ∀ f : (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family) →
          (rationalPoints (bernsteinLeviScheme i ν a.roots) →* ℂˣ) → ℂ,
        (∀ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
          haveI : IsClosedImmersion
              (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left :=
            Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots)
          haveI : IsAffine (bernsteinLeviScheme i ν a.roots).X.left :=
            isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left
          haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν a.roots).X.hom := by
            rw [← (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.w]
            infer_instance
          letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
            rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X
          let Xa := unramifiedCharacters
            (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
          let twista : Xa → SmoothRep.{0, uF, max uF uV} ℂ
              (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
            fun ω => rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation
          let inda : Xa → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) := fun ω =>
            (normalizedInductionFunctor (family.decomposition a.roots)
              (family.closedUnipotent a.roots)).obj
                (bernsteinLiteralLeviRep i ν a.roots (twista ω))
          (fun ω : Xa => f a ω.val.toMonoidHom) ∈ unramifiedRegularFunctions
            (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul) ∧
          ∀ b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
            haveI : IsClosedImmersion
                (Standard.leviHom i ν (rootSet i ν b.roots)).hom.hom.left :=
              Standard.isClosedSubgroup_leviHom i ν (rootSet i ν b.roots)
            haveI : IsAffine (bernsteinLeviScheme i ν b.roots).X.left :=
              isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν b.roots)).hom.hom.left
            haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν b.roots).X.hom := by
              rw [← (Standard.leviHom i ν (rootSet i ν b.roots)).hom.hom.w]
              infer_instance
            letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν b.roots)) :=
              rationalPointTopology F (bernsteinLeviScheme i ν b.roots).X
            let Xb := unramifiedCharacters
              (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν b.roots) χ).toMul)
            let twistb : Xb → SmoothRep.{0, uF, max uF uV} ℂ
                (rationalPoints (bernsteinLeviScheme i ν b.roots)) :=
              fun ω => rationalUnramifiedTwist (bernsteinLeviScheme i ν b.roots) ω b.representation
            let indb : Xb → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) := fun ω =>
              (normalizedInductionFunctor (family.decomposition b.roots)
                (family.closedUnipotent b.roots)).obj
                  (bernsteinLiteralLeviRep i ν b.roots (twistb ω))
            ∀ (ω : Xa) (ω' : Xb),
              (∃ c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν a.roots))
                  (Standard.leviHom i ν (rootSet i ν b.roots)),
                Nonempty (twista ω ≅ rationalIsoPullback c.iso (twistb ω'))) →
              f a ω.val.toMonoidHom = f b ω'.val.toMonoidHom) →
        ∃ z : CatCenter (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
          (∀ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
            haveI : IsClosedImmersion
                (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left :=
              Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots)
            haveI : IsAffine (bernsteinLeviScheme i ν a.roots).X.left :=
              isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left
            haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν a.roots).X.hom := by
              rw [← (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.w]
              infer_instance
            letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
              rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X
            let Xa := unramifiedCharacters
              (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
            let twista : Xa → SmoothRep.{0, uF, max uF uV} ℂ
                (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
              fun ω => rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation
            let inda : Xa → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) := fun ω =>
              (normalizedInductionFunctor (family.decomposition a.roots)
                (family.closedUnipotent a.roots)).obj
                  (bernsteinLiteralLeviRep i ν a.roots (twista ω))
            ∀ (ω : Xa) (x : inda ω),
              SmoothRep.hom (z.app (inda ω)) x = f a ω.val.toMonoidHom • x)

open Classical in
/-- Renard VI.10.4, Remark 2, for the actual standard cuspidal data of a standard family, at
carriers in `Type (max uF uV)`: an element `z` of the centre of the category of smooth
representations is the central idempotent `e_Ω` of the block of an inertial class `s` (the
identity on `M(G)_s` and zero on every other block, as in the published VI.7.4 statement)
exactly when, for every datum `a` and `ω ∈ X(M_a)`, `z` acts on `i_{P_a}^G(ρ_a ⊗ ω)` by `1` if
`a` lies in `s` and by `0` otherwise: `e_Ω` is the characteristic function of `Ω`. -/
def BernsteinCentralIdempotentFunctionStatement : Prop :=
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
      ∀ (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
        (z : CatCenter (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))),
        ((∀ V, bernsteinSaturatedBlockProperty i ν family s V → z.app V = 𝟙 V) ∧
          ∀ t, t ≠ s → ∀ V, bernsteinSaturatedBlockProperty i ν family t V → z.app V = 0) ↔
          (∀ a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
            haveI : IsClosedImmersion
                (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left :=
              Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots)
            haveI : IsAffine (bernsteinLeviScheme i ν a.roots).X.left :=
              isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left
            haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν a.roots).X.hom := by
              rw [← (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.w]
              infer_instance
            letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
              rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X
            let Xa := unramifiedCharacters
              (fun χ => (rationalNormCharacters (bernsteinLeviScheme i ν a.roots) χ).toMul)
            let twista : Xa → SmoothRep.{0, uF, max uF uV} ℂ
                (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
              fun ω => rationalUnramifiedTwist (bernsteinLeviScheme i ν a.roots) ω a.representation
            let inda : Xa → SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) := fun ω =>
              (normalizedInductionFunctor (family.decomposition a.roots)
                (family.closedUnipotent a.roots)).obj
                  (bernsteinLiteralLeviRep i ν a.roots (twista ω))
            ∀ (ω : Xa) (x : inda ω),
              SmoothRep.hom (z.app (inda ω)) x =
                (if bernsteinInertialClass i ν family a = s then (1 : ℂ) else 0) • x)

/-- Renard VI.10.4, Theorem and Remarks 1–2. -/
def BernsteinCenterFunctionsStatements : Prop :=
  BernsteinBlockCenterFunctionsStatement.{uF, uV} ∧
    BernsteinCenterFunctionsStatement.{uF, uV} ∧
    BernsteinCentralIdempotentFunctionStatement.{uF, uV}

end Langlands.CuspidalSupport
