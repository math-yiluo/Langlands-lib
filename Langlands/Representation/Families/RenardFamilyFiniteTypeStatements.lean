import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.Families.RenardFamilyParabolicFunctors
import Langlands.Representation.Jacquet.CoefficientScalarRestriction
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.CategoryTheory.Center.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Basic

/-! # Renard VI.10.7, Variant: `(G, B)`-modules of finite type

Renard 2026, VI.10.7, Variant (printed p.217 / PDF p.223): the Theorem and the Proposition of
VI.10.7 hold for `(G, B)`-modules. A `(G, B)`-module `(τ, E)` is of finite type if and only if
it is `B ⊗_ℂ ℨ(G)`-admissible and has nonzero components in only finitely many Bernstein
blocks `M(G)_𝔰`; consequently the induction functors `i_P^G` preserve `B`-modules of finite
type.

A `(G, B)`-module (VI.8.1, Definition) is a complex vector space `V` carrying a flat
`B`-module structure that extends its complex structure (`IsScalarTower ℂ B V`) and a smooth
`B`-linear representation `ρ` of `G(F)`; the `B`-linearity of the operators `ρ g` is the
commutation of the two actions. The underlying smooth complex representation `τ` is the
published coefficient restriction `complexRepresentation ρ` (same carrier, same operators).
Finite type means finite generation over the group algebra `B[G(F)]`, as in the published
VI.8.3 statement `JacquetFiniteTypeStatement`. The centre `ℨ(G)` is the published `CatCenter`
of the category of smooth complex representations; `z ∈ ℨ(G)` acts on `V` through `z.app τ`.
The `K`-fixed vectors are the `B`-submodule `fixedVectors ρ K`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Jacquet.CoefficientRestriction

section RepresentedParabolic

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

universe u v uB

/-- Renard VI.10.7, Variant of the Theorem: let `B` be a reduced Noetherian finitely
generated commutative `ℂ`-algebra and let `(ρ, V)` be a `(G(F), B)`-module: a smooth `B`-linear
representation on a flat `B`-module `V` whose `B`-structure extends a complex structure, with
underlying smooth complex representation `τ = complexRepresentation ρ`. If `V` is finitely
generated over `B[G(F)]`, then `V` is `B ⊗_ℂ ℨ(G)`-admissible: for every compact open subgroup
`K` there are finitely many `K`-fixed vectors `s₁, …, s_n` such that every `K`-fixed vector
lies in the `B`-span of the vectors `z · sⱼ`, where `z` runs over the centre
`ℨ(G) = CatCenter` of the category of smooth complex representations, acting on `τ` through
`z.app τ`. -/
def FamilyFiniteTypeCenterAdmissibleStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (B : Type uB) [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
      [Algebra.FiniteType ℂ B] [IsReduced B]
      (V : Type v) [AddCommGroup V] [Module B V] [Module ℂ V] [IsScalarTower ℂ B V]
      (ρ : Representation B (rationalPoints G) V) (hρ : IsSmooth ρ),
      Module.Flat B V →
      let τ : SmoothRep.{0, u, v} ℂ (rationalPoints G) :=
        SmoothRep.of (complexRepresentation ρ) ((isSmooth_complexRepresentation ρ).2 hρ)
      Module.Finite (MonoidAlgebra B (rationalPoints G)) ρ.asModule →
      ∀ K : OpenSubgroup (rationalPoints G), IsCompact (K : Set (rationalPoints G)) →
        ∃ (n : ℕ) (s : Fin n → V),
          (∀ j, s j ∈ fixedVectors ρ K.toSubgroup) ∧
          fixedVectors ρ K.toSubgroup ≤
            Submodule.span B {y : V | ∃ (j : Fin n)
              (z : CatCenter (SmoothRep.{0, u, v} ℂ (rationalPoints G))),
                y = SmoothRep.hom (z.app τ) (s j)}

/-- Renard VI.10.7, Variant, last sentence: for every actual rational parabolic with rational
Levi and matching geometric unipotent radical, and every reduced Noetherian finitely generated
commutative `ℂ`-algebra `B`, the normalized parabolic induction `i_P^G` of a smooth
`(M(F), B)`-module that is finitely generated over `B[M(F)]` is finitely generated over
`B[G(F)]`. The binders are those of the published VI.8.2 statement
`InductionBaseChangeStatement`. -/
def FamilyLeviInductionFiniteTypeStatement.{u', uB', uE'} : Prop :=
  ∀ (k : Type u') [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      ∀ (B : Type uB') [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
        [Algebra.FiniteType ℂ B] [IsReduced B]
        (E : Type uE') [AddCommGroup E] [Module B E]
        (σ : Representation B (rationalPoints M) E),
        IsSmooth σ → Module.Flat B E →
          Module.Finite (MonoidAlgebra B (rationalPoints M)) σ.asModule →
            Module.Finite (MonoidAlgebra B (rationalPoints G))
              (leviInducedRepresentation p l r hp hr hl hmul σ).asModule

end RepresentedParabolic

section BernsteinComponents

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme Langlands.CuspidalSupport

universe uF uV uB

/-- Renard VI.10.7, Variant of the Lemma and the Proposition, for the actual standard cuspidal
data of a standard family: let `B` be a reduced Noetherian finitely generated commutative
`ℂ`-algebra and let `(ρ, V)` be a `(G(F), B)`-module (carrier universe `max uF uV`): a smooth
`B`-linear representation on a flat `B`-module `V` whose `B`-structure extends a complex
structure, with underlying smooth complex representation `τ = complexRepresentation ρ`. Then
`V` is finitely generated over `B[G(F)]` if and only if

* it is `B ⊗_ℂ ℨ(G)`-admissible: for every compact open `K` there are finitely many `K`-fixed
  vectors `s₁, …, s_n` such that every `K`-fixed vector lies in the `B`-span of the vectors
  `z · sⱼ`, where `z` runs over the centre `ℨ(G) = CatCenter` of the category of smooth complex
  representations, acting on `τ` through `z.app τ`; and
* only finitely many inertial classes are the inertial support of an irreducible subquotient
  of the complex representation `τ`. -/
def FamilyFiniteTypeComponentCharacterizationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      (B : Type uB) [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
      [Algebra.FiniteType ℂ B] [IsReduced B]
      (V : Type (max uF uV)) [AddCommGroup V] [Module B V] [Module ℂ V]
      [IsScalarTower ℂ B V] (ρ : Representation B (rationalPoints G) V) (hρ : IsSmooth ρ),
      Module.Flat B V →
      let τ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
        SmoothRep.of (complexRepresentation ρ) ((isSmooth_complexRepresentation ρ).2 hρ)
      (Module.Finite (MonoidAlgebra B (rationalPoints G)) ρ.asModule ↔
        (∀ K : OpenSubgroup (rationalPoints G), IsCompact (K : Set (rationalPoints G)) →
          ∃ (n : ℕ) (s : Fin n → V),
            (∀ j, s j ∈ fixedVectors ρ K.toSubgroup) ∧
            fixedVectors ρ K.toSubgroup ≤
              Submodule.span B {y : V | ∃ (j : Fin n)
                (z : CatCenter (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))),
                  y = SmoothRep.hom (z.app τ) (s j)}) ∧
        {s : BernsteinInertialClass.{uF, max uF uV} i ν family |
          ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
            SmoothRep.IsSubquotient π τ ∧ IsBernsteinInertialSupport i ν family s π}.Finite)

end BernsteinComponents

end Langlands.Renard.AlgebraicFamily
