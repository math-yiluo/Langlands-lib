module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Essentially of finite type and of finite presentation are stable under composition

All rings are commutative with unit; a ring map is a unital ring homomorphism `f : R -> S`,
and `S` is viewed as an `R`-algebra via `f`.

An `R`-algebra `A` is *of finite type* if it is generated as an `R`-algebra by finitely many
elements, i.e. there is a surjective `R`-algebra map `R[x_1, ..., x_n] ->> A`, and *of finite
presentation* if it is `R`-isomorphic to `R[x_1, ..., x_n] / I` for a finitely generated ideal
`I`. A *localization* of a ring `A` is `T^{-1} A` for a multiplicatively closed subset `T`
containing `1`, together with the canonical map `A -> T^{-1} A`; following the Stacks
convention `T` is an arbitrary multiplicative subset, not necessarily a prime complement.

Then (Stacks tag 00QM) `R -> S` is *essentially of finite type* if `S` is, up to `R`-algebra
isomorphism, a localization of an `R`-algebra of finite type, and *essentially of finite
presentation* if `S` is, up to `R`-algebra isomorphism, a localization of an `R`-algebra of
finite presentation. Both classes are stable under composition; this is Stacks tag 07DS,
Lemma 10.54.2.

For "essentially of finite type" we use Mathlib's `RingHom.EssFiniteType`, whose definition —
an algebra is a localization of a finitely generated subalgebra — matches tag 00QM (1), so the
first statement is `RingHom.EssFiniteType.comp`. Mathlib has no predicate for "essentially of
finite presentation", so `RingHom.EssentiallyOfFinitePresentation` is introduced here after
tag 00QM (2): there is an intermediate `R`-algebra `A` of finite presentation, `S` carries a
compatible `A`-algebra structure (`IsScalarTower R A S`, so `R -> S` factors through `A`), and
`S` is a localization `T^{-1} A` of `A` at some submonoid `T`, encoded by `IsLocalization T S`.
Up to `R`-algebra isomorphism that is precisely the tag 00QM (2) condition.
-/

@[expose] public section

universe u v w uC

/-- A ring map `f : R -> S` is *essentially of finite presentation* if `S` is,
as an `R`-algebra, a localization of an `R`-algebra of finite presentation.

Concretely: there exist an `R`-algebra `A` of finite presentation, a compatible
`A`-algebra structure on `S` (so that the structure map `R -> S` agrees with
`R -> A -> S`), and a submonoid `T` of `A` exhibiting `S` as the localization
`T^{-1} A`. This is the Stacks Tag 00QM (2) condition, stated up to `R`-algebra
isomorphism. -/
def RingHom.EssentiallyOfFinitePresentation {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra A S)
    (_ : IsScalarTower R A S) (_ : Algebra.FinitePresentation R A) (T : Submonoid A),
    IsLocalization T S

/-- Re-present a finitely presented localization witness in a smaller universe. -/
private theorem essFP_reuniverse_aux
    {R : Type u} {T : Type w} [CommRing R] [CommRing T] [Algebra R T]
    (C : Type uC) [CommRing C] [Algebra R C] [Algebra C T]
    [IsScalarTower R C T] [Algebra.FinitePresentation R C]
    (U : Submonoid C) [IsLocalization U T] :
    ∃ (A' : Type (max u w)) (_ : CommRing A') (_ : Algebra R A') (_ : Algebra A' T)
      (_ : IsScalarTower R A' T) (_ : Algebra.FinitePresentation R A') (U' : Submonoid A'),
      IsLocalization U' T := by
  -- `Algebra.FinitePresentation.iff` gives `n`, an ideal `I` with `I.FG`, and an `R`-algebra
  -- isomorphism `MvPolynomial (Fin n) R ⧸ I ≃ₐ[R] C`. Take
  -- `A' := ULift.{w} (MvPolynomial (Fin n) R ⧸ I)` and pull the `C`-algebra structure on `T`
  -- back to `A'` along the resulting `e : A' ≃ₐ[R] C`, with `U' := U.comap e`. The same
  -- pullback instance is used for the tower and the localization, to avoid a diamond.
  obtain ⟨n, I, fpIso, hIfg⟩ := Algebra.FinitePresentation.iff.mp ‹Algebra.FinitePresentation R C›
  let ue : ULift.{w} (MvPolynomial (Fin n) R ⧸ I) ≃ₐ[R] (MvPolynomial (Fin n) R ⧸ I) :=
    ULift.algEquiv
  let e : ULift.{w} (MvPolynomial (Fin n) R ⧸ I) ≃ₐ[R] C := ue.trans fpIso
  let eR : ULift.{w} (MvPolynomial (Fin n) R ⧸ I) ≃+* C := e.toRingEquiv
  let instA'T : Algebra (ULift.{w} (MvPolynomial (Fin n) R ⧸ I)) T :=
    ((algebraMap C T).comp
      (eR : ULift.{w} (MvPolynomial (Fin n) R ⧸ I) →+* C)).toAlgebra
  refine ⟨ULift.{w} (MvPolynomial (Fin n) R ⧸ I), inferInstance, inferInstance, instA'T, ?_,
    Algebra.FinitePresentation.equiv e.symm,
    Submonoid.comap (eR : ULift.{w} (MvPolynomial (Fin n) R ⧸ I) →+* C) U, ?_⟩
  · refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    change algebraMap R T a =
      (algebraMap C T) (e (algebraMap R (ULift.{w} (MvPolynomial (Fin n) R ⧸ I)) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  · exact IsLocalization.of_ringEquiv_left (M₁ := U) (e := eR)
      (Submonoid.map_comap_eq_of_surjective eR.surjective _) fun _ => rfl

/-- **Universe re-presentation for essentially-finite-presentation witnesses.**
A finitely presented `R`-algebra `C` together with a localization `IsLocalization U T`
of it can always be re-presented by a finitely presented `R`-algebra `A'` living
in the smaller universe `Type (max u w)` (where `R : Type u`, `T : Type w`),
carrying a compatible `T`-localization structure.  Indeed every finitely
presented `R`-algebra is `R`-isomorphic to `MvPolynomial ι R ⧸ I` with `ι`
finite and `I` finitely generated, an object in `Type u ⊆ Type (max u w)`;
transport the algebra structure on `T` and the localization data across this
`R`-algebra isomorphism. -/
theorem essFP_reuniverse
    {R : Type u} {T : Type w} [CommRing R] [CommRing T] [Algebra R T]
    (C : Type uC) [CommRing C] [Algebra R C] [Algebra C T]
    [IsScalarTower R C T] [Algebra.FinitePresentation R C]
    (U : Submonoid C) [IsLocalization U T] :
    ∃ (A' : Type (max u w)) (_ : CommRing A') (_ : Algebra R A') (_ : Algebra A' T)
      (_ : IsScalarTower R A' T) (_ : Algebra.FinitePresentation R A') (U' : Submonoid A'),
      IsLocalization U' T :=
  essFP_reuniverse_aux C U

/-! ### Transport along a lifting of universes -/

universe x y
