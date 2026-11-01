import Langlands.Algebra.IdempotentAnnihilatorQuotient.NamedCarrier
import Langlands.Algebra.NonUnitalModuleCorner
import Mathlib.CategoryTheory.Whiskering

/-!
# Quotient idempotence and the fixed-part quotient comparison

Prop-valued targets for Renard (9 July 2026), I.3.2, printed pp.20–21/PDF26–27.
The ambient arbitrary-ring statements and natural-isomorphism packaging are
internal strengthenings. All carriers, actions, maps and functors are published
constructions. These declarations do not prove the targets.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory

universe uA uM uN uC

variable {A : Type uA} [NonUnitalRing A]

/-- The annihilator of the quotient vanishes; its actual second projection is
bijective with an original-linear inverse, and agrees with the quotient of the
first projection. Every action on a quotient is the named inherited action. -/
def IdempotentAnnihilatorQuotientIdempotence (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M] : Prop :=
  letI := annihilatorQuotientAddCommGroup e M
  letI := annihilatorQuotientModule e M
  let QM := annihilatorQuotientCarrier e M
  letI := annihilatorQuotientAddCommGroup e QM
  letI := annihilatorQuotientModule e QM
  let q := annihilatorQuotientProjection e QM
  (∀ x : QM, x ∈ NonUnitalSubmodule.idempotentAnnihilator e QM → x = 0) ∧
    Function.Bijective q ∧
    (∃ r : NonUnitalModuleHom A (annihilatorQuotientCarrier e QM) QM,
      r.comp q = NonUnitalModuleHom.id A QM ∧
      q.comp r = NonUnitalModuleHom.id A (annihilatorQuotientCarrier e QM)) ∧
    NonUnitalModuleHom.annihilatorQuotientMap e (annihilatorQuotientProjection e M) = q

/-- Both objects satisfy quotient idempotence, and the entire forward and
inverse maps are natural for every original intertwiner. Source and target
carrier universes are independent. Inverses exist in the preceding conjuncts. -/
def IdempotentAnnihilatorQuotientIdempotenceNaturality (e : Idempotent A)
    (M : Type uM) (N : Type uN) [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A M] [NonUnitalModule A N] : Prop :=
  letI := annihilatorQuotientAddCommGroup e M
  letI := annihilatorQuotientModule e M
  letI := annihilatorQuotientAddCommGroup e N
  letI := annihilatorQuotientModule e N
  let QM := annihilatorQuotientCarrier e M
  let QN := annihilatorQuotientCarrier e N
  letI := annihilatorQuotientAddCommGroup e QM
  letI := annihilatorQuotientModule e QM
  letI := annihilatorQuotientAddCommGroup e QN
  letI := annihilatorQuotientModule e QN
  let qM := annihilatorQuotientProjection e QM
  let qN := annihilatorQuotientProjection e QN
  IdempotentAnnihilatorQuotientIdempotence e M ∧
    IdempotentAnnihilatorQuotientIdempotence e N ∧
    ∀ f : NonUnitalModuleHom A M N,
      let Qf := NonUnitalModuleHom.annihilatorQuotientMap e f
      let QQf := NonUnitalModuleHom.annihilatorQuotientMap e Qf
      QQf.comp qM = qN.comp Qf ∧
      ∀ (rM : NonUnitalModuleHom A (annihilatorQuotientCarrier e QM) QM)
        (rN : NonUnitalModuleHom A (annihilatorQuotientCarrier e QN) QN),
        rM.comp qM = NonUnitalModuleHom.id A QM →
        qM.comp rM = NonUnitalModuleHom.id A (annihilatorQuotientCarrier e QM) →
        rN.comp qN = NonUnitalModuleHom.id A QN →
        qN.comp rN = NonUnitalModuleHom.id A (annihilatorQuotientCarrier e QN) →
        Qf.comp rM = rN.comp QQf

/-- The actual projection gives `Q ≅ Q ⋙ Q`, with its actual nondegenerate
restriction. Both directions agree after the published inclusion, as equalities
of entire natural transformations. -/
def IdempotentAnnihilatorQuotientIdempotenceNaturalIso (e : Idempotent A) : Prop :=
  let Q := NonUnitalModuleCat.annihilatorQuotientFunctor.{uA, uC} e
  let Qnd := NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor.{uA, uC} e
  let inc := nondegenerateInclusion.{uA, uC} A
  ∃ E : Q ≅ Q ⋙ Q,
    E.hom = Functor.whiskerLeft Q (NonUnitalModuleCat.annihilatorQuotientπ e) ∧
    ∃ End : Qnd ≅ Qnd ⋙ Qnd,
      End.hom =
        Functor.whiskerLeft Qnd (NonUnitalModuleCat.nondegenerateAnnihilatorQuotientπ e) ∧
      Functor.whiskerRight End.hom inc = Functor.whiskerLeft inc E.hom ∧
      Functor.whiskerRight End.inv inc = Functor.whiskerLeft inc E.inv

/-- The closed quotient-idempotence family, for independently sized rings,
pointwise carriers and the fixed carrier universe of categorical packaging. -/
def IdempotentAnnihilatorQuotientIdempotenceTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A),
    (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
      IdempotentAnnihilatorQuotientIdempotence e M) ∧
    (∀ (M : Type uM) (N : Type uN) [AddCommGroup M] [AddCommGroup N]
      [NonUnitalModule A M] [NonUnitalModule A N],
      IdempotentAnnihilatorQuotientIdempotenceNaturality e M N) ∧
    IdempotentAnnihilatorQuotientIdempotenceNaturalIso.{uA, uC} e

/-- The actual restriction of the quotient projection is bijective, with an
asserted corner-linear inverse and equivalence having exactly that forward map.
The two inverse identities are equalities of entire linear maps. -/
def IdempotentAnnihilatorFixedPartComparison (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M] : Prop :=
  letI := annihilatorQuotientAddCommGroup e M
  letI := annihilatorQuotientModule e M
  let QM := annihilatorQuotientCarrier e M
  letI := Idempotent.Corner.ring e
  letI := NonUnitalModuleCorner.fixedPartAddCommGroup e M
  letI := NonUnitalModuleCorner.fixedPartModule e M
  letI := NonUnitalModuleCorner.fixedPartAddCommGroup e QM
  letI := NonUnitalModuleCorner.fixedPartModule e QM
  let j := NonUnitalModuleCorner.restrict e (annihilatorQuotientProjection e M)
  Function.Bijective j ∧
    ∃ r : NonUnitalModuleCorner.FixedPart e QM →ₗ[Idempotent.Corner e]
        NonUnitalModuleCorner.FixedPart e M,
      r.comp j = LinearMap.id ∧
      j.comp r = LinearMap.id ∧
      ∃ E : NonUnitalModuleCorner.FixedPart e M ≃ₗ[Idempotent.Corner e]
          NonUnitalModuleCorner.FixedPart e QM,
        E.toLinearMap = j ∧ E.symm.toLinearMap = r

/-- The fixed-part comparisons exist at both objects; the complete forward
maps and every pair of their two-sided inverses are natural under every original
intertwiner, in independent source and target carrier universes. -/
def IdempotentAnnihilatorFixedPartComparisonNaturality (e : Idempotent A)
    (M : Type uM) (N : Type uN) [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A M] [NonUnitalModule A N] : Prop :=
  letI := annihilatorQuotientAddCommGroup e M
  letI := annihilatorQuotientModule e M
  letI := annihilatorQuotientAddCommGroup e N
  letI := annihilatorQuotientModule e N
  let QM := annihilatorQuotientCarrier e M
  let QN := annihilatorQuotientCarrier e N
  letI := Idempotent.Corner.ring e
  letI := NonUnitalModuleCorner.fixedPartAddCommGroup e M
  letI := NonUnitalModuleCorner.fixedPartModule e M
  letI := NonUnitalModuleCorner.fixedPartAddCommGroup e N
  letI := NonUnitalModuleCorner.fixedPartModule e N
  letI := NonUnitalModuleCorner.fixedPartAddCommGroup e QM
  letI := NonUnitalModuleCorner.fixedPartModule e QM
  letI := NonUnitalModuleCorner.fixedPartAddCommGroup e QN
  letI := NonUnitalModuleCorner.fixedPartModule e QN
  let jM := NonUnitalModuleCorner.restrict e (annihilatorQuotientProjection e M)
  let jN := NonUnitalModuleCorner.restrict e (annihilatorQuotientProjection e N)
  IdempotentAnnihilatorFixedPartComparison e M ∧
    IdempotentAnnihilatorFixedPartComparison e N ∧
    ∀ f : NonUnitalModuleHom A M N,
      let Jf := NonUnitalModuleCorner.restrict e f
      let JQf := NonUnitalModuleCorner.restrict e
        (NonUnitalModuleHom.annihilatorQuotientMap e f)
      JQf.comp jM = jN.comp Jf ∧
      ∀ (rM : NonUnitalModuleCorner.FixedPart e QM →ₗ[Idempotent.Corner e]
          NonUnitalModuleCorner.FixedPart e M)
        (rN : NonUnitalModuleCorner.FixedPart e QN →ₗ[Idempotent.Corner e]
          NonUnitalModuleCorner.FixedPart e N),
        rM.comp jM = LinearMap.id →
        jM.comp rM = LinearMap.id →
        rN.comp jN = LinearMap.id →
        jN.comp rN = LinearMap.id →
        Jf.comp rM = rN.comp JQf

/-- The actual corner functor satisfies `J ≅ Q ⋙ J` via the published quotient
projection. The corresponding comparison on nondegenerate modules is exactly
its restriction along the published inclusion, in both directions. -/
def IdempotentAnnihilatorFixedPartComparisonNaturalIso (e : Idempotent A) : Prop :=
  let Q := NonUnitalModuleCat.annihilatorQuotientFunctor.{uA, uC} e
  let J := NonUnitalModuleCorner.functor.{uA, uC} e
  let Qnd := NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor.{uA, uC} e
  let Jnd := NonUnitalModuleCorner.nondegenerateFunctor.{uA, uC} e
  let inc := nondegenerateInclusion.{uA, uC} A
  ∃ E : J ≅ Q ⋙ J,
    E.hom = Functor.whiskerRight (NonUnitalModuleCat.annihilatorQuotientπ e) J ∧
    ∃ End : Jnd ≅ Qnd ⋙ Jnd,
      End.hom =
        Functor.whiskerRight (NonUnitalModuleCat.nondegenerateAnnihilatorQuotientπ e) Jnd ∧
      Functor.whiskerLeft inc E.hom = End.hom ∧
      Functor.whiskerLeft inc E.inv = End.inv

/-- The closed fixed-part comparison family. Tensor induction, simplicity and
any separate complex scalar compatibility are absent from its premises. -/
def IdempotentAnnihilatorFixedPartComparisonTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A),
    (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
      IdempotentAnnihilatorFixedPartComparison e M) ∧
    (∀ (M : Type uM) (N : Type uN) [AddCommGroup M] [AddCommGroup N]
      [NonUnitalModule A M] [NonUnitalModule A N],
      IdempotentAnnihilatorFixedPartComparisonNaturality e M N) ∧
    IdempotentAnnihilatorFixedPartComparisonNaturalIso.{uA, uC} e

/-- The two related statement families, grouped for review. Their separate
closed targets remain available for independent exact-proof successors. -/
def IdempotentAnnihilatorComparisonsTheorem : Prop :=
  IdempotentAnnihilatorQuotientIdempotenceTheorem.{uA, uM, uN, uC} ∧
    IdempotentAnnihilatorFixedPartComparisonTheorem.{uA, uM, uN, uC}

/-! Complete unapplied signatures: no conclusion is an input, and every target is Prop. -/

example : {A : Type uA} → [NonUnitalRing A] → Idempotent A →
    (M : Type uM) → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @IdempotentAnnihilatorQuotientIdempotence.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → Idempotent A →
    (M : Type uM) → (N : Type uN) → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] → Prop :=
  @IdempotentAnnihilatorQuotientIdempotenceNaturality.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] → Idempotent A → Prop :=
  @IdempotentAnnihilatorQuotientIdempotenceNaturalIso.{uA, uC}

example : Prop := IdempotentAnnihilatorQuotientIdempotenceTheorem.{uA, uM, uN, uC}

example : {A : Type uA} → [NonUnitalRing A] → Idempotent A →
    (M : Type uM) → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @IdempotentAnnihilatorFixedPartComparison.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → Idempotent A →
    (M : Type uM) → (N : Type uN) → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] → Prop :=
  @IdempotentAnnihilatorFixedPartComparisonNaturality.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] → Idempotent A → Prop :=
  @IdempotentAnnihilatorFixedPartComparisonNaturalIso.{uA, uC}

example : Prop := IdempotentAnnihilatorFixedPartComparisonTheorem.{uA, uM, uN, uC}

example : Prop := IdempotentAnnihilatorComparisonsTheorem.{uA, uM, uN, uC}

/-! Unequal universe assignments check both directions of ring/carrier size. -/

example : {A : Type} → [NonUnitalRing A] → Idempotent A →
    (M : Type 1) → (N : Type 2) → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] → Prop :=
  @IdempotentAnnihilatorQuotientIdempotenceNaturality.{0, 1, 2}

example : {A : Type 2} → [NonUnitalRing A] → Idempotent A →
    (M : Type 1) → (N : Type) → [AddCommGroup M] → [AddCommGroup N] →
    [NonUnitalModule A M] → [NonUnitalModule A N] → Prop :=
  @IdempotentAnnihilatorFixedPartComparisonNaturality.{2, 1, 0}

example : {A : Type 1} → [NonUnitalRing A] → Idempotent A → Prop :=
  @IdempotentAnnihilatorQuotientIdempotenceNaturalIso.{1, 0}

example : {A : Type} → [NonUnitalRing A] → Idempotent A → Prop :=
  @IdempotentAnnihilatorFixedPartComparisonNaturalIso.{0, 1}

example : Prop := IdempotentAnnihilatorQuotientIdempotenceTheorem.{2, 1, 0, 3}

example : Prop := IdempotentAnnihilatorFixedPartComparisonTheorem.{0, 1, 2, 0}

end Langlands.Algebra
