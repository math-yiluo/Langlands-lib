/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 173, 13 November 2026:
Extract the proof of M162.012 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 36-237 and 267-319).
Prefix the namespace with Langlands.NYLL, give the theorem the published
statement relNorm_eq_pow_inertiaDeg_of_isSeparableStatement R S P p as its
type, and import only the U012 Statements module and the U011 Proofs module,
which supplies M162.011. The source's anonymous local instances M162.001 and
M162.008 (both FractionRing.liftAlgebra R (FractionRing S)) are replaced by
the local instance attribute on FractionRing.liftAlgebra, as in the statement
module. The private source helpers M162.002, M162.004, M162.007 and M162.009
are kept as private theorems of this module with their source names,
statements and proofs; the section variable IsIntegrallyClosed R (omitted by
the source for M162.007, and not mentioned by M162.002 and M162.004) is
dropped, together with the omit commands. M162.003, M162.005 and M162.006 are
used only through the imported M162.011 and are not repeated. All other
source declarations are omitted. The proof steps are unchanged. The upstream
LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U012.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U011.Proofs

/-!
# Relative norms of maximal ideals in finite separable extensions

For Dedekind domains `R → S` with `Frac S / Frac R` finite and separable, the
relative ideal norm of a maximal ideal `P` of `S` over the maximal ideal `p`
of `R` is `p ^ P.inertiaDeg R`. The proof descends from the Galois case in
Mathlib's `Ring.NormalClosure R S`, which is finite over `S` and Dedekind.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v w

attribute [local instance] FractionRing.liftAlgebra

section SeparableIdealNorm

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [IsIntegrallyClosed S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

/-- A normal closure inside a separable ambient field is separable over the
base whenever the extension being closed is separable.  Keeping this
field-theoretic step separate prevents the integral-closure transport below
from repeatedly elaborating the full `iSup` of embedding ranges. -/
private theorem intermediateNormalClosure_isSeparable_of_isSeparable
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [Field A]
    [Algebra K L] [Algebra K A] [Algebra L A]
    [IsScalarTower K L A] [Algebra.IsSeparable K L] :
    Algebra.IsSeparable K (IntermediateField.normalClosure K L A) := by
  change Algebra.IsSeparable K ↥(⨆ f : L →ₐ[K] A, f.fieldRange)
  exact IntermediateField.isSeparable_iSup K A
    (h := fun f => AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f))

/-- A finite extension remains finite over the field-theoretic normal
closure when viewed from the top of the tower. -/
private theorem intermediateNormalClosure_finiteDimensional_top
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [Field A]
    [Algebra K L] [Algebra K A] [Algebra L A]
    [IsScalarTower K L A] [FiniteDimensional K L] :
    let E := IntermediateField.normalClosure K L A
    letI : Algebra L E := normalClosure.algebra K L A
    FiniteDimensional L E := by
  exact Module.Finite.right K L (IntermediateField.normalClosure K L A)

/-- Finiteness of the integral normal closure follows from separability of
the original fraction-field extension. -/
private theorem ringNormalClosure_moduleFinite_of_isSeparable
    [IsNoetherianRing S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] :
    Module.Finite S (Ring.NormalClosure R S) := by
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let : Algebra L E := normalClosure.algebra K L A
  let T := Ring.NormalClosure R S
  let : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  let : IsScalarTower S L E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Algebra T E := by
    change Algebra (integralClosure S E) E
    infer_instance
  let : IsScalarTower S T E :=
    IsScalarTower.subalgebra' S E E (integralClosure S E)
  let : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E
  let : FiniteDimensional L E :=
    intermediateNormalClosure_finiteDimensional_top K L A
  let : Algebra.IsSeparable K E :=
    intermediateNormalClosure_isSeparable_of_isSeparable K L A
  let : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable K L E
  change Module.Finite S (integralClosure S E)
  exact IsIntegralClosure.finite S L E (integralClosure S E)

end SeparableIdealNorm

section SeparableIdealNormDedekind

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

/-- The same separable normal-closure construction is Dedekind when the
original rings are Dedekind. -/
private theorem ringNormalClosure_isDedekindDomain_of_isSeparable
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] :
    IsDedekindDomain (Ring.NormalClosure R S) := by
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let : Algebra L E := normalClosure.algebra K L A
  let T := Ring.NormalClosure R S
  let : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  let : IsScalarTower S L E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Algebra T E := by
    change Algebra (integralClosure S E) E
    infer_instance
  let : IsScalarTower S T E :=
    IsScalarTower.subalgebra' S E E (integralClosure S E)
  let : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E
  let : FiniteDimensional L E :=
    intermediateNormalClosure_finiteDimensional_top K L A
  let : Algebra.IsSeparable K E :=
    intermediateNormalClosure_isSeparable_of_isSeparable K L A
  let : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable K L E
  change IsDedekindDomain (integralClosure S E)
  exact integralClosure.isDedekindDomain S L E

end SeparableIdealNormDedekind

section SeparableIdealNormRelNorm

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

/-- Relative ideal norm of a maximal ideal in a finite separable extension.
This is the separable replacement for mathlib's perfect-base theorem and is
proved by the same normal-closure descent. -/
theorem relNorm_eq_pow_inertiaDeg_of_isSeparable
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p]
    [P.IsMaximal] [p.IsMaximal] :
    relNorm_eq_pow_inertiaDeg_of_isSeparableStatement R S P p := by
  let T := Ring.NormalClosure R S
  let : Module.Finite S T :=
    ringNormalClosure_moduleFinite_of_isSeparable R S
  let : Module.Finite R T := Module.Finite.trans S T
  let : IsDedekindDomain T :=
    ringNormalClosure_isDedekindDomain_of_isSeparable R S
  let : IsScalarTower R (FractionRing S) (FractionRing T) :=
    IsScalarTower.to₁₃₄ R S (FractionRing S) (FractionRing T)
  let : IsScalarTower (FractionRing R) (FractionRing S) (FractionRing T) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply IsFractionRing.ringHom_ext (A := R)
      intro x
      rw [← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing T)]
      change algebraMap R (FractionRing T) x =
        algebraMap (FractionRing S) (FractionRing T)
          (algebraMap (FractionRing R) (FractionRing S)
            (algebraMap R (FractionRing R) x))
      rw [← IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing S),
        ← IsScalarTower.algebraMap_apply R (FractionRing S) (FractionRing T)])
  let : IsGalois (FractionRing R) (FractionRing T) :=
    ringNormalClosure_isGalois_of_isSeparable R S
  let : IsGalois (FractionRing S) (FractionRing T) :=
    IsGalois.tower_top_of_isGalois
      (FractionRing R) (FractionRing S) (FractionRing T)
  obtain ⟨Q, hQm, hQP⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
  let : Q.IsMaximal := hQm
  let : Q.LiesOver P := hQP
  let : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h := Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  rwa [← Ideal.relNorm_relNorm R S,
    Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    Ideal.inertiaDeg_tower (R := R) P Q, pow_mul, pow_left_inj] at h
  exact Nat.ne_zero_iff_zero_lt.mpr (Ideal.inertiaDeg_pos Q S)

end SeparableIdealNormRelNorm

end

end Langlands.NYLL.LocalClassFieldTheory
