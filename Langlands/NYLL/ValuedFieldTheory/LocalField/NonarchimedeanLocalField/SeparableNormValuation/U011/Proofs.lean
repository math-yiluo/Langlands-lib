/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 173, 13 November 2026:
Extract the proof of M162.011 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 36-165 and 240-264).
Prefix the namespace with Langlands.NYLL, give the theorem the published
statement ringNormalClosure_isGalois_of_isSeparableStatement R S as its
type, and import only the U011 Statements module. The source's anonymous
local instances M162.001 and M162.010 (both FractionRing.liftAlgebra R
(FractionRing S)) are replaced by the local instance attribute on
FractionRing.liftAlgebra, as in the statement module. The private source
helpers M162.002-M162.006 are kept as private theorems of this module with
their source names, statements and proofs; the unused section variables
IsIntegrallyClosed R and IsIntegrallyClosed S (omitted by the source for
M162.005 and M162.006, and not mentioned by M162.002-M162.004) are dropped,
together with the omit commands. M162.007-M162.009 and all other source
declarations are omitted. The proof steps are unchanged. The upstream
LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U011.Statements

/-!
# Normal closures of separable fraction-field extensions are Galois

The normal closure of `Frac S / Frac R` inside an algebraic closure of
`Frac S` is Galois as soon as `Frac S / Frac R` is finite and separable.
Its Galois property transfers to the fraction field of Mathlib's
`Ring.NormalClosure R S`, which is the integral closure of `S` in that
field-theoretic normal closure.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v w

attribute [local instance] FractionRing.liftAlgebra

section SeparableIdealNorm

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
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

/-- The field-theoretic normal closure of a finite separable extension is
Galois, with no perfectness assumption on the base. -/
private theorem intermediateNormalClosure_isGalois_of_isSeparable
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [Field A]
    [Algebra K L] [Algebra K A] [Algebra L A]
    [IsScalarTower K L A] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [Normal K A] :
    IsGalois K (IntermediateField.normalClosure K L A) := by
  exact
    { to_isSeparable :=
        intermediateNormalClosure_isSeparable_of_isSeparable K L A
      to_normal := normalClosure.normal K L A }

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

/-- The integral normal closure has the field-theoretic normal closure as
its fraction field. -/
private theorem ringNormalClosure_isFractionRing :
    let K := FractionRing R
    let L := FractionRing S
    let A := AlgebraicClosure L
    let E := IntermediateField.normalClosure K L A
    let T := Ring.NormalClosure R S
    letI : Algebra L E := normalClosure.algebra K L A
    letI : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
    letI : Algebra T E := by
      change Algebra (integralClosure S E) E
      infer_instance
    IsFractionRing T E := by
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
  let : FiniteDimensional L E :=
    intermediateNormalClosure_finiteDimensional_top K L A
  change IsFractionRing (integralClosure S E) E
  exact integralClosure.isFractionRing_of_finite_extension L E

/-- Transport Galoisness from the field-theoretic normal closure to the
fraction field of the integral normal closure. -/
private theorem ringNormalClosure_isGalois_transport :
    let K := FractionRing R
    let L := FractionRing S
    let A := AlgebraicClosure L
    let E := IntermediateField.normalClosure K L A
    let T := Ring.NormalClosure R S
    letI : Algebra K E := SubalgebraClass.toAlgebra E
    letI : Algebra K (FractionRing T) :=
      FractionRing.liftAlgebra R (FractionRing T)
    IsGalois K E → IsGalois K (FractionRing T) := by
  simp only
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
  let : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E
  let : IsScalarTower R S E := IsScalarTower.to₁₂₄ R S L E
  let : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E
  let : IsFractionRing T E := ringNormalClosure_isFractionRing R S
  intro hGalois
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext
  simpa using IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv T E).symm _

end SeparableIdealNorm

section SeparableIdealNormGalois

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

/-- The normal closure of a finite separable extension of fraction fields is
Galois without assuming that the base fraction field is perfect.  Mathlib's
default instance uses perfectness because it treats arbitrary finite
extensions; here separability is precisely the available hypothesis. -/
theorem ringNormalClosure_isGalois_of_isSeparable
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] :
    ringNormalClosure_isGalois_of_isSeparableStatement R S := by
  let K := FractionRing R
  let L := FractionRing S
  let A := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L A
  let T := Ring.NormalClosure R S
  exact ringNormalClosure_isGalois_transport R S
    (intermediateNormalClosure_isGalois_of_isSeparable K L A)

end SeparableIdealNormGalois

end

end Langlands.NYLL.LocalClassFieldTheory
