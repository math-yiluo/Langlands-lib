import Langlands.Global.CompletionPadic
import Langlands.ClassField.Global.CompletionTower

/-! # Canonical p-adic completion packages in towers -/

noncomputable section

namespace Langlands.Global.CompletionPadic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open AdelicFunctoriality ClassFieldTheory.Local

universe u t

section Transport

variable {K : Type u} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-- The canonical p-adic map with its prime index transported. -/
def padicMapAt {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) :
    Padic p →+* w.adicCompletion K := by
  subst p
  exact padicMap w

/-- Prime transport changes only the scalar index, keeping the actual completion. -/
@[instance_reducible]
def padicAlgebraAt {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) :
    Algebra (Padic p) (w.adicCompletion K) :=
  (padicMapAt w h).toAlgebra

/-- The transported algebra agrees with the original canonical algebra. -/
theorem padicAlgebraAt_heq {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) :
    HEq (padicAlgebraAt w h) (padicAlgebra w) := by
  subst p
  rfl

/-- The canonical package at an equal prime, with definitionally unchanged carrier. -/
abbrev padicFieldAt {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) : PadicField.{u} p where
  Carrier := w.adicCompletion K
  algebra := padicAlgebraAt w h
  finiteDimensional := by
    subst p
    exact padicFinite w

/-- Prime transport agrees with the existing canonical package. -/
theorem padicFieldAt_heq {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) :
    HEq (padicFieldAt w h) (padicField w) := by
  subst p
  rfl

/-- Every family of absolute invariant maps respects this equality transport. -/
theorem absolute_padicFieldAt
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u,t} p)
    {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) :
    (I p).absolute (padicFieldAt w h) =
      (I (residuePrime w)).absolute (padicField w) := by
  subst p
  rfl

/-- Every family of relative invariant maps respects this equality transport. -/
theorem relative_padicFieldAt
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u,t} p)
    {p : ℕ} [Fact p.Prime] (h : residuePrime w = p)
    (L : Type t) [Field L] [Algebra (w.adicCompletion K) L]
    [FiniteDimensional (w.adicCompletion K) L] [IsGalois (w.adicCompletion K) L] :
    (I p).relative (padicFieldAt w h) L =
      (I (residuePrime w)).relative (padicField w) L := by
  subst p
  rfl

/-- Computing the transported map using the corresponding rational place. -/
theorem padicMapAt_eq_of_rationalPlace_eq
    (q : HeightOneSpectrum (𝓞 ℚ)) [w.asIdeal.LiesOver q.asIdeal]
    (h : rationalPlace w = q) :
    padicMapAt w (congrArg (fun q => (Rat.HeightOneSpectrum.primesEquiv q : ℕ)) h) =
      (FiniteExtension.completionMap q w).comp
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv q).symm.toRingEquiv.toRingHom := by
  subst q
  rfl

end Transport

section Tower

variable {F K : Type u} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Places in a number-field tower have the same rational contraction. -/
theorem rationalPlace_eq : rationalPlace w = rationalPlace v := by
  have := Ideal.LiesOver.trans w.asIdeal v.asIdeal (rationalPlace v).asIdeal
  exact HeightOneSpectrum.ext (Ideal.over_def w.asIdeal (rationalPlace v).asIdeal).symm

/-- Places in a number-field tower have the same residue prime. -/
theorem residuePrime_eq : residuePrime w = residuePrime v :=
  congrArg (fun q => (Rat.HeightOneSpectrum.primesEquiv q : ℕ)) (rationalPlace_eq v w)

/-- The upper completion, canonically packaged over the lower place's residue prime. -/
abbrev towerPadicField : PadicField.{u} (residuePrime v) :=
  padicFieldAt w (residuePrime_eq v w)

/-- The canonical p-adic maps commute with the finite completion embedding. -/
theorem completionMap_comp_padicMap :
    (FiniteExtension.completionMap v w).comp (padicMap v) =
      padicMapAt w (residuePrime_eq v w) := by
  have := Ideal.LiesOver.trans w.asIdeal v.asIdeal (rationalPlace v).asIdeal
  rw [padicMapAt_eq_of_rationalPlace_eq w (rationalPlace v) (rationalPlace_eq v w)]
  unfold padicMap
  rw [← RingHom.comp_assoc, ClassField.Global.CompletionTower.completionMap_comp]

/-- The transported upper canonical algebra is compatible with the existing completion algebra. -/
theorem towerPadicField_isScalarTower :
    letI := (padicField v).algebra
    letI := (towerPadicField v w).algebra
    IsScalarTower (Padic (residuePrime v)) (v.adicCompletion F) (w.adicCompletion K) := by
  let := (padicField v).algebra
  let := (towerPadicField v w).algebra
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (congrArg (fun f => f x) (completionMap_comp_padicMap v w)).symm

/-- The upper tower package equals the canonical upper package after prime transport. -/
theorem towerPadicField_heq : HEq (towerPadicField v w) (padicField w) :=
  padicFieldAt_heq w (residuePrime_eq v w)

/-- Absolute invariant maps agree for the upper tower package and its canonical package. -/
theorem absolute_towerPadicField
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u,t} p) :
    (I (residuePrime v)).absolute (towerPadicField v w) =
      (I (residuePrime w)).absolute (padicField w) :=
  absolute_padicFieldAt w I (residuePrime_eq v w)

/-- Relative invariant maps agree without any naturality assumption on the family. -/
theorem relative_towerPadicField
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u,t} p)
    (L : Type t) [Field L] [Algebra (w.adicCompletion K) L]
    [FiniteDimensional (w.adicCompletion K) L] [IsGalois (w.adicCompletion K) L] :
    (I (residuePrime v)).relative (towerPadicField v w) L =
      (I (residuePrime w)).relative (padicField w) L :=
  relative_padicFieldAt w I (residuePrime_eq v w) L

end Tower

end Langlands.Global.CompletionPadic
