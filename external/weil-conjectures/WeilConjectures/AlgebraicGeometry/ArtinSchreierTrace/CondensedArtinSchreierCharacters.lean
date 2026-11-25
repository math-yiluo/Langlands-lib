/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierTraceTensorAdd
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierTraceTensorInverse
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Mathlib.Tactic.LinearCombination
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierScalars
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear
import WeilConjectures.Mathlib.CategoryTheory.Conj
import Mathlib.Algebra.GroupWithZero.Units.Basic
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierRootCharts
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedCharacterRootEvaluation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! # Character decomposition with condensed Artin–Schreier coefficients

Source: latest blueprint, sec-fourier-transform/sk-lem-as-properties,
lemma-artin-schreier-character-sheaf and its proof, Steps 1–5 (blueprint:
lemma-artin-schreier-character-sheaf).

The coefficient ring is the recorded pulled-back condensed ring, not a discrete
constant ring. The projectors, pullbacks and degree-q sheaves are specializations
of the constructions in ArtinSchreierTraceComparison. The coproduct comparison is
specified by its actual image inclusions, which fixes the canonical decomposition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

/-- Regard a Qbar-valued character as a character into the global sections of the
condensed coefficient ring, using its canonical constant-section ring homomorphism.
Source: blueprint lemma-artin-schreier-character-sheaf, coefficient convention in proof Step 1
(blueprint: lemma-artin-schreier-character-sheaf). -/
abbrev qlbarCharacter (ℓ : ℕ) [Fact ℓ.Prime] {G : Type v} [AddMonoid G]
    (χ : AddChar G (PadicAlgCl ℓ)) :
    AddChar G (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) :=
  (Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar χ

/-- The recorded degree-q sheaf of lemma-artin-schreier-character-sheaf--1,
`ProEtale.condensedArtinSchreierSheafOf`, with its actual condensed Qbar coefficients
and the character Psi composed with the field trace. This is an abbreviation, not a
second Artin–Schreier construction.
Source: blueprint lemma-artin-schreier-character-sheaf, the clause beginning "In particular"
(blueprint: lemma-artin-schreier-character-sheaf). -/
abbrev qlbarTraceSheafOf (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (Ψ : AddChar (ZMod p) (PadicAlgCl ℓ))
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :=
  ProEtale.condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k X
    ((qlbarCharacter ℓ Ψ).compTrace k) f

/-- Tensor addition and the tensor inverse, with inverse-character identification,
for the trace character psi=Psi o Tr. Both tensor orders express the inverse object.
Source: blueprint lemma-artin-schreier-character-sheaf, final sentence and proof Step 5
(blueprint: lemma-artin-schreier-character-sheaf).

Proof: lemma-artin-schreier-character-sheaf with a=1 identifies the degree-q sheaves for f, g,
f+g and -f with the Psi-images for the prime covers. On common splitting charts
for these three covers choose roots r,s,t. Their difference r+s-t is locally
F_p-valued by lem-fd-frobenius-fixed-sections; refine so r+s is a component label.
The eigenfunction v_{f,r}(r+a)=Psi(a) freely generates its image. Send
(lambda v_{f,r}) tensor (mu v_{g,s}) to lambda mu v_{f+g,r+s}; the balanced-map
universal property of prose-03-02 constructs this module map
and its inverse. Changing roots to r+c,s+d multiplies the generators by
Psi(-c),Psi(-d), and Psi(-c-d), respectively, so maps and inverses agree on overlaps.
The sheaf equalizer condition (def-weil-pbc-sites-and-cohomology) glues them.
With g=-f the zero-function trivialization gives both inverse pairings.
Finally root negation sends an inverse-character function w(r+b)=Psi(-b)lambda
to w(r-a)=Psi(a)lambda on the cover of -f. The overlap factors agree, so these
maps glue too. This includes p=2, and never uses psi restricted to F_p, which
can be trivial when p divides [k:F_p]. Transport by the comparison gives all
displayed formulas in the recorded degree-q model. -/
theorem qlbar_artinSchreier_trace_tensor_properties
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (Ψ : AddChar (ZMod p) (PadicAlgCl ℓ)) (hΨ : Ψ ≠ 1)
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f g : Γ(X, ⊤)) :
    Nonempty (qlbarTraceSheafOf p ℓ k Ψ X f ⊗ qlbarTraceSheafOf p ℓ k Ψ X g ≅
      qlbarTraceSheafOf p ℓ k Ψ X (f + g)) ∧
    Nonempty (qlbarTraceSheafOf p ℓ k Ψ X f ⊗ qlbarTraceSheafOf p ℓ k Ψ X (-f) ≅
      Mod.regular (ProEtale.padicAlgClRingObj X ℓ)) ∧
    Nonempty (qlbarTraceSheafOf p ℓ k Ψ X (-f) ⊗ qlbarTraceSheafOf p ℓ k Ψ X f ≅
      Mod.regular (ProEtale.padicAlgClRingObj X ℓ)) ∧
    Nonempty (qlbarTraceSheafOf p ℓ k Ψ⁻¹ X f ≅ qlbarTraceSheafOf p ℓ k Ψ X (-f))   := by
  letI : CharP k p := (Algebra.charP_iff (ZMod p) k p).mp inferInstance
  have hq : IsUnit (Fintype.card k : MonObj.Γ (Profinite.padicAlgClRingObj ℓ)) := by
    have hk : IsUnit (Fintype.card k : PadicAlgCl ℓ) := by
      apply isUnit_iff_ne_zero.mpr
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card k ≠ 0)
    simpa only [map_natCast] using (Profinite.PadicAlgCl.constRingHom ℓ).isUnit_map hk
  letI : Nontrivial (MonObj.Γ (Profinite.padicAlgClRingObj ℓ)) :=
    ⟨⟨1, 0, fun h ↦ Profinite.PadicAlgCl.one_ne_zero_end_regular ℓ
      (by rw [← map_one Mod.regularEndRingHom, h, map_zero])⟩⟩
  have hχ : qlbarCharacter ℓ Ψ ≠ 1 := by
    intro h
    apply hΨ
    ext a
    apply (Profinite.PadicAlgCl.constRingHom ℓ).injective
    have ha := congrArg (fun c : AddChar (ZMod p)
        (MonObj.Γ (Profinite.padicAlgClRingObj ℓ)) ↦ c a) h
    simpa [qlbarCharacter] using ha
  have hΨ' : (qlbarCharacter ℓ Ψ).compTrace k ≠ 1 :=
    AddChar.compTrace_ne_one hχ
  have hadd := condensedArtinSchreier_tensor_add_generic
    (Profinite.padicAlgClRingObj ℓ) k ((qlbarCharacter ℓ Ψ).compTrace k) hΨ' hq
    X f g
  have hinv := condensedArtinSchreier_tensor_inverse_generic
    (Profinite.padicAlgClRingObj ℓ) k ((qlbarCharacter ℓ Ψ).compTrace k) hΨ' hq X f
  rcases hinv with ⟨hinv, hneg, hchar⟩
  have hinvchar : (qlbarCharacter ℓ Ψ⁻¹).compTrace k =
      ((qlbarCharacter ℓ Ψ).compTrace k)⁻¹ := by
    ext x
    simp [qlbarCharacter, AddChar.compTrace_apply, AddChar.inv_apply]
  have hchar' : Nonempty (qlbarTraceSheafOf p ℓ k Ψ⁻¹ X f ≅
      qlbarTraceSheafOf p ℓ k Ψ X (-f)) := by
    obtain ⟨e⟩ := hchar
    change Nonempty (ProEtale.condensedArtinSchreierSheafOf
      (Profinite.padicAlgClRingObj ℓ) k X ((qlbarCharacter ℓ Ψ⁻¹).compTrace k) f ≅
      ProEtale.condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k X ((qlbarCharacter ℓ Ψ).compTrace k) (-f))
    rw [hinvchar]
    exact ⟨e⟩
  exact ⟨hadd, hinv, hneg, hchar'⟩

end AlgebraicGeometry.ArtinSchreierTrace
