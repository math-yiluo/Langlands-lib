import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.BaseChange.PseudoCoefficient
import Langlands.Global.AdelicFunctoriality.Norm
import Langlands.Global.CompletionPadic
import Langlands.Group.GL.LocalFieldTopology
import Langlands.TraceFormula.CyclicFieldGlobalizationStatement

/-!
# Globalization of a σ-discrete series as a local component of a σ-stable cusp

Statement only (no proof). Let `E/F` be a cyclic extension of number fields of any degree `l`
with generator `σ`, split at every infinite place. Let `v` be a finite place of `F` with exactly
one place `w` of `E` above it, and let `v₁, v₂, v₃` be three distinct finite places of `F`,
different from `v`, that split completely in `E`. Give `F_v ⊗_F E` its module topology over
`F_v` and let `σv = id ⊗ σ`. Then every σv-discrete series `ρ` of `GL_{r+1}(F_v ⊗_F E)` is,
through the `w`-component `F_v ⊗_F E → E_w` of the Library's `finiteTensorMap v`, isomorphic
to the local component at `w` of a spectral presentation `P` of a cuspidal operator realization
`T` of `GL_{r+1}` over `E` with unitary central character and `σ`-stable class, whose local
components at all places above `v₁` and above `v₂` are supercuspidal and whose local component
at `w` is irreducible and admissible.

This is the twisted globalization step of the global proof of descent for σ-discrete series
(Henniart–Lemaire 2011, II.6.16; Arthur–Clozel 1989, Chapter 1, §6.3(b)). It is derived
content: the statement is formulated for this Library from the argument of these sources.

Sources: Henniart–Lemaire 2011, II.6.16 (printed pp. 131–132), with II.5.13–II.5.15;
Arthur–Clozel 1989, Chapter 1, Lemmas 2.4–2.5 (printed pp. 13–15) and §6.3 (printed
pp. 54–57). See the paired Markdown.
-/

noncomputable section

universe uF uE uR uW

open NumberField IsDedekindDomain
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic Langlands.BaseChange
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.TraceFormula

local instance sigmaDiscreteGlobalizationRationalAddCommGroup (F : Type*) [Field F]
    [NumberField F] (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance sigmaDiscreteGlobalizationContinuousAddCommGroup (F : Type*) [Field F]
    [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance sigmaDiscreteGlobalizationSmoothAddCommGroup (F : Type*) [Field F]
    [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance sigmaDiscreteGlobalizationFormsAddCommGroup (F : Type*) [Field F]
    [NumberField F] (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance sigmaDiscreteGlobalizationLocalSpaceAddCommGroup {F : Type*} [Field F]
    [NumberField F] {n : ℕ} {v : Langlands.Global.FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- **Twisted globalization of a σ-discrete series.** Let `E/F` be a cyclic extension of number
fields of degree `l` with generator `σ` (`IsCyclicAlgebra σ l`; `l` need not be prime), both
adele quotients being compact, such that every infinite place `u` of `F` splits completely in
`E` with `σ` acting as the cyclic shift (`IsCyclicShiftSplit F E u.Completion σ l`). Let `v` be
a finite place of `F` with exactly one place `w` of `E` above it, and `v₁, v₂, v₃` pairwise
distinct finite places of `F`, all different from `v`, with
`IsCyclicShiftSplit F E (vᵢ.adicCompletion F) σ l`. Give `F_v ⊗_F E` its module topology over
`F_v` and let `σv = id ⊗ σ`.

Then for every `r` and every σv-discrete series representation `ρ` of `GL_{r+1}(F_v ⊗_F E)` on a
complex vector space in `Type uR` (`IsSigmaDiscreteSeries σv (r + 1) ρ`) there are a cuspidal
operator realization `T` of `GL_{r+1}` over `E` and a spectral presentation `P` of `T` (local
spaces in the free universe `uW`) such that

* `T` has unitary central character and its class is `σ`-stable,
* the local components of `P` at all places above `v₁` and above `v₂` are supercuspidal,
* the local component `Π_w` of `P` at `w` is irreducible and admissible,
* `Π_w`, viewed as a representation of `GL_{r+1}(F_v ⊗_F E)` through the `w`-component
  `F_v ⊗_F E → E_w` of `finiteTensorMap v`, is isomorphic to `ρ`. -/
def SigmaDiscreteTwistedGlobalizationStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    (∀ u : NumberField.InfinitePlace F, IsCyclicShiftSplit F E u.Completion σ l) →
    ∀ (v : Langlands.Global.FinitePlace F) (w : FinitePlacesAbove E v),
      (∀ w' : FinitePlacesAbove E v, w' = w) →
    ∀ (v₁ v₂ v₃ : Langlands.Global.FinitePlace F), v₁ ≠ v₂ → v₁ ≠ v₃ → v₂ ≠ v₃ →
      v₁ ≠ v → v₂ ≠ v → v₃ ≠ v →
      IsCyclicShiftSplit F E (v₁.adicCompletion F) σ l →
      IsCyclicShiftSplit F E (v₂.adicCompletion F) σ l →
      IsCyclicShiftSplit F E (v₃.adicCompletion F) σ l →
    ∀ (r : ℕ),
      letI : TopologicalSpace (v.adicCompletion F ⊗[F] E) :=
        moduleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)
      haveI : IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := ⟨rfl⟩
      haveI : IsTopologicalRing (v.adicCompletion F ⊗[F] E) :=
        IsModuleTopology.isTopologicalRing (v.adicCompletion F) _
      let σv : (v.adicCompletion F ⊗[F] E) ≃ₐ[v.adicCompletion F]
          (v.adicCompletion F ⊗[F] E) :=
        Algebra.TensorProduct.congr AlgEquiv.refl σ
    ∀ (W : Type uR) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (GeneralLinear (r + 1) (v.adicCompletion F ⊗[F] E)) W),
      IsSigmaDiscreteSeries σv (r + 1) ρ →
    ∃ (T : CuspidalOperatorRealization E r) (P : CuspidalSpectralPresentation.{uE, uW} T),
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T ∧
      T.isoClass.IsGaloisStable σ ∧
      (∀ w₁ : FinitePlacesAbove E v₁, (P.localComponent w₁.1).IsSupercuspidal) ∧
      (∀ w₂ : FinitePlacesAbove E v₂, (P.localComponent w₂.1).IsSupercuspidal) ∧
      (P.localComponent w.1).IsIrreducible ∧ (P.localComponent w.1).IsAdmissible ∧
      Nonempty (Representation.Equiv
        ((P.localComponent w.1).representation.comp
          (Matrix.GeneralLinearGroup.map
            ((Pi.evalRingHom (fun q : FinitePlacesAbove E v => q.1.adicCompletion E) w).comp
              (finiteTensorMap v).toRingHom)))
        ρ)

end Langlands.TraceFormula
