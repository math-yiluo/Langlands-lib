import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.Unramified.WeakTransfer
import Langlands.BaseChange.Norm
import Langlands.Representation.Character.Basic
import Langlands.Global.CompletionPadic
import Langlands.Group.GL.LocalFieldTopology
import Mathlib.RingTheory.Norm.Basic

/-!
# Equal local traces on norm determinants in a fibre of weak base change

Statement only (no proof). Let `E/F` be a cyclic extension of number fields
(`IsCyclicAlgebra σ l`) with compact adele quotients, `T` a cuspidal operator realization of
`GL_{r+1}` over `E`, and `S`, `S'` cuspidal operator realizations of `GL_{r+1}` over `F` whose
classes both have the class of `T` as weak base change. Let `D`, `D'` be spectral presentations
of `S`, `S'` and `v` a finite place of `F` at which the local components `π_v`, `π'_v` of `D`,
`D'` are irreducible and admissible. Then `tr π_v(f) = tr π'_v(f)` for every Haar measure on
`GL_{r+1}(F_v)` and every Schwartz–Bruhat function `f` on `GL_{r+1}(F_v)` such that `det g` is a
norm from `(F_v ⊗_F E)ˣ` whenever `f g ≠ 0`.

The reason is the description of the fibres of base change (Arthur–Clozel 1989, Chapter 3,
Theorem 3.1, printed p. 201; Library `CyclicCuspidalFiberStatement`): `S'` is the twist of `S`
by `χ ∘ det` for an idele class character `χ` of `F` trivial on the norms from `E`, so
`π'_v ≅ π_v ⊗ (χ_v ∘ det)` and `χ_v ∘ det` is trivial on the support of `f`. This is the step
"the fibre and the determinant condition" of the comparison of Arthur–Clozel 1989, Chapter 1,
§6.3(b) (printed p. 57) and Henniart–Lemaire 2011, II.6.12 (printed pp. 128–129). See the
paired Markdown.
-/

noncomputable section

universe uF uE uV uW

open NumberField IsDedekindDomain MeasureTheory
open Langlands.Global
open Langlands.Automorphic Langlands.BaseChange Langlands.HarmonicAnalysis
open scoped TensorProduct

namespace Langlands.Automorphic.Unramified

local instance fiberNormTraceRationalAddCommGroup (F : Type*) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance fiberNormTraceContinuousAddCommGroup (F : Type*) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance fiberNormTraceSmoothAddCommGroup (F : Type*) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance fiberNormTraceFormsAddCommGroup (F : Type*) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance fiberNormTraceLocalSpaceAddCommGroup {F : Type*} [Field F] [NumberField F]
    {n : ℕ} {v : Langlands.Global.FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

/-- **Equal local traces on norm determinants in a fibre of weak base change.** Let `E/F` be a
cyclic extension of number fields of degree `l` with generator `σ` (`IsCyclicAlgebra σ l`),
both adele quotients being compact. Let `T` be a cuspidal operator realization of `GL_{r+1}`
over `E` and `S`, `S'` cuspidal operator realizations of `GL_{r+1}` over `F` such that the class
of `T` is a weak base change of the class of `S` and of the class of `S'`. Let `D`, `D'` be
spectral presentations of `S`, `S'`, and `v` a finite place of `F` at which the local
components `π_v` of `D` and `π'_v` of `D'` are irreducible and admissible.

Then, for the Borel σ-algebra on `GL_{r+1}(F_v)`, every Haar measure `μ` on `GL_{r+1}(F_v)` and
every Schwartz–Bruhat function `f` on `GL_{r+1}(F_v)` such that `det g` lies in the image of the
norm `(F_v ⊗_F E)ˣ → F_vˣ` whenever `f g ≠ 0`, the traces `tr π_v(f)` and `tr π'_v(f)` for `μ`
are equal. -/
def WeakBaseChangeFiberNormTraceStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (r : ℕ) (T : CuspidalOperatorRealization E r) (S S' : CuspidalOperatorRealization F r),
      CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW}
        T.isoClass S.isoClass →
      CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW}
        T.isoClass S'.isoClass →
    ∀ (D : CuspidalSpectralPresentation.{uF, uV} S)
      (D' : CuspidalSpectralPresentation.{uF, uV} S') (v : Langlands.Global.FinitePlace F),
      (D.localComponent v).IsIrreducible → (D'.localComponent v).IsIrreducible →
    ∀ (hπ : Langlands.IsAdmissible (D.localComponent v).representation)
      (hπ' : Langlands.IsAdmissible (D'.localComponent v).representation),
      letI : ValuativeRel (v.adicCompletion F) :=
        (CompletionPadic.topologicalData v).valuativeRel
      haveI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
        (CompletionPadic.topologicalData v).localField
      haveI := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion F) (r + 1)
      haveI := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion F) (r + 1)
      haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace
        (v.adicCompletion F) (r + 1)
      letI : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion F)) := borel _
      haveI : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion F)) := ⟨rfl⟩
      ∀ (μ : Measure (GeneralLinear (r + 1) (v.adicCompletion F))) [μ.IsHaarMeasure]
        (f : SchwartzBruhat (GeneralLinear (r + 1) (v.adicCompletion F))),
        (∀ g : GeneralLinear (r + 1) (v.adicCompletion F), f g ≠ 0 →
          GeneralLinear.determinant g ∈
            (Units.map (Algebra.norm (v.adicCompletion F) :
              (v.adicCompletion F ⊗[F] E) →* v.adicCompletion F)).range) →
          Character.distribution μ (D.localComponent v).representation hπ f =
            Character.distribution μ (D'.localComponent v).representation hπ' f

end Langlands.Automorphic.Unramified
