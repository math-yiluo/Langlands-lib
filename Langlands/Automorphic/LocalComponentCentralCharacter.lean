import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.OperatorScalarCentralCharacter

/-! # Local central characters of presented automorphic components

If an actual cuspidal realization has the Hecke character `χ` as central character,
then the scalar matrix `a ∈ GL_n(F_v)` acts on every presented local component at the
finite place `v` by the local component `χ_v(a)` of `χ`.
-/

noncomputable section
universe uF uP

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL
open ContinuousRationalFunctions

variable {F : Type uF} [Field F] [NumberField F]

local instance localCentralRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance localCentralContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance localCentralSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance localCentralFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance localCentralLocalSpaceAddCommGroup {n : ℕ} {v : FinitePlace F}
    (S : LocalRealization F n v) : AddCommGroup S.Space := Submodule.addCommGroup _

namespace LocalRealization

variable {n : ℕ} {v : FinitePlace F} (S : LocalRealization F n v)

/-- In a local realization with global central character `χ`, the local scalar matrix
`a` acts by the value `χ_v(a)` of the local component of `χ`. -/
theorem representation_scalar_of_hasCentralCharacter (χ : HeckeCharacter F)
    (hχ : S.HasCentralCharacter χ) (a : (FiniteCompletion F v)ˣ) (f : S.Space) :
    S.representation (Matrix.GeneralLinearGroup.scalar (Fin n) a) f =
      (χ.finiteComponent v a : ℂ) • f := by
  apply S.toContinuous_injective
  apply toContinuousMap_injective F n
  ext x
  change evaluate F n (S.toContinuous (S.representation _ f)) x =
    evaluate F n (S.toContinuous ((χ.finiteComponent v a : ℂ) • f)) x
  rw [S.evaluate_representation]
  have hx : x * AdelicGL.ofFinite F n
        (localInclusion F n v (Matrix.GeneralLinearGroup.scalar (Fin n) a)) =
      AdelicGL.scalar F n (finiteIdeleInclusion F v a) * x := by
    have hc := (AdelicGL.scalar_commute F n (finiteIdeleInclusion F v a) x).eq
    rw [AdelicGL.scalar_finiteIdeleInclusion] at hc ⊢
    exact hc.symm
  rw [hx, S.centralCharacter_evaluate χ hχ f]
  exact ((congrArg (fun φ => evaluate F n φ x)
    (S.toContinuous.map_smul (χ.finiteComponent v a : ℂ) f)).trans rfl).symm

end LocalRealization

namespace CuspidalSpectralPresentation

variable [CompactSpace (AdeleQuotient F)]
variable {r : ℕ} {T : CuspidalOperatorRealization F r}
variable (P : CuspidalSpectralPresentation.{uF, uP} T)

/-- Every presented local component inherits the global central character condition. -/
theorem localComponent_hasCentralCharacter (v : FinitePlace F) (χ : HeckeCharacter F)
    (hχ : T.HasCentralCharacter χ) : (P.localComponent v).HasCentralCharacter χ :=
  FiniteTensorPresentation.localComponent_hasCentralCharacter P.presentation
    P.finiteSlice.nonzero v χ (P.finiteSlice.hasCentralCharacter χ hχ)

end CuspidalSpectralPresentation

end Langlands.Automorphic
