import Langlands.Automorphic.AssociatedDeterminantTwistStatement
import Langlands.Automorphic.OperatorDeterminantTwist
import Langlands.Automorphic.CuspidalSpectralDeterminantTwist
import Langlands.Automorphic.FiniteLocalDeterminantTwist
import Langlands.Representation.Unramified.SpectralSystemScaling

/-! # Twists by arbitrary Hecke characters

Henniart (2000), §2.2: for a character `χ` of `C_F`, `(χ ∘ τ_F) ⊗ S` and `(χ ∘ det) ⊗ Π`
are associated whenever `S` and `Π` are. The Library states this for finite-order `χ`
only. Henniart's §3.7 twists by an unramified unitary character of infinite order, so
this module states it for every Hecke character.

For an arbitrary `χ`, the twist is the relation `OperatorRealization.IsDeterminantMultiple`:
the space of the target is the image of the space of the source under multiplication by
`χ ∘ det`, as continuous functions on `GL_n(𝔸_F)`. The module proves that this relation
has at most one target, and that for finite-order `χ` its target is the existing
`OperatorRealization.determinantTwist`. It then states, as proposition definitions only,
that cuspidal twists and twisted presentations exist, and that weak association passes to
the twist; `RelativeWeilGroup.HeckeDeterminantTwistStatement` is their conjunction.
-/

noncomputable section

universe u uF uV uW uP uQ

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions Langlands.Unramified

variable {F : Type uF} [Field F] [NumberField F]

local instance heckeTwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeTwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeTwistSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeTwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance heckeTwistStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

section Realization

variable {n : ℕ}

namespace OperatorRealization

local instance heckeTwistSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- `T` is the twist of `S` by `χ ∘ det`: some linear equivalence `S → T` sends each
vector to a vector whose continuous function is `g ↦ χ(det g) f(g)`, for `f` the
continuous function of the original vector. The space of `T` is then the image of the
space of `S` under this multiplication. Every Hecke character is allowed. -/
def IsDeterminantMultiple (χ : HeckeCharacter F) (S T : OperatorRealization F n) : Prop :=
  ∃ e : S.Space ≃ₗ[ℂ] T.Space, ∀ f : S.Space,
    T.toContinuous (e f) = determinantMultiplier n χ (S.toContinuous f)

/-- Vectors of two realizations with the same continuous function are the same stable
function. -/
theorem val_eq_of_toContinuous_eq {S T : OperatorRealization F n} {x : S.Space}
    {y : T.Space} (h : S.toContinuous x = T.toContinuous y) :
    (x : StableAutomorphicFunctions F n) = y :=
  stableAutomorphicInclusion_injective F n (automorphicToContinuous_injective F n h)

/-- The finite-order twist `S.determinantTwist χ hχ` is a determinant multiple. -/
theorem isDeterminantMultiple_determinantTwist (S : OperatorRealization F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    IsDeterminantMultiple χ S (S.determinantTwist χ hχ) :=
  ⟨(S.determinantTwistEquiv χ hχ).toLinearEquiv, fun _ => rfl⟩

/-- Multiplication by the trivial character relates every realization to itself. -/
theorem isDeterminantMultiple_refl (S : OperatorRealization F n) :
    IsDeterminantMultiple 1 S S := by
  refine ⟨LinearEquiv.refl ℂ S.Space, fun f => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change evaluate F n (S.toContinuous f) x = 1 * evaluate F n (S.toContinuous f) x
  exact (one_mul _).symm

/-- A source and a character have at most one target. -/
theorem IsDeterminantMultiple.eq {χ : HeckeCharacter F} {S T U : OperatorRealization F n}
    (h : IsDeterminantMultiple χ S T) (h' : IsDeterminantMultiple χ S U) : T = U := by
  have key : ∀ {T U : OperatorRealization F n}, IsDeterminantMultiple χ S T →
      IsDeterminantMultiple χ S U →
        ∀ x, x ∈ T.toSubmodule → x ∈ U.toSubmodule := by
    rintro T U ⟨e, he⟩ ⟨e', he'⟩ x hx
    have hxy : ((e' (e.symm ⟨x, hx⟩) : U.Space) : StableAutomorphicFunctions F n) = x :=
      val_eq_of_toContinuous_eq (y := (⟨x, hx⟩ : T.Space))
        (by rw [he', ← he, LinearEquiv.apply_symm_apply])
    rw [← hxy]
    exact (e' (e.symm ⟨x, hx⟩)).property
  apply Subrepresentation.toSubmodule_injective
  ext x
  exact ⟨key h h' x, key h' h x⟩

/-- For the trivial character the relation is equality of realizations. -/
theorem isDeterminantMultiple_one_iff {S T : OperatorRealization F n} :
    IsDeterminantMultiple 1 S T ↔ S = T := by
  constructor
  · intro h
    exact (isDeterminantMultiple_refl S).eq h
  · rintro rfl
    exact isDeterminantMultiple_refl S

/-- For finite-order `χ` the target is the existing finite-order twist. -/
theorem IsDeterminantMultiple.eq_determinantTwist {χ : HeckeCharacter F}
    {S T : OperatorRealization F n} (h : IsDeterminantMultiple χ S T)
    (hχ : χ.HasFiniteOrder) : T = S.determinantTwist χ hχ :=
  h.eq (isDeterminantMultiple_determinantTwist S χ hχ)

/-- For finite-order `χ` the relation implies the existing finite-order twist relation. -/
theorem IsDeterminantMultiple.isFiniteOrderDeterminantTwist {χ : HeckeCharacter F}
    {S T : OperatorRealization F n} (h : IsDeterminantMultiple χ S T)
    (hχ : χ.HasFiniteOrder) : IsFiniteOrderDeterminantTwist χ S T := by
  rw [h.eq_determinantTwist hχ]
  exact S.isFiniteOrderDeterminantTwist χ hχ

end OperatorRealization

end Realization

section Presentation

variable [CompactSpace (AdeleQuotient F)]

namespace CuspidalSpectralPresentation

variable {r : ℕ} {S T : CuspidalOperatorRealization F r}

/-- `P'` is a twist of `P` by `χ ∘ det`: the realization of `P'` is the determinant
multiple of the realization of `P`; at every finite place `v` the local component of `P'`
is equivalent to the local component of `P` twisted by `χ_v ∘ det`; and at almost every
place the Euler polynomial of `P'` is that of `P` with every Satake parameter multiplied
by `χ_v(ϖ_v)`. Every Hecke character is allowed. -/
def IsDeterminantMultiple (χ : HeckeCharacter F) (P : CuspidalSpectralPresentation.{uF, uV} S)
    (P' : CuspidalSpectralPresentation.{uF, uW} T) : Prop :=
  OperatorRealization.IsDeterminantMultiple χ S.realization T.realization ∧
    (∀ v : FinitePlace F,
      Nonempty ((Langlands.twist (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom
        (P.localComponent v).representation).Equiv (P'.localComponent v).representation)) ∧
    (SpectralSystem.scale χ.finiteUniformizerValue P.spectralSystem).SameEulerPolynomials
      P'.spectralSystem

/-- For finite-order `χ` the existing twisted presentation is a twist in this sense. -/
theorem isDeterminantMultiple_determinantTwist (P : CuspidalSpectralPresentation.{uF, uV} S)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    P.IsDeterminantMultiple χ (P.determinantTwist χ hχ) :=
  ⟨OperatorRealization.isDeterminantMultiple_determinantTwist S.realization χ hχ,
    fun v => ⟨((P.localComponent v).determinantTwistRepresentationEquiv χ hχ).trans
      (P.determinantTwistLocalComponentEquiv χ hχ v).symm⟩,
    P.sameEulerPolynomials_determinantTwist χ hχ⟩

end CuspidalSpectralPresentation

end Presentation

/-- Henniart (2000), §2.2, existence of twists by arbitrary Hecke characters: for every
irreducible cuspidal realization `S` of `GL_{r+1}(𝔸_F)`, every presentation `P` of `S` and
every Hecke character `χ` of `F`, some irreducible cuspidal realization `T` and some
presentation `P'` of `T` form a twist of `P` by `χ ∘ det`. -/
def CuspidalDeterminantMultipleStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (S : CuspidalOperatorRealization F r) (P : CuspidalSpectralPresentation.{u, uP} S)
    (χ : HeckeCharacter F),
    ∃ (T : CuspidalOperatorRealization F r) (P' : CuspidalSpectralPresentation.{u, uP} T),
      P.IsDeterminantMultiple χ P'

end Langlands.Automorphic

namespace Langlands.ClassField.Global

open Langlands.Global

namespace RelativeWeilGroup

/-- Henniart (2000), §2.2, for twists by arbitrary Hecke characters, presented form: at an
arithmetic class family, if `S` is weakly associated with the spectral system of a
presentation of `T`, and the realization of `T'` is the determinant multiple of that of
`T` by a Hecke character `χ`, then `(χ ∘ τ_F) ⊗ S` is weakly associated with the
spectral system of every presentation of `T'`. -/
def PresentedDeterminantMultipleAssociationStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (T T' : Automorphic.CuspidalOperatorRealization F r)
    (P : Automorphic.CuspidalSpectralPresentation.{u, uP} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T') (χ : HeckeCharacter F),
    Automorphic.OperatorRealization.IsDeterminantMultiple χ T.realization T'.realization →
    IsWeaklyAssociated S P.spectralSystem →
    IsWeaklyAssociated (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S)
      P'.spectralSystem

/-- The existence and association assertions of Henniart (2000), §2.2, for twists by
arbitrary Hecke characters. -/
def HeckeDeterminantTwistStatement : Prop :=
  Automorphic.CuspidalDeterminantMultipleStatement.{u, uP} ∧
    PresentedDeterminantMultipleAssociationStatement.{u, uV, uP, uQ}

end RelativeWeilGroup

end Langlands.ClassField.Global
