import Langlands.Automorphic.AssociatedPresentationComparison
import Langlands.Automorphic.FiniteOrderDeterminantTwist
import Langlands.Automorphic.LocalDeterminantCharacter
import Langlands.Automorphic.Unramified.CyclicTransferStatement
import Langlands.Global.Arithmetic.ArtinNormStatement
import Langlands.Representation.Twist.SubquotientProof

/-! # Actual local components of finite-order determinant twists -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Global.HeckeCharacter

open AdelicFunctoriality
open scoped NumberField FiniteExtension

/-- A global norm-kernel character restricts to the given local norm kernel
when the local-global norm-image comparison is supplied. -/
theorem finiteComponent_ker_eq_localNorm_of_localGlobalNormImage
    (hNorm : LocalGlobalNormImageStatement.{uF, uE})
    {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] (hAbel : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ)
    (v : FinitePlace F) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]
    {χ : HeckeCharacter F} (hχ : χ.HasNormKernel E) :
    (χ.finiteComponent v).toMonoidHom.ker =
      (Units.map (Algebra.norm (FiniteCompletion F v) :
        FiniteCompletion E w →* FiniteCompletion F v)).range := by
  have hRange : Set.range (ideleClassNorm (K := F) (L := E)) =
      Set.range ((ideleClassMap F).comp (ideleNorm (K := F) (L := E))) := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨a, hx⟩
    · rintro ⟨a, ha⟩
      exact ⟨ideleClassMap E a, ha⟩
  have hLocal := (hNorm F E hAbel).1 v w
  ext z
  change χ (finiteClassInclusion F v z) = 1 ↔
    z ∈ (FiniteExtension.localUnitNorm v w).toMonoidHom.range
  rw [hχ, hRange]
  exact SetLike.ext_iff.mp hLocal z

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic.CuspidalSpectralPresentation

open Langlands.Global Langlands.Global.AdelicFunctoriality
open CuspidalOperatorRealization
open scoped NumberField FiniteExtension

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance detTwistRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance detTwistContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance detTwistSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance detTwistFormAddCommGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance detTwistStableFormAddCommGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance detTwistOperatorAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance detTwistLocalAddCommGroup {v : FinitePlace F} (A : LocalRealization F n v) :
    AddCommGroup A.Space := Submodule.addCommGroup _

private def localEquiv_of_determinantTwistEquations
    {S T : OperatorRealization F n}
    (v : FinitePlace F) (χ : HeckeCharacter F)
    (e : S.Space ≃ₗ[ℂ] T.Space)
    (he : OperatorRealization.DeterminantTwistEquations χ S T e) :
    (twist (χ.finiteLocalDeterminant n v).toMonoidHom
      (S.localRepresentation v)).Equiv (T.localRepresentation v) := by
  refine Representation.Equiv.mk e ?_
  intro g
  apply LinearMap.ext
  intro x
  change e ((χ.finiteLocalDeterminant n v g : ℂ) • S.localRepresentation v g x) =
    T.localRepresentation v g (e x)
  rw [e.map_smul]
  exact (he.1 (FiniteAdelicGL.localInclusion F n v g) x).symm

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} {S T : CuspidalOperatorRealization F r}

set_option maxHeartbeats 800000 in
/-- At each finite place with irreducible factors, the full determinant-twist
class relation restricts to the actual determinant twist of the local action. -/
theorem nonempty_localComponent_equiv_of_finiteOrderDeterminantTwist
    (P : CuspidalSpectralPresentation.{uF, uV} S) (Q : CuspidalSpectralPresentation.{uF, uW} T)
    (v : FinitePlace F) (χ : HeckeCharacter F)
    (h : S.isoClass.IsFiniteOrderDeterminantTwist χ T.isoClass)
    (hP : (P.localComponent v).IsIrreducible) (hQ : (Q.localComponent v).IsIrreducible) :
    Nonempty ((twist ((χ.finiteComponent v).toMonoidHom.comp GeneralLinear.determinant)
      (P.localComponent v).representation).Equiv (Q.localComponent v).representation) := by
  obtain ⟨_, e, he⟩ := IsoClass.isFiniteOrderDeterminantTwist_isoClass_iff.mp h
  let κ := (χ.finiteLocalDeterminant (r + 1) v).toMonoidHom
  have hκ : (χ.finiteComponent v).toMonoidHom.comp GeneralLinear.determinant = κ :=
    MonoidHom.ext fun g => (χ.finiteLocalDeterminant_eq_finiteComponent_det (r + 1) v g).symm
  rw [hκ]
  let eLoc := localEquiv_of_determinantTwistEquations v χ e he
  let fP := S.realization.localSubspaceInclusion v _ (P.localComponent_le_full v)
  let f : (twist κ (P.localComponent v).representation).IntertwiningMap
      (T.realization.localRepresentation v) :=
    eLoc.toIntertwiningMap.comp (twistIntertwining κ fP)
  have hf : Function.Injective f := by
    change Function.Injective (fun x => e (fP x))
    exact e.injective.comp
      (S.realization.localSubspaceInclusion_injective v _ (P.localComponent_le_full v))
  have : T.realization.IsIrreducible := T.irreducible
  have : (twist κ (P.localComponent v).representation).IsIrreducible :=
    (isIrreducible_twist_iff κ _).mpr hP
  have : (Q.localComponent v).representation.IsIrreducible := hQ
  exact T.realization.nonempty_local_equiv_of_injective v _ _ f hf
    (T.realization.localSubspaceInclusion v _ (Q.localComponent_le_full v))
    (T.realization.localSubspaceInclusion_injective v _ (Q.localComponent_le_full v))

/-- Finite-order determinant twists of full cuspidal classes restrict to the
actual local twists at places with irreducible factors. -/
def LocalFiniteOrderDeterminantTwistStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (S T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{uF, uV} S) (Q : CuspidalSpectralPresentation.{uF, uW} T)
    (v : FinitePlace F) (χ : HeckeCharacter F),
    S.isoClass.IsFiniteOrderDeterminantTwist χ T.isoClass →
    (P.localComponent v).IsIrreducible → (Q.localComponent v).IsIrreducible →
    Nonempty ((twist ((χ.finiteComponent v).toMonoidHom.comp GeneralLinear.determinant)
      (P.localComponent v).representation).Equiv (Q.localComponent v).representation)

theorem localFiniteOrderDeterminantTwist : LocalFiniteOrderDeterminantTwistStatement.{uF, uV, uW} :=
  fun _ _ _ _ _ _ _ P Q v χ =>
    P.nonempty_localComponent_equiv_of_finiteOrderDeterminantTwist Q v χ

/-- The global norm-kernel self-twist gives the local self-twist clause of
the cyclic induction criterion, using the local-global norm-image comparison. -/
theorem exists_localDeterminantSelfTwist_of_normKernel
    (hNorm : LocalGlobalNormImageStatement.{uF, uE})
    {E : Type uE} [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    (hAbel : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ)
    (P : CuspidalSpectralPresentation.{uF, uV} S)
    (v : FinitePlace F) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]
    (χ : HeckeCharacter F) (hχ : χ.HasNormKernel E)
    (hSelf : S.isoClass.IsFiniteOrderDeterminantTwist χ S.isoClass)
    (hP : (P.localComponent v).IsIrreducible) :
    ∃ κ : (FiniteCompletion F v)ˣ →* ℂˣ, Continuous κ ∧
      κ.ker = (Units.map (Algebra.norm (FiniteCompletion F v) :
        FiniteCompletion E w →* FiniteCompletion F v)).range ∧
      Nonempty ((P.localComponent v).representation.Equiv
        (twist (κ.comp GeneralLinear.determinant) (P.localComponent v).representation)) := by
  obtain ⟨e⟩ := P.nonempty_localComponent_equiv_of_finiteOrderDeterminantTwist P v χ hSelf hP hP
  exact ⟨(χ.finiteComponent v).toMonoidHom, (χ.finiteComponent v).continuous,
    HeckeCharacter.finiteComponent_ker_eq_localNorm_of_localGlobalNormImage hNorm hAbel v w hχ,
    ⟨e.symm⟩⟩

end Langlands.Automorphic.CuspidalSpectralPresentation
