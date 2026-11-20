import Langlands.BaseChange.TwistedCharacter

/-! # Transport of sigma-lifts along representation equivalences -/

noncomputable section

universe uF uE uV uV' uW uW'

set_option autoImplicit false

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis JacquetLanglands

section Distribution

variable {G : Type uE} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']

/-- Transporting a twist and its admissible action by the same equivariant
linear equivalence preserves its distribution character. -/
theorem twistedDistribution_eq_of_equivalent
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    {τ : Representation ℂ G W} {τ' : Representation ℂ G W'}
    (hτ : IsAdmissible τ) (hτ' : IsAdmissible τ') (e : τ.Equiv τ') (A : Module.End ℂ W) :
    twistedDistribution μ τ' hτ' (e.toLinearEquiv.conj A) = twistedDistribution μ τ hτ A := by
  apply LinearMap.ext
  intro f
  have he := Character.finiteRankIntegratedAction_equivariant μ τ hτ τ' hτ' e.toLinearEquiv
    (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap) f
  rw [twistedDistribution_apply, twistedDistribution_apply, he]
  let T := Character.finiteRankIntegratedAction μ τ hτ f
  let C : finiteRankEnd W := ⟨T.val.comp A, T.property.comp_right A⟩
  rw [← FiniteRankEnd.trace_conjugate e.toLinearEquiv C]
  apply congrArg FiniteRankEnd.trace
  exact Subtype.ext (e.toLinearEquiv.conj_comp A T.val).symm

end Distribution

section Intertwiner

variable {F : Type uF} {E : Type uE} [CommRing F] [CommRing E] [Algebra F E] {n : ℕ}
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
  {σ : E ≃ₐ[F] E} {τ : Representation ℂ (GeneralLinear n E) W}
  {τ' : Representation ℂ (GeneralLinear n E) W'}

/-- Conjugate a sigma-intertwiner by an actual equivalence of the underlying
upstairs representations. -/
def SigmaIntertwiner.transport (A : SigmaIntertwiner σ n τ) (e : τ.Equiv τ') :
    SigmaIntertwiner σ n τ' :=
  (e.symm.trans A).trans (Representation.Equiv.mk e.toLinearEquiv
    (fun g => e.toIntertwiningMap.isIntertwining' (entrywiseAut σ n g)))

@[simp]
theorem SigmaIntertwiner.transport_toLinearMap (A : SigmaIntertwiner σ n τ) (e : τ.Equiv τ') :
    (A.transport e).toLinearMap = e.toLinearEquiv.conj A.toLinearMap := rfl

end Intertwiner

section Lift

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {E : Type uE} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E] {n : ℕ}
  [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
  [TotallyDisconnectedSpace (GeneralLinear n F)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']

/-- The sigma-lift identity transports through independent equivalences on
both groups, with the same scalar. -/
theorem IsSigmaLift.transport
    {σ : E ≃ₐ[F] E} {d : ℕ} {c : ℂ}
    {π : Representation ℂ (GeneralLinear n F) V} {hπ : IsAdmissible π}
    {τ : Representation ℂ (GeneralLinear n E) W} {hτ : IsAdmissible τ}
    {A : SigmaIntertwiner σ n τ} (h : IsSigmaLift σ d π hπ τ hτ A c)
    {π' : Representation ℂ (GeneralLinear n F) V'} (hπ' : IsAdmissible π') (eF : π.Equiv π')
    {τ' : Representation ℂ (GeneralLinear n E) W'} (hτ' : IsAdmissible τ') (eE : τ.Equiv τ') :
    IsSigmaLift σ d π' hπ' τ' hτ' (A.transport eE) c := by
  let : MeasurableSpace (GeneralLinear n F) := borel _
  have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n E) := borel _
  have : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  refine ⟨h.1, ?_⟩
  intro μF _ μE _ φ f hmatch
  rw [SigmaIntertwiner.transport_toLinearMap, twistedDistribution_eq_of_equivalent μE hτ hτ' eE,
    ← Character.distribution_eq_of_equivariant μF π hπ π' hπ' eF.toLinearEquiv
      (Representation.IntertwiningMap.isIntertwining _ _ eF.toIntertwiningMap)]
  exact h.2 μF μE φ f hmatch

end Lift

end Langlands.BaseChange
