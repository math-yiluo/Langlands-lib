import Langlands.BaseChange.SigmaStableSupercuspidalDescentStatement
import Langlands.BaseChange.CuspidalSigmaLiftExistenceStatement
import Langlands.BaseChange.SigmaLiftTransport
import Langlands.BaseChange.CommonShintaniLiftNonvanishing
import Langlands.LocalField.FiniteExtensionModuleTopology
import Langlands.Group.GL.RankReindex

/-!
# Descent of σ-stable supercuspidal representations from the supercuspidal σ-lift converse

`SigmaStableSupercuspidalDescentReductionStatement` is the implication
`CuspidalSigmaLiftExistenceStatement → SigmaStableSupercuspidalDescentStatement`, proved by
`sigmaStableSupercuspidalDescentReduction`: the converse is applied with orbit length `s = 1`.
See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

universe u v uV uW uW'

section Stability

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E] {n : ℕ}
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A σ-stable representation of `GL_n(E)` is `σ^i`-stable for every `i`. -/
theorem SigmaIntertwiner.nonempty_pow {σ : E ≃ₐ[F] E}
    {τ : Representation ℂ (GeneralLinear n E) W} (A : SigmaIntertwiner σ n τ) (i : ℕ) :
    Nonempty (τ.Equiv (τ.comp (entrywiseAut (σ ^ i) n).toMonoidHom)) := by
  induction i with
  | zero =>
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ W) (fun g => ?_)⟩
    change (LinearMap.id : W →ₗ[ℂ] W) ∘ₗ τ g = τ (entrywiseAut (σ ^ 0) n g) ∘ₗ LinearMap.id
    rw [pow_zero, entrywiseAut_one_apply, LinearMap.id_comp, LinearMap.comp_id]
  | succ i ih =>
    obtain ⟨e⟩ := ih
    let e' : Representation.Equiv (τ.comp (entrywiseAut σ n).toMonoidHom)
        (τ.comp (entrywiseAut (σ ^ (i + 1)) n).toMonoidHom) :=
      Representation.Equiv.mk e.toLinearEquiv (fun g => by
        change (e.toLinearEquiv : W →ₗ[ℂ] W) ∘ₗ τ (entrywiseAut σ n g) =
          τ (entrywiseAut (σ ^ (i + 1)) n g) ∘ₗ e.toLinearEquiv
        rw [pow_succ, entrywiseAut_mul_apply]
        exact e.isIntertwining' (entrywiseAut σ n g))
    exact ⟨A.trans e'⟩

end Stability

section Rank

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]

/-- A σ-lift at rank `m` of a representation `Π` equivalent to `τ` after the reindexing along
`m = n` gives a σ-lift of `τ` at rank `n`, with a supercuspidal irreducible representation of
`GL_n(F)` on the same space. -/
theorem exists_isSigmaLift_of_rank_eq {σ : E ≃ₐ[F] E} {l m n : ℕ} (h : m = n)
    [T2Space (GeneralLinear m F)] [LocallyCompactSpace (GeneralLinear m F)]
    [TotallyDisconnectedSpace (GeneralLinear m F)]
    [T2Space (GeneralLinear m E)] [LocallyCompactSpace (GeneralLinear m E)]
    [TotallyDisconnectedSpace (GeneralLinear m E)]
    [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
    [TotallyDisconnectedSpace (GeneralLinear n F)]
    [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
    [TotallyDisconnectedSpace (GeneralLinear n E)]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GeneralLinear m F) V} (hπ : GeneralLinear.IsSupercuspidal π)
    (hπirr : π.IsIrreducible)
    {P : Representation ℂ (GeneralLinear m E) W'} {hP : IsAdmissible P}
    {A₀ : SigmaIntertwiner σ m P} {c : ℂ} (hlift : IsSigmaLift σ l π hπ.1 P hP A₀ c)
    {τ : Representation ℂ (GeneralLinear n E) W} (hτ : IsAdmissible τ)
    (b : Representation.Equiv P
      (τ.comp (GeneralLinear.reindex (R := E) (finCongr h.symm)).symm.toMonoidHom)) :
    ∃ (π' : Representation ℂ (GeneralLinear n F) V) (hπ' : GeneralLinear.IsSupercuspidal π'),
      π'.IsIrreducible ∧ ∃ A : SigmaIntertwiner σ n τ, IsSigmaLift σ l π' hπ'.1 τ hτ A c := by
  subst h
  let e : Representation.Equiv
      (τ.comp (GeneralLinear.reindex (R := E) (finCongr (rfl : m = m))).symm.toMonoidHom) τ :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ W) (fun g => by
      change (LinearMap.id : W →ₗ[ℂ] W) ∘ₗ
          τ ((GeneralLinear.reindex (R := E) (finCongr (rfl : m = m))).symm g) =
        τ g ∘ₗ LinearMap.id
      rw [GeneralLinear.reindex_finCongr_rfl, LinearMap.id_comp, LinearMap.comp_id]
      rfl)
  exact ⟨π, hπ, hπirr, A₀.transport (b.trans e),
    hlift.transport hπ.1 (Representation.Equiv.refl π) hτ (b.trans e)⟩

end Rank

/-- The supercuspidal σ-lift converse (`CuspidalSigmaLiftExistenceStatement`) implies the descent
of σ-stable irreducible supercuspidal representations of `GL_n(E)`, for every σ-intertwiner. -/
def SigmaStableSupercuspidalDescentReductionStatement : Prop :=
  CuspidalSigmaLiftExistenceStatement.{u, v, uV, uW} →
    SigmaStableSupercuspidalDescentStatement.{u, v, uV, uW}

/-- Apply the converse with orbit length one, return from rank `1 * n` to rank `n`, and rescale
the constant for the given σ-intertwiner by Schur's lemma. -/
theorem sigmaStableSupercuspidalDescentReduction :
    SigmaStableSupercuspidalDescentReductionStatement.{u, v, uV, uW} := by
  intro hExist F _ _ _ _ _ E _ _ _ _ _ σ l n hE hn
  have : Module.Finite F E := hE.1
  let := LocalField.FiniteExtension.valuativeRel F E
  have := LocalField.FiniteExtension.isLocalField_of_isModuleTopology F E
  intro W _ _ τ hτ hirr A
  have hstab : ∀ i : ℕ,
      Nonempty (τ.Equiv (τ.comp (entrywiseAut (σ ^ i) n).toMonoidHom)) ↔ 1 ∣ i :=
    fun i => ⟨fun _ => one_dvd i, fun _ => A.nonempty_pow i⟩
  obtain ⟨_, hP, V, _, _, π, hπ, A₀, c₀, hπsc, hπirr, _, hlift⟩ :=
    hExist F E σ l hE 1 n hn W τ hτ hirr hstab
  obtain ⟨b⟩ := sigmaOrbitProduct_one_equiv σ hn τ hτ.1.1
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  have := LocalFieldTopology.generalLinear_t2Space F (1 * n)
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F (1 * n)
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (1 * n)
  have := LocalFieldTopology.generalLinear_t2Space E (1 * n)
  have := LocalFieldTopology.generalLinear_locallyCompactSpace E (1 * n)
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (1 * n)
  obtain ⟨π', hπ', hπ'irr, A', hlift'⟩ :=
    exists_isSigmaLift_of_rank_eq (Nat.one_mul n) hπsc hπirr hlift hτ.1 b
  obtain ⟨a, ha, hA⟩ := A'.exists_smul_toLinearMap A hτ.1 hirr
  let : MeasurableSpace (GeneralLinear n F) := borel _
  have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n E) := borel _
  have : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  refine ⟨V, inferInstance, inferInstance, π', hπ', a * c₀, hπ'irr,
    mul_ne_zero ha hlift'.1, ?_⟩
  intro μF _ μE _ φ f hconc
  rw [hA, twistedDistribution_smul, LinearMap.smul_apply, hlift'.2 μF μE φ f hconc, smul_eq_mul,
    mul_assoc]

end Langlands.BaseChange
