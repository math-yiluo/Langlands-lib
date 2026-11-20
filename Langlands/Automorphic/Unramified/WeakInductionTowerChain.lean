import Langlands.Automorphic.Unramified.TowerSpectralInvariant
import Langlands.Automorphic.Unramified.HeckeFamilyEndpoint
import Langlands.Automorphic.WeakAutomorphicInduction
import Langlands.Automorphic.CuspidalUnitaryForm
import Langlands.Automorphic.AssociatedFactorStatement

/-!
# Unitary chains up a prime cyclic tower from a weak induction

Let `T` be a prime cyclic tower from `F` to `K`, with `K/F` Galois, and suppose every unitary
datum at one level has a unitary weak base change at the next level. Start from the
one-constituent data of a cuspidal realization `S` over `F` with unitary central character,
pulled back to the bottom level. Then there is a unitary chain of successive weak base changes
along `T`. If `S` is a weak automorphic induction of a Hecke character `χ` of an intermediate
field `F ⊆ M ⊆ K`, and the cuspidal transport statement holds, then the terminal datum over `K`
has the Hecke family of the conjugates `χ ∘ N_{K/M} ∘ ρ i` for representatives `ρ i` of the
right cosets of `Gal(K/M)` in `Gal(K/F)`.
-/

noncomputable section

universe u uV

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified

/-- The pullback along a field isomorphism of the one-constituent data of a cuspidal
realization with unitary central character is unitary. -/
theorem isUnitary_arithmeticComap_ofCuspidal {F F' : Type u} [Field F] [NumberField F]
    [Field F'] [NumberField F'] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient F')] (e : F ≃+* F') {r : ℕ}
    (S : CuspidalOperatorRealization F' r)
    (hS : Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S) :
    ((IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)).arithmeticComap
      e).IsUnitary := by
  rw [IsobaricData.arithmeticComap_ofCuspidal,
    PositiveRankCuspidalClass.arithmeticComap_ofFixedRank, IsobaricData.isUnitary_ofCuspidal]
  obtain ⟨χ, hχ, hSχ⟩ := hS
  exact CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter
    (S.arithmeticComap e)
    ⟨HeckeCharacter.comap e χ, fun x => by simpa using hχ _,
      (S.arithmeticComap_hasCentralCharacter_iff e χ).mpr hSχ⟩

/-- Isobaric data have a Hecke family as soon as, at almost every finite place, all the
characters are unramified and the spectrum of an attached system is the multiset of their
values at every uniformizer. -/
theorem IsobaricData.hasHeckeFamily_of_eventually {K : Type u} [Field K] [NumberField K]
    [CompactSpace (AdeleQuotient K)] {D : IsobaricData K} {r : ℕ}
    (μ : Fin r → HeckeCharacter K) (hr : D.rank = r)
    (s : SpectralSystem (Global.FinitePlace K) D.rank)
    (hs : IsobaricData.HasSpectralSystem.{u, uV} D s)
    (h : ∀ᶠ v in Filter.cofinite, (∀ i, (μ i).IsUnramifiedAt v) ∧
      ∀ (hv : v ∉ s.exceptional) (π : (FiniteCompletion K v)ˣ),
        Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
        ((s.eigenvalues v hv : Eigenvalues D.rank) : Multiset ℂˣ) =
          (Finset.univ : Finset (Fin r)).val.map fun i => (μ i).finiteComponent v π) :
    IsobaricData.HasHeckeFamily.{u, uV} D μ := by
  classical
  have hfin := Filter.eventually_cofinite.mp h
  have hgood : ∀ v, v ∉ s.exceptional ∪ hfin.toFinset →
      (∀ i, (μ i).IsUnramifiedAt v) ∧
        ∀ (hv : v ∉ s.exceptional) (π : (FiniteCompletion K v)ˣ),
          Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
          ((s.eigenvalues v hv : Eigenvalues D.rank) : Multiset ℂˣ) =
            (Finset.univ : Finset (Fin r)).val.map fun i => (μ i).finiteComponent v π := by
    intro v hv
    have hv' : v ∉ hfin.toFinset := fun h' => hv (Finset.mem_union_right _ h')
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv'
    exact hv'
  refine ⟨hr, s, hs, s.exceptional ∪ hfin.toFinset, Finset.subset_union_left,
    fun i v hv => (hgood v hv).1 i, fun v hv π hπ => ?_⟩
  rw [SpectralSystem.eulerPolynomial, Eigenvalues.eulerPolynomial, (hgood v hv).2 _ π hπ,
    Multiset.map_map, HeckeFamily.eulerPolynomial, Finset.prod_eq_multiset_prod]
  rfl

/-- The profile of a system at a place where it is defined. -/
theorem underPowerProfile_of_notMem {K L : Type u} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {n : ℕ} (s : SpectralSystem (Global.FinitePlace K) n)
    (w : Global.FinitePlace L) (h : w.under (𝓞 K) ∉ s.exceptional) :
    underPowerProfile s w =
      (((s.eigenvalues (w.under (𝓞 K)) h).power (w.asIdeal.inertiaDeg (𝓞 K)) :
        Eigenvalues n) : Multiset ℂˣ) := by
  rw [underPowerProfile, dite_eq_left_of_eq_true (eq_true h)]
  rfl

namespace PrimeCyclicBaseChangeTower

variable {F K : Type u} [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]
  (T : PrimeCyclicBaseChangeTower F K)

omit [NumberField F] [NumberField K] in
/-- The bottom identification is compatible with the embeddings into `K`. -/
theorem algebraMap_bottomEquiv (x : T.level 0) :
    algebraMap F K (T.bottomEquiv x) = algebraMap (T.level 0) K x := by
  have h := T.bottomEquiv.symm.commutes (T.bottomEquiv x)
  rw [Algebra.algebraMap_self, RingHom.id_apply, AlgEquiv.symm_apply_apply] at h
  conv_rhs => rw [h]
  exact IsScalarTower.algebraMap_apply F (T.level 0) K _

omit [NumberField F] [NumberField K] in
/-- The inverse top identification is compatible with the embeddings into `K`. -/
theorem algebraMap_topEquiv_symm (x : K) :
    algebraMap (T.level (Fin.last T.length)) K (T.topEquiv.symm x) = x := by
  have h : ∀ y : T.level (Fin.last T.length), T.topEquiv y = algebraMap _ K y := fun _ => rfl
  rw [← h, AlgEquiv.apply_symm_apply]

variable [∀ i, CompactSpace (AdeleQuotient (T.level i))]

/-- If every unitary datum at one level has a unitary weak base change at the next level,
every unitary datum at the bottom level starts a unitary chain of successive weak base
changes. -/
theorem exists_isobaricChain_of_step
    (hBC : ∀ (i : Fin T.length) (DF : IsobaricData (T.level i.castSucc)), DF.IsUnitary →
      ∃ DE : IsobaricData (T.level i.succ), DE.IsUnitary ∧
        letI := T.stepAlgebra i
        IsobaricData.IsWeakBaseChangeOf.{u, u, uV, uV} DE DF)
    (D0 : IsobaricData (T.level 0)) (h0 : D0.IsUnitary) :
    ∃ D : T.IsobaricChain, D 0 = D0 ∧ D.IsUnitary ∧
      D.IsSuccessiveWeakBaseChange.{u, u, uV, uV} := by
  classical
  have hBC' : ∀ (i : Fin T.length) (DF : IsobaricData (T.level i.castSucc)),
      ∃ DE : IsobaricData (T.level i.succ), DF.IsUnitary → DE.IsUnitary ∧
        letI := T.stepAlgebra i
        IsobaricData.IsWeakBaseChangeOf.{u, u, uV, uV} DE DF := by
    intro i DF
    by_cases h : DF.IsUnitary
    · obtain ⟨DE, h1, h2⟩ := hBC i DF h
      exact ⟨DE, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose step hstep using hBC'
  let D : T.IsobaricChain :=
    Fin.induction (motive := fun i => IsobaricData (T.level i)) D0 step
  have hD0 : D 0 = D0 := Fin.induction_zero _ _
  have hDs : ∀ i : Fin T.length, D i.succ = step i (D i.castSucc) :=
    fun i => Fin.induction_succ _ _ i
  have hU : ∀ i, (D i).IsUnitary := by
    intro i
    induction i using Fin.induction with
    | zero => rw [hD0]; exact h0
    | succ i ih => rw [hDs]; exact (hstep i _ ih).1
  refine ⟨D, hD0, hU, fun i => ?_⟩
  have := (hstep i _ (hU i.castSucc)).2
  rw [← hDs] at this
  exact this

/-- The tower invariant passes from the bottom level to every level of a chain of
successive weak base changes. -/
theorem IsobaricChain.towerSpectralInvariant {D : T.IsobaricChain}
    (hD : D.IsSuccessiveWeakBaseChange.{u, u, uV, uV}) {N : ℕ}
    {X : Global.FinitePlace K → Multiset ℂˣ}
    (h0 : TowerSpectralInvariant.{u, uV} (L := K) (T.level 0) N (D 0) X)
    (i : Fin (T.length + 1)) :
    TowerSpectralInvariant.{u, uV} (L := K) (T.level i) N (D i) X := by
  induction i using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    let := T.stepAlgebra i
    have : IsScalarTower (T.level i.castSucc) (T.level i.succ) K :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact ih.weakBaseChange (hD i)

/-- **Chains from a weak induction.** Under the cuspidal transport statement and the existence
of unitary weak base changes along the steps, a cuspidal realization `S` over `F` with unitary
central character that is a weak automorphic induction of a Hecke character `χ` of `M` starts
a unitary chain of successive weak base changes along `T` ending at the Hecke family of the
conjugates `χ ∘ N_{K/M} ∘ ρ i`, for representatives `ρ i` of the right cosets of `Gal(K/M)`
in `Gal(K/F)`. -/
theorem exists_isobaricChain_endsAtHeckeFamily [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient K)] [IsGalois F K] {M : Type u} [Field M] [NumberField M]
    [Algebra F M] [Algebra M K] [IsScalarTower F M K]
    (hP : CuspidalArithmeticSpectralTransportStatement.{u, u, uV})
    (hBC : ∀ (i : Fin T.length) (DF : IsobaricData (T.level i.castSucc)), DF.IsUnitary →
      ∃ DE : IsobaricData (T.level i.succ), DE.IsUnitary ∧
        letI := T.stepAlgebra i
        IsobaricData.IsWeakBaseChangeOf.{u, u, uV, uV} DE DF)
    {r : ℕ} (S : CuspidalOperatorRealization F r)
    (hS : Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S)
    (χ : HeckeCharacter M)
    (hind : CuspidalOperatorRealization.IsoClass.IsWeakAutomorphicInductionOf.{u, u, uV}
      S.isoClass χ)
    (ρ : Fin (r + 1) → K ≃ₐ[F] K) (hρ : IsRightCosetFamily M ρ) :
    ∃ D : T.IsobaricChain, D.IsUnitary ∧ D.IsSuccessiveWeakBaseChange.{u, u, uV, uV} ∧
      D.StartsAtCuspidal S.isoClass ∧
      D.EndsAtHeckeFamily.{u, u, uV} (WeakInduction.conjugateNormFamily χ ρ) := by
  obtain ⟨sc, hsc, hwi⟩ := hind
  obtain ⟨D, hD0, hU, hD⟩ := T.exists_isobaricChain_of_step hBC _
    (isUnitary_arithmeticComap_ofCuspidal T.bottomEquiv.toRingEquiv S hS)
  refine ⟨D, hU, hD, hD0, ?_⟩
  have h0 : TowerSpectralInvariant.{u, uV} (L := K) (T.level 0) (r + 1) (D 0)
      (underPowerProfile (L := K) sc) := by
    rw [hD0]
    exact (towerSpectralInvariant_ofCuspidal (L := K) hsc).arithmeticComap hP
      T.bottomEquiv.toRingEquiv T.algebraMap_bottomEquiv
  obtain ⟨hN, s, hs, hev⟩ :=
    ((IsobaricChain.towerSpectralInvariant T hD h0 (Fin.last _)).arithmeticComap hP
      (A := K) T.topEquiv.symm.toRingEquiv T.algebraMap_topEquiv_symm).eventually_coe_eigenvalues
  refine IsobaricData.hasHeckeFamily_of_eventually _ hN s hs ?_
  filter_upwards [hev, WeakInduction.eventually_power_eq_conjugateNormFamily sc χ hwi ρ hρ]
    with w hw hbc
  obtain ⟨hu, hunr, heq⟩ := hbc
  refine ⟨hunr, fun hw' π hπ => (hw hw').trans ?_⟩
  rw [underPowerProfile_of_notMem sc w hu, heq π hπ]

end PrimeCyclicBaseChangeTower

end Langlands.Automorphic.Unramified
