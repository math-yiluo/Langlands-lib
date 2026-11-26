import Langlands.BaseChange.TwistedCharacter.Exactness
import Langlands.BaseChange.TwistedCharacter.Socle
import Langlands.Representation.Classification.CuspidalProductContragredient
import Langlands.Representation.Smooth.Admissibility.ExactProof

/-! # Reduction of finite-length twisted distributions to irreducibles -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis CategoryTheory

universe uG z

variable {G : Type uG} [Group G]
  {V : Type z} [AddCommGroup V] [Module ℂ V]

private theorem exists_finite_atom_decomposition (ρ : Representation ℂ G V)
    [IsNoetherian (MonoidAlgebra ℂ G) ρ.asModule]
    [IsSemisimpleModule (MonoidAlgebra ℂ G) ρ.asModule] :
    ∃ (n : ℕ) (S : Fin n → Subrepresentation ρ),
      (∀ i, IsAtom (S i)) ∧ iSupIndep S ∧ ⨆ i, S i = ⊤ := by
  obtain ⟨s, hind, htop, hs⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top
    (MonoidAlgebra ℂ G) ρ.asModule
  have hfin : s.Finite := WellFoundedGT.finite_of_sSupIndep hind
  have := hfin.to_subtype
  let e := Finite.equivFin s
  let O := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  refine ⟨Nat.card s, fun i => O.symm (e.symm i).val,
    fun i => (O.symm.isAtom_iff _).mpr (isSimpleModule_iff_isAtom.mp (hs _ (e.symm i).property)),
    (((sSupIndep_iff s).mp hind).comp e.symm.injective).map_orderIso O.symm, ?_⟩
  rw [← O.symm.map_iSup (fun i => (e.symm i).val), e.symm.iSup_comp (g := fun m : s => m.val),
    ← sSup_eq_iSup', htop, O.symm.map_top]

section Semisimple

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  (θ : G ≃* G) (L : Submodule ℂ (Distribution G))

/-- The trace of a twisted intertwining map on a Noetherian semisimple representation
lies in any subspace containing the twisted traces of its irreducible subrepresentations. -/
theorem twistedDistribution_mem_of_semisimple (B : SmoothRep.{0,uG,z} ℂ G)
    (hB : B.IsAdmissible) [IsNoetherian (MonoidAlgebra ℂ G) B.representation.asModule]
    [IsSemisimpleModule (MonoidAlgebra ℂ G) B.representation.asModule]
    (T : B.representation.IntertwiningMap (B.representation.comp θ.toMonoidHom))
    (hspan : ∀ (D : SmoothRep.{0,uG,z} ℂ G) (hD : D.IsAdmissible),
      D.IsIrreducible → SmoothRep.IsSubrepresentation D B →
      ∀ A : D.representation.Equiv (D.representation.comp θ.toMonoidHom),
        twistedDistribution μ D.representation hD A.toLinearMap ∈ L) :
    twistedDistribution μ B.representation hB T.toLinearMap ∈ L := by
  classical
  obtain ⟨n, S, hS, hin, htop⟩ := exists_finite_atom_decomposition B.representation
  let W (i : Fin n) : Type z := (S i).toSubmodule
  let π (i : Fin n) : Representation ℂ G (W i) := (S i).toRepresentation
  let M := Representation.directSum π
  have hint : DirectSum.IsInternal (fun i => (S i).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (FiniteCharacter.iSupIndep_toSubmodule hin) (by
        rw [← Langlands.Subrepresentation.toSubmodule_iSup, htop]
        rfl)
  let e : M.Equiv B.representation := Representation.Equiv.mk
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i => (S i).toSubmodule) hint) fun g => by
      refine DirectSum.linearMap_ext ℂ fun i => LinearMap.ext fun x => ?_
      change DirectSum.coeLinearMap (fun i => (S i).toSubmodule)
          (DirectSum.lmap (fun i => π i g) (DirectSum.lof ℂ (Fin n) W i x)) =
        B.representation g (DirectSum.coeLinearMap (fun i => (S i).toSubmodule)
          (DirectSum.lof ℂ (Fin n) W i x))
      rw [DirectSum.lmap_lof, DirectSum.coeLinearMap_lof, DirectSum.coeLinearMap_lof]
      rfl
  let j (i : Fin n) : (π i).IntertwiningMap B.representation :=
    ⟨(S i).toSubmodule.subtype, fun _ => rfl⟩
  let p (i : Fin n) : M.IntertwiningMap (π i) :=
    ⟨DirectSum.component ℂ (Fin n) W i, fun _ => rfl⟩
  let q (i : Fin n) : B.representation.IntertwiningMap (π i) :=
    (p i).comp e.symm.toIntertwiningMap
  have hsum : ∑ i, (j i).toLinearMap ∘ₗ (q i).toLinearMap = LinearMap.id := by
    ext v
    rw [LinearMap.sum_apply]
    let x := e.symm v
    have hx : (∑ i, DirectSum.lof ℂ (Fin n) W i (x i)) = x := by
      ext i
      simp [DirectSum.lof_eq_of, DirectSum.of_apply]
    have he := congrArg e hx
    rw [map_sum] at he
    change (∑ i, (j i).toLinearMap ((q i).toLinearMap v)) = v
    calc
      (∑ i, (j i).toLinearMap ((q i).toLinearMap v)) =
          ∑ i, e (DirectSum.lof ℂ (Fin n) W i (x i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        change (x i : B) = DirectSum.coeLinearMap (fun i => (S i).toSubmodule)
          (DirectSum.lof ℂ (Fin n) W i (x i))
        rw [DirectSum.coeLinearMap_lof]
      _ = v := he.trans (e.apply_symm_apply v)
  have hπ (i : Fin n) : IsAdmissible (π i) :=
    isAdmissible_of_injective (j i) Subtype.val_injective hB
  rw [twistedDistribution_eq_sum_diagonal μ _ hB π hπ j q hsum]
  apply L.sum_mem
  intro i _
  let Ti : (π i).IntertwiningMap ((π i).comp θ.toMonoidHom) :=
    ⟨(q i).toLinearMap ∘ₗ T.toLinearMap ∘ₗ (j i).toLinearMap, fun g => by
      apply LinearMap.ext
      intro w
      change q i (T (j i (π i g w))) = π i (θ g) (q i (T (j i w)))
      rw [(j i).isIntertwining]
      have h := LinearMap.congr_fun (T.isIntertwining' g) (j i w)
      change T (B.representation g (j i w)) = B.representation (θ g) (T (j i w)) at h
      rw [h, (q i).isIntertwining]⟩
  have hirr : (π i).IsIrreducible :=
    FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom _ (hS i)
  let := hirr
  let := (CuspidalSupport.isIrreducible_comp_mulEquiv_iff (π i) θ).mpr hirr
  rcases Representation.IsIrreducible.bijective_or_eq_zero Ti with hTi | hzero
  · exact hspan (SmoothRep.of (π i) (hπ i).1) (hπ i) hirr
      ⟨SmoothRep.ofHom (j i), Subtype.val_injective⟩ (Ti.ofBijective hTi)
  · change twistedDistribution μ _ _ Ti.toLinearMap ∈ L
    rw [hzero]
    have h0 : twistedDistribution μ (π i) (hπ i) 0 = 0 := by
      ext f
      simp [twistedDistribution_apply, show (⟨0, _⟩ : finiteRankEnd (W i)) = 0 from rfl]
    exact h0.symm ▸ L.zero_mem

end Semisimple

section Quotients

variable [TopologicalSpace G]
  {B : SmoothRep.{0,uG,z} ℂ G} (θ : G ≃* G) (S : Subrepresentation B.representation)
  (A : B.representation.Equiv (B.representation.comp θ.toMonoidHom))
  (hS : S.toSubmodule.map A.toLinearMap = S.toSubmodule)

/-- Restrict a twisting isomorphism to an invariant subrepresentation it preserves. -/
def subrepresentationTwistingEquiv :
    let C := B.subrepresentation S
    C.representation.Equiv (C.representation.comp θ.toMonoidHom) :=
  Representation.Equiv.mk
    ((A.toLinearEquiv.submoduleMap S.toSubmodule).trans (LinearEquiv.ofEq _ _ hS)) fun g => by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact LinearMap.congr_fun (A.isIntertwining' g) x.val

/-- Descend a twisting isomorphism to the quotient by a subrepresentation it preserves. -/
def quotientTwistingEquiv :
    let C := B.quotient S
    C.representation.Equiv (C.representation.comp θ.toMonoidHom) :=
  Representation.Equiv.mk (Submodule.Quotient.equiv S.toSubmodule S.toSubmodule A.toLinearEquiv hS)
    fun g => by
      apply Submodule.linearMap_qext
      apply LinearMap.ext
      intro x
      exact congrArg S.toSubmodule.mkQ (LinearMap.congr_fun (A.isIntertwining' g) x)

end Quotients

section FiniteLength

open Classification

/-- The twisted distribution of an admissible finite-length representation belongs to
every subspace containing the twisted distributions of its stable irreducible subquotients. -/
def TwistedDistributionConstituentSpanStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (θ : G ≃* G) (L : Submodule ℂ (Distribution G))
    (B : SmoothRep.{0,uG,z} ℂ G) (hB : B.IsAdmissible), B.HasFiniteLength →
    ∀ A : B.representation.Equiv (B.representation.comp θ.toMonoidHom),
      (∀ (D : SmoothRep.{0,uG,z} ℂ G) (hD : D.IsAdmissible),
        D.IsIrreducible → SmoothRep.IsSubquotient D B →
        ∀ A' : D.representation.Equiv (D.representation.comp θ.toMonoidHom),
          twistedDistribution μ D.representation hD A'.toLinearMap ∈ L) →
      twistedDistribution μ B.representation hB A.toLinearMap ∈ L

/-- Remove the preserved socle of each quotient and use additivity of twisted traces. -/
theorem twistedDistribution_mem_of_finiteLength :
    TwistedDistributionConstituentSpanStatement.{uG,z} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ θ L B hB hfin A hspan
  classical
  have hcofinal (U : OpenSubgroup G) :
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ U := by
    obtain ⟨K, hKU, hK, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ U
    exact ⟨K, hK, hKU⟩
  have hBnoeth := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := B.representation)
  have hWF : WellFounded (fun S T : Subrepresentation B.representation => T < S) :=
    e.dual.toOrderEmbedding.wellFounded hBnoeth.wf
  have hQ (S : Subrepresentation B.representation) :
      ∀ (Q : SmoothRep.{0,uG,z} ℂ G) (hQadm : Q.IsAdmissible)
        (p : B.representation.IntertwiningMap Q.representation),
        Function.Surjective p → p.ker = S →
        ∀ A' : Q.representation.Equiv (Q.representation.comp θ.toMonoidHom),
          twistedDistribution μ Q.representation hQadm A'.toLinearMap ∈ L := by
    induction S using hWF.induction with
    | h S ih =>
      intro Q hQadm p hp hker A'
      cases subsingleton_or_nontrivial Q with
      | inl hz =>
        have hzero : twistedDistribution μ Q.representation hQadm A'.toLinearMap = 0 := by
          apply LinearMap.ext
          intro f
          let t := Character.finiteRankIntegratedAction μ Q.representation hQadm f
          let b : finiteRankEnd Q := ⟨t.val.comp A'.toLinearMap,
            t.property.comp_right A'.toLinearMap⟩
          change FiniteRankEnd.trace b = 0
          have hb : b = 0 := Subtype.ext (LinearMap.ext fun _ => hz.elim _ _)
          rw [hb, map_zero]
        exact hzero.symm ▸ L.zero_mem
      | inr hn =>
        have hfQ : Q.HasFiniteLength :=
          hfin.of_surjective (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ p) hp
        let := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfQ).2
        let R := socle Q.representation
        let U := Q.subrepresentation R
        let C := Q.quotient R
        let j : U.representation.IntertwiningMap Q.representation := SmoothRep.hom (Q.subtype R)
        let q : Q.representation.IntertwiningMap C.representation := SmoothRep.hom (Q.mkQ R)
        have hj := Q.subtype_injective R
        have hq := Q.mkQ_surjective R
        have hseq : LinearMap.range j.toLinearMap = LinearMap.ker q.toLinearMap := by
          change LinearMap.range R.toSubmodule.subtype = LinearMap.ker R.toSubmodule.mkQ
          rw [Submodule.range_subtype, Submodule.ker_mkQ]
        obtain ⟨hU, hC⟩ := (isAdmissible_iff_of_shortExact hcofinal j q hj hq hseq Q.isSmooth).mp hQadm
        have hR := map_socle_eq θ A'
        let AS := subrepresentationTwistingEquiv θ R A' hR
        let AC := quotientTwistingEquiv θ R A' hR
        have hT := twistedDistribution_shortExact μ hU hQadm hC j q hj hq hseq
          AS.toLinearMap A'.toLinearMap AC.toLinearMap rfl rfl
        rw [hT]
        apply L.add_mem
        · have hUfin : U.HasFiniteLength := hfQ.of_injective
            (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ j) hj
          let := (isFiniteLength_iff_isNoetherian_isArtinian.mp hUfin).1
          let : IsSemisimpleModule (MonoidAlgebra ℂ G) U.representation.asModule :=
            isSemisimpleModule_socle Q.representation
          refine twistedDistribution_mem_of_semisimple μ θ L U hU AS.toIntertwiningMap ?_
          rintro D hD hirr ⟨i, hi⟩ AD
          apply hspan D hD hirr _ AD
          exact CuspidalProductContragredient.isSubquotient_of_injective_of_surjective
            (i ≫ Q.subtype R) (hj.comp hi) (SmoothRep.ofHom p) hp
        · let p' := q.comp p
          have hlt : S < p'.ker := by
            rw [← hker]
            have hle : p.ker ≤ p'.ker := by
              intro x hx
              change p x = 0 at hx
              change q (p x) = 0
              rw [hx, map_zero]
            refine lt_of_le_of_ne hle ?_
            intro heq
            have hRne : R.toSubmodule ≠ ⊥ := fun h =>
              socle_ne_bot_of_artinian (ρ := Q.representation)
                (Subrepresentation.toSubmodule_injective h)
            obtain ⟨v, hv, hvne⟩ := R.toSubmodule.ne_bot_iff.mp hRne
            obtain ⟨x, hx⟩ := hp v
            have hxp : x ∈ p'.ker := by
              change R.toSubmodule.mkQ (p x) = 0
              rw [hx]
              exact (Submodule.Quotient.mk_eq_zero (p := R.toSubmodule)).mpr hv
            have hx0 : p x = 0 := show x ∈ p.ker from heq ▸ hxp
            exact hvne (hx.symm.trans hx0)
          exact ih p'.ker hlt C hC p' (hq.comp hp) rfl AC
  exact hQ _ B hB (Representation.IntertwiningMap.id B.representation) Function.surjective_id rfl A

end FiniteLength

end Langlands.BaseChange
