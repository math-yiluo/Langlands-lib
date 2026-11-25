import Langlands.GaloisCohomology.Global.PoitouTate.FinitePlaces
import Langlands.GaloisCohomology.Global.Dimension.Proof

/-!
# Poitou–Tate duality for odd `N`

For `N` odd, the real places contribute nothing to the cohomology of modules killed by `N` in
positive degrees: `Gal(ℂ/ℝ)` has order two, so `Hⁿ(K_w, A) = 0` for `n ≥ 1`, and every invariant of
`A` is a norm. Hence forgetting the real places is an isomorphism `Ĥ_cⁿ(G_S, A) ≅ H_cⁿ(G_S, A)` for
`n ≥ 1` (`bijective_tateForget_of_odd`, from `isIso_tateForget`), the trace `trace` is a trace for
the compact support at the finite places composed with this isomorphism (`trace_eq_comp_tateForget`),
and the duality map with the real places is the duality map without them composed with it
(`dualityMap_eq_of_odd`). So Poitou–Tate duality with the real places follows from the duality at
the finite places (`bijective_dualityMap_of_odd`).
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory CategoryTheory.Limits Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain OrderTwo

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))

section RealPlaces

variable {N : ℕ} (hN : Odd N) (A : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
  [IsSmoothRep A] (hA : ∀ a : A, N • a = 0)

include hN hA in
/-- At a real place, a module killed by an odd number has no cohomology in positive degrees. -/
theorem isZero_cohomology_realLocalModule_of_odd (w : {w : InfinitePlace K // w.IsReal}) (n : ℕ) :
    IsZero (cohomology (realLocalModule ι A w.1) (n + 1)) :=
  @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y =>
    (eq_zero_cohomology_closureGalois_of_odd w.1 w.2 (realLocalModule ι A w.1) hN hA
      (Nat.succ_ne_zero n) x).trans
    (eq_zero_cohomology_closureGalois_of_odd w.1 w.2 (realLocalModule ι A w.1) hN hA
      (Nat.succ_ne_zero n) y).symm⟩

omit [IsSmoothRep A] in
include hN hA in
/-- At a real place, every invariant of a module killed by an odd number is a norm. -/
theorem exists_norm_realLocalModule_of_odd (w : {w : InfinitePlace K // w.IsReal}) :
    ∀ x ∈ (realLocalModule ι A w.1).ρ.invariants, ∃ m, (realLocalModule ι A w.1).ρ.norm m = x := by
  intro x hx
  obtain ⟨k, hk⟩ := hN
  refine ⟨(k + 1) • x, ?_⟩
  rw [norm_apply _ (eq_one_or_eq_closureConj w.1 w.2) (closureConj_ne_one w.1 w.2), map_nsmul,
    hx (closureConj w.1 w.2), ← add_nsmul]
  have h : k + 1 + (k + 1) = N + 1 := by omega
  rw [h, add_nsmul, one_nsmul, hA, zero_add]

include hN hA in
/-- For a module killed by an odd number, forgetting the real places is an isomorphism in positive
degrees. -/
theorem bijective_tateForget_of_odd {n : ℕ} (hn : 1 ≤ n) :
    Function.Bijective (forgetReal ι S A n).hom := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := isIso_tateForget (localFamily ι S) (realFamily ι S) A _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _)
    (fun w m => isZero_cohomology_realLocalModule_of_odd ι S hN A hA w m)
    (fun w => exists_norm_realLocalModule_of_odd ι S hN A hA w) n
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

end RealPlaces

section Trace

variable [Finite S] (N : ℕ) [NeZero N] (hN : Odd N)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

omit [Finite S] in
include hN hS in
/-- For odd `N`, `∏ H²(·, μ_N) → Ĥ_c³(G_S, μ_N)` is surjective: `H³(G_S, μ_N) = 0`. -/
theorem surjective_ptTLocalToCompact_two_of_odd :
    Function.Surjective
      (ptTLocalToCompact (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 2).hom := by
  intro z
  have h3 := cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le S (NeZero.ne N) hS
    (Or.inl hN) (dualizingModule K Ω S N) (nsmul_dualizingModule S N) (le_refl 3)
  exact (ptTExact_compact (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 2 z).1
    (Subsingleton.elim _ _)

include hN hS in
/-- For odd `N`, the trace is a trace for the compact support at the finite places, composed with
forgetting the real places. -/
theorem trace_eq_comp_tateForget
    (T : compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S N) 3 →+ ZMod N)
    (hT : IsFiniteTrace ι S N T) :
    trace ι S N = T.comp (forgetReal ι S (dualizingModule K Ω S N) 3).hom.toAddMonoidHom := by
  let _ : Fintype S := Fintype.ofFinite S
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨ξ, rfl⟩ := surjective_ptTLocalToCompact_two_of_odd ι S N hN hS z
  apply zmodToQZ_injective (n := N)
  rw [trace_localToCompact, sumInvariants_apply, AddMonoidHom.comp_apply]
  have hf := hom_apply_hom_apply_eq_of_comp_eq (tateLocalToCompact_tateForget (localFamily ι S)
    (realFamily ι S) (dualizingModule K Ω S N) _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) 2) ξ
  change _ = zmodToQZ N (T ((forgetReal ι S (dualizingModule K Ω S N) 3).hom
    ((ptTLocalToCompact (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 2).hom ξ)))
  rw [hf, hT]
  have h0 : ∑ w : {w : InfinitePlace K // w.IsReal}, realInvariantAt ι S N w.1 (ξ.2 w) = 0 :=
    Finset.sum_eq_zero fun w _ => by
      have h := eq_zero_cohomology_closureGalois_of_odd w.1 w.2
        (realLocalModule ι (dualizingModule K Ω S N) w.1) hN (nsmul_dualizingModule S N)
        two_ne_zero (ξ.2 w)
      rw [h, map_zero]
  refine (congrArg₂ (· + ·) rfl h0).trans ((add_zero _).trans ?_)
  exact Finset.sum_congr rfl fun v _ => rfl

end Trace

section Duality

variable [Finite S] (N : ℕ) [NeZero N] (hN : Odd N)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  (T : compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S N) 3 →+ ZMod N)
  (hT : IsFiniteTrace ι S N T)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

include hN hS hT in
/-- For odd `N`, the duality map with the real places is the duality map at the finite places
composed with forgetting the real places. -/
theorem dualityMap_eq_of_odd {r s : ℕ} (h : r + s = 3) (x : cohomology M r)
    (y : compactCohomology ι (dual N M) s) :
    dualityMap ι N M h x y = GaloisCohomology.compactDualityMap (localFamily ι S)
      (dualizingModule K Ω S N) h T M x ((forgetReal ι S (dual N M) s).hom y) := by
  rw [dualityMap, tateCompactDualityMap_apply, trace_eq_comp_tateForget ι S N hN hS T hT,
    AddMonoidHom.comp_apply, compactDualityMap_apply]
  exact congrArg T (tateForget_tateCompactCupRes (localFamily ι S) (realFamily ι S)
    (dualEvalPairing (dualizingModule K Ω S N) M) _ y x)

include hN hS hT in
/-- **Poitou–Tate duality for odd `N`** with the real places, from the duality at the finite
places. -/
theorem bijective_dualityMap_of_odd
    (hdual : ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective
      (GaloisCohomology.compactDualityMap (localFamily ι S) (dualizingModule K Ω S N) h T M))
    {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (dualityMap ι N M h) := by
  have hM' : ∀ f : dual N M, N • f = 0 := nsmul_dualRep_eq_zero (nsmul_dualizingModule S N)
  have hF := bijective_tateForget_of_odd ι S hN (dual N M) hM' hs
  set F := (forgetReal ι S (dual N M) s).hom.toAddMonoidHom with hFdef
  have hpre : Function.Bijective fun g : compactSupportCohomologyRes (localFamily ι S) (dual N M) s
      →+ ZMod N => g.comp F := by
    let e := AddEquiv.ofBijective F hF
    exact Function.bijective_iff_has_inverse.2 ⟨fun g => g.comp e.symm.toAddMonoidHom,
      fun g => AddMonoidHom.ext fun b => by
        change g (e (e.symm b)) = g b
        rw [e.apply_symm_apply],
      fun g => AddMonoidHom.ext fun b => by
        change g (e.symm (e b)) = g b
        rw [e.symm_apply_apply]⟩
  have heq : ⇑(dualityMap ι N M h) = (fun g => g.comp F) ∘
      ⇑(GaloisCohomology.compactDualityMap (localFamily ι S) (dualizingModule K Ω S N) h T M) :=
    funext fun x => AddMonoidHom.ext fun y => dualityMap_eq_of_odd ι S N hN hS T hT M h x y
  rw [heq]
  exact hpre.comp (hdual h)

end Duality

end

end Langlands.GaloisCohomology.PoitouTate
