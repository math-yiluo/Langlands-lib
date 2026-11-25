import Langlands.GaloisCohomology.Global.PoitouTate.Trace

/-!
# The maps of the Poitou–Tate sequence for `G_S`

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)`, `ι : PlaceEmbeddings K Ω`, `N ≥ 1`, `μ_N = μ_N(K_S)` and, for a finite smooth
`G_S`-module `M`, `M' = Hom(M, μ_N)` (`dual`). This file defines the groups and maps of the
nine-term sequence of Poitou and Tate

`0 → H⁰(G_S, M) → P̂⁰(M) → H²(G_S, M')^∨ → H¹(G_S, M) → P¹(M) → H¹(G_S, M')^∨ → H²(G_S, M) → P²(M)
  → H⁰(G_S, M')^∨ → 0`

with `X^∨ = Hom(X, ℚ/ℤ)`:

* `LocalTerm ι M n = Pⁿ(M) = ∏_{v ∈ S} Hⁿ(K_v, M) × ∏_{w real} Hⁿ(K_w, M)` and, in degree `0`,
  `LocalTermHat ι M = P̂⁰(M)`, in which `H⁰(K_w, M)` is replaced by Tate's `Ĥ⁰(K_w, M)` at the real
  places;
* the localizations `loc ι M n` and `locHat ι M`;
* `locDual ι N M h` (`r + s = 2`) and `locDualHat ι N M`: the sum of the local pairings
  `Hʳ(K_v, M) × Hˢ(K_v, M') → H²(K_v, μ_N) → ℚ/ℤ` with the localizations of global classes;
* the cohomology with compact support `compactCohomology ι M n` of `G_S` with respect to the places
  of `S` and the real places, with Tate's `Ĥ⁰` in degree `0` at the real places, and the duality maps
  `compactDualityMap ι N M h : Ĥ_cʳ(G_S, M) → Hˢ(G_S, M')^∨` and
  `dualityMap ι N M h : Hʳ(G_S, M) → Hom(Ĥ_cˢ(G_S, M'), ℤ/N)` (`r + s = 3`), both given by the cup
  product with the evaluation `M ⊗ M' → μ_N` and the trace `Ĥ_c³(G_S, μ_N) → ℤ/N`;
* the connecting maps `connecting ι N M h : Hˢ(G_S, M')^∨ → Hʳ(G_S, M)` (`r + s = 3`): the inverse of
  `compactDualityMap` followed by `Ĥ_cʳ(G_S, M) → Hʳ(G_S, M)`. The definition takes no proof: it is
  `0` when `compactDualityMap` is not bijective, which never happens for `r ≥ 1` by the duality
  theorem;
* the pairing `shaPairing ι N M : Ш¹(M) × Ш²(M') → ℚ/ℤ` of the Tate–Shafarevich groups `sha` of
  `Langlands.GaloisCohomology.Global.Localization`;
* `locDual_apply`: `locDual` is the sum of the local pairings with the localizations, and
  `compactDualityMap_localToCompact`: on the image of the local terms, `compactDualityMap` is
  `locDual`.

All of these are the abstract maps of `Langlands.GaloisCohomology.CompactSupport.TateModified.NineTerm`
for the families `localFamily ι S`, `realFamily ι S`, the dualizing module `μ_N`, the trace `trace`
and the local invariants `invariantAt`, `realInvariantAt` of `Langlands.GaloisCohomology.Global.PoitouTate.Trace`.
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω)

section Terms

variable (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]

/-- A finite module of `G_S` is finite as a module of a local Galois group at a finite place. -/
instance finite_localModule [Finite M] (v : HeightOneSpectrum (𝓞 K)) : Finite (localModule ι M v) :=
  inferInstanceAs (Finite M)

/-- A finite module of `G_S` is finite as a module of a local Galois group at an infinite place. -/
instance finite_realLocalModule [Finite M] (w : InfinitePlace K) :
    Finite (realLocalModule ι M w) :=
  inferInstanceAs (Finite M)

/-- The local terms `Pⁿ(M) = ∏_{v ∈ S} Hⁿ(K_v, M) × ∏_{w real} Hⁿ(K_w, M)`. -/
abbrev LocalTerm (n : ℕ) : Type u :=
  ptTLocal (localFamily ι S) (realFamily ι S) M n

/-- The local terms in degree `0` with Tate's `Ĥ⁰` at the real places:
`P̂⁰(M) = ∏_{v ∈ S} H⁰(K_v, M) × ∏_{w real} Ĥ⁰(K_w, M)`. -/
abbrev LocalTermHat : Type u :=
  ptTLocalHat (localFamily ι S) (realFamily ι S) M

/-- The localization `Hⁿ(G_S, M) → Pⁿ(M)`. -/
def loc (n : ℕ) : cohomology M n →+ LocalTerm ι M n :=
  (ptTGlobalToLocal (localFamily ι S) (realFamily ι S) M n).hom.toAddMonoidHom

theorem loc_apply (n : ℕ) (x : cohomology M n) :
    loc ι M n x = (fun v : S => localization ι M v n x,
      fun w : {w : InfinitePlace K // w.IsReal} => realLocalization ι M w.1 n x) :=
  ptTGlobalToLocal_apply _ _ M n x

/-- A class is in the kernel of `loc` exactly when all its localizations vanish. -/
theorem loc_eq_zero_iff {n : ℕ} (x : cohomology M n) :
    loc ι M n x = 0 ↔ (∀ v : S, localization ι M v n x = 0) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, realLocalization ι M w.1 n x = 0 := by
  rw [loc_apply, Prod.ext_iff, funext_iff, funext_iff]
  rfl

/-- The localization in degree `0` with Tate's `Ĥ⁰` at the real places, `H⁰(G_S, M) → P̂⁰(M)`. -/
def locHat : cohomology M 0 →+ LocalTermHat ι M :=
  ptTGlobalToLocalHat (localFamily ι S) (realFamily ι S) M

/-- The quotient map `P⁰(M) → P̂⁰(M)`. -/
def hatMk : LocalTerm ι M 0 →+ LocalTermHat ι M :=
  ptTHatMk (localFamily ι S) (realFamily ι S) M

theorem hatMk_surjective : Function.Surjective (hatMk ι M) :=
  ptTHatMk_surjective _ _ M

theorem locHat_apply (x : cohomology M 0) : locHat ι M x = hatMk ι M (loc ι M 0 x) :=
  rfl

/-- The cohomology `Ĥ_cⁿ(G_S, M)` with compact support with respect to the places of `S` and the
real places, with Tate's `Ĥ⁰` in degree `0` at the real places. -/
abbrev compactCohomology (n : ℕ) : ModuleCat.{u} (ULift.{u} ℤ) :=
  tateCompactCohomologyRes (localFamily ι S) (realFamily ι S) M n

/-- The map `Ĥ_cⁿ(G_S, M) → Hⁿ(G_S, M)`. -/
def compactToGlobal (n : ℕ) : compactCohomology ι M n →+ cohomology M n :=
  (ptTToGlobal (localFamily ι S) (realFamily ι S) M n).hom.toAddMonoidHom

/-- The map `Pⁿ(M) → Ĥ_cⁿ⁺¹(G_S, M)`. -/
def localToCompact (n : ℕ) : LocalTerm ι M n →+ compactCohomology ι M (n + 1) :=
  (ptTLocalToCompact (localFamily ι S) (realFamily ι S) M n).hom.toAddMonoidHom

/-- The map `P̂⁰(M) → Ĥ_c¹(G_S, M)`. -/
def localHatToCompact : LocalTermHat ι M →+ compactCohomology ι M 1 :=
  ptTLocalHatToCompact (localFamily ι S) (realFamily ι S) M

/-- The long exact sequence of cohomology with compact support: exactness at `Hⁿ⁺¹(G_S, M)`. -/
theorem exact_compactToGlobal_loc (n : ℕ) :
    Function.Exact (compactToGlobal ι M (n + 1)) (loc ι M (n + 1)) :=
  ptTExact_global _ _ M n

/-- The long exact sequence of cohomology with compact support: exactness at `Pⁿ⁺¹(M)`. -/
theorem exact_loc_localToCompact (n : ℕ) :
    Function.Exact (loc ι M (n + 1)) (localToCompact ι M (n + 1)) :=
  ptTExact_local _ _ M n

/-- The long exact sequence of cohomology with compact support: exactness at `Ĥ_cⁿ⁺¹(G_S, M)`. -/
theorem exact_localToCompact_compactToGlobal (n : ℕ) :
    Function.Exact (localToCompact ι M n) (compactToGlobal ι M (n + 1)) :=
  ptTExact_compact _ _ M n

/-- The long exact sequence of cohomology with compact support: exactness at `P̂⁰(M)`. -/
theorem exact_locHat_localHatToCompact :
    Function.Exact (locHat ι M) (localHatToCompact ι M) :=
  exact_ptTGlobalToLocalHat_ptTLocalHatToCompact M

/-- The long exact sequence of cohomology with compact support: exactness at `Ĥ_c¹(G_S, M)`. -/
theorem exact_localHatToCompact_compactToGlobal :
    Function.Exact (localHatToCompact ι M) (compactToGlobal ι M 1) :=
  exact_ptTLocalHatToCompact_ptTToGlobal M

/-- `Шⁿ_S(M)` is the kernel of `loc`. -/
theorem mem_sha_iff_loc_eq_zero {n : ℕ} (x : cohomology M n) :
    x ∈ sha ι M n ↔ loc ι M n x = 0 := by
  rw [mem_sha, loc_eq_zero_iff]
  exact ⟨fun h => ⟨fun v => h.1 v.1 v.2, fun w => h.2 w.1 w.2⟩,
    fun h => ⟨fun v hv => h.1 ⟨v, hv⟩, fun w hw => h.2 ⟨w, hw⟩⟩⟩

/-- `Шⁿ_S(M)` is the kernel `ptTSha` of the abstract localization. -/
theorem sha_eq_ptTSha (n : ℕ) :
    sha ι M n = ptTSha (localFamily ι S) (realFamily ι S) M n := by
  ext x
  rw [mem_sha_iff_loc_eq_zero, mem_ptTSha]
  rfl

end Terms

section Dual

variable (N : ℕ) [NeZero N]

variable (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))

/-- The dual `M' = Hom(M, μ_N)` of a module of `G_S`. -/
abbrev dual : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S) :=
  dualRep (dualizingModule K Ω S N) M

variable [IsSmoothRep M] [Finite M]

/-- `M'` is a smooth module of `G_S`. -/
instance isSmoothRep_dual : IsSmoothRep (dual N M) :=
  isSmoothRep_dualRep _ _

/-- `M'` as a module of a local Galois group at a finite place is smooth. -/
instance isSmoothRep_localModule_dual (v : HeightOneSpectrum (𝓞 K)) :
    IsSmoothRep (localModule ι (dualRep (dualizingModule K Ω S N) M) v) :=
  isSmoothRep_res _ _

/-- `M'` as a module of a local Galois group at an infinite place is smooth. -/
instance isSmoothRep_realLocalModule_dual (w : InfinitePlace K) :
    IsSmoothRep (realLocalModule ι (dualRep (dualizingModule K Ω S N) M) w) :=
  isSmoothRep_res _ _

variable [Finite S]

/-- The sum of the local pairings `Hʳ(K_v, M) × Hˢ(K_v, M') → ℚ/ℤ` (`r + s = 2`), at the places of
`S` and at the real places, with the localizations of global classes: `Pʳ(M) → Hˢ(G_S, M')^∨`. -/
def locDual {r s : ℕ} (h : r + s = 2) : LocalTerm ι M r →+ (cohomology (dual N M) s →+ QZ) :=
  letI : Fintype S := Fintype.ofFinite S
  ptTLocalDualMap (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) M
    (fun v => invariantAt ι S N v) (fun w => realInvariantAt ι S N w) h

/-- The sum of the local pairings in degree `0`, through `Ĥ⁰` at the real places:
`P̂⁰(M) → H²(G_S, M')^∨`. -/
def locDualHat : LocalTermHat ι M →+ (cohomology (dual N M) 2 →+ QZ) :=
  letI : Fintype S := Fintype.ofFinite S
  ptTLocalHatDualMap (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) M
    (fun v => invariantAt ι S N v) (fun w => realInvariantAt ι S N w)

omit [NeZero N] in
theorem locDualHat_hatMk (ξ : LocalTerm ι M 0) :
    locDualHat ι N M (hatMk ι M ξ) = locDual ι N M (show 0 + 2 = 2 from rfl) ξ := by
  let _ : Fintype S := Fintype.ofFinite S
  exact ptTLocalHatDualMap_hatMk _ _ _ M _ _ ξ

/-- The duality map `Ĥ_cʳ(G_S, M) → Hˢ(G_S, M')^∨` (`r + s = 3`): cup product with the evaluation
`M ⊗ M' → μ_N`, followed by the trace `Ĥ_c³(G_S, μ_N) → ℤ/N ⊂ ℚ/ℤ`. -/
def compactDualityMap {r s : ℕ} (h : r + s = 3) :
    compactCohomology ι M r →+ (cohomology (dual N M) s →+ QZ) :=
  ptTCompactDualMap (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) M (trace ι S N) h

/-- The duality map `Hʳ(G_S, M) → Hom(Ĥ_cˢ(G_S, M'), ℤ/N)` (`r + s = 3`): cup product with the
evaluation `M' ⊗ M → μ_N`, followed by the trace. -/
def dualityMap {r s : ℕ} (h : r + s = 3) :
    cohomology M r →+ (compactCohomology ι (dual N M) s →+ ZMod N) :=
  tateCompactDualityMap (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) h
    (trace ι S N) M

/-- The connecting map `Hˢ(G_S, M')^∨ → Hʳ(G_S, M)` (`r + s = 3`) of the nine-term sequence: the
inverse of `compactDualityMap` followed by `Ĥ_cʳ(G_S, M) → Hʳ(G_S, M)` (and `0` if
`compactDualityMap` is not bijective). -/
def connecting {r s : ℕ} (h : r + s = 3) : (cohomology (dual N M) s →+ QZ) →+ cohomology M r :=
  ptTDualToGlobal (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) (trace ι S N) M h

/-- When the duality map is bijective, the connecting map is its inverse followed by
`Ĥ_cʳ(G_S, M) → Hʳ(G_S, M)`. -/
theorem connecting_compactDualityMap {r s : ℕ} (h : r + s = 3)
    (hb : Function.Bijective (compactDualityMap ι N M h)) (x : compactCohomology ι M r) :
    connecting ι N M h (compactDualityMap ι N M h x) = compactToGlobal ι M r x := by
  rw [connecting, ptTDualToGlobal_eq _ _ _ _ M h hb]
  change (ptTToGlobal _ _ M r).hom ((AddEquiv.ofBijective _ hb).symm
    ((AddEquiv.ofBijective _ hb) x)) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- The pairing `Ш¹(M) × Ш²(M') → ℚ/ℤ` of the Tate–Shafarevich groups: `x ∈ Ш¹(M)` is lifted to
`Ĥ_c¹(G_S, M)` and paired with `y ∈ Ш²(M')` by `compactDualityMap`. -/
def shaPairing : sha ι M 1 →+ sha ι (dual N M) 2 →+ QZ :=
  ((ptTShaPairing (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) M (trace ι S N)).comp
      (AddSubgroup.inclusion (sha_eq_ptTSha ι M 1).le)).compl₂
    (AddSubgroup.inclusion (sha_eq_ptTSha ι (dual N M) 2).le)

/-- `shaPairing` is `compactDualityMap` on a lift to `Ĥ_c¹(G_S, M)`. -/
theorem shaPairing_compactToGlobal (x : compactCohomology ι M 1) (hx : compactToGlobal ι M 1 x ∈ sha ι M 1)
    (y : sha ι (dual N M) 2) :
    shaPairing ι N M ⟨_, hx⟩ y = compactDualityMap ι N M (show 1 + 2 = 3 from rfl) x y :=
  ptTShaPairing_apply _ _ _ M (trace ι S N) x _

end Dual

end

end Langlands.GaloisCohomology.PoitouTate

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]

section Compact

variable [Finite S] (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
  [Finite M]

/-- On the image of the local terms, the duality map is the sum of the local pairings. -/
theorem compactDualityMap_localToCompact {r s : ℕ} (h : r + s = 2) (h' : r + 1 + s = 3)
    (ξ : LocalTerm ι M r) :
    PoitouTate.compactDualityMap ι N M h' (PoitouTate.localToCompact ι M r ξ) =
      locDual ι N M h ξ := by
  let _ : Fintype S := Fintype.ofFinite S
  refine AddMonoidHom.ext fun y => ?_
  change zmodToQZ N (trace ι S N (tateCompactCupRes (localFamily ι S) (realFamily ι S)
    (evalPairing (dualizingModule K Ω S N) M) h'
      ((ptTLocalToCompact (localFamily ι S) (realFamily ι S) M r).hom ξ) y)) = _
  rw [tateCompactCupRes_ptTLocalToCompact, trace_localToCompact, sumInvariants_apply]
  change _ = ptTLocalDualMap (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) M
    (fun v => invariantAt ι S N v) (fun w => realInvariantAt ι S N w) h ξ y
  rw [ptTLocalDualMap_apply]
  rfl

omit [IsSmoothRep M] [NeZero N] in
/-- `locDual` is the sum of the local pairings with the localizations. -/
theorem locDual_apply [IsSmoothRep M] {r s : ℕ} (h : r + s = 2) (ξ : LocalTerm ι M r)
    (y : cohomology (dual N M) s) :
    locDual ι N M h ξ y = letI : Fintype S := Fintype.ofFinite S
      ∑ v, ptLocalPairing (localFamily ι S) (dualizingModule K Ω S N) M
          (fun v => invariantAt ι S N v) v h (ξ.1 v) (ptRes (localFamily ι S) (dual N M) v s y) +
        ∑ w, ptLocalPairing (realFamily ι S) (dualizingModule K Ω S N) M
          (fun w => realInvariantAt ι S N w) w h (ξ.2 w)
          (ptRes (realFamily ι S) (dual N M) w s y) :=
  letI : Fintype S := Fintype.ofFinite S
  ptTLocalDualMap_apply _ _ _ M _ _ h ξ y

end Compact

end

end Langlands.GaloisCohomology

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section LocalVanishing

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))

/-- At a finite place, a module killed by `n ≠ 0` has no cohomology in degrees `≥ 3`. -/
theorem subsingleton_cohomology_localModule_of_three_le (v : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (hn : n ≠ 0) (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology (localModule ι M v) r) := by
  let _ := Langlands.Global.FiniteCompletion.valuativeRel v
  have := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
  exact Local.subsingleton_cohomology_of_three_le (v.adicCompletion K)
    (AlgebraicClosure (v.adicCompletion K)) (Nat.cast_ne_zero.2 hn) (localModule ι M v)
    (fun m => hM m) hr

end LocalVanishing

end

end Langlands.GaloisCohomology.PoitouTate

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate

universe u

noncomputable section

section FiniteDual

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- `μ_N(K_S)` is finite. -/
instance instFiniteDualizingModule [NeZero N] : Finite (dualizingModule K Ω S N) :=
  inferInstanceAs (Finite (Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S))))

/-- `M' = Hom(M, μ_N)` is finite. -/
instance instFiniteDual [NeZero N] : Finite (PoitouTate.dual N M) :=
  finite_dualRep

end FiniteDual

end

end Langlands.GaloisCohomology
