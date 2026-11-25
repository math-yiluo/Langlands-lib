import Langlands.GaloisCohomology.Global.PoitouTate.OpenSubgroups
import Langlands.GaloisCohomology.Global.PoitouTate.OddDuality
import Langlands.GaloisCohomology.Global.RealPlaces.HighDegree
import Langlands.GaloisCohomology.CompactSupport.TateModified.Coinduced
import Langlands.GaloisCohomology.Field.KummerSequence
import Langlands.GaloisCohomology.Global.PoitouTate.LocalDuality

/-!
# Poitou–Tate duality for even `N`

For `N` even the real places matter, and the duality with the Tate-modified cohomology with
compact support is obtained from the abstract dévissage `TateCompactDualityHypotheses`: the
vanishing of `Ĥ_c⁴(G_S, M)` for finite modules killed by `N`, and the duality for the modules
coinduced from `ℤ/N` on open subgroups `U` of `G_S` fixing `K(i)`. Such a `U` meets the conjugates of
the complex conjugations trivially (`freeOnCosets_of_le`), so `Ĥ_c(G_S, Coind_U ℤ/N)` is `H_c(U, ℤ/N)`
for the Mackey family, and `U` is `G_{S_L}(L)` for its fixed field `L`, which is totally complex
(`isTotallyComplex_of_le`). The duality for `ℤ/N` over `U` is then the duality without real places
for `L` (`FinitePlacesDualityStatement`), transported by `bijective_compactZmodDualityMap_fixingOpenSubgroup`;
the traces differ by a unit because the trace of `G_S` is surjective (`surjective_trace`, from the
local Kummer sequences, `exists_invariantAt_eq`) and corestriction to `Ĥ_c³` is surjective.

## Main results

* `exists_invariantAt_eq`: every element of `(1/N)ℤ/ℤ` is a local invariant of `H²(K_v, μ_N)`.
* `surjective_trace`: the trace `Ĥ_c³(G_S, μ_N) → ℤ/N` is surjective for `N ≠ 1`.
* `exists_eq_mul_of_bijective_zero`: with `compactCupRes_zmodH0Class_of_surjective` of the module
  `Langlands.GaloisCohomology.CompactSupport.BaseCase` (cup product with the class of `a ∈ ℤ/N` in degree
  `0` is multiplication by `a` on `H_c³`, when `∏ H²(local) → H_c³` is onto), every map `H_c³ → ℤ/N` is a
  multiple of the trace when the duality for `ℤ/N` holds in degrees `(0, 3)`.
* `bijective_dualityMap_of_even`: Poitou–Tate duality for `N` even from the vanishing of `Ĥ_c⁴` and
  the duality without real places for the totally complex fields `L ⊆ K_S`.
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory CategoryTheory.Limits MonoidalCategory Langlands.ProfiniteCohomology
  Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section LocalKummer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) [NeZero N]

/-- The local Kummer sequence `0 → μ_N(K_S) → K̄_vˣ → K̄_vˣ → 0` at a finite place `v`, `μ_N(K_S)`
embedded by `ι`. -/
def localKummerSequence (v : HeightOneSpectrum (𝓞 K)) :
    ShortComplex (Rep.{u} (ULift.{u} ℤ)
      Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K)) :=
  ShortComplex.mk (rootsOfUnityLocalHom ι S N v) (N • 𝟙 _) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (N • 𝟙 (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)))).hom
      ((rootsOfUnityLocalHom ι S N v).hom x) = 0
    rw [nsmul_id_hom_apply, ← map_nsmul, nsmul_dualizingModule S N x, map_zero])

theorem localKummerSequence_shortExact
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K)) : (localKummerSequence ι S N v).ShortExact := by
  have hc : CharZero (AlgebraicClosure (v.adicCompletion K)) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure (v.adicCompletion K))).injective
  have hN : ((N : ℕ) : AlgebraicClosure (v.adicCompletion K)) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  refine
    { exact := shortComplex_exact_of_forall_exists _ fun x hx => ?_
      mono_f := (Rep.mono_iff_injective _).2 (injective_rootsOfUnityLocalHom ι S N v)
      epi_g := (Rep.epi_iff_surjective _).2 (nsmul_id_unitsModule_surjective N hN) }
  -- An `N`-th root of unity of `K̄_v` comes from `μ_N(K_S)`, which has `N` elements.
  let j : maximalUnramifiedOutside K Ω S →+* AlgebraicClosure (v.adicCompletion K) :=
    ((ι.finite v).comp (maximalUnramifiedOutside K Ω S).val).toRingHom
  have hx' : (Additive.toMul (α := (AlgebraicClosure (v.adicCompletion K))ˣ) x) ^ N = 1 := by
    have h := (nsmul_id_hom_apply _ N x).symm.trans hx
    exact congrArg (Additive.toMul (α := (AlgebraicClosure (v.adicCompletion K))ˣ)) h
  have hinj : Function.Injective (restrictRootsOfUnity j N) := fun a b hab => by
    apply Subtype.ext
    apply Units.ext
    exact j.injective (congrArg (fun z : rootsOfUnity N (AlgebraicClosure (v.adicCompletion K)) =>
      ((z : (AlgebraicClosure (v.adicCompletion K))ˣ) : AlgebraicClosure (v.adicCompletion K))) hab)
  have hbij : Function.Bijective (restrictRootsOfUnity j N) :=
    hinj.bijective_of_nat_card_le ((card_rootsOfUnity _ N).trans
      (card_rootsOfUnity_maximalUnramifiedOutside N hS).ge)
  obtain ⟨ζ, hζ⟩ := hbij.2 ⟨_, (mem_rootsOfUnity N _).2 hx'⟩
  refine ⟨Additive.ofMul ζ, ?_⟩
  apply Additive.toMul.injective
  exact congrArg Subtype.val hζ

/-- **Local invariants of `μ_N`.** Every element of `QZ` killed by `N` is the invariant of a class in
`H²(K_v, μ_N)`. -/
theorem exists_invariantAt_eq
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K)) (q : QZ) (hq : N • q = 0) :
    ∃ ξ, invariantAt ι S N v ξ = q := by
  have : IsSmoothRep (localKummerSequence ι S N v).X₁ :=
    inferInstanceAs (IsSmoothRep (localModule ι (dualizingModule K Ω S N) v))
  have : IsSmoothRep (localKummerSequence ι S N v).X₂ :=
    inferInstanceAs (IsSmoothRep
      (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))))
  have : IsSmoothRep (localKummerSequence ι S N v).X₃ :=
    inferInstanceAs (IsSmoothRep
      (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))))
  let x : LocalBrauerGroup v := (finiteInvariant v).symm (QZ.toRationalModIntegers q)
  have hx : (coeffMap (localKummerSequence ι S N v).g 2).hom x = 0 := by
    change (coeffMap (N • 𝟙 (unitsModule (v.adicCompletion K)
      (AlgebraicClosure (v.adicCompletion K)))) 2).hom x = 0
    rw [cohomologyMap_nsmul_id_apply, ← map_nsmul, ← map_nsmul, hq, map_zero, map_zero]
  refine (exists_cohomologyMap_f_eq (localKummerSequence_shortExact ι S N hS v) 2 x hx).elim
    fun ξ hξ => ⟨ξ, ?_⟩
  change QZ.toRationalModIntegers.symm (finiteInvariant v
    ((coeffMap (localKummerSequence ι S N v).f 2).hom ξ)) = q
  rw [hξ, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]

/-- **Surjectivity of the trace.** For `N ≠ 1`, the trace `Ĥ_c³(G_S, μ_N) → ℤ/N` is surjective. -/
theorem surjective_trace [Finite S] (hN : N ≠ 1)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Function.Surjective (trace ι S N) := by
  classical
  obtain ⟨v⟩ := nonempty_of_natCast_mem hN hS
  obtain ⟨ξv, hξv⟩ := exists_invariantAt_eq ι S N hS v.1 (zmodToQZ N 1) (by
    rw [← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero])
  let ξ₁ : ∀ w : S, cohomology (localModule ι (dualizingModule K Ω S N) w.1) 2 := Pi.single v ξv
  have hξ₁ : ∀ w, w ≠ v → ξ₁ w = 0 := fun w hw =>
    Pi.single_eq_of_ne (M := fun w : S => cohomology (localModule ι (dualizingModule K Ω S N) w.1) 2)
      hw ξv
  have hξ₁v : ξ₁ v = ξv :=
    Pi.single_eq_same (M := fun w : S => cohomology (localModule ι (dualizingModule K Ω S N) w.1) 2)
      v ξv
  let ξ : ptTLocal (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 2 := (ξ₁, 0)
  have h1 : trace ι S N
      ((ptTLocalToCompact (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) 2).hom ξ) =
        1 := by
    apply zmodToQZ_injective (n := N)
    refine (trace_localToCompact ι S N ξ).trans ?_
    rw [sumInvariants_apply, ← hξv]
    let _ : Fintype S := Fintype.ofFinite S
    have h0 : ∑ w : {w : InfinitePlace K // w.IsReal}, realInvariantAt ι S N w.1 (ξ.2 w) = 0 :=
      Finset.sum_eq_zero fun w _ => map_zero _
    refine (congrArg₂ (· + ·) rfl h0).trans ((add_zero _).trans ?_)
    refine (Finset.sum_eq_single v (fun w _ hw => ?_) (fun h => absurd (Finset.mem_univ v) h)).trans
      ?_
    · show invariantAt ι S N w.1 (ξ₁ w) = 0
      rw [hξ₁ w hw, map_zero]
    · show invariantAt ι S N v.1 (ξ₁ v) = _
      rw [hξ₁v]
  intro z
  refine ⟨z.val • (ptTLocalToCompact (localFamily ι S) (realFamily ι S)
    (dualizingModule K Ω S N) 2).hom ξ, ?_⟩
  rw [map_nsmul, h1, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

end LocalKummer

section ZModDuality

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {n : ℕ} [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D] (hD : ∀ d : D, n • d = 0)

/-- If the duality map for `ℤ/n` is bijective at `(r, s) = (0, 3)` and `∏_v H²(H_v, D) → H_c³(G, D)`
is surjective, every homomorphism `H_c³(G, D) → ℤ/n` is a multiple of the trace. -/
theorem exists_eq_mul_of_bijective_zero (h : 0 + 3 = 3)
    (hsurj : Function.Surjective
      (GaloisCohomology.localToCompact φ D (fun v => Rep.res (φ v : H v →* G) D) (fun _ => 𝟙 _) 2).hom)
    (T : compactSupportCohomologyRes φ D 3 →+ ZMod n)
    (hb : Function.Bijective (compactZmodDualityMap φ D hD T h))
    (χ : compactSupportCohomologyRes φ D 3 →+ ZMod n) : ∃ c : ZMod n, ∀ y, χ y = c * T y := by
  refine (hb.2 χ).elim fun x hx => (zmodH0Class_surjective (H := G) (n := n) x).elim
    fun a ha => ⟨a, fun y => ?_⟩
  rw [← hx, ← ha, compactZmodDualityMap_apply, compactCupRes_zmodH0Class_of_surjective φ D hD hsurj,
    map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

end ZModDuality

section Imaginary

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))
  {i : Ω} (hi : i ^ 2 = -1) (hiS : i ∈ maximalUnramifiedOutside K Ω S)
  {L₀ : IntermediateField K Ω} [NumberField L₀]
  (hL₀ : ∀ x : L₀, algebraMap L₀ Ω x ∈ maximalUnramifiedOutside K Ω S)
  (hL₀i : L₀ = IntermediateField.adjoin K {i})

include hi in
/-- The conjugates of the complex conjugations send `i` to `-i`. -/
theorem conj_realLocalizationHom_closureConj_apply (x : GaloisGroupUnramifiedOutside K Ω S)
    (w : InfinitePlace K) (hw : w.IsReal) :
    (x * realLocalizationHom ι S w (closureConj w hw) * x⁻¹) ⟨i, hiS⟩ = -⟨i, hiS⟩ := by
  have hc := realLocalizationHom_closureConj_apply S ι hi hiS w hw
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
  have e : x (x⁻¹ ⟨i, hiS⟩) = ⟨i, hiS⟩ := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  rcases apply_sqrt_neg_one S hi hiS x⁻¹ with h | h
  · rw [h] at e
    rw [h, hc, map_neg, e]
  · rw [h, map_neg] at e
    rw [h, map_neg, hc, neg_neg, neg_eq_iff_eq_neg.1 e]

include hiS hL₀i in
/-- The elements of the subgroup fixing `K(i)` fix `i`. -/
theorem apply_sqrt_neg_one_of_mem (σ : GaloisGroupUnramifiedOutside K Ω S)
    (hσ : σ ∈ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀) :
    σ ⟨i, hiS⟩ = ⟨i, hiS⟩ := by
  have hiL : i ∈ L₀ := hL₀i ▸ IntermediateField.mem_adjoin_simple_self K i
  have h1 := (GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff S hL₀ σ).1 hσ ⟨i, hiL⟩
  have he : embeddingMaximalUnramifiedOutside hL₀ ⟨i, hiL⟩ = ⟨i, hiS⟩ := Subtype.ext rfl
  rwa [he] at h1

include hi hiS hL₀i in
/-- **Open subgroups fixing `K(i)` meet the conjugates of the complex conjugations trivially.** -/
theorem freeOnCosets_of_le (U : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S))
    (hU : U ≤ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀) :
    FreeOnCosets (realFamily ι S) (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) := by
  intro w x h hmem
  rcases eq_one_or_eq_closureConj w.1 w.2 h with h1 | h1
  · exact h1
  · exfalso
    subst h1
    have e1 := apply_sqrt_neg_one_of_mem S hiS hL₀ hL₀i
      (x * realLocalizationHom ι S w.1 (closureConj w.1 w.2) * x⁻¹) (hU hmem)
    have e2 := conj_realLocalizationHom_closureConj_apply ι S hi hiS x w.1 w.2
    change (x * realLocalizationHom ι S w.1 (closureConj w.1 w.2) * x⁻¹) ⟨i, hiS⟩ = _ at e1
    rw [e2] at e1
    have h2 : (2 : Ω) * i = 0 := by
      have := congrArg Subtype.val e1
      change -i = i at this
      linear_combination -this
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
    have hi0 : i = 0 := (mul_eq_zero.1 h2).resolve_left two_ne_zero
    rw [hi0] at hi
    norm_num at hi

include hi hiS hL₀i in
/-- **The fixed fields of the open subgroups fixing `K(i)` are totally complex.** -/
theorem isTotallyComplex_of_le {L : IntermediateField K Ω} [NumberField L]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    (hU : GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL ≤
      GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀) : IsTotallyComplex L := by
  let E : IntermediateField K (maximalUnramifiedOutside K Ω S) :=
    (embeddingMaximalUnramifiedOutside hL).fieldRange
  have hE : E.fixingSubgroup =
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) := by
    ext σ
    change _ ↔ σ ∈ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL
    rw [IntermediateField.mem_fixingSubgroup_iff,
      GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff]
    constructor
    · exact fun h y => h _ ⟨y, rfl⟩
    · rintro h _ ⟨y, rfl⟩
      exact h y
  have hmem : (⟨i, hiS⟩ : maximalUnramifiedOutside K Ω S) ∈
      IntermediateField.fixedField E.fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [hE] at hσ
    exact apply_sqrt_neg_one_of_mem S hiS hL₀ hL₀i σ (hU hσ)
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
  obtain ⟨y, hy⟩ := hmem
  refine Langlands.Global.CMRealization.isTotallyComplex_of_sq_neg (a := -1) (x := y)
    (by norm_num) ?_
  rw [map_neg, map_one]
  apply (embeddingMaximalUnramifiedOutside hL).injective
  rw [map_pow, hy, map_neg, map_one]
  exact Subtype.ext hi

end Imaginary

section Coind

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (N : ℕ) [NeZero N]

omit [Finite S] in
/-- `μ_N(K_S)` is finite. -/
theorem finite_dualizingModule
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Finite (dualizingModule K Ω S N) :=
  (nonempty_addEquiv_dualizingModule hS).elim fun e => Finite.of_equiv _ e.toEquiv.symm

omit [Finite S] [NeZero N] in
/-- The dual `Hom(Coind_U^{G_S}(ℤ/N), μ_N)` is smooth. -/
instance isSmoothRep_dualRep_dualizingModule_coind
    (U : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
    IsSmoothRep (dualRep (dualizingModule K Ω S N)
      (Rep.coind (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRep.{u} (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) N))) :=
  isSmoothRep_dualRep_coind_zmodRep _ U

/-- **Duality for the modules coinduced from `ℤ/N`** on an open subgroup `U` fixing `K(i)`: the fixed
field `L` of `U` is totally complex, and the duality without real places for `L`
(`FinitePlacesDualityStatement`) gives the Tate-modified duality for `Coind_U^{G_S}(ℤ/N)`. -/
theorem bijective_tateCompactDualityMap_coind_fixingOpenSubgroup
    (hfin : FinitePlacesDualityStatement.{u}) (hN : N ≠ 1)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hV : ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
      [Finite M], (∀ m : M, N • m = 0) → Subsingleton (compactCohomology ι M 4))
    {i : Ω} (hi : i ^ 2 = -1) (hiS : i ∈ maximalUnramifiedOutside K Ω S)
    {L₀ : IntermediateField K Ω} [NumberField L₀]
    (hL₀ : ∀ x : L₀, algebraMap L₀ Ω x ∈ maximalUnramifiedOutside K Ω S)
    (hL₀i : L₀ = IntermediateField.adjoin K {i})
    (U : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S))
    {L : IntermediateField K Ω} [NumberField L]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    (hUL : GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL = U)
    (hU : U ≤ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀)
    {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (tateCompactDualityMap (localFamily ι S) (realFamily ι S)
      (dualizingModule K Ω S N) h (trace ι S N)
      (Rep.coind (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (zmodRep.{u} (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) N))) := by
  subst hUL
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hfree := freeOnCosets_of_le ι S hi hiS hL₀ hL₀i _ hU
  have : Finite (dualizingModule K Ω S N) := finite_dualizingModule S N hS
  refine bijective_tateCompactDualityMap_coind (localFamily ι S) (realFamily ι S) _ hfree
    (nsmul_dualizingModule S N) (trace ι S N) h ?_
  -- The field `L` and the data for the duality without real places.
  have : IsSepClosure L Ω :=
    ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  have hLc : IsTotallyComplex L := isTotallyComplex_of_le S hi hiS hL₀ hL₀i hL hU
  have : Finite (finitePlacesAbove L S) := (finite_finitePlacesAbove (Set.toFinite S)).to_subtype
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L), ((N : ℕ) : 𝓞 L) ∈ w.asIdeal →
      w ∈ finitePlacesAbove L S := fun w hw => by
    rw [mem_finitePlacesAbove_iff_under]
    refine hS _ ?_
    change algebraMap (𝓞 K) (𝓞 L) ((N : ℕ) : 𝓞 K) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  let ι₀ : PlaceEmbeddings L Ω := Classical.choice inferInstance
  have h3 := cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le (K := L) (Ω := Ω)
    (finitePlacesAbove L S) (NeZero.ne N) hSL (Or.inr hLc)
    (dualizingModule L Ω (finitePlacesAbove L S) N) (nsmul_dualizingModule _ N) (le_refl 3)
  have hsurjL := surjective_localToCompact_two
    (localFamily (placeEmbeddingsOver hL ι ι₀) (finitePlacesAbove L S))
    (dualizingModule L Ω (finitePlacesAbove L S) N) h3
  have hTsurj : Function.Surjective (tateCoresTrace (localFamily ι S) (realFamily ι S) _ hfree
      (trace ι S N)) :=
    (surjective_trace ι S N hN hS).comp (surjective_tateCompactCores_three (localFamily ι S)
      (realFamily ι S) _ hfree (dualizingModule K Ω S N) (nsmul_dualizingModule S N) hV)
  refine (hfin L Ω (finitePlacesAbove L S) (placeEmbeddingsOver hL ι ι₀) N hSL (Or.inr hLc)).elim
    fun T' hT' => ?_
  have hb : ∀ {r' s' : ℕ} (h' : r' + s' = 3), Function.Bijective (compactZmodDualityMap
      (localFamily (placeEmbeddingsOver hL ι ι₀) (finitePlacesAbove L S))
      (dualizingModule L Ω (finitePlacesAbove L S) N)
      (nsmul_dualizingModule (finitePlacesAbove L S) N) T' h') := fun h' =>
    bijective_compactZmodDualityMap_of_compactDualityMap _ _ _ h' T'
      (hT'.2 (zmodRep.{u} _ N) (nsmul_zmodRep_eq_zero _ N) h')
  have key := bijective_compactZmodDualityMap_fixingOpenSubgroup (hDU := isSmoothRep_res_subtype _ _)
    hL ι ι₀ N h T' (exists_eq_mul_of_bijective_zero _ _ _ (show 0 + 3 = 3 from rfl) hsurjL T' (hb _))
    (hb h) _ hTsurj
  -- The statement of `key` carries the local groups as `(fun v => Gal(K̄_v/K_v)) v`; reducing these
  -- makes it syntactically the goal (the unifier otherwise unfolds the cohomology groups).
  beta_reduce at key
  exact key

/-- **Poitou–Tate duality for even `N`**, from the vanishing of `Ĥ_c⁴(G_S, M)` for the modules killed
by `N` and the duality without real places for the totally complex fields `L ⊆ K_S`. -/
theorem bijective_dualityMap_of_even (hfin : FinitePlacesDualityStatement.{u}) (hN : Even N)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hV : ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
      [Finite M], (∀ m : M, N • m = 0) → Subsingleton (compactCohomology ι M 4))
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, N • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (dualityMap ι N M h) := by
  have hN1 : N ≠ 1 := by
    rintro rfl
    exact Nat.not_even_one hN
  have h2 : ∀ v : HeightOneSpectrum (𝓞 K), ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := fun v hv =>
    hS v (by
      obtain ⟨k, hk⟩ := hN
      rw [hk, ← two_mul, Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hv)
  obtain ⟨i, L₀, _, hL₀, -, hi, hiS, hL₀i⟩ := exists_isTotallyComplex_intermediateField (Ω := Ω) S h2
  have hyp : TateCompactDualityHypotheses (localFamily ι S) (realFamily ι S) N
      (dualizingModule K Ω S N) (trace ι S N)
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀) :=
    { nonempty_addEquiv := nonempty_addEquiv_dualizingModule hS
      subsingleton_four := hV
      bijective_coind := fun U hU {r s} h hs =>
        (GaloisGroupUnramifiedOutside.exists_fixingOpenSubgroup_eq U).elim fun L ⟨_, hL, hUL⟩ =>
          bijective_tateCompactDualityMap_coind_fixingOpenSubgroup ι S N hfin hN1 hS hV hi hiS
            hL₀ hL₀i U hL hUL hU h hs }
  exact hyp.bijective_tateCompactDualityMap M hM h hs

end Coind

end

end Langlands.GaloisCohomology.PoitouTate

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate

universe u

noncomputable section

section RealKummer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) [NeZero N]

/-- The Kummer sequence `0 → μ_N(K_S) → K̄_wˣ → K̄_wˣ → 0` at an infinite place `w`, `μ_N(K_S)`
embedded by `ι`. -/
def realKummerSequence (w : InfinitePlace K) :
    ShortComplex (Rep.{u} (ULift.{u} ℤ) Gal(AlgebraicClosure w.Completion/w.Completion)) :=
  ShortComplex.mk (rootsOfUnityRealHom ι S N w) (N • 𝟙 _) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (N • 𝟙 (unitsModule w.Completion (AlgebraicClosure w.Completion))).hom
      ((rootsOfUnityRealHom ι S N w).hom x) = 0
    rw [nsmul_id_hom_apply, ← map_nsmul, nsmul_dualizingModule S N x, map_zero])

instance isSmoothRep_realKummerSequence_X₁ (w : InfinitePlace K) :
    IsSmoothRep (realKummerSequence ι S N w).X₁ :=
  inferInstanceAs (IsSmoothRep (realLocalModule ι (dualizingModule K Ω S N) w))

instance isSmoothRep_realKummerSequence_X₂ (w : InfinitePlace K) :
    IsSmoothRep (realKummerSequence ι S N w).X₂ :=
  inferInstanceAs (IsSmoothRep (unitsModule w.Completion (AlgebraicClosure w.Completion)))

instance isSmoothRep_realKummerSequence_X₃ (w : InfinitePlace K) :
    IsSmoothRep (realKummerSequence ι S N w).X₃ :=
  inferInstanceAs (IsSmoothRep (unitsModule w.Completion (AlgebraicClosure w.Completion)))

theorem realKummerSequence_shortExact
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (w : InfinitePlace K) : (realKummerSequence ι S N w).ShortExact := by
  have hc : CharZero (AlgebraicClosure w.Completion) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure w.Completion)).injective
  have hN : ((N : ℕ) : AlgebraicClosure w.Completion) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  refine
    { exact := shortComplex_exact_of_forall_exists _ fun x hx => ?_
      mono_f := (Rep.mono_iff_injective _).2 (injective_rootsOfUnityRealHom ι S N w)
      epi_g := (Rep.epi_iff_surjective _).2 (nsmul_id_unitsModule_surjective N hN) }
  -- An `N`-th root of unity of `K̄_w` comes from `μ_N(K_S)`, which has `N` elements.
  let j : maximalUnramifiedOutside K Ω S →+* AlgebraicClosure w.Completion :=
    ((ι.infinite w).comp (maximalUnramifiedOutside K Ω S).val).toRingHom
  have hx' : (Additive.toMul (α := (AlgebraicClosure w.Completion)ˣ) x) ^ N = 1 := by
    have h := (nsmul_id_hom_apply _ N x).symm.trans hx
    exact congrArg (Additive.toMul (α := (AlgebraicClosure w.Completion)ˣ)) h
  have hinj : Function.Injective (restrictRootsOfUnity j N) := fun a b hab => by
    apply Subtype.ext
    apply Units.ext
    exact j.injective (congrArg (fun z : rootsOfUnity N (AlgebraicClosure w.Completion) =>
      ((z : (AlgebraicClosure w.Completion)ˣ) : AlgebraicClosure w.Completion)) hab)
  have hbij : Function.Bijective (restrictRootsOfUnity j N) :=
    hinj.bijective_of_nat_card_le ((card_rootsOfUnity _ N).trans
      (card_rootsOfUnity_maximalUnramifiedOutside N hS).ge)
  obtain ⟨ζ, hζ⟩ := hbij.2 ⟨_, (mem_rootsOfUnity N _).2 hx'⟩
  refine ⟨Additive.ofMul ζ, ?_⟩
  apply Additive.toMul.injective
  exact congrArg Subtype.val hζ

end RealKummer

end

end Langlands.GaloisCohomology
