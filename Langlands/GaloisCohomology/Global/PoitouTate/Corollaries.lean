import Langlands.GaloisCohomology.Global.PoitouTate.DualityProof
import Langlands.GaloisCohomology.Global.PoitouTate.NineTermProof
import Langlands.GaloisCohomology.Global.PoitouTate.ShaProof

/-!
# Consequences of Poitou–Tate duality for `G_S`

* `dualityEquiv`, `compactDualityEquiv`, `shaDualEquiv`: the isomorphisms
  `Hʳ(G_S, M) ≃ Ĥ_cˢ(G_S, M')^∨`, `Ĥ_cʳ(G_S, M) ≃ Hˢ(G_S, M')^∨` and `Ш¹(G_S, M) ≃ Ш²(G_S, M')^∨` given
  by `PoitouTate.IsDuality` and `PoitouTate.IsShaDuality`.
* `mem_range_loc_one_iff`, `mem_range_loc_two_iff`: from the nine-term exact sequence, a family of local
  classes in degree `1` (resp. `2`) comes from a global class if and only if it is orthogonal, for the
  sum of the local pairings, to the localizations of all global classes of `M'` in degree `1`
  (resp. `0`).
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Equivs

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] {ι : PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)} [IsSmoothRep M] [Finite M]

/-- The duality isomorphism `Hʳ(G_S, M) ≃ Ĥ_cˢ(G_S, M')^∨` (`r + s = 3`, `s ≥ 1`). -/
def dualityEquiv (hD : IsDuality ι N M) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    cohomology M r ≃+ (compactCohomology ι (dual N M) s →+ ZMod N) :=
  AddEquiv.ofBijective (dualityMap ι N M h) (hD.bijective_dualityMap h hs)

theorem dualityEquiv_apply (hD : IsDuality ι N M) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s)
    (x : cohomology M r) : dualityEquiv hD h hs x = dualityMap ι N M h x :=
  rfl

/-- The duality isomorphism `Ĥ_cʳ(G_S, M) ≃ Hˢ(G_S, M')^∨` (`r + s = 3`, `r ≥ 1`). -/
def compactDualityEquiv (hD : IsDuality ι N M) {r s : ℕ} (h : r + s = 3) (hr : 1 ≤ r) :
    compactCohomology ι M r ≃+ (cohomology (dual N M) s →+ QZ) :=
  AddEquiv.ofBijective (compactDualityMap ι N M h) (hD.bijective_compactDualityMap h hr)

theorem compactDualityEquiv_apply (hD : IsDuality ι N M) {r s : ℕ} (h : r + s = 3) (hr : 1 ≤ r)
    (x : compactCohomology ι M r) :
    compactDualityEquiv hD h hr x = compactDualityMap ι N M h x :=
  rfl

/-- The duality isomorphism `Ш¹(G_S, M) ≃ Ш²(G_S, M')^∨`. -/
def shaDualEquiv (hD : IsShaDuality ι N M) : sha ι M 1 ≃+ (sha ι (dual N M) 2 →+ QZ) :=
  AddEquiv.ofBijective (shaPairing ι N M) hD.bijective_shaPairing

theorem shaDualEquiv_apply (hD : IsShaDuality ι N M) (x : sha ι M 1) :
    shaDualEquiv hD x = shaPairing ι N M x :=
  rfl

end Equivs

section Annihilator

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- **The image of the localization in degree `1`** is the annihilator of the localizations of
`H¹(G_S, M')` for the sum of the local pairings. -/
theorem mem_range_loc_one_iff (hNT : IsNineTermExact ι N M) (ξ : LocalTerm ι M 1) :
    ξ ∈ Set.range (loc ι M 1) ↔
      ∀ y : cohomology (dual N M) 1, locDual ι N M (show 1 + 1 = 2 from rfl) ξ y = 0 := by
  rw [← hNT.exact_loc_locDual_one ξ]
  exact ⟨fun h y => by rw [h, AddMonoidHom.zero_apply], fun h => AddMonoidHom.ext h⟩

/-- **The image of the localization in degree `2`** is the annihilator of the localizations of
`H⁰(G_S, M')` for the sum of the local pairings. -/
theorem mem_range_loc_two_iff (hNT : IsNineTermExact ι N M) (ξ : LocalTerm ι M 2) :
    ξ ∈ Set.range (loc ι M 2) ↔
      ∀ y : cohomology (dual N M) 0, locDual ι N M (show 2 + 0 = 2 from rfl) ξ y = 0 := by
  rw [← hNT.exact_loc_locDual_two ξ]
  exact ⟨fun h y => by rw [h, AddMonoidHom.zero_apply], fun h => AddMonoidHom.ext h⟩

end Annihilator

end

end Langlands.GaloisCohomology.PoitouTate

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

attribute [local instance 2000] IsSepClosure.isGalois

section Connecting

/-- The connecting map `H¹(G_S, M')^∨ → H²(G_S, M)` kills the image of `P¹(M)`: on the image of
`localToCompact` the duality map is `locDual`, and `H_c²` maps to `H²` through `H_c² → H²` with
the image of `P¹(M)` in its kernel. -/
theorem connecting_locDual_one (ξ : LocalTerm ι M 1) :
    PoitouTate.connecting ι N M (show 2 + 1 = 3 from rfl)
      (locDual ι N M (show 1 + 1 = 2 from rfl) ξ) = 0 := by
  by_cases hb : Function.Bijective (PoitouTate.compactDualityMap ι N M (show 2 + 1 = 3 from rfl))
  · have h := compactDualityMap_localToCompact ι N M (r := 1) (s := 1) rfl rfl ξ
    change PoitouTate.compactDualityMap ι N M (show 2 + 1 = 3 from rfl)
      (PoitouTate.localToCompact ι M 1 ξ) = _ at h
    rw [← h, PoitouTate.connecting_compactDualityMap ι N M _ hb]
    exact (PoitouTate.exact_localToCompact_compactToGlobal ι M 1 _).2 ⟨ξ, rfl⟩
  · have hb' : ¬ Function.Bijective (ptTCompactDualMap (localFamily ι S) (realFamily ι S)
        (dualizingModule K Ω S N) M (trace ι S N) (show 2 + 1 = 3 from rfl)) := hb
    change ptTDualToGlobal (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N) (trace ι S N)
      M (show 2 + 1 = 3 from rfl) _ = 0
    rw [ptTDualToGlobal, dite_eq_right hb']
    rfl

/-- **The image of the localization in degree one** is the orthogonal, for the sum of the local
pairings, of the image of the localization of `M'` (exactness of the nine-term sequence at
`P¹(M)`). -/
theorem leftOrthogonal_range_loc
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) :
    leftOrthogonal (localTermPairing ι N M) (loc ι (PoitouTate.dual N M) 1).range =
      (loc ι M 1).range := by
  have hNT := poitouTateNineTermStatement K Ω S ι N hS M hM
  ext a
  change (∀ b ∈ (loc ι (PoitouTate.dual N M) 1).range, localTermPairing ι N M a b = 0) ↔
    a ∈ Set.range (loc ι M 1)
  rw [← hNT.exact_loc_locDual_one a]
  constructor
  · intro h
    refine AddMonoidHom.ext fun y => ?_
    rw [locDual_one_apply, AddMonoidHom.zero_apply]
    exact h _ ⟨y, rfl⟩
  · rintro h _ ⟨y, rfl⟩
    rw [← locDual_one_apply, h, AddMonoidHom.zero_apply]

end Connecting

end

end Langlands.GaloisCohomology
