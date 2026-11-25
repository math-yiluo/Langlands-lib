import Langlands.GaloisCohomology.Global.Selmer.LocalConditions

/-!
# Selmer groups

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)`, `M` a smooth `G_S`-module and `L` a family of local conditions for `M`
(`LocalConditions`). The Selmer group of `L` is the subgroup

`Sel_L(M) = {x ∈ H¹(G_S, M) | loc_v(x) ∈ L_v for v ∈ S and loc_w(x) ∈ L_w for w real}`

of `H¹(G_S, M)`, the preimage of `L.toLocalTerm ⊆ P¹(M)` under the localization
`PoitouTate.loc ι M 1` of the Poitou–Tate sequence (`LocalConditions.selmerGroup`,
`LocalConditions.mem_selmerGroup`). It grows with `L`; for the zero family it is
`Ш¹_S(M)` (`sha ι M 1`, `LocalConditions.selmerGroup_bot`) and for the full family it is
`H¹(G_S, M)` (`LocalConditions.selmerGroup_top`). It is finite when `M` is finite and `S` contains
the places above `#M` (`LocalConditions.finite_selmerGroup`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {ι : PlaceEmbeddings K Ω}
  {M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)} [IsSmoothRep M]

namespace LocalConditions

/-- The Selmer group `Sel_L(M) ⊆ H¹(G_S, M)` of a family of local conditions: the classes whose
localization lies in `L_v` at every `v ∈ S` and in `L_w` at every real place `w`. -/
def selmerGroup (L : LocalConditions ι M) : AddSubgroup (cohomology M 1) :=
  L.toLocalTerm.comap (loc ι M 1)

theorem mem_selmerGroup_iff_loc_mem {L : LocalConditions ι M} {x : cohomology M 1} :
    x ∈ L.selmerGroup ↔ loc ι M 1 x ∈ L.toLocalTerm :=
  Iff.rfl

/-- A class is in the Selmer group exactly when its localizations satisfy the local conditions. -/
theorem mem_selmerGroup {L : LocalConditions ι M} {x : cohomology M 1} :
    x ∈ L.selmerGroup ↔ (∀ v : S, localization ι M v 1 x ∈ L.finite v) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal}, realLocalization ι M w.1 1 x ∈ L.real w := by
  rw [mem_selmerGroup_iff_loc_mem, loc_apply, mem_toLocalTerm]

theorem selmerGroup_mono {L L' : LocalConditions ι M} (h : L ≤ L') :
    L.selmerGroup ≤ L'.selmerGroup :=
  AddSubgroup.comap_mono (toLocalTerm_mono h)

/-- **The Selmer group of the zero conditions is `Ш¹_S(M)`**: the kernel of the localization. -/
theorem selmerGroup_bot : (⊥ : LocalConditions ι M).selmerGroup = sha ι M 1 := by
  ext x
  rw [mem_selmerGroup_iff_loc_mem, toLocalTerm_bot, AddSubgroup.mem_bot, mem_sha_iff_loc_eq_zero]

/-- **The Selmer group of the full conditions is `H¹(G_S, M)`.** -/
theorem selmerGroup_top : (⊤ : LocalConditions ι M).selmerGroup = ⊤ := by
  rw [selmerGroup, toLocalTerm_top, AddSubgroup.comap_top]

/-- `Ш¹_S(M)` lies in every Selmer group. -/
theorem sha_le_selmerGroup (L : LocalConditions ι M) : sha ι M 1 ≤ L.selmerGroup := by
  rw [← selmerGroup_bot]
  exact selmerGroup_mono (bot_le L)

/-- The Selmer group is finite for a finite module whose order is a unit outside `S`. -/
theorem finite_selmerGroup [Finite S] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (L : LocalConditions ι M) : Finite L.selmerGroup := by
  have := finite_cohomology_of_le_two M hS 1 (by norm_num)
  infer_instance

end LocalConditions

end

end Langlands.GaloisCohomology
