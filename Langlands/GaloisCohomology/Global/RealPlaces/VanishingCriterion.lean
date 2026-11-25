import Langlands.GaloisCohomology.Global.PoitouTate.FinitePlaces
import Langlands.GaloisCohomology.Global.PoitouTate.Sequence
import Langlands.GaloisCohomology.Global.RealPlaces.HighDegree
import Langlands.GaloisCohomology.Local.Dimension

/-!
# The vanishing of `Ĥ_cʳ(G_S, M)` in degrees `≥ 4`: criterion and closure properties

**Abstract part.** For a group `G` with families `(φ_v : H_v →ₜ* G)` and `(ψ_w : F_w →ₜ* G)` (the
`F_w` finite), the vanishing of the Tate-modified cohomology with compact support
`Ĥ_cⁿ(G, A) = tateCompactCohomologyRes φ ψ A n` in a fixed degree `n` passes to extensions
(`subsingleton_tateCompactCohomologyRes_of_shortExact`) and to retracts
(`subsingleton_tateCompactCohomologyRes_of_retract`), both of
`Langlands.GaloisCohomology.CompactSupport.TateModified.Duality`; it holds for the zero module
(`PoitouTate.subsingleton_tateCompactCohomologyRes` of the module
`Langlands.GaloisCohomology.Global.PoitouTate.Assembly`).

**For `G_S`.** Let `M` be a smooth `G_S`-module killed by `n ≠ 0`. At the finite places the local
groups have no cohomology in degrees `≥ 3`, so for `r ≥ 3` the exact sequence

`Ĥ_cʳ(G_S, M) → Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M) → Ĥ_cʳ⁺¹(G_S, M) → Hʳ⁺¹(G_S, M)`

shows:

* `subsingleton_compactCohomology_of_surjective_of_injective`: if the localization to the real places is
  surjective in degree `r` and injective in degree `r + 1`, then `Ĥ_cʳ⁺¹(G_S, M) = 0`;
* `injective_realLocalization_of_subsingleton`: if `Ĥ_cʳ(G_S, M) = 0`, the localization to the real
  places is injective in degree `r`;
* `surjective_realLocalization_of_subsingleton`: if `Ĥ_cʳ⁺¹(G_S, M) = 0`, it is surjective in degree
  `r`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open Langlands.GaloisCohomology.PoitouTate

universe u

noncomputable section

section Criterion

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) {S : Set (HeightOneSpectrum (𝓞 K))} {n : ℕ} (hn : n ≠ 0)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
  (hM : ∀ m : M, n • m = 0)

include hn hM in
/-- **Criterion for the vanishing of `Ĥ_cʳ⁺¹(G_S, M)`**, `r ≥ 3`: the localization to the real places is
surjective in degree `r` and injective in degree `r + 1`. -/
theorem subsingleton_compactCohomology_of_surjective_of_injective {r : ℕ} (hr : 3 ≤ r)
    (hs : Function.Surjective fun (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 r x)
    (hi : Function.Injective fun (x : cohomology M (r + 1))
      (w : {w : InfinitePlace K // w.IsReal}) => realLocalization ι M w.1 (r + 1) x) :
    Subsingleton (compactCohomology ι M (r + 1)) := by
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  refine ⟨fun x x' => ?_⟩
  suffices h : ∀ x : compactCohomology ι M (p + 1 + 1), x = 0 from (h x).trans (h x').symm
  intro x
  -- The image of `x` in `Hʳ⁺¹(G_S, M)` vanishes at the real places, hence vanishes.
  have hy : (ptTToGlobal (localFamily ι S) (realFamily ι S) M (p + 1 + 1)).hom x = 0 := by
    have hloc := ((ptTExact_global (localFamily ι S) (realFamily ι S) M (p + 1))
      ((ptTToGlobal (localFamily ι S) (realFamily ι S) M (p + 1 + 1)).hom x)).2 ⟨x, rfl⟩
    refine hi (funext fun w => ?_)
    show realLocalization ι M w.1 _ _ = realLocalization ι M w.1 _ 0
    rw [map_zero]
    exact congrFun (congrArg Prod.snd hloc) w
  obtain ⟨ξ, rfl⟩ := ((ptTExact_compact (localFamily ι S) (realFamily ι S) M (p + 1)) x).1 hy
  -- The local class comes from a global class: surjectivity at the real places in degree `r ≥ 3`
  -- and vanishing at the finite places.
  obtain ⟨z, hz⟩ := hs ξ.2
  have hξ : (ptTGlobalToLocal (localFamily ι S) (realFamily ι S) M (p + 1)).hom z = ξ := by
    rw [ptTGlobalToLocal_apply]
    refine Prod.ext (funext fun v => ?_) (funext fun w => congrFun hz w)
    have := subsingleton_cohomology_localModule_of_three_le ι S v.1 hn M hM (r := p + 1)
      (by omega)
    exact Subsingleton.elim _ _
  rw [← hξ]
  exact ((ptTExact_local (localFamily ι S) (realFamily ι S) M p)
    ((ptTGlobalToLocal (localFamily ι S) (realFamily ι S) M (p + 1)).hom z)).2 ⟨z, rfl⟩

include hn hM in
/-- If `Ĥ_cʳ(G_S, M) = 0` with `r ≥ 3`, the localization to the real places is injective in degree
`r`. -/
theorem injective_realLocalization_of_subsingleton {r : ℕ} (hr : 3 ≤ r)
    (h : Subsingleton (compactCohomology ι M r)) :
    Function.Injective fun (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 r x := by
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  refine (injective_iff_map_eq_zero (AddMonoidHom.mk' (fun (x : cohomology M (p + 1))
    (w : {w : InfinitePlace K // w.IsReal}) => realLocalization ι M w.1 (p + 1) x)
      fun x y => funext fun w => map_add _ x y)).2 fun x hx => ?_
  have hx' : (ptTGlobalToLocal (localFamily ι S) (realFamily ι S) M (p + 1)).hom x = 0 := by
    rw [ptTGlobalToLocal_apply]
    refine Prod.ext (funext fun v => ?_) (funext fun w => congrFun hx w)
    have := subsingleton_cohomology_localModule_of_three_le ι S v.1 hn M hM (r := p + 1)
      (by omega)
    exact Subsingleton.elim _ _
  obtain ⟨y, rfl⟩ := ((ptTExact_global (localFamily ι S) (realFamily ι S) M p) x).1 hx'
  rw [Subsingleton.elim y 0, map_zero]

/-- If `Ĥ_cʳ⁺¹(G_S, M) = 0` with `r ≥ 3`, the localization to the real places is surjective in degree
`r`. -/
theorem surjective_realLocalization_of_subsingleton {r : ℕ} (hr : 3 ≤ r)
    (h : Subsingleton (compactCohomology ι M (r + 1))) :
    Function.Surjective fun (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 r x := by
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  intro t
  have hloc := ((ptTExact_local (localFamily ι S) (realFamily ι S) M p)
    ((fun v => 0, t) : ptTLocal (localFamily ι S) (realFamily ι S) M (p + 1))).1
      (Subsingleton.elim _ _)
  obtain ⟨z, hz⟩ := hloc
  refine ⟨z, funext fun w => ?_⟩
  have e := congrFun (congrArg Prod.snd hz) w
  rw [ptTGlobalToLocal_apply] at e
  exact e

end Criterion

end

end Langlands.GaloisCohomology
