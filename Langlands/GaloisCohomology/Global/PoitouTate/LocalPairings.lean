import Langlands.GaloisCohomology.Global.PoitouTate.Sequence

/-!
# The local pairings of the Poitou–Tate sequence

For a place `w` with local Galois group `Gal(L/F)` (`L` an algebraic closure of the completion `F`),
a homomorphism `φ : Gal(L/F) →ₜ* G_S` and an injective coefficient map `j : μ_N(K_S) → Lˣ`, the
dual `M' = Hom(M, μ_N)` of a `G_S`-module `M` killed by `N`, restricted to `Gal(L/F)`, is the Cartier
dual `Hom(M, Lˣ)` of `M`: post-composition with `j` is an isomorphism (`dualToCartier`,
`bijective_dualToCartier`), and the local pairing of the Poitou–Tate sequence,
`Hʳ(F, M) × Hˢ(F, M') → H²(F, μ_N) → ℚ/ℤ`, is the cup product with the Cartier pairing
`M ⊗ Hom(M, Lˣ) → Lˣ` followed by the invariant (`cupPairing_dualToCartier`).

At the real places this identifies the local pairings with those of `realLocalDuality`, which gives
the surjectivity statements the abstract nine-term sequence needs
(`surjective_realPairing_zero`, `exists_realPairing_two`). At the finite places it reduces the same
statements to local Tate duality for the completions (`localTateDualityStatement` and
`surjective_localPairing` of `Langlands.GaloisCohomology.Global.PoitouTate.LocalDuality`).
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory MonoidalCategory Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain OrderTwo

universe u

noncomputable section



section NormClass

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [Fintype F]

/-- The image of a norm class under a coefficient map is the norm class of the image. -/
theorem coeffMap_normClass {B B' : Rep.{u} k F} [IsSmoothRep B] [IsSmoothRep B'] (f : B ⟶ B')
    (m : B) : (coeffMap f 0).hom (normClass B m) = normClass B' (f.hom m) := by
  obtain ⟨z, hz, hiz⟩ := exists_normClass_cycle B m
  obtain ⟨z', hz', hiz'⟩ := exists_normClass_cycle B' (f.hom m)
  rw [hz, hz']
  change (HomologicalComplex.homologyMap (coeffCochainsMap f) 0).hom _ = _
  rw [homologyMap_homologyπ_apply]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, hiz, hiz']
  apply cochainOf_injective
  funext σ
  change f.hom ((∑ g, B.ρ g) m) = (∑ g, B'.ρ g) (f.hom m)
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ => Rep.hom_comm_apply f g m

end NormClass

section Finite

/-- A finite module stays finite under restriction. -/
instance finite_res {k G H : Type u} [CommRing k] [Monoid G] [Monoid H] (φ : H →* G)
    (M : Rep.{u} k G) [Finite M] : Finite (Rep.res φ M) :=
  inferInstanceAs (Finite M)

end Finite

section Glue

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  {G : Type u} [Group G] [TopologicalSpace G] (φ : Gal(L/F) →ₜ* G)
  (D : Rep.{u} (ULift.{u} ℤ) G) (j : Rep.res (φ : Gal(L/F) →* G) D ⟶ unitsModule F L)
  (M : Rep.{u} (ULift.{u} ℤ) G)

/-- The evaluation `M ⊗ Hom(M, D) → D`, restricted to `Gal(L/F)`. -/
abbrev resEval :
    Rep.res (φ : Gal(L/F) →* G) M ⊗ Rep.res (φ : Gal(L/F) →* G) (dualRep D M) ⟶
      Rep.res (φ : Gal(L/F) →* G) D :=
  (Rep.resFunctor (φ : Gal(L/F) →* G)).map (evalPairing D M)

/-- Post-composition with `j : D → Lˣ`, `Hom(M, D) → Hom(M, Lˣ)`, as a morphism of modules of
`Gal(L/F)`. -/
def dualToCartier :
    Rep.res (φ : Gal(L/F) →* G) (dualRep D M) ⟶ cartierDual F L (Rep.res (φ : Gal(L/F) →* G) M) :=
  Rep.tensorHomEquiv _ _ _ (resEval φ D M ≫ j)

@[simp]
theorem dualToCartier_hom_apply (f : M →ₗ[ULift.{u} ℤ] D) (m : M) :
    (((dualToCartier φ D j M).hom f : M →ₗ[ULift.{u} ℤ] unitsModule F L)) m = j.hom (f m) :=
  rfl

/-- `dualToCartier` is bijective when `M` is killed by `N`, `D ≅ ℤ/N`, `j` is injective and the
`N`-th roots of unity of `L` form a cyclic group of order `N`. -/
theorem bijective_dualToCartier {N : ℕ} [NeZero N]
    (hL : Nonempty (rootsOfUnityModule F L N ≃+ ZMod N)) (hD : Nonempty (D ≃+ ZMod N))
    (hj : Function.Injective j.hom) [Finite M] (hM : ∀ m : M, N • m = 0) :
    Function.Bijective (dualToCartier φ D j M).hom := by
  have : Finite D := finite_of_nonempty_addEquiv hD
  have : Finite (rootsOfUnityModule F L N) := finite_of_nonempty_addEquiv hL
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (dualRep D (dualRep D M)) := finite_dualRep
  have : Finite (Rep.res (φ : Gal(L/F) →* G) M) := inferInstanceAs (Finite M)
  have : Finite ((Rep.ihom (Rep.res (φ : Gal(L/F) →* G) M)).obj (rootsOfUnityModule F L N)) :=
    finite_dualRep (D := rootsOfUnityModule F L N) (M := Rep.res (φ : Gal(L/F) →* G) M)
  set e := cartierDualIsoHomRootsOfUnityOfNsmul F L (Rep.res (φ : Gal(L/F) →* G) M) N hM
  have he : Function.Injective e.inv.hom := fun a b hab => by
    have h := congrArg e.hom.hom hab
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, e.inv_hom_id] at h
  have : Finite (cartierDual F L (Rep.res (φ : Gal(L/F) →* G) M)) := Finite.of_injective _ he
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · intro f f' hff'
    exact LinearMap.ext fun m => hj (LinearMap.congr_fun hff' m)
  · calc _ ≤ Nat.card ((Rep.ihom (Rep.res (φ : Gal(L/F) →* G) M)).obj (rootsOfUnityModule F L N)) :=
          Nat.card_le_card_of_injective _ he
      _ ≤ Nat.card M := card_dualRep_le hL
      _ ≤ Nat.card (dualRep D (dualRep D M)) :=
          Nat.card_le_card_of_injective _ (bijective_toDualDual hD hM).1
      _ ≤ Nat.card (dualRep D M) := card_dualRep_le hD

/-- The evaluation pairing followed by `j` is the Cartier pairing after `dualToCartier`. -/
theorem tensorHom_dualToCartier_cartierPairing :
    (𝟙 (Rep.res (φ : Gal(L/F) →* G) M) ⊗ₘ dualToCartier φ D j M) ≫
        cartierPairing F L (Rep.res (φ : Gal(L/F) →* G) M) =
      resEval φ D M ≫ j := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.inductionOn with
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The cup product with the restricted evaluation, followed by `j`, is the cup product with the
Cartier pairing after `dualToCartier`. -/
theorem cupPairing_dualToCartier [IsTopologicalGroup G] [Algebra.IsIntegral F L] [IsSmoothRep D] [IsSmoothRep M] [Finite M]
    [IsSmoothRep (cartierDual F L (Rep.res (φ : Gal(L/F) →* G) M))] {r s : ℕ} (h : r + s = 2) (ξ : cohomology (Rep.res (φ : Gal(L/F) →* G) M) r)
    (η : cohomology (Rep.res (φ : Gal(L/F) →* G) (dualRep D M)) s) :
    cupPairing (cartierPairing F L (Rep.res (φ : Gal(L/F) →* G) M)) h ξ
        ((coeffMap (dualToCartier φ D j M) s).hom η) =
      (coeffMap j 2).hom (cupPairing (resEval φ D M) h ξ η) := by
  have hc := cupPairing_cohomologyMap (cartierPairing F L (Rep.res (φ : Gal(L/F) →* G) M))
    (𝟙 _) (dualToCartier φ D j M) h ξ η
  rw [coeffMap_id] at hc
  refine (hc.trans ?_)
  rw [tensorHom_dualToCartier_cartierPairing, cohomologyMap_cupPairing]

end Glue

section CohomologyIso

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The additive isomorphism of cohomology groups induced by an isomorphism of modules. -/
def coeffAddEquiv {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] (e : A ≅ B) (m : ℕ) :
    cohomology A m ≃+ cohomology B m where
  toFun := (coeffMap e.hom m).hom
  invFun := (coeffMap e.inv m).hom
  left_inv x := by
    rw [← ModuleCat.comp_apply, ← coeffMap_comp, e.hom_inv_id, coeffMap_id]
    rfl
  right_inv x := by
    rw [← ModuleCat.comp_apply, ← coeffMap_comp, e.inv_hom_id, coeffMap_id]
    rfl
  map_add' := map_add _

theorem coeffAddEquiv_apply {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] (e : A ≅ B)
    (m : ℕ) (x : cohomology A m) : coeffAddEquiv e m x = (coeffMap e.hom m).hom x :=
  rfl

end CohomologyIso

section OrderTwo

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [DiscreteTopology Gal(L/F)]
  [Fintype Gal(L/F)] [Algebra.IsIntegral F L]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : Gal(L/F) →ₜ* G)
  (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D]
  (j : Rep.res (φ : Gal(L/F) →* G) D ⟶ unitsModule F L)
  (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
  (invariant : cohomology (unitsModule F L) 2 →+ QZ)
  {c : Gal(L/F)} (hG : ∀ g : Gal(L/F), g = 1 ∨ g = c) (hc : c ≠ 1)
  (hinv : ∀ (t : unitsModule F L) (ht : (unitsModule F L).ρ c t = t), 2 • t = 0 → t ≠ 0 →
    invariant (cohomologyπ _ 2 (cocycleTwo (unitsModule F L) hG hc t ht)) = QZ.mk (1 / 2))
  (hconj : ∀ ζ : unitsModule F L, (∃ k : ℕ, 0 < k ∧ k • ζ = 0) → (unitsModule F L).ρ c ζ = -ζ)
  (hroots : ∀ k : ℕ, 0 < k → Nonempty (rootsOfUnityModule F L k ≃+ ZMod k))

include hinv hconj hroots in
/-- For a Galois group of order two: every character of `H²(Gal(L/F), M')` is the pairing with a
class of `H⁰(Gal(L/F), M)`. -/
theorem exists_orderTwo_pairing_zero {N : ℕ} [NeZero N] (hD : Nonempty (D ≃+ ZMod N))
    (hj : Function.Injective j.hom) (hM : ∀ m : M, N • m = 0)
    (χ : cohomology (Rep.res (φ : Gal(L/F) →* G) (dualRep D M)) 2 →+ QZ) :
    ∃ ξ : cohomology (Rep.res (φ : Gal(L/F) →* G) M) 0, ∀ η,
      invariant ((coeffMap j 2).hom (cupPairing (resEval φ D M) (show 0 + 2 = 2 from rfl) ξ η)) =
        χ η := by
  have hf := bijective_dualToCartier φ D j M (hroots N (Nat.pos_of_ne_zero (NeZero.ne N))) hD hj hM
  let e := coeffAddEquiv (repIsoOfBijective _ hf) 2
  obtain ⟨x, hx⟩ := (orderTwoLocalDuality invariant hG hc hinv hconj hroots
    (Rep.res (φ : Gal(L/F) →* G) M)).1.1.2 (χ.comp e.symm.toAddMonoidHom)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨x, fun η => ?_⟩
  have e1 := DFunLike.congr_fun hx (e η)
  rw [orderTwoDualityPairingZeroTwo_mk, orderTwoDualityPairing_apply] at e1
  rw [← cupPairing_dualToCartier]
  refine e1.trans ?_
  change χ (e.symm (e η)) = χ η
  rw [AddEquiv.symm_apply_apply]

include hinv hconj hroots in
/-- For a Galois group of order two: every character of `H⁰(Gal(L/F), M')` vanishing on the norm
classes is the pairing with a class of `H²(Gal(L/F), M)`. -/
theorem exists_orderTwo_pairing_two {N : ℕ} [NeZero N] (hD : Nonempty (D ≃+ ZMod N))
    (hj : Function.Injective j.hom) (hM : ∀ m : M, N • m = 0)
    (χ : cohomology (Rep.res (φ : Gal(L/F) →* G) (dualRep D M)) 0 →+ QZ)
    (hχ : ∀ x ∈ normClasses (Rep.res (φ : Gal(L/F) →* G) (dualRep D M)), χ x = 0) :
    ∃ ξ : cohomology (Rep.res (φ : Gal(L/F) →* G) M) 2, ∀ η,
      invariant ((coeffMap j 2).hom (cupPairing (resEval φ D M) (show 2 + 0 = 2 from rfl) ξ η)) =
        χ η := by
  set f := dualToCartier φ D j M
  have hf := bijective_dualToCartier φ D j M (hroots N (Nat.pos_of_ne_zero (NeZero.ne N))) hD hj hM
  let e := coeffAddEquiv (repIsoOfBijective f hf) 0
  let χ' := χ.comp e.symm.toAddMonoidHom
  have hχ' : ∀ y ∈ normClasses (cartierDual F L (Rep.res (φ : Gal(L/F) →* G) M)), χ' y = 0 :=
    fun y hy => by
      obtain ⟨m', rfl⟩ := exists_normClass_eq_of_mem _ y hy
      obtain ⟨m, rfl⟩ := hf.2 m'
      have hem : e (normClass _ m) = normClass _ (f.hom m) := by
        rw [coeffAddEquiv_apply]
        exact coeffMap_normClass f m
      rw [← hem]
      change χ (e.symm (e (normClass _ m))) = 0
      rw [AddEquiv.symm_apply_apply]
      exact hχ _ (normClass_mem_normClasses _ m)
  obtain ⟨ξ, hξ⟩ := (orderTwoLocalDuality invariant hG hc hinv hconj hroots
    (Rep.res (φ : Gal(L/F) →* G) M)).2.2.1.2 (QuotientAddGroup.lift _ χ' hχ')
  refine ⟨ξ, fun η => ?_⟩
  have e1 := DFunLike.congr_fun hξ (Submodule.Quotient.mk (e η))
  rw [orderTwoDualityPairingTwoZero_mk, orderTwoDualityPairing_apply] at e1
  rw [← cupPairing_dualToCartier]
  refine e1.trans ?_
  change χ (e.symm (e η)) = χ η
  rw [AddEquiv.symm_apply_apply]

end OrderTwo

section Embeddings

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ)

/-- The coefficient map `μ_N(K_S) → K̄_vˣ` at a finite place is injective. -/
theorem injective_rootsOfUnityLocalHom (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (rootsOfUnityLocalHom ι S N v).hom := by
  intro a b hab
  have h := congrArg (fun x => ((Additive.toMul x : (AlgebraicClosure (v.adicCompletion K))ˣ) :
    AlgebraicClosure (v.adicCompletion K))) hab
  change ι.finite v _ = ι.finite v _ at h
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact (ι.finite v).toRingHom.injective h

/-- The coefficient map `μ_N(K_S) → K̄_wˣ` at an infinite place is injective. -/
theorem injective_rootsOfUnityRealHom (w : InfinitePlace K) :
    Function.Injective (rootsOfUnityRealHom ι S N w).hom := by
  intro a b hab
  have h := congrArg (fun x => ((Additive.toMul x : (AlgebraicClosure w.Completion)ˣ) :
    AlgebraicClosure w.Completion)) hab
  change ι.infinite w _ = ι.infinite w _ at h
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact (ι.infinite w).toRingHom.injective h

end Embeddings

section RealPlaces

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) [NeZero N]
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- At a real place, every character of `H²(K_w, M')` is the local pairing with a class of
`H⁰(K_w, M)` (local duality at the real places, `realLocalDuality`). -/
theorem surjective_realPairing_zero (hD : Nonempty (dualizingModule K Ω S N ≃+ ZMod N))
    (hM : ∀ m : M, N • m = 0) (w : {w : InfinitePlace K // w.IsReal}) :
    Function.Surjective (ptLocalPairing (realFamily ι S) (dualizingModule K Ω S N) M
      (fun w => realInvariantAt ι S N w.1) w (show 0 + 2 = 2 from rfl)) := fun χ => by
  obtain ⟨ξ, hξ⟩ := exists_orderTwo_pairing_zero (realLocalizationHom ι S w.1)
    (dualizingModule K Ω S N) (rootsOfUnityRealHom ι S N w.1) M (realInvariantQZ w.1)
    (eq_one_or_eq_closureConj w.1 w.2) (closureConj_ne_one w.1 w.2)
    (realInvariantQZ_cocycleTwo w.1 w.2) (closureConj_unitsModule_of_torsion w.1 w.2)
    (nonempty_rootsOfUnityModule_addEquiv_zmod w.1) hD (injective_rootsOfUnityRealHom ι S N w.1)
    hM χ
  exact ⟨ξ, AddMonoidHom.ext fun η => hξ η⟩

/-- At a real place, every character of `H⁰(K_w, M')` vanishing on the norm classes is the local
pairing with a class of `H²(K_w, M)`. -/
theorem exists_realPairing_two (hD : Nonempty (dualizingModule K Ω S N ≃+ ZMod N))
    (hM : ∀ m : M, N • m = 0) (w : {w : InfinitePlace K // w.IsReal})
    (χ : cohomology (realLocalModule ι (dualRep (dualizingModule K Ω S N) M) w.1) 0 →+ QZ)
    (hχ : ∀ x ∈ normClasses (realLocalModule ι (dualRep (dualizingModule K Ω S N) M) w.1),
      χ x = 0) :
    ∃ ξ, ptLocalPairing (realFamily ι S) (dualizingModule K Ω S N) M
      (fun w => realInvariantAt ι S N w.1) w (show 2 + 0 = 2 from rfl) ξ = χ := by
  obtain ⟨ξ, hξ⟩ := exists_orderTwo_pairing_two (realLocalizationHom ι S w.1)
    (dualizingModule K Ω S N) (rootsOfUnityRealHom ι S N w.1) M (realInvariantQZ w.1)
    (eq_one_or_eq_closureConj w.1 w.2) (closureConj_ne_one w.1 w.2)
    (realInvariantQZ_cocycleTwo w.1 w.2) (closureConj_unitsModule_of_torsion w.1 w.2)
    (nonempty_rootsOfUnityModule_addEquiv_zmod w.1) hD (injective_rootsOfUnityRealHom ι S N w.1)
    hM χ hχ
  exact ⟨ξ, AddMonoidHom.ext fun η => hξ η⟩

end RealPlaces

end

end Langlands.GaloisCohomology.PoitouTate

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate

universe u

noncomputable section

section DegreeOne

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- The local pairing `H¹(K_v, M) × H¹(K_v, M') → ℚ/ℤ` at a place `v ∈ S`: the cup product with the
evaluation `M ⊗ M' → μ_N` followed by the local invariant `H²(K_v, μ_N) → ℚ/ℤ`; the pairing of
`PoitouTate.locDual` in degrees `1 + 1` at `v`. -/
def localPairing (v : S) :
    cohomology (localModule ι M v) 1 →+ cohomology (localModule ι (dual N M) v) 1 →+ QZ :=
  ptLocalPairing (localFamily ι S) (dualizingModule K Ω S N) M (fun v => invariantAt ι S N v) v
    (show 1 + 1 = 2 from rfl)

theorem localPairing_eq (v : S) :
    localPairing ι N M v = ptLocalPairing (localFamily ι S) (dualizingModule K Ω S N) M
      (fun v => invariantAt ι S N v) v (show 1 + 1 = 2 from rfl) :=
  rfl

/-- The local pairing `H¹(K_w, M) × H¹(K_w, M') → ℚ/ℤ` at a real place `w`: the cup product with the
evaluation followed by the real invariant `H²(K_w, μ_N) → ℚ/ℤ`; the pairing of `PoitouTate.locDual`
in degrees `1 + 1` at `w`. -/
def realLocalPairing (w : {w : InfinitePlace K // w.IsReal}) :
    cohomology (realLocalModule ι M w.1) 1 →+ cohomology (realLocalModule ι (dual N M) w.1) 1 →+ QZ :=
  ptLocalPairing (realFamily ι S) (dualizingModule K Ω S N) M (fun w => realInvariantAt ι S N w.1)
    w (show 1 + 1 = 2 from rfl)

theorem realLocalPairing_eq (w : {w : InfinitePlace K // w.IsReal}) :
    realLocalPairing ι N M w = ptLocalPairing (realFamily ι S) (dualizingModule K Ω S N) M
      (fun w => realInvariantAt ι S N w.1) w (show 1 + 1 = 2 from rfl) :=
  rfl

variable [Finite S]

/-- The sum of the local pairings in degree one, `P¹(M) × P¹(M') → ℚ/ℤ`. -/
def localTermPairing : LocalTerm ι M 1 →+ LocalTerm ι (dual N M) 1 →+ QZ :=
  letI : Fintype S := Fintype.ofFinite S
  prodPairing (piPairing (localPairing ι N M)) (piPairing (realLocalPairing ι N M))

theorem localTermPairing_apply (ξ : LocalTerm ι M 1) (η : LocalTerm ι (dual N M) 1) :
    localTermPairing ι N M ξ η = letI : Fintype S := Fintype.ofFinite S
      ∑ v, localPairing ι N M v (ξ.1 v) (η.1 v) + ∑ w, realLocalPairing ι N M w (ξ.2 w) (η.2 w) := by
  let _ : Fintype S := Fintype.ofFinite S
  rw [localTermPairing, prodPairing_apply, piPairing_apply, piPairing_apply]

/-- **`locDual` in degrees `1 + 1`** is the sum of the local pairings with the localizations of global
classes of `M'`. -/
theorem locDual_one_apply (ξ : LocalTerm ι M 1) (y : cohomology (dual N M) 1) :
    locDual ι N M (show 1 + 1 = 2 from rfl) ξ y = localTermPairing ι N M ξ (loc ι (dual N M) 1 y) := by
  rw [locDual_apply, localTermPairing_apply]
  rfl

end DegreeOne

end

end Langlands.GaloisCohomology
