import Langlands.GaloisCohomology.Global.PoitouTate.Hypotheses
import Langlands.GaloisCohomology.Global.PoitouTate.Sequence
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Corollaries
import Langlands.GaloisCohomology.Global.Selmer.Orthogonal

/-!
# The local pairings in degree one

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`N ≥ 1`, `M` a finite smooth module of `G_S = Gal(K_S/K)` and `M' = Hom(M, μ_N)` (`PoitouTate.dual`).
The map `PoitouTate.locDual` of the Poitou–Tate sequence in degrees `1 + 1` is the sum of the local
pairings

* `localPairing ι N M v : H¹(K_v, M) × H¹(K_v, M') → ℚ/ℤ` at the places `v ∈ S`, and
* `realLocalPairing ι N M w : H¹(K_w, M) × H¹(K_w, M') → ℚ/ℤ` at the real places `w`,

both the cup product with the evaluation `M ⊗ M' → μ_N` followed by the local invariant
(`ptLocalPairing` with `PoitouTate.invariantAt`, `PoitouTate.realInvariantAt`), with the
localizations of global classes of `M'`: `locDual ι N M ξ y = localTermPairing ι N M ξ (loc y)`
(`locDual_one_apply`), `localTermPairing` being the sum of all local pairings on
`P¹(M) × P¹(M')`.

When `S` contains the places above `N` and `N` kills `M`, every local pairing is perfect:

* at `v ∈ S` by local Tate duality (`PoitouTate.localTateDualityStatement`, from
  `Langlands.GaloisCohomology.Local.tatePairing_bijective`), the local pairing being the Tate
  pairing with the Cartier dual through the isomorphism `PoitouTate.dualToCartier`
  (`bijective_localPairing`, `bijective_localPairing_flip`);
* at a real place by local duality for `Gal(ℂ/ℝ)` (`realLocalDuality`), through the same
  isomorphism (`bijective_realLocalPairing`, `bijective_realLocalPairing_flip`);

hence so is `localTermPairing` (`bijective_localTermPairing`, `bijective_localTermPairing_flip`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω) (N : ℕ)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

section Perfect

variable [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  (hM : ∀ m : M, N • m = 0)

/-- At a finite place, `M' = Hom(M, μ_N)` is the Cartier dual `Hom(M, K̄_vˣ)` through `dualToCartier`. -/
def dualIsoCartierDual (v : HeightOneSpectrum (𝓞 K)) :
    localModule ι (dual N M) v ≅
      cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) (localModule ι M v) :=
  repIsoOfBijective _ (bijective_dualToCartier (localizationHom ι S v) (dualizingModule K Ω S N)
    (rootsOfUnityLocalHom ι S N v) M
    (nonempty_addEquiv_rootsOfUnityModule (Nat.cast_ne_zero.2 (NeZero.ne N)))
    (nonempty_addEquiv_dualizingModule hS) (injective_rootsOfUnityLocalHom ι S N v) hM)

include hS hM in
/-- **Local duality in degree one at the places of `S`**: `H¹(K_v, M) ≅ H¹(K_v, M')^∨`. -/
theorem bijective_localPairing (v : S) : Function.Bijective (localPairing ι N M v) := by
  let e := coeffAddEquiv (dualIsoCartierDual ι N M hS hM v.1) 1
  have key : ∀ η, (coeffMap (dualToCartier (localizationHom ι S v.1) (dualizingModule K Ω S N)
      (rootsOfUnityLocalHom ι S N v.1) M) 1).hom (e.symm η) = η := e.apply_symm_apply
  refine bijective_of_pairing_eq_addEquiv (localPairing ι N M v)
    (localTatePairing v.1 (localModule ι M v.1) (show 1 + 1 = 2 from rfl)) (AddEquiv.refl _) e.symm
    QZ.toRationalModIntegers.symm (fun ξ η => ?_)
    (localTateDualityStatement K v.1 (localModule ι M v.1) (show 1 + 1 = 2 from rfl)).1
  rw [AddEquiv.refl_apply, localPairing_eq, ptLocalPairing_eq_localTatePairing, key]

include hS hM in
/-- **Local duality in degree one at the places of `S`**, the other side:
`H¹(K_v, M') ≅ H¹(K_v, M)^∨`. -/
theorem bijective_localPairing_flip (v : S) : Function.Bijective (localPairing ι N M v).flip := by
  let e := coeffAddEquiv (dualIsoCartierDual ι N M hS hM v.1) 1
  have key : ∀ η, (coeffMap (dualToCartier (localizationHom ι S v.1) (dualizingModule K Ω S N)
      (rootsOfUnityLocalHom ι S N v.1) M) 1).hom (e.symm η) = η := e.apply_symm_apply
  refine bijective_flip_of_pairing_eq_addEquiv (localPairing ι N M v)
    (localTatePairing v.1 (localModule ι M v.1) (show 1 + 1 = 2 from rfl)) (AddEquiv.refl _) e.symm
    QZ.toRationalModIntegers.symm (fun ξ η => ?_)
    (localTateDualityStatement K v.1 (localModule ι M v.1) (show 1 + 1 = 2 from rfl)).2
  rw [AddEquiv.refl_apply, localPairing_eq, ptLocalPairing_eq_localTatePairing, key]

/-- At a real place, `M' = Hom(M, μ_N)` is the Cartier dual `Hom(M, K̄_wˣ)` through `dualToCartier`. -/
def realDualIsoCartierDual (w : InfinitePlace K) :
    realLocalModule ι (dual N M) w ≅
      cartierDual w.Completion (AlgebraicClosure w.Completion) (realLocalModule ι M w) :=
  repIsoOfBijective _ (bijective_dualToCartier (realLocalizationHom ι S w) (dualizingModule K Ω S N)
    (rootsOfUnityRealHom ι S N w) M
    (nonempty_rootsOfUnityModule_addEquiv_zmod w N (Nat.pos_of_ne_zero (NeZero.ne N)))
    (nonempty_addEquiv_dualizingModule hS) (injective_rootsOfUnityRealHom ι S N w) hM)

omit [NeZero N] in
/-- At a real place, the local pairing is the pairing of `realLocalDuality` after `dualToCartier`. -/
theorem realLocalPairing_eq_orderTwoDualityPairing (w : {w : InfinitePlace K // w.IsReal})
    (ξ : cohomology (realLocalModule ι M w.1) 1)
    (η : cohomology (realLocalModule ι (dual N M) w.1) 1) :
    realLocalPairing ι N M w ξ η = orderTwoDualityPairing (realInvariantQZ w.1)
      (realLocalModule ι M w.1) (show 1 + 1 = 2 from rfl) ξ
        ((coeffMap (dualToCartier (realLocalizationHom ι S w.1) (dualizingModule K Ω S N)
          (rootsOfUnityRealHom ι S N w.1) M) 1).hom η) := by
  rw [realLocalPairing_eq, ptLocalPairing_apply, orderTwoDualityPairing_apply,
    cupPairing_dualToCartier]
  rfl

include hS hM in
/-- **Local duality in degree one at the real places**: `H¹(K_w, M) ≅ H¹(K_w, M')^∨`. -/
theorem bijective_realLocalPairing (w : {w : InfinitePlace K // w.IsReal}) :
    Function.Bijective (realLocalPairing ι N M w) := by
  let e := coeffAddEquiv (realDualIsoCartierDual ι N M hS hM w.1) 1
  have key : ∀ η, (coeffMap (dualToCartier (realLocalizationHom ι S w.1) (dualizingModule K Ω S N)
      (rootsOfUnityRealHom ι S N w.1) M) 1).hom (e.symm η) = η := e.apply_symm_apply
  refine bijective_of_pairing_eq_addEquiv (realLocalPairing ι N M w)
    (orderTwoDualityPairing (realInvariantQZ w.1) (realLocalModule ι M w.1)
      (show 1 + 1 = 2 from rfl)) (AddEquiv.refl _) e.symm (AddEquiv.refl _) (fun ξ η => ?_)
    (realLocalDuality w.1 w.2 (realLocalModule ι M w.1)).2.1.1
  rw [AddEquiv.refl_apply, AddEquiv.refl_apply, realLocalPairing_eq_orderTwoDualityPairing, key]

include hS hM in
/-- **Local duality in degree one at the real places**, the other side:
`H¹(K_w, M') ≅ H¹(K_w, M)^∨`. -/
theorem bijective_realLocalPairing_flip (w : {w : InfinitePlace K // w.IsReal}) :
    Function.Bijective (realLocalPairing ι N M w).flip := by
  let e := coeffAddEquiv (realDualIsoCartierDual ι N M hS hM w.1) 1
  have key : ∀ η, (coeffMap (dualToCartier (realLocalizationHom ι S w.1) (dualizingModule K Ω S N)
      (rootsOfUnityRealHom ι S N w.1) M) 1).hom (e.symm η) = η := e.apply_symm_apply
  refine bijective_flip_of_pairing_eq_addEquiv (realLocalPairing ι N M w)
    (orderTwoDualityPairing (realInvariantQZ w.1) (realLocalModule ι M w.1)
      (show 1 + 1 = 2 from rfl)) (AddEquiv.refl _) e.symm (AddEquiv.refl _) (fun ξ η => ?_)
    (realLocalDuality w.1 w.2 (realLocalModule ι M w.1)).2.1.2
  rw [AddEquiv.refl_apply, AddEquiv.refl_apply, realLocalPairing_eq_orderTwoDualityPairing, key]

variable [Finite S]

omit [NeZero N] in
/-- `P¹(M)` is finite. -/
theorem finite_localTerm_one : Finite (LocalTerm ι M 1) := by
  have := IsSepClosure.isGalois (k := K) (K := Ω)
  have := fun v : S => finite_cohomology_localModule ι M v 1
  have := fun w : {w : InfinitePlace K // w.IsReal} =>
    finite_cohomology_realLocalModule ι M w 1 (by norm_num)
  infer_instance

include hS hM in
/-- **Local duality on `P¹`**: `P¹(M) ≅ P¹(M')^∨` through the sum of the local pairings. -/
theorem bijective_localTermPairing : Function.Bijective (localTermPairing ι N M) := by
  let _ : Fintype S := Fintype.ofFinite S
  exact bijective_prodPairing _ _ (bijective_piPairing _ (bijective_localPairing ι N M hS hM))
    (bijective_piPairing _ (bijective_realLocalPairing ι N M hS hM))

include hS hM in
/-- **Local duality on `P¹`**, the other side: `P¹(M') ≅ P¹(M)^∨`. -/
theorem bijective_localTermPairing_flip : Function.Bijective (localTermPairing ι N M).flip := by
  let _ : Fintype S := Fintype.ofFinite S
  exact bijective_prodPairing_flip _ _
    (bijective_piPairing_flip _ (bijective_localPairing_flip ι N M hS hM))
    (bijective_piPairing_flip _ (bijective_realLocalPairing_flip ι N M hS hM))

end Perfect

end

end Langlands.GaloisCohomology
