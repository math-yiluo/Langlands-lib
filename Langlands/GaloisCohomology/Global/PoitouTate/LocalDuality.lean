import Langlands.GaloisCohomology.Global.PoitouTate.LocalPairings
import Langlands.GaloisCohomology.Local.Duality.Main

/-!
# Local Tate duality at the places of `S`

For a finite place `v` of a number field `K`, the local Tate pairing
`Hʳ(K_v, M) × Hˢ(K_v, M^D) → H²(K_v, K̄_vˣ) → ℚ/ℤ` (`r + s = 2`, `M^D = Hom(M, K̄_vˣ)` the Cartier
dual, the last map the invariant of local class field theory `finiteInvariant`) is `localTatePairing`.
`LocalTateDualityStatement` says that it is perfect on both sides for every finite smooth module, for
number fields in a given universe; it holds in every universe (`localTateDualityStatement`), by local
Tate duality of the Library (`Langlands.GaloisCohomology.Local.tatePairing_bijective` and
`tatePairing_flip_bijective`) for the local field `v.adicCompletion K`.

From it, through `dualToCartier`, the local pairings of the Poitou–Tate sequence at the places of `S`
are perfect (`surjective_localPairing`).
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Statement

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The local Tate pairing `Hʳ(K_v, M) × Hˢ(K_v, Hom(M, K̄_vˣ)) → ℚ/ℤ` at a finite place. -/
def localTatePairing
    (M : Rep.{u} (ULift.{u} ℤ) Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K))
    [IsSmoothRep M] [Finite M] {r s : ℕ} (h : r + s = 2) :
    cohomology M r →+ cohomology (cartierDual (v.adicCompletion K)
      (AlgebraicClosure (v.adicCompletion K)) M) s →+ Langlands.ClassFieldTheory.Local.RationalModIntegers :=
  (AddMonoidHom.compHom (finiteInvariant v).toAddMonoidHom).comp
    (bilinAddHom (cupPairing (cartierPairing _ _ M) h))

theorem localTatePairing_apply
    (M : Rep.{u} (ULift.{u} ℤ) Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K))
    [IsSmoothRep M] [Finite M] {r s : ℕ} (h : r + s = 2) (x : cohomology M r)
    (y : cohomology (cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) M) s) :
    localTatePairing v M h x y = finiteInvariant v (cupPairing (cartierPairing _ _ M) h x y) :=
  rfl

end Statement

/-- **Local Tate duality** at the finite places of the number fields in universe `u`: the local
Tate pairing is perfect on both sides, for every finite smooth module. -/
def LocalTateDualityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (M : Rep.{u} (ULift.{u} ℤ) Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K))
    [IsSmoothRep M] [Finite M] {r s : ℕ} (h : r + s = 2),
    Function.Bijective (localTatePairing v M h) ∧ Function.Bijective (localTatePairing v M h).flip

/-- **Local Tate duality at the finite places** of the number fields of every universe, from the
Library's local duality theorem (`Local.tatePairing_bijective`, `Local.tatePairing_flip_bijective`). -/
theorem localTateDualityStatement : LocalTateDualityStatement.{u} := by
  intro K _ _ v M _ _ r s h
  let _ := Langlands.Global.FiniteCompletion.valuativeRel v
  have := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
  have hM : (Nat.card M : v.adicCompletion K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  exact ⟨Local.tatePairing_bijective _ _ M hM h, Local.tatePairing_flip_bijective _ _ M hM h⟩

section Pairings

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) [NeZero N]
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- The Cartier dual of `M` as a module of a local Galois group at a finite place is smooth. -/
instance isSmoothRep_cartierDual_localModule (v : HeightOneSpectrum (𝓞 K)) :
    IsSmoothRep (cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
      (localModule ι M v)) :=
  isSmoothRep_cartierDual _

omit [NeZero N] in
/-- At a finite place, the local pairing of the Poitou–Tate sequence is the local Tate pairing after
`dualToCartier`. -/
theorem ptLocalPairing_eq_localTatePairing (v : S) {r s : ℕ} (h : r + s = 2)
    (ξ : cohomology (localModule ι M v.1) r)
    (η : cohomology (localModule ι (dualRep (dualizingModule K Ω S N) M) v.1) s) :
    ptLocalPairing (localFamily ι S) (dualizingModule K Ω S N) M (fun v => invariantAt ι S N v) v h
        ξ η =
      QZ.toRationalModIntegers.symm (localTatePairing v.1 (localModule ι M v.1) h ξ
        ((coeffMap (dualToCartier (localizationHom ι S v.1) (dualizingModule K Ω S N)
          (rootsOfUnityLocalHom ι S N v.1) M) s).hom η)) := by
  rw [ptLocalPairing_apply, localTatePairing_apply, cupPairing_dualToCartier]
  rfl

/-- From local Tate duality (`localTateDualityStatement`): at the places of `S` the local pairings of
the Poitou–Tate sequence are surjective. -/
theorem surjective_localPairing
    (hD : Nonempty (dualizingModule K Ω S N ≃+ ZMod N)) (hM : ∀ m : M, N • m = 0) (v : S)
    {r s : ℕ} (h : r + s = 2) :
    Function.Surjective
      (ptLocalPairing (localFamily ι S) (dualizingModule K Ω S N) M (fun v => invariantAt ι S N v) v
        h) := by
  intro χ
  have hL : Nonempty (rootsOfUnityModule (v.1.adicCompletion K)
      (AlgebraicClosure (v.1.adicCompletion K)) N ≃+ ZMod N) :=
    nonempty_addEquiv_rootsOfUnityModule (Nat.cast_ne_zero.2 (NeZero.ne N))
  have hf := bijective_dualToCartier (localizationHom ι S v.1) (dualizingModule K Ω S N)
    (rootsOfUnityLocalHom ι S N v.1) M hL hD (injective_rootsOfUnityLocalHom ι S N v.1) hM
  let e := coeffAddEquiv (repIsoOfBijective _ hf) s
  obtain ⟨ξ, hξ⟩ := (localTateDualityStatement K v.1 (localModule ι M v.1) h).1.2
    (QZ.toRationalModIntegers.toAddMonoidHom.comp (χ.comp e.symm.toAddMonoidHom))
  refine ⟨ξ, AddMonoidHom.ext fun η => ?_⟩
  rw [ptLocalPairing_eq_localTatePairing]
  have h1 := DFunLike.congr_fun hξ (e η)
  change localTatePairing v.1 (localModule ι M v.1) h ξ (e η) =
    QZ.toRationalModIntegers (χ (e.symm (e η))) at h1
  rw [AddEquiv.symm_apply_apply] at h1
  change QZ.toRationalModIntegers.symm (localTatePairing v.1 (localModule ι M v.1) h ξ (e η)) = χ η
  rw [h1, AddEquiv.symm_apply_apply]

end Pairings

end

end Langlands.GaloisCohomology.PoitouTate

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  MonoidalCategory PoitouTate

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]

attribute [local instance 2000] IsSepClosure.isGalois

section LocalPairing

variable (B : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

/-- Postcomposition with `μ_N(K_S) → K̄_vˣ`, from `Hom(B, μ_N)` as a module of `G_{K_v}` to the
Cartier dual of `B` as a module of `G_{K_v}`. -/
def toCartierDualLocal (v : HeightOneSpectrum (𝓞 K)) :
    localModule ι (dual N B) v ⟶
      cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        (localModule ι B v) :=
  Rep.ofHom ⟨LinearMap.llcomp (ULift.{u} ℤ) B (dualizingModule K Ω S N)
      (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)))
      (rootsOfUnityLocalHom ι S N v).hom.toLinearMap, fun σ => LinearMap.ext fun f =>
    LinearMap.ext fun m => by
      have e : localizationHom ι S v σ⁻¹ = (localizationHom ι S v σ)⁻¹ := map_inv _ σ
      have h := Rep.hom_comm_apply (rootsOfUnityLocalHom ι S N v) σ
        (f (B.ρ (localizationHom ι S v σ)⁻¹ m))
      refine h.trans ?_
      change _ = (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))).ρ σ
          ((rootsOfUnityLocalHom ι S N v).hom (f (B.ρ (localizationHom ι S v σ⁻¹) m)))
      rw [e]⟩

omit [NeZero N] in
theorem toCartierDualLocal_hom_apply (v : HeightOneSpectrum (𝓞 K))
    (f : B →ₗ[ULift.{u} ℤ] dualizingModule K Ω S N) (m : B) :
    ((toCartierDualLocal ι N B v).hom f : B →ₗ[ULift.{u} ℤ]
      unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) m =
      (rootsOfUnityLocalHom ι S N v).hom (f m) :=
  rfl

/-- The Cartier dual of a finite module of `G_S`, as a module of a local Galois group, is smooth. -/
instance isSmoothRep_cartierDual_localModule [IsSmoothRep B] [Finite B]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsSmoothRep (cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
      (localModule ι B v)) :=
  isSmoothRep_cartierDual (localModule ι B v)

include hS in
/-- On `H⁰`, postcomposition with `μ_N(K_S) → K̄_vˣ` is bijective for `B` killed by `N`:
`Hom_{G_{K_v}}(B, μ_N(K_S)) = Hom_{G_{K_v}}(B, K̄_vˣ)`. -/
theorem bijective_coeffMap_toCartierDualLocal_zero [IsSmoothRep B] [Finite B]
    (hB : ∀ b : B, N • b = 0)
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Bijective (coeffMap (toCartierDualLocal ι N B v) 0).hom := by
  have hinj := rootsOfUnityLocalHom_injective ι N (S := S) v
  refine ⟨injective_cohomologyMap_zero _ fun f f' h => LinearMap.ext fun m =>
    hinj (LinearMap.congr_fun h m), fun c => ?_⟩
  set a := (zeroIso _).hom.hom c with ha
  have htors : ∀ m : B, N • (a : B →ₗ[ULift.{u} ℤ]
      unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) m = 0 := fun m => by
    rw [← map_nsmul, hB m, map_zero]
  choose pre hpre using fun m => exists_rootsOfUnityLocalHom_eq ι N hS v _ (htors m)
  let f0 : B →+ dualizingModule K Ω S N :=
    { toFun := pre
      map_zero' := hinj (by rw [hpre, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [map_add, hpre, hpre, hpre, map_add]) }
  let f1 : B →ₗ[ULift.{u} ℤ] dualizingModule K Ω S N := (uliftIntLinearEquivAddHom _ _).symm f0
  have hf1 : ∀ m, (rootsOfUnityLocalHom ι S N v).hom (f1 m) =
      (a : B →ₗ[ULift.{u} ℤ] unitsModule (v.adicCompletion K)
        (AlgebraicClosure (v.adicCompletion K))) m := hpre
  have hinv : f1 ∈ (localModule ι (dual N B) v).ρ.invariants := fun σ => LinearMap.ext fun m =>
    hinj (by
      have e : localizationHom ι S v σ⁻¹ = (localizationHom ι S v σ)⁻¹ := map_inv _ σ
      have h := Rep.hom_comm_apply (rootsOfUnityLocalHom ι S N v) σ
        (f1 (B.ρ (localizationHom ι S v σ)⁻¹ m))
      change (rootsOfUnityLocalHom ι S N v).hom ((dualizingModule K Ω S N).ρ
          (localizationHom ι S v σ) (f1 (B.ρ (localizationHom ι S v σ)⁻¹ m))) = _
      refine h.trans ?_
      have h2 := LinearMap.congr_fun (a.2 σ) m
      rw [hf1, hf1, ← h2]
      change _ = (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))).ρ σ
          ((a : B →ₗ[ULift.{u} ℤ] unitsModule (v.adicCompletion K)
            (AlgebraicClosure (v.adicCompletion K))) (B.ρ (localizationHom ι S v σ⁻¹) m))
      rw [e])
  refine ⟨(zeroIso _).inv.hom ⟨f1, hinv⟩, ?_⟩
  have e := congrArg (fun φ => φ.hom ((zeroIso _).inv.hom ⟨f1, hinv⟩))
    (cohomologyMap_zero_comp_zeroIso_hom (toCartierDualLocal ι N B v))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  rw [← zeroIso_inv_hom_apply _ ((coeffMap (toCartierDualLocal ι N B v) 0).hom _), e,
    ← zeroIso_inv_hom_apply _ c]
  congr 1
  refine Subtype.ext (LinearMap.ext fun m => ?_)
  rw [zeroIso_hom_inv_apply]
  exact hf1 m

omit [NeZero N] in
/-- The evaluation pairing with values in `μ_N(K_S)` followed by `μ_N(K_S) → K̄_vˣ` is the Cartier
pairing after `toCartierDualLocal`. -/
theorem ptLocalEval_comp_rootsOfUnityLocalHom [Finite S] (v : S) :
    ptLocalEval (localFamily ι S) (dualizingModule K Ω S N) B v ≫
        rootsOfUnityLocalHom ι S N (v : HeightOneSpectrum (𝓞 K)) =
      (𝟙 _ ⊗ₘ toCartierDualLocal ι N B (v : HeightOneSpectrum (𝓞 K))) ≫
        cartierPairing _ _ (localModule ι B (v : HeightOneSpectrum (𝓞 K))) := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.inductionOn with
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NeZero N] in
/-- The local pairing of the Poitou–Tate sequence at a place of `S` is the local Tate pairing with
the Cartier dual, through `toCartierDualLocal`. -/
theorem ptLocalPairing_eq_tatePairing [Finite S] [IsSmoothRep B] [Finite B] (v : S) {r s : ℕ}
    (h : r + s = 2) (ξ : cohomology (localModule ι B v) r)
    (y : cohomology (localModule ι (dual N B) v) s) :
    letI := Langlands.Global.FiniteCompletion.valuativeRel (v : HeightOneSpectrum (𝓞 K))
    letI := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField
      (v : HeightOneSpectrum (𝓞 K))
    ptLocalPairing (localFamily ι S) (dualizingModule K Ω S N) B (fun v => invariantAt ι S N v) v h
        ξ y =
      QZ.toRationalModIntegers.symm (Local.tatePairing
        ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)
        (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (localModule ι B v) h ξ
          ((coeffMap (toCartierDualLocal ι N B v) s).hom y)) := by
  let := Langlands.Global.FiniteCompletion.valuativeRel (v : HeightOneSpectrum (𝓞 K))
  let := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField (v : HeightOneSpectrum (𝓞 K))
  have hc := cupPairing_cohomologyMap (cartierPairing _ _ (localModule ι B v)) (𝟙 _)
    (toCartierDualLocal ι N B v) h ξ y
  rw [coeffMap_id, ModuleCat.id_apply] at hc
  rw [ptLocalPairing_apply, invariantAt_apply, Local.tatePairing_apply, hc,
    cohomologyMap_cupPairing, ptLocalEval_comp_rootsOfUnityLocalHom]
  rfl

include hS in
/-- **Local duality in the Poitou–Tate sequence.** At a place `v ∈ S`, the local pairing
`H²(K_v, B) → H⁰(K_v, B')^∨` is surjective for `B` killed by `N`. -/
theorem surjective_ptLocalPairing_two [Finite S] [IsSmoothRep B] [Finite B]
    (hB : ∀ b : B, N • b = 0) (v : S) :
    Function.Surjective (ptLocalPairing (localFamily ι S) (dualizingModule K Ω S N) B
      (fun v => invariantAt ι S N v) v (show 2 + 0 = 2 from rfl)) := by
  let := Langlands.Global.FiniteCompletion.valuativeRel (v : HeightOneSpectrum (𝓞 K))
  let := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField (v : HeightOneSpectrum (𝓞 K))
  intro χ
  let Φ := AddEquiv.ofBijective (coeffMap (toCartierDualLocal ι N B v) 0).hom.toAddMonoidHom
    (bijective_coeffMap_toCartierDualLocal_zero ι N B hS hB v)
  have hb := Local.tatePairing_bijective (K := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K)
    (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (localModule ι B v)
    (Nat.cast_ne_zero.2 Nat.card_pos.ne') (show 2 + 0 = 2 from rfl)
  obtain ⟨ξ, hξ⟩ := hb.2 (QZ.toRationalModIntegers.toAddMonoidHom.comp
    (χ.comp Φ.symm.toAddMonoidHom))
  refine ⟨ξ, AddMonoidHom.ext fun y => ?_⟩
  rw [ptLocalPairing_eq_tatePairing ι N B v _ ξ y]
  change QZ.toRationalModIntegers.symm (Local.tatePairing _ _ (localModule ι B v) _ ξ (Φ y)) = χ y
  rw [hξ]
  simp

include hS in
/-- **Local duality in the Poitou–Tate sequence**, both sides: at a place `v ∈ S`, the local
pairing identifies `H²(K_v, B)` with `H⁰(K_v, B')^∨` for `B` killed by `N`. -/
theorem bijective_ptLocalPairing_two [Finite S] [IsSmoothRep B] [Finite B]
    (hB : ∀ b : B, N • b = 0) (v : S) :
    Function.Bijective (ptLocalPairing (localFamily ι S) (dualizingModule K Ω S N) B
      (fun v => invariantAt ι S N v) v (show 2 + 0 = 2 from rfl)) := by
  let := Langlands.Global.FiniteCompletion.valuativeRel (v : HeightOneSpectrum (𝓞 K))
  let := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField (v : HeightOneSpectrum (𝓞 K))
  refine ⟨(injective_iff_map_eq_zero _).2 fun ξ hξ => ?_, surjective_ptLocalPairing_two ι N B hS hB v⟩
  have hb := Local.tatePairing_bijective (K := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K)
    (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) (localModule ι B v)
    (Nat.cast_ne_zero.2 Nat.card_pos.ne') (show 2 + 0 = 2 from rfl)
  refine hb.1 ((AddMonoidHom.ext fun φ => ?_).trans (map_zero _).symm)
  obtain ⟨y, rfl⟩ := (bijective_coeffMap_toCartierDualLocal_zero ι N B hS hB v).2 φ
  have h := ptLocalPairing_eq_tatePairing ι N B v (show 2 + 0 = 2 from rfl) ξ y
  rw [hξ, AddMonoidHom.zero_apply] at h
  exact (QZ.toRationalModIntegers.symm.map_eq_zero_iff.1 h.symm).trans rfl

end LocalPairing

end

end Langlands.GaloisCohomology
