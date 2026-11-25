import Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Basic

/-!
# The base case: the local pairings

At a finite place `v ∈ S` of a number field `K` containing the `n`-th roots of unity, the pairing
`μ_n ⊗ ℤ/n → μ_n → K̄_vˣ` identifies `ℤ/n` with the Cartier dual of `μ_n` (`zmodToCartier`,
`bijective_zmodToCartier`, `tensorHom_zmodToCartier_cartierPairing`). Local Tate duality for `μ_n`
(`localTateDualityStatement`) then shows that the pairings `Hˢ(K_v, μ_n) × Hʳ(K_v, ℤ/n) → ℤ/n`
(`r + s = 2`), cup product with `μ_n ⊗ ℤ/n → μ_n` followed by the local trace, are perfect in the
second variable (`bijective_localTrace_cupPairing`): these are the local hypotheses of the abstract
base case.
-/

namespace Langlands.GaloisCohomology.PoitouTate.Internal

open CategoryTheory MonoidalCategory Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n]
  (v : HeightOneSpectrum (𝓞 K))

/-- `ℤ/n → Hom(μ_n, K̄_vˣ)`, `a ↦ (ζ ↦ ι_v(ζ)^a)`, the adjoint of `μ_n ⊗ ℤ/n → μ_n → K̄_vˣ`. -/
def zmodToCartier :
    localModule ι (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) v ⟶
      cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        (localModule ι (dualizingModule K Ω S n) v) :=
  Rep.tensorHomEquiv _ _ _ (pairingRes (localizationHom ι S v :
      Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →*
        GaloisGroupUnramifiedOutside K Ω S)
    (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n)) ≫
      rootsOfUnityLocalHom ι S n v)

omit [NeZero n] in
theorem zmodToCartier_hom_apply (a : ZMod n) (ζ : dualizingModule K Ω S n) :
    (((zmodToCartier ι S n v).hom (ULift.up a : zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) :
      dualizingModule K Ω S n →ₗ[ULift.{u} ℤ] unitsModule (v.adicCompletion K)
        (AlgebraicClosure (v.adicCompletion K))) ζ) =
      (rootsOfUnityLocalHom ι S n v).hom ((ZMod.cast a : ℤ) • ζ) :=
  rfl

omit [NeZero n] in
/-- The Cartier pairing after `zmodToCartier` is `μ_n ⊗ ℤ/n → μ_n → K̄_vˣ`. -/
theorem tensorHom_zmodToCartier_cartierPairing :
    (𝟙 (localModule ι (dualizingModule K Ω S n) v) ⊗ₘ zmodToCartier ι S n v) ≫
        cartierPairing (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
          (localModule ι (dualizingModule K Ω S n) v) =
      pairingRes (localizationHom ι S v :
        Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →*
          GaloisGroupUnramifiedOutside K Ω S)
        (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n)) ≫
      rootsOfUnityLocalHom ι S n v := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.inductionOn with
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- With the places above `n` in `S`, `zmodToCartier` is bijective. -/
theorem bijective_zmodToCartier
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Function.Bijective (zmodToCartier ι S n v).hom := by
  obtain ⟨e⟩ := nonempty_addEquiv_dualizingModule (Ω := Ω) (S := S) (N := n) hS
  have hL : Nonempty (rootsOfUnityModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
      n ≃+ ZMod n) := nonempty_addEquiv_rootsOfUnityModule (Nat.cast_ne_zero.2 (NeZero.ne n))
  have : Finite (dualizingModule K Ω S n) := Finite.of_equiv _ e.toEquiv.symm
  have : Finite (localModule ι (dualizingModule K Ω S n) v) := inferInstanceAs (Finite (dualizingModule K Ω S n))
  set c := cartierDualIsoHomRootsOfUnityOfNsmul (v.adicCompletion K)
    (AlgebraicClosure (v.adicCompletion K)) (localModule ι (dualizingModule K Ω S n) v) n
    (nsmul_dualizingModule S n)
  have hc : Function.Injective c.inv.hom := fun a b hab => by
    have h := congrArg c.hom.hom hab
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, c.inv_hom_id] at h
  have : Finite ((Rep.ihom (localModule ι (dualizingModule K Ω S n) v)).obj
      (rootsOfUnityModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) n)) :=
    finite_dualRep
  have : Finite (cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
      (localModule ι (dualizingModule K Ω S n) v)) := Finite.of_injective _ hc
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · intro a b hab
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    have h : (rootsOfUnityLocalHom ι S n v).hom ((ZMod.cast a : ℤ) • e.symm 1) =
        (rootsOfUnityLocalHom ι S n v).hom ((ZMod.cast b : ℤ) • e.symm 1) :=
      congrArg (fun F : dualizingModule K Ω S n →ₗ[ULift.{u} ℤ] unitsModule (v.adicCompletion K)
        (AlgebraicClosure (v.adicCompletion K)) => F (e.symm 1)) hab
    have h' := congrArg e (injective_rootsOfUnityLocalHom ι S n v h)
    rw [map_zsmul, map_zsmul, AddEquiv.apply_symm_apply, zsmul_eq_mul, zsmul_eq_mul, mul_one,
      mul_one, ZMod.intCast_cast, ZMod.intCast_cast, ZMod.cast_id'] at h'
    exact congrArg ULift.up h'
  · calc _ ≤ Nat.card ((Rep.ihom (localModule ι (dualizingModule K Ω S n) v)).obj
          (rootsOfUnityModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) n)) :=
          Nat.card_le_card_of_injective _ hc
      _ ≤ Nat.card (localModule ι (dualizingModule K Ω S n) v) := card_dualRep_le hL
      _ = Nat.card (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) := by
          change Nat.card (dualizingModule K Ω S n) = Nat.card (ULift.{u} (ZMod n))
          rw [Nat.card_congr e.toEquiv, Nat.card_ulift]

attribute [local instance] isSmoothRep_res_zmodRep_base in
/-- **The local pairings of the base case.** With `K ⊇ μ_n` and the places above `n` in `S`, the map
`Hʳ(K_v, ℤ/n) → Hom(Hˢ(K_v, μ_n), ℤ/n)` (`r + s = 2`), cup product with `μ_n ⊗ ℤ/n → μ_n` followed by
the local trace, is bijective. -/
theorem bijective_localTrace_cupPairing
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {r s : ℕ} (h : s + r = 2) :
    Function.Bijective fun ξ : cohomology (localModule ι
        (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) v) r =>
      (localTrace ι S n v).comp ((bilinAddHom (cupPairing (pairingRes (localizationHom ι S v :
        Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →*
          GaloisGroupUnramifiedOutside K Ω S)
        (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))) h)).flip ξ) := by
  obtain ⟨e⟩ := nonempty_addEquiv_dualizingModule (Ω := Ω) (S := S) (N := n) hS
  have : Finite (dualizingModule K Ω S n) := Finite.of_equiv _ e.toEquiv.symm
  have : Finite (localModule ι (dualizingModule K Ω S n) v) := inferInstanceAs (Finite (dualizingModule K Ω S n))
  -- Local Tate duality for `μ_n`, in the second variable.
  have hflip := (localTateDualityStatement K v (localModule ι (dualizingModule K Ω S n) v) h).2
  have : IsSmoothRep (cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
      (localModule ι (dualizingModule K Ω S n) v)) := isSmoothRep_cartierDual _
  let f := zmodToCartier ι S n v
  have hf : Function.Bijective (coeffMap f r).hom :=
    (coeffAddEquiv (repIsoOfBijective f (bijective_zmodToCartier ι S n v hS)) r).bijective
  -- The pairing is the local Tate pairing after `zmodToCartier`.
  have key : ∀ (ξ : cohomology (localModule ι
      (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) v) r)
      (y : cohomology (localModule ι (dualizingModule K Ω S n) v) s),
      QZ.toRationalModIntegers (zmodToQZ n (localTrace ι S n v (cupPairing (pairingRes
        (localizationHom ι S v : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →*
          GaloisGroupUnramifiedOutside K Ω S)
        (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))) h y ξ))) =
        localTatePairing v (localModule ι (dualizingModule K Ω S n) v) h y ((coeffMap f r).hom ξ) := by
    intro ξ y
    rw [zmodToQZ_localTrace, invariantAt_apply, AddEquiv.apply_symm_apply, localTatePairing_apply]
    congr 1
    have hc := cupPairing_cohomologyMap (cartierPairing (v.adicCompletion K)
      (AlgebraicClosure (v.adicCompletion K)) (localModule ι (dualizingModule K Ω S n) v))
      (𝟙 _) f h y ξ
    rw [coeffMap_id] at hc
    refine (hc.trans ?_).symm
    rw [tensorHom_zmodToCartier_cartierPairing, cohomologyMap_cupPairing]
  refine ⟨fun ξ ξ' hξ => hf.1 (hflip.1 (AddMonoidHom.ext fun y => ?_)), fun χ => ?_⟩
  · have h1 := congrArg (fun F => QZ.toRationalModIntegers (zmodToQZ n (F y))) hξ
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply] at h1
    change localTatePairing v _ h y _ = localTatePairing v _ h y _
    rw [← key, ← key]
    exact h1
  · obtain ⟨z, hz⟩ := hflip.2 ((QZ.toRationalModIntegers.toAddMonoidHom.comp (zmodToQZ n)).comp χ)
    obtain ⟨ξ, rfl⟩ := hf.2 z
    refine ⟨ξ, AddMonoidHom.ext fun y => zmodToQZ_injective (n := n) (QZ.toRationalModIntegers.injective ?_)⟩
    have h1 := DFunLike.congr_fun hz y
    simp only [AddMonoidHom.flip_apply, AddMonoidHom.comp_apply] at h1 ⊢
    exact (key ξ y).trans h1

end

end Langlands.GaloisCohomology.PoitouTate.Internal
