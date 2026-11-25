import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.BaseLocal
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.InducedPlaces
import Langlands.GaloisCohomology.Global.RealPlaces.LocalDuality

/-!
# The infinite places of `L` as a `Gal(L/K)`-set

Let `L ⊆ K_S` be finite Galois over `K` with group `Γ`. For an infinite place `w` of `K`, the place
`w̃_w` of `L` given by the chosen embedding `ι_w` (`infiniteBasePlace`) lies above `w`, and the
infinite places of `L` are `⊔_w Γ/Stab(w̃_w)` as a `Γ`-set (`infinitePlacesEquiv`, from Mathlib's
transitivity of `Γ` on the places above `w`), so that
`d(𝔽_ℓ[∞_L]) = ∑_w d(𝔽_ℓ[Γ/Stab(w̃_w)])` (`toFun_infinitePlaces`). At a complex place the stabilizer
is trivial (`stabilizer_infiniteBasePlace_eq_bot`); at a real place it is `{1, τ_w}` with `τ_w` the
restriction of the complex conjugation at `w` (`mem_stabilizer_infiniteBasePlace_iff`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  Langlands.GaloisCohomology.Local Representation Module

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {L : Type u} [Field L] [NumberField L] [Algebra K L]
  [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) [IsGalois K L]
  (ι : PlaceEmbeddings K Ω)

attribute [local instance 2000] IsSepClosure.isGalois

section Places

/-- The infinite place of `L` above `w` given by the chosen embedding `ι_w`. -/
def infiniteBasePlace (w : InfinitePlace K) : InfinitePlace L :=
  InfinitePlace.mk (complexEmbeddingAt hL ι w 1)

omit [IsGalois K L] in
theorem comap_infiniteBasePlace (w : InfinitePlace K) :
    (infiniteBasePlace hL ι w).comap (algebraMap K L) = w := by
  rw [infiniteBasePlace, InfinitePlace.comap_mk, complexEmbeddingAt_comp_algebraMap,
    InfinitePlace.mk_embedding]

/-- The place `τ • w̃_w` attached to a coset `τ Stab(w̃_w)`. -/
def infinitePlacesFun
    (p : Σ w : InfinitePlace K, (L ≃ₐ[K] L) ⧸ MulAction.stabilizer (L ≃ₐ[K] L)
      (infiniteBasePlace hL ι w)) : InfinitePlace L :=
  Quotient.liftOn' p.2 (fun τ => τ • infiniteBasePlace hL ι p.1) (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab
    have h : (a⁻¹ * b) • infiniteBasePlace hL ι p.1 = infiniteBasePlace hL ι p.1 := hab
    calc a • infiniteBasePlace hL ι p.1 = a • ((a⁻¹ * b) • infiniteBasePlace hL ι p.1) := by rw [h]
      _ = b • infiniteBasePlace hL ι p.1 := by rw [smul_smul, mul_inv_cancel_left])

omit [IsGalois K L] in
theorem infinitePlacesFun_mk (w : InfinitePlace K) (τ : L ≃ₐ[K] L) :
    infinitePlacesFun hL ι ⟨w, QuotientGroup.mk τ⟩ = τ • infiniteBasePlace hL ι w :=
  rfl

theorem comap_infinitePlacesFun
    (p : Σ w : InfinitePlace K, (L ≃ₐ[K] L) ⧸ MulAction.stabilizer (L ≃ₐ[K] L)
      (infiniteBasePlace hL ι w)) :
    (infinitePlacesFun hL ι p).comap (algebraMap K L) = p.1 := by
  obtain ⟨w, q⟩ := p
  induction q using QuotientGroup.induction_on with
  | H τ =>
    rw [infinitePlacesFun_mk]
    have h := InfinitePlace.mem_orbit_iff.1 (MulAction.mem_orbit (infiniteBasePlace hL ι w) τ)
    exact h.symm.trans (comap_infiniteBasePlace hL ι w)

/-- The infinite places of `L` are `⊔_w Gal(L/K)/Stab(w̃_w)`. -/
def infinitePlacesEquiv :
    (Σ w : InfinitePlace K, (L ≃ₐ[K] L) ⧸ MulAction.stabilizer (L ≃ₐ[K] L)
      (infiniteBasePlace hL ι w)) ≃ InfinitePlace L :=
  Equiv.ofBijective (infinitePlacesFun hL ι) (by
    constructor
    · rintro ⟨w, q⟩ ⟨w', q'⟩ h
      have hw : w = w' := (comap_infinitePlacesFun hL ι ⟨w, q⟩).symm.trans
        ((congrArg (fun x : InfinitePlace L => x.comap (algebraMap K L)) h).trans
          (comap_infinitePlacesFun hL ι ⟨w', q'⟩))
      subst hw
      induction q using QuotientGroup.induction_on with
      | H τ =>
      induction q' using QuotientGroup.induction_on with
      | H τ' =>
      simp only [infinitePlacesFun_mk] at h
      congr 1
      rw [QuotientGroup.eq, MulAction.mem_stabilizer_iff, mul_smul, ← h, ← mul_smul, inv_mul_cancel,
        one_smul]
    · intro x
      obtain ⟨τ, hτ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := K)
        (w := infiniteBasePlace hL ι (x.comap (algebraMap K L))) (w' := x)
        (comap_infiniteBasePlace hL ι _)
      exact ⟨⟨x.comap (algebraMap K L), QuotientGroup.mk τ⟩, hτ⟩)

theorem infinitePlacesEquiv_smul (γ : L ≃ₐ[K] L)
    (p : Σ w : InfinitePlace K, (L ≃ₐ[K] L) ⧸ MulAction.stabilizer (L ≃ₐ[K] L)
      (infiniteBasePlace hL ι w)) :
    infinitePlacesEquiv hL ι (γ • p) = γ • infinitePlacesEquiv hL ι p := by
  obtain ⟨w, q⟩ := p
  induction q using QuotientGroup.induction_on with
  | H τ =>
    change infinitePlacesFun hL ι ⟨w, QuotientGroup.mk (γ * τ)⟩ = γ • infinitePlacesFun hL ι ⟨w, _⟩
    rw [infinitePlacesFun_mk, infinitePlacesFun_mk, mul_smul]

/-- **The permutation module of the infinite places.** For every additive function `d`:
`d(𝔽_ℓ[∞_L]) = ∑_w d(𝔽_ℓ[Gal(L/K)/Stab(w̃_w)])`. -/
theorem toFun_infinitePlaces {ℓ : ℕ} [NeZero ℓ] (d : AdditiveFunction.{u} ℓ (L ≃ₐ[K] L)) :
    d.toFun (InfinitePlace L → ZMod ℓ) (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) (InfinitePlace L)) =
      ∑ w : InfinitePlace K, d.toFun ((L ≃ₐ[K] L) ⧸ MulAction.stabilizer (L ≃ₐ[K] L)
          (infiniteBasePlace hL ι w) → ZMod ℓ)
        (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) ((L ≃ₐ[K] L) ⧸ MulAction.stabilizer (L ≃ₐ[K] L)
          (infiniteBasePlace hL ι w))) := by
  rw [← d.toFun_piFamilyRep (InfinitePlace K)
    (fun w => (L ≃ₐ[K] L) ⧸ MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w) → ZMod ℓ)]
  refine d.toFun_congr _ _
    ((LinearEquiv.funCongrLeft (ZMod ℓ) (ZMod ℓ) (infinitePlacesEquiv hL ι)).trans
      (LinearEquiv.piCurry (ZMod ℓ)
        fun (w : InfinitePlace K) (_ : (L ≃ₐ[K] L) ⧸ MulAction.stabilizer (L ≃ₐ[K] L)
          (infiniteBasePlace hL ι w)) => ZMod ℓ))
    fun γ f => ?_
  funext w q
  change f (infinitePlacesEquiv hL ι ⟨w, q⟩ |> fun x => γ⁻¹ • x) =
    f (infinitePlacesEquiv hL ι (γ⁻¹ • ⟨w, q⟩))
  rw [infinitePlacesEquiv_smul]

end Places

section Stabilizers

omit [IsGalois K L] in
/-- At a complex place the stabilizer of the base place is trivial. -/
theorem stabilizer_infiniteBasePlace_eq_bot (w : InfinitePlace K) (hw : w.IsComplex) :
    MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w) = ⊥ := by
  apply InfinitePlace.IsUnramified.stabilizer_eq_bot
  rw [InfinitePlace.isUnramified_iff]
  right
  rw [comap_infiniteBasePlace]
  exact hw

/-- The restriction to `L` of the complex conjugation at a real place `w`. -/
def realConjRestrict (w : InfinitePlace K) (hw : w.IsReal) : L ≃ₐ[K] L :=
  Galois.galRestrict hL (realLocalizationHom ι S w (closureConj w hw))

/-- The restricted complex conjugation is conjugation for the embedding defining `w̃_w`. -/
theorem isConj_realConjRestrict (w : InfinitePlace K) (hw : w.IsReal) :
    ComplexEmbedding.IsConj (complexEmbeddingAt hL ι w 1) (realConjRestrict hL ι w hw) := by
  ext x
  change starRingEnd ℂ (complexEmbeddingAt hL ι w 1 x) =
    complexEmbeddingAt hL ι w 1 (realConjRestrict hL ι w hw x)
  have h1 : ((embeddingMaximalUnramifiedOutside hL (realConjRestrict hL ι w hw x) :
      maximalUnramifiedOutside K Ω S) : Ω) =
      ((realLocalizationHom ι S w (closureConj w hw) (embeddingMaximalUnramifiedOutside hL x) :
        maximalUnramifiedOutside K Ω S) : Ω) := by
    rw [realConjRestrict, Galois.galRestrict_apply]
  rw [complexEmbeddingAt_apply, complexEmbeddingAt_apply, infiniteEmbedding_apply,
    infiniteEmbedding_apply, inv_one, AlgEquiv.one_apply, AlgEquiv.one_apply, h1,
    realLocalizationHom_apply, closureToComplex_closureConj w hw]

/-- At a real place the stabilizer of the base place is `{1, τ_w}`. -/
theorem mem_stabilizer_infiniteBasePlace_iff (w : InfinitePlace K) (hw : w.IsReal) (σ : L ≃ₐ[K] L) :
    σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w) ↔
      σ = 1 ∨ σ = realConjRestrict hL ι w hw := by
  have h := (isConj_realConjRestrict hL ι w hw).coe_stabilizer_mk
  rw [← SetLike.mem_coe]
  change σ ∈ (MulAction.stabilizer (L ≃ₐ[K] L) (InfinitePlace.mk (complexEmbeddingAt hL ι w 1)) :
    Set (L ≃ₐ[K] L)) ↔ _
  rw [h]
  rfl

end Stabilizers

end

end Langlands.GaloisCohomology
