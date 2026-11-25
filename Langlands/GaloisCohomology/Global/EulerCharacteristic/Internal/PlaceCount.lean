import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.PlaceOrbits
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.Artin
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.TwistCount
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.DualDimension

/-!
# Additive functions on the permutation modules of places

For a finite group `Γ`, a subgroup `H` and the additive function `d(X) = dim (X ⊗ N)^Γ` of a
representation `N` (over `ULift (ZMod ℓ)`, `Local.AdditiveFunction.invariantsTensorULift`), the
permutation module of `Γ/H` has `d(𝔽_ℓ[Γ/H]) = dim N^H` (`toFun_invariantsTensorULift_quotient`),
and `d(𝔽_ℓ) = dim N^Γ` (`one_invariantsTensorULift`). For a Galois extension `L ⊆ K_S` of `K`, the places of
`L` above `S` are `⊔_{v ∈ S} Γ/D_v` (`placesAboveEquiv`), so
`d(𝔽_ℓ[S_L]) = ∑_{v ∈ S} dim N^{D_v}` (`toFun_finitePlacesAbove`).
-/

namespace Langlands.GaloisCohomology

open Langlands.Galois NumberField IsDedekindDomain Langlands.Global.AdelicFunctoriality
open Representation Module Langlands.GaloisCohomology.Local

universe u

noncomputable section

section Induced

variable {k Γ N : Type*} [Field k] [Group Γ] [AddCommGroup N] [Module k N]
  (σ : Representation k Γ N) (H : Subgroup Γ)

/-- The invariants of the module induced from `H`, `(Γ/H → N)^Γ ≅ N^H`, by evaluation at the trivial
coset. -/
def funRepQuotientInvariantsEquiv :
    (funRep (Γ ⧸ H) σ).invariants ≃ₗ[k] Representation.invariants (σ.comp H.subtype) where
  toFun F := ⟨F.1 (QuotientGroup.mk 1), fun h => by
    have := congrFun (F.2 h) (QuotientGroup.mk 1)
    rw [funRep_apply] at this
    change σ h (F.1 _) = F.1 _
    have hh : ((h : Γ)⁻¹ • (QuotientGroup.mk 1 : Γ ⧸ H)) = QuotientGroup.mk 1 := by
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      simp [h.2]
    rw [hh] at this
    exact this⟩
  invFun n := ⟨fun q => Quotient.liftOn' q (fun γ => σ γ n.1) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab
      have := n.2 ⟨a⁻¹ * b, hab⟩
      change σ (a⁻¹ * b) n.1 = n.1 at this
      change σ a n.1 = σ b n.1
      calc σ a n.1 = σ a (σ (a⁻¹ * b) n.1) := by rw [this]
        _ = σ b n.1 := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]),
    fun γ => funext fun q => by
      induction q using QuotientGroup.induction_on with
      | H δ =>
        rw [funRep_apply, MulAction.Quotient.smul_mk]
        change σ γ (σ (γ⁻¹ * δ) n.1) = σ δ n.1
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]⟩
  map_add' F G := rfl
  map_smul' c F := rfl
  left_inv F := by
    apply Subtype.ext
    funext q
    induction q using QuotientGroup.induction_on with
    | H γ =>
      change σ γ (F.1 (QuotientGroup.mk 1)) = F.1 (QuotientGroup.mk γ)
      have := congrFun (F.2 γ) (QuotientGroup.mk γ)
      rw [funRep_apply, MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel] at this
      exact this
  right_inv n := by
    apply Subtype.ext
    change σ 1 n.1 = n.1
    rw [map_one, Module.End.one_apply]

end Induced

section Twist

variable {Γ : Type u} [Group Γ] [Finite Γ] {ℓ : ℕ} [Fact ℓ.Prime] (hΓ : Nat.Coprime (Nat.card Γ) ℓ)
  {N : Type u} [AddCommGroup N] [Module (ULift.{u} (ZMod ℓ)) N] [Module.Finite (ULift.{u} (ZMod ℓ)) N]
  (σ : Representation (ULift.{u} (ZMod ℓ)) Γ N)

/-- **Induced permutation modules.** `d(𝔽_ℓ[Γ/H]) = dim N^H` for `d(X) = dim (X ⊗ N)^Γ`. -/
theorem toFun_invariantsTensorULift_quotient (H : Subgroup Γ) :
    (AdditiveFunction.invariantsTensorULift ℓ Γ hΓ σ).toFun (Γ ⧸ H → ZMod ℓ)
      (funPermRep (ZMod ℓ) Γ (Γ ⧸ H)) =
      Module.finrank (ULift.{u} (ZMod ℓ)) (Representation.invariants (σ.comp H.subtype)) := by
  classical
  have := Fintype.ofFinite Γ
  have : Finite (Γ ⧸ H) := inferInstance
  have := Fintype.ofFinite (Γ ⧸ H)
  rw [AdditiveFunction.invariantsTensorULift_apply]
  -- `𝔽_ℓ^X` over `ULift (ZMod ℓ)` is the permutation module over `ULift (ZMod ℓ)`
  let e₁ : (Γ ⧸ H → ZMod ℓ) ≃+ (Γ ⧸ H → ULift.{u} (ZMod ℓ)) :=
    AddEquiv.piCongrRight fun _ => AddEquiv.ulift.symm
  have h1 := finrank_invariants_tprod_eq_of_linearEquiv
    (zmodRepULift.{u} (funPermRep (ZMod ℓ) Γ (Γ ⧸ H)))
    (funPermRep (ULift.{u} (ZMod ℓ)) Γ (Γ ⧸ H)) σ (addEquivZModLinear e₁) (fun γ f => rfl)
  have h2 := finrank_invariants_eq_of_linearEquiv
    ((funPermRep (ULift.{u} (ZMod ℓ)) Γ (Γ ⧸ H)).tprod σ) (funRep (Γ ⧸ H) σ)
    (funTensorEquiv (k := ULift.{u} (ZMod ℓ)) (X := Γ ⧸ H) (N := N))
    (fun γ t => funext fun x => by rw [funTensorEquiv_tprod, funRep_apply])
  have h3 := LinearEquiv.finrank_eq (funRepQuotientInvariantsEquiv σ H)
  norm_cast
  exact h1.trans (h2.trans h3)

/-- `d(𝔽_ℓ) = dim N^Γ` for `d(X) = dim (X ⊗ N)^Γ`. -/
theorem one_invariantsTensorULift :
    (AdditiveFunction.invariantsTensorULift ℓ Γ hΓ σ).one =
      Module.finrank (ULift.{u} (ZMod ℓ)) σ.invariants := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : Subsingleton (Γ ⧸ (⊤ : Subgroup Γ)) := QuotientGroup.subsingleton_quotient_top
  let e : (Γ ⧸ (⊤ : Subgroup Γ) → ZMod ℓ) ≃ₗ[ZMod ℓ] ULift.{u} (ZMod ℓ) :=
    { toFun := fun f => ULift.up (f (QuotientGroup.mk 1))
      invFun := fun a _ => a.down
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun f => funext fun q => congrArg f (Subsingleton.elim _ _)
      right_inv := fun _ => rfl }
  have hc := (AdditiveFunction.invariantsTensorULift ℓ Γ hΓ σ).toFun_congr
    (funPermRep (ZMod ℓ) Γ (Γ ⧸ (⊤ : Subgroup Γ))) (Representation.trivial (ZMod ℓ) Γ _) e
    (fun γ f => by
      change ULift.up (f (γ⁻¹ • QuotientGroup.mk 1)) = ULift.up (f (QuotientGroup.mk 1))
      rw [Subsingleton.elim (γ⁻¹ • (QuotientGroup.mk 1 : Γ ⧸ (⊤ : Subgroup Γ))) _])
  rw [AdditiveFunction.one, ← hc, toFun_invariantsTensorULift_quotient]
  have : (Representation.invariants (σ.comp (⊤ : Subgroup Γ).subtype)).map (LinearMap.id) =
      σ.invariants := by
    ext n
    simp only [Submodule.map_id]
    exact ⟨fun h g => h ⟨g, trivial⟩, fun h g => h g⟩
  rw [← this, Submodule.map_id]

end Twist

section Places

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {L : Type u} [Field L] [NumberField L] [Algebra K L]
  [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) [IsGalois K L]
  (ι : PlaceEmbeddings K Ω)

attribute [local instance 2000] IsSepClosure.isGalois

/-- The place `τ • w_v` of `L` attached to a coset `τ D_v`. -/
def placesAboveFun (p : Σ v : S, (L ≃ₐ[K] L) ⧸ decompositionGroup hL ι v) :
    HeightOneSpectrum (𝓞 L) :=
  Quotient.liftOn' p.2 (fun τ => τ • ((basePlace hL ι p.1).1 : HeightOneSpectrum (𝓞 L)))
    (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab
      have h := (smul_basePlace_eq_iff hL ι p.1 _).2 hab
      calc a • ((basePlace hL ι p.1).1 : HeightOneSpectrum (𝓞 L)) =
            a • ((a⁻¹ * b) • ((basePlace hL ι p.1).1 : HeightOneSpectrum (𝓞 L))) := by rw [h]
        _ = b • ((basePlace hL ι p.1).1 : HeightOneSpectrum (𝓞 L)) := by
          rw [smul_smul, mul_inv_cancel_left])

theorem placesAboveFun_mk (v : S) (τ : L ≃ₐ[K] L) :
    placesAboveFun hL ι ⟨v, QuotientGroup.mk τ⟩ = τ • ((basePlace hL ι v).1 : HeightOneSpectrum (𝓞 L)) :=
  rfl

theorem under_placesAboveFun (p : Σ v : S, (L ≃ₐ[K] L) ⧸ decompositionGroup hL ι v) :
    (placesAboveFun hL ι p).under (𝓞 K) = p.1 := by
  obtain ⟨v, q⟩ := p
  induction q using QuotientGroup.induction_on with
  | H τ =>
    rw [placesAboveFun_mk, under_smul_finitePlace]
    exact (liesOver_iff_eq_under.1 (basePlace hL ι v).2).symm

/-- The places of `L` above `S` are `⊔_{v ∈ S} Gal(L/K)/D_v`. -/
def placesAboveEquiv :
    (Σ v : S, (L ≃ₐ[K] L) ⧸ decompositionGroup hL ι v) ≃ finitePlacesAbove L S :=
  Equiv.ofBijective (fun p => ⟨placesAboveFun hL ι p, by
      rw [mem_finitePlacesAbove_iff_under, under_placesAboveFun]
      exact p.1.2⟩) (by
    constructor
    · rintro ⟨v, q⟩ ⟨v', q'⟩ h
      have h' := congrArg Subtype.val h
      have hv : v = v' := Subtype.ext ((under_placesAboveFun hL ι ⟨v, q⟩).symm.trans
        ((congrArg (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) h').trans
          (under_placesAboveFun hL ι ⟨v', q'⟩)))
      subst hv
      induction q using QuotientGroup.induction_on with
      | H τ =>
      induction q' using QuotientGroup.induction_on with
      | H τ' =>
      simp only [placesAboveFun_mk] at h'
      congr 1
      rw [QuotientGroup.eq, ← smul_basePlace_eq_iff hL ι v, mul_smul, ← h', ← mul_smul, inv_mul_cancel,
        one_smul]
    · rintro ⟨w, hw⟩
      have hv : w.under (𝓞 K) ∈ S := mem_finitePlacesAbove_iff_under.1 hw
      have hlo : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := liesOver_iff_eq_under.2 rfl
      obtain ⟨σ, hσ⟩ := exists_galRestrict_smul_eq hL ι (w.under (𝓞 K)) ⟨w, hlo⟩
      exact ⟨⟨⟨w.under (𝓞 K), hv⟩, QuotientGroup.mk (Galois.galRestrict hL σ)⟩, Subtype.ext hσ⟩)

theorem placesAboveEquiv_smul (γ : L ≃ₐ[K] L)
    (p : Σ v : S, (L ≃ₐ[K] L) ⧸ decompositionGroup hL ι v) :
    placesAboveEquiv hL ι (γ • p) = γ • placesAboveEquiv hL ι p := by
  obtain ⟨v, q⟩ := p
  induction q using QuotientGroup.induction_on with
  | H τ =>
    apply Subtype.ext
    change placesAboveFun hL ι ⟨v, QuotientGroup.mk (γ * τ)⟩ = γ • placesAboveFun hL ι ⟨v, _⟩
    rw [placesAboveFun_mk, placesAboveFun_mk, mul_smul]

/-- **The permutation module of the places above `S`.** For every additive function `d`:
`d(𝔽_ℓ[S_L]) = ∑_{v ∈ S} d(𝔽_ℓ[Gal(L/K)/D_v])`. -/
theorem toFun_finitePlacesAbove [Finite S] {ℓ : ℕ} [NeZero ℓ]
    (d : AdditiveFunction.{u} ℓ (L ≃ₐ[K] L)) :
    haveI : Finite (finitePlacesAbove L S) :=
      (finite_finitePlacesAbove (L := L) (Set.toFinite S)).to_subtype
    haveI : Fintype S := Fintype.ofFinite S
    d.toFun (finitePlacesAbove L S → ZMod ℓ)
        (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) (finitePlacesAbove L S)) =
      ∑ v : S, d.toFun ((L ≃ₐ[K] L) ⧸ decompositionGroup hL ι v → ZMod ℓ)
        (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) ((L ≃ₐ[K] L) ⧸ decompositionGroup hL ι v)) := by
  have : Finite (finitePlacesAbove L S) :=
    (finite_finitePlacesAbove (L := L) (Set.toFinite S)).to_subtype
  let : Fintype S := Fintype.ofFinite S
  rw [← d.toFun_piFamilyRep S (fun v => (L ≃ₐ[K] L) ⧸ decompositionGroup hL ι v → ZMod ℓ)]
  refine d.toFun_congr _ _
    ((LinearEquiv.funCongrLeft (ZMod ℓ) (ZMod ℓ) (placesAboveEquiv hL ι)).trans
      (LinearEquiv.piCurry (ZMod ℓ)
        fun (v : S) (_ : (L ≃ₐ[K] L) ⧸ decompositionGroup hL ι v) => ZMod ℓ))
    fun γ f => ?_
  funext v q
  change f (placesAboveEquiv hL ι ⟨v, q⟩ |> fun w => γ⁻¹ • w) = f (placesAboveEquiv hL ι (γ⁻¹ • ⟨v, q⟩))
  rw [placesAboveEquiv_smul]

end Places

end

end Langlands.GaloisCohomology
