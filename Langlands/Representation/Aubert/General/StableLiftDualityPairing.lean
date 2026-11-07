import Langlands.Representation.Aubert.General.IwahoriJacquetStableLift
import Langlands.Representation.Aubert.General.ContragredientJacquetTransport
import Langlands.Representation.Aubert.General.StableLiftAsymptotics

/-! # The pairing of a stable-lift duality and its asymptotic evaluation

A natural isomorphism `Ψ : r_U(π~) ≅ (r_O π)~` pairs a smooth functional `ℓ` of `π` with a
vector `w` by evaluating `Ψ` at the class of `ℓ` on the class of `w`. When `Ψ` has the
stable-lift property `IsStableLiftDuality`, every vector has stable lifts for this pairing.
When the two normalizing characters are reciprocal, `M`-equivariance of `Ψ` makes the
pairing invariant under simultaneous translation. Together with
`exists_compact_forall_stableLiftPairing_translate_eq` this gives the asymptotic
evaluation of Renard VI.9.6.4–5 for every `t ∈ M` central in `M`. The isomorphism and the
pairing transport unchanged to pullbacks along identifications `H ≃ₜ* M`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

section Pairing

variable (U M O : Subgroup G) (hU : IsClosed (U : Set G)) (hO : IsClosed (O : Set G))
  (hMU : M ≤ Subgroup.normalizer U) (hMO : M ≤ Subgroup.normalizer O)

/-- The pairing defined by `Ψ : r_U(π~) ≅ (r_O π)~` on `A`: the value of `Ψ` at the class of
the smooth functional `ℓ` in `r_U(Ã)`, evaluated at the class of `w` in `r_O(A)`. -/
def stableLiftDualityPairing
    (Ψ : SmoothRep.contragredientFunctor.{0, uG, uV} ⋙
        normalizedJacquetFunctor.{uG, uV} U M hU hMU ≅
      (normalizedJacquetFunctor.{uG, uV} O M hO hMO).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, uV})
    (A : SmoothRep.{0, uG, uV} ℂ G) : SmoothDual A.representation → A → ℂ :=
  fun ℓ w =>
    smoothDualPairing ((normalizedJacquetFunctor.{uG, uV} O M hO hMO).obj A).representation
      (SmoothRep.hom (Ψ.hom.app (Opposite.op A))
        (Jacquet.Localization.mk (smoothContragredient A.representation) U 1 ℓ))
      (Jacquet.Localization.mk A.representation O 1 w)

variable {U M O hU hO hMU hMO}

/-- The stable-lift property of `Ψ` says that every vector has stable lifts for its pairing. -/
theorem hasStableLifts_stableLiftDualityPairing {g : G}
    {Ψ : SmoothRep.contragredientFunctor.{0, uG, uV} ⋙
        normalizedJacquetFunctor.{uG, uV} U M hU hMU ≅
      (normalizedJacquetFunctor.{uG, uV} O M hO hMO).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, uV}}
    (hΨ : IsStableLiftDuality.{uG, uV} U M O hU hO hMU hMO g Ψ)
    (A : SmoothRep.{0, uG, uV} ℂ G) (x : A) :
    HasStableLifts A.representation U M O g
      (stableLiftDualityPairing U M O hU hO hMU hMO Ψ A) x := by
  obtain ⟨W, hW⟩ := hΨ A (Jacquet.Localization.mk A.representation O 1 x)
  refine ⟨W, fun K hK hUp hLow hKW => ?_⟩
  obtain ⟨v, hv, hvx, hvP⟩ := hW K hK hUp hLow hKW
  refine ⟨v, hv, hvx, fun Λ hΛ => ?_⟩
  change smoothDualPairing _ _ (Jacquet.Localization.mk A.representation O 1 v) = _
  rw [hvx]
  exact hvP Λ hΛ

/-- Simultaneous translation: if the normalizing characters of `U` and `O` are reciprocal at
`m ∈ M`, then `⟨Ψ [π̃(m⁻¹) ℓ], [w]⟩ = ⟨Ψ [ℓ], [π(m) w]⟩`. This is the `M`-equivariance of `Ψ`. -/
theorem stableLiftDualityPairing_translate
    (Ψ : SmoothRep.contragredientFunctor.{0, uG, uV} ⋙
        normalizedJacquetFunctor.{uG, uV} U M hU hMU ≅
      (normalizedJacquetFunctor.{uG, uV} O M hO hMO).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, uV})
    (A : SmoothRep.{0, uG, uV} ℂ G) (m : M)
    (hχ : (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) *
      (HaarModulus.closedInverseHalfCharacter O hO M hMO m : ℂ) = 1)
    (ℓ : SmoothDual A.representation) (w : A) :
    stableLiftDualityPairing U M O hU hO hMU hMO Ψ A
        (smoothContragredient A.representation (m : G)⁻¹ ℓ) w =
      stableLiftDualityPairing U M O hU hO hMU hMO Ψ A ℓ (A.representation m w) := by
  set χU := HaarModulus.closedInverseHalfCharacter U hU M hMU
  set χO := HaarModulus.closedInverseHalfCharacter O hO M hMO
  set f := SmoothRep.hom (Ψ.hom.app (Opposite.op A))
  set rO := (normalizedJacquetFunctor.{uG, uV} O M hO hMO).obj A
  have h := Representation.IntertwiningMap.isIntertwining _ _ f m⁻¹
    (Jacquet.Localization.mk (smoothContragredient A.representation) U 1 ℓ)
  have h2 := congrArg (fun φ => smoothDualPairing rO.representation φ
    (Jacquet.Localization.mk A.representation O 1 w)) h
  let F : Jacquet.Localization.Coinvariants (smoothContragredient A.representation) U 1 →ₗ[ℂ]
      SmoothDual rO.representation := f.toLinearMap
  let pr : SmoothDual rO.representation →ₗ[ℂ]
      Jacquet.Localization.Coinvariants A.representation O 1 →ₗ[ℂ] ℂ :=
    smoothDualPairing rO.representation
  change pr (F ((χU m⁻¹ : ℂ) • Jacquet.Localization.mk (smoothContragredient A.representation) U 1
        (smoothContragredient A.representation ((m⁻¹ : M) : G) ℓ)))
      (Jacquet.Localization.mk A.representation O 1 w) =
    pr (F (Jacquet.Localization.mk (smoothContragredient A.representation) U 1 ℓ))
      ((χO m⁻¹⁻¹ : ℂ) • Jacquet.Localization.mk A.representation O 1
        (A.representation ((m⁻¹⁻¹ : M) : G) w)) at h2
  rw [inv_inv, map_smul, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
    smul_eq_mul] at h2
  have hinv : (χU m⁻¹ : ℂ) = (χO m : ℂ) := by
    rw [map_inv, Units.val_inv_eq_inv_val, inv_eq_of_mul_eq_one_right hχ]
  rw [hinv] at h2
  exact mul_left_cancel₀ (χO m).ne_zero h2

/-- The asymptotic evaluation of a stable-lift duality: for reciprocal normalizing
characters and every `x` and `ℓ` there is a compact `C ⊆ O` such that every `t ∈ M` central
in `M` that conjugates `C` into the stabilizer of `ℓ` has
`⟨Ψ [ℓ], [π(t) x]⟩ = ℓ(π(t) x)`. -/
theorem exists_compact_forall_stableLiftDualityPairing_translate_eq {g : G}
    (hBasis : Jacquet.HasOppositeIwahoriContractionBasis U M O g)
    {Ψ : SmoothRep.contragredientFunctor.{0, uG, uV} ⋙
        normalizedJacquetFunctor.{uG, uV} U M hU hMU ≅
      (normalizedJacquetFunctor.{uG, uV} O M hO hMO).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, uV}}
    (hΨ : IsStableLiftDuality.{uG, uV} U M O hU hO hMU hMO g Ψ)
    (hχ : ∀ m : M, (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) *
      (HaarModulus.closedInverseHalfCharacter O hO M hMO m : ℂ) = 1)
    (A : SmoothRep.{0, uG, uV} ℂ G) (x : A) (ℓ : SmoothDual A.representation) :
    ∃ C : Set G, IsCompact C ∧ C ⊆ O ∧
      ∀ t ∈ M, (∀ m ∈ M, t * m = m * t) →
        (∀ c ∈ C, smoothContragredient A.representation (t * c * t⁻¹) ℓ = ℓ) →
          stableLiftDualityPairing U M O hU hO hMU hMO Ψ A ℓ (A.representation t x) =
            smoothDualPairing A.representation ℓ (A.representation t x) := by
  have hPO : ∀ (ℓ : SmoothDual A.representation) (w w' : A),
      Jacquet.Localization.mk A.representation O 1 w =
        Jacquet.Localization.mk A.representation O 1 w' →
      stableLiftDualityPairing U M O hU hO hMU hMO Ψ A ℓ w =
        stableLiftDualityPairing U M O hU hO hMU hMO Ψ A ℓ w' := by
    intro ℓ w w' h
    change smoothDualPairing _ _ (Jacquet.Localization.mk A.representation O 1 w) =
      smoothDualPairing _ _ (Jacquet.Localization.mk A.representation O 1 w')
    rw [h]
  have hPU : ∀ (ℓ ℓ' : SmoothDual A.representation) (w : A),
      Jacquet.Localization.mk (smoothContragredient A.representation) U 1 ℓ =
        Jacquet.Localization.mk (smoothContragredient A.representation) U 1 ℓ' →
      stableLiftDualityPairing U M O hU hO hMU hMO Ψ A ℓ w =
        stableLiftDualityPairing U M O hU hO hMU hMO Ψ A ℓ' w := by
    intro ℓ ℓ' w h
    change smoothDualPairing _ (SmoothRep.hom (Ψ.hom.app (Opposite.op A))
        (Jacquet.Localization.mk (smoothContragredient A.representation) U 1 ℓ)) _ =
      smoothDualPairing _ (SmoothRep.hom (Ψ.hom.app (Opposite.op A))
        (Jacquet.Localization.mk (smoothContragredient A.representation) U 1 ℓ')) _
    rw [h]
  obtain ⟨C, hC, hCO, hCt⟩ := exists_compact_forall_stableLiftPairing_translate_eq
    A.representation U M O hO g hBasis _ hPO hPU x (hasStableLifts_stableLiftDualityPairing hΨ A x) ℓ
  refine ⟨C, hC, hCO, fun t ht htM hfix => hCt t (hMO ht) htM hfix fun ℓ' w => ?_⟩
  exact stableLiftDualityPairing_translate Ψ A ⟨t, ht⟩ (hχ _) ℓ' w

end Pairing

section Pullback

variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Pulling `Ψ` back along identifications `e₁ : H ≃ₜ* M₁` and `e₂ : H ≃ₜ* M₂` with equal
values in `G` (with `M₁ = M₂`) gives an isomorphism `e₁^*(r_U(π~)) ≅ (e₂^*(r_O π))~` with the
same pairing on classes. -/
theorem exists_pullback_iso_smoothDualPairing_eq
    (U O : Subgroup G) {M₁ M₂ : Subgroup G} (hM : M₁ = M₂)
    (hU : IsClosed (U : Set G)) (hO : IsClosed (O : Set G))
    (hMU₁ : M₁ ≤ Subgroup.normalizer U) (hMU₂ : M₂ ≤ Subgroup.normalizer U)
    (hMO₂ : M₂ ≤ Subgroup.normalizer O)
    (e₁ : H ≃ₜ* M₁) (e₂ : H ≃ₜ* M₂) (he : ∀ x, (e₁ x : G) = e₂ x)
    (Ψ : SmoothRep.contragredientFunctor.{0, uG, uV} ⋙
        normalizedJacquetFunctor.{uG, uV} U M₂ hU hMU₂ ≅
      (normalizedJacquetFunctor.{uG, uV} O M₂ hO hMO₂).op ⋙
        SmoothRep.contragredientFunctor.{0, uG, uV})
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    ∃ E : (normalizedJacquetFunctor.{uG, uV} U M₁ hU hMU₁ ⋙
          SmoothRep.pullbackFunctor e₁).obj A.contragredient ≅
        ((normalizedJacquetFunctor.{uG, uV} O M₂ hO hMO₂ ⋙
          SmoothRep.pullbackFunctor e₂).obj A).contragredient,
      ∀ (ℓ : SmoothDual A.representation) (w : A),
        smoothDualPairing ((normalizedJacquetFunctor.{uG, uV} O M₂ hO hMO₂ ⋙
            SmoothRep.pullbackFunctor e₂).obj A).representation
          (SmoothRep.hom E.hom
            (Jacquet.Localization.mk (smoothContragredient A.representation) U 1 ℓ))
          (Jacquet.Localization.mk A.representation O 1 w) =
        stableLiftDualityPairing U M₂ O hU hO hMU₂ hMO₂ Ψ A ℓ w := by
  subst hM
  obtain rfl : e₁ = e₂ := ContinuousMulEquiv.ext fun x => Subtype.ext (he x)
  exact ⟨(contragredientCompPullbackIso _ _ e₁ Ψ).app (Opposite.op A), fun ℓ w => rfl⟩

end Pullback

end Langlands.Aubert.General
