import Langlands.Representation.Unitary.HermitianAdmissibleProof
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.LinearAlgebra.LocallyFiniteHermitian

/-! # Hermitian self-duality: admissibility and the asymmetry operator -/

noncomputable section

universe u v

namespace Langlands.Renard.CompactRepresentation.HermitianProof

section SelfDual

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  (π : SmoothRep.{0, u, v} ℂ G)
  (e : π ≃ₗ⋆[ℂ] SmoothDual π.representation)
  (he : ∀ (g : G) (x : π), e (π.representation g x) =
    smoothContragredient π.representation g (e x))

include he

theorem selfDual_admissible : π.IsAdmissible := by
  refine ⟨π.isSmooth, fun H => ?_⟩
  obtain ⟨K, hK, hKH⟩ := compactOpenCofinal G H
  let U := fixedVectors π.representation K.toSubgroup
  let D := fixedVectors (smoothContragredient π.representation) K.toSubgroup
  let F : U →ₗ⋆[ℂ] D :=
    { toFun := fun x => ⟨e x, fun k => by
        change smoothContragredient π.representation k.val (e x.val) = e x.val
        rw [← he]
        exact congrArg e (x.property k)⟩
      map_add' := fun x y => Subtype.ext (e.map_add x y)
      map_smul' := fun c x => Subtype.ext (e.map_smulₛₗ c x) }
  have hF : Function.Bijective F := by
    constructor
    · intro x y h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
    · intro ℓ
      obtain ⟨x, hx⟩ := e.surjective ℓ.val
      have hfix : x ∈ U := by
        intro k
        apply e.injective
        change e (π.representation k.val x) = e x
        rw [he, hx]
        exact ℓ.property k
      exact ⟨⟨x, hfix⟩, Subtype.ext hx⟩
  let E := LinearEquiv.ofBijective F hF
  let R := LinearEquiv.ofBijective (smoothDualFixedRestriction π.representation K.toSubgroup)
    (smoothDualFixedRestriction_bijective π.representation π.isSmooth K hK)
  let L : U ≃ₗ[ℂ] Module.Dual ℂ U := ((basisConjugation U).trans E).trans R
  let : FiniteDimensional ℂ U := Basis.linearEquiv_dual_iff_finiteDimensional.mp ⟨L⟩
  let j : fixedVectors π.representation H.toSubgroup →ₗ[ℂ] U :=
    { toFun := fun x => ⟨x.val, fun k => x.property ⟨k.val, hKH k.property⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective j (fun _ _ h =>
    Subtype.ext (congrArg (fun z : U => z.val) h))

def selfDualPairing : π →ₗ⋆[ℂ] π →ₗ[ℂ] ℂ :=
  (smoothDualPairing π.representation).comp e.toLinearMap

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] he in
@[simp] theorem selfDualPairing_apply (x y : π) : selfDualPairing π e x y = (e x).val y := rfl

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem selfDualPairing_invariant (g : G) (x y : π) :
    selfDualPairing π e (π.representation g x) (π.representation g y) = selfDualPairing π e x y := by
  change (e (π.representation g x)).val (π.representation g y) = (e x).val y
  rw [he]
  change (e x).val (π.representation g⁻¹ (π.representation g y)) = _
  rw [Representation.inv_self_apply]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] he in
theorem selfDualPairing_nondegenerate (x : π) (hx : ∀ y, selfDualPairing π e x y = 0) : x = 0 := by
  apply e.injective
  rw [map_zero]
  apply Subtype.ext
  ext y
  exact hx y

end SelfDual

end Langlands.Renard.CompactRepresentation.HermitianProof

namespace Langlands.Renard.CompactRepresentation

open HermitianProof

/-- Hermitian self-duality gives a nondegenerate invariant hermitian form. -/
theorem hermitianOfSelfDual : HermitianOfSelfDualStatement.{u, v} := by
  intro G _ _ _ _ _ _ π
  rintro ⟨e, he⟩
  have ha := selfDual_admissible π e he
  let B := selfDualPairing π e
  have hBinv := selfDualPairing_invariant π e he
  let Bstar := LinearAlgebra.adjointPairing B
  have hBstarInv (g : G) (x y : π) :
      Bstar (π.representation g x) (π.representation g y) = Bstar x y := by
    exact congrArg (starRingEnd ℂ) (hBinv g y x)
  have hBstarND (x : π) (hx : ∀ y, Bstar x y = 0) : x = 0 := by
    have hBx (y : π) : B y x = 0 := by
      have h := congrArg (starRingEnd ℂ) (hx y)
      simpa only [Bstar, LinearAlgebra.adjointPairing_apply, starRingEnd_self_apply,
        map_zero] using h
    apply smoothBidual_injective_of_compact_cofinal (compactOpenCofinal G)
      π.representation π.isSmooth
    apply Subtype.ext
    ext ℓ
    change ℓ.val x = ℓ.val 0
    rw [map_zero]
    obtain ⟨y, rfl⟩ := e.surjective ℓ
    exact hBx y
  let eStar := pairingEquiv π.representation Bstar hBstarInv (compactOpenCofinal G) ha hBstarND
  let T : π ≃ₗ[ℂ] π := eStar.trans e.symm
  have hTe (x : π) : e (T x) = eStar x := e.apply_symm_apply (eStar x)
  have hBT (x y : π) : B (T x) y = starRingEnd ℂ (B y x) :=
    congrArg (fun ℓ : SmoothDual π.representation => ℓ.val y) (hTe x)
  have hTact (g : G) (x : π) : T (π.representation g x) = π.representation g (T x) := by
    apply e.injective
    calc
      e (T (π.representation g x)) = eStar (π.representation g x) := hTe _
      _ = smoothContragredient π.representation g (eStar x) :=
        pairingToSmoothDual_action π.representation Bstar hBstarInv ha.1 g x
      _ = smoothContragredient π.representation g (e (T x)) :=
        congrArg (smoothContragredient π.representation g) (hTe x).symm
      _ = e (π.representation g (T x)) := (he g (T x)).symm
  have hTfinite : LinearAlgebra.IsLocallyFinite T.toLinearMap := by
    intro x
    obtain ⟨K, hK⟩ := π.isSmooth x
    let P : LinearAlgebra.FiniteInvariantSubspace T.toLinearMap :=
      { carrier := fixedVectors π.representation K.toSubgroup
        finite := ha.2 K
        invariant := by
          intro y hy k
          change π.representation k.val (T y) = T y
          rw [← hTact]
          exact congrArg T (hy k) }
    exact ⟨P, hK⟩
  obtain ⟨H, hHherm, hHnd, hHinv⟩ :=
    LinearAlgebra.exists_hermitian_of_locallyFinite_asymmetry B T.toLinearMap hTfinite hBT
      (selfDualPairing_nondegenerate π e)
  refine ⟨H, hHherm, hHnd, fun g x y => ?_⟩
  apply hHinv (π.representation g) _ (hBinv g) x y
  ext z
  exact hTact g z

/-- Renard IV.2.1, Remarks 1 and 2, with the complete published telescope. -/
theorem hermitianRepresentationStatements : HermitianRepresentationStatements.{u, v} :=
  ⟨hermitianOfSelfDual, selfDualOfHermitian, hermitianFormUniqueness⟩

end Langlands.Renard.CompactRepresentation
