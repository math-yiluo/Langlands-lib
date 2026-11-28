import Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.GenericRegularity
import Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.FibreGeneric
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Open subsets containing the generic points of nearby fibres -/

universe u

open AlgebraicGeometry CategoryTheory Topology

namespace Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction

variable {X Y : Scheme.{u}}

/-- Let `g : Y ⟶ X` be smooth and quasi-compact with `X` locally noetherian, let `Z` be open in
`Y`, and let `ξ` be a point of `X` such that `Z` contains the generic points of the irreducible
components of the fibre over `ξ`. Then there is an open neighbourhood `N` of `ξ` such that `Z`
contains the generic points of the irreducible components of the fibre over every
specialization of `ξ` in `N`. -/
theorem exists_open_forall_isFibreGeneric_mem (g : Y ⟶ X) [Smooth g] [QuasiCompact g]
    [IsLocallyNoetherian X] (Z : Set Y) (hZ : IsOpen Z) (ξ : X)
    (hξ : ∀ q : Y, g q = ξ → IsFibreGeneric g q → q ∈ Z) :
    ∃ N : Set X, IsOpen N ∧ ξ ∈ N ∧
      ∀ x ∈ N, ξ ⤳ x → ∀ q : Y, g q = x → IsFibreGeneric g q → q ∈ Z := by
  classical
  obtain ⟨U, hU, hξU, -⟩ := exists_isAffineOpen_mem_and_subset (x := ξ) (U := ⊤) trivial
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hc : IsCompact (g ⁻¹' (U : Set X)) :=
    QuasiCompact.isCompact_preimage _ U.2 hU.isCompact
  let ι := {W : Y.Opens // IsAffineOpen W ∧ W ≤ g ⁻¹ᵁ U}
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun W : ι => (W.1 : Set Y)) (fun W => W.1.2) (by
    intro y hy
    obtain ⟨W, hW, hyW, hWsub⟩ :=
      exists_isAffineOpen_mem_and_subset (x := y) (U := g ⁻¹ᵁ U) hy
    exact Set.mem_iUnion.mpr ⟨⟨W, hW, hWsub⟩, hyW⟩)
  have hinjU : Function.Injective hU.fromSpec := hU.fromSpec.isOpenEmbedding.injective
  have key : ∀ W : ι, ∃ a : Γ(X, U), ξ ∈ X.basicOpen a ∧ ∀ x ∈ X.basicOpen a, ξ ⤳ x →
      ∀ q ∈ (W.1 : Set Y), g q = x → IsFibreGeneric g q → q ∈ Z := by
    rintro ⟨W, hW, hWU⟩
    let φ := g.appLE U W hWU
    have hsm : φ.hom.Smooth := HasRingHomProperty.appLE @Smooth g inferInstance ⟨U, hU⟩ ⟨W, hW⟩ hWU
    algebraize [φ.hom]
    have : Algebra.Smooth Γ(X, U) Γ(Y, W) := RingHom.smooth_algebraMap.mp hsm
    have hinjW : Function.Injective hW.fromSpec := hW.fromSpec.isOpenEmbedding.injective
    have hpt (Q : PrimeSpectrum Γ(Y, W)) :
        g (hW.fromSpec Q) = hU.fromSpec (PrimeSpectrum.comap φ.hom Q) := by
      have := congrArg (fun h => h.base Q) (IsAffineOpen.SpecMap_appLE_fromSpec g hU hW hWU)
      exact this.symm
    have hmemW (q : Y) (hq : q ∈ (W : Set Y)) :
        ∃ Q : PrimeSpectrum Γ(Y, W), hW.fromSpec Q = q := by
      rw [← hW.range_fromSpec] at hq; exact hq
    have hbo (a : Γ(X, U)) (p : PrimeSpectrum Γ(X, U)) :
        hU.fromSpec p ∈ X.basicOpen a ↔ a ∉ p.asIdeal := by
      let p' : ↥(Spec Γ(X, U)) := p
      exact SetLike.ext_iff.mp (hU.fromSpec_preimage_basicOpen a) p'
    set P := hU.primeIdealOf ⟨ξ, hξU⟩ with hPdef
    have hPξ : hU.fromSpec P = ξ := hU.fromSpec_primeIdealOf ⟨ξ, hξU⟩
    obtain ⟨a, haP, ha⟩ := exists_notMem_forall_minimal_mem (A := Γ(X, U)) (T := Γ(Y, W))
      P.asIdeal (hW.fromSpec ⁻¹' Z) (hZ.preimage hW.fromSpec.continuous) (by
        intro Q hQP hQmin
        have hcomap : PrimeSpectrum.comap φ.hom Q = P := PrimeSpectrum.ext hQP
        apply hξ
        · rw [hpt, hcomap, hPξ]
        · intro q' hq' hgq'
          have hq'W : q' ∈ (W : Set Y) :=
            hq'.mem_open W.2 (by rw [← hW.range_fromSpec]; exact ⟨Q, rfl⟩)
          obtain ⟨Q', rfl⟩ := hmemW q' hq'W
          have hle : Q' ≤ Q := (PrimeSpectrum.le_iff_specializes _ _).mpr
            (hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hq')
          have hc' : PrimeSpectrum.comap φ.hom Q' = P := by
            apply hinjU
            rw [← hpt, hgq', hpt, hcomap]
          rw [hQmin Q' hle (congrArg PrimeSpectrum.asIdeal hc')])
    refine ⟨a, ?_, ?_⟩
    · rw [← hPξ, hbo]
      exact haP
    · intro x hx hξx q hqW hgq hq
      obtain ⟨Q, rfl⟩ := hmemW q hqW
      have hxp : hU.fromSpec (PrimeSpectrum.comap φ.hom Q) = x := by rw [← hpt, hgq]
      have hPQ : P ≤ PrimeSpectrum.comap φ.hom Q := (PrimeSpectrum.le_iff_specializes _ _).mpr
        (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp (by rw [hPξ, hxp]; exact hξx))
      have haQ : a ∉ (PrimeSpectrum.comap φ.hom Q).asIdeal := by
        rw [← hbo, hxp]; exact hx
      refine ha Q hPQ haQ ?_
      intro Q' hQ' hQ'c
      apply hinjW
      apply hq
      · exact (PrimeSpectrum.le_iff_specializes _ _).mp hQ' |>.map hW.fromSpec.continuous
      · rw [hpt, hpt]
        exact congrArg hU.fromSpec (PrimeSpectrum.ext hQ'c)
  choose a ha₁ ha₂ using key
  refine ⟨(U : Set X) ∩ ⋂ W ∈ t, (X.basicOpen (a W) : Set X), ?_, ?_, ?_⟩
  · exact U.2.inter (isOpen_biInter_finset fun W _ => (X.basicOpen (a W)).2)
  · exact ⟨hξU, Set.mem_iInter₂.mpr fun W _ => ha₁ W⟩
  · rintro x ⟨hxU, hx⟩ hξx q hqx hq
    obtain ⟨W, hWt, hqW⟩ := Set.mem_iUnion₂.mp (ht (show q ∈ g ⁻¹' (U : Set X) by
      rw [Set.mem_preimage, hqx]; exact hxU))
    exact ha₂ W x (Set.mem_iInter₂.mp hx W hWt) hξx q hqW hqx hq

end Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction
