import Langlands.Geometry.Building.KPLocalMoyPrasadIntersectionRoot

/-!
# Clauses 4, 6 and 7 of the K-level Moy–Prasad group properties at depth zero

The depth-zero cases of clauses 4, 6 and 7 of `LocalMoyPrasadGroupPropertiesStatement`, from two
depth-zero intersection facts taken as explicit hypotheses (the two clauses of the statement
requested in Task 6570): `U⁺(μ)(K) ∩ G(K)_{x,0} = U⁺_{x,0}` for generic `μ`, and
`M_ν(K) ∩ G(K)_{x,0} ⊆ j(Z(K)_0) · U_{Φ⁰(ν),x,0}`. Combined with the positive-depth results
derived from the sign product cover, they give the three clauses at every depth.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

/-- A generic integral cocharacter, viewed in `V`, pairs nontrivially with every relative
root, so no relative root vanishes on it. -/
theorem zeroPairingRoots_tmul_eq_empty {mu : cocharacterLattice B.S}
    (hmu : IsGenericCocharacter B.i mu) :
    B.zeroPairingRoots ((1 : ℝ) ⊗ₜ[ℤ] mu) = ∅ := by
  ext b
  simp only [zeroPairingRoots, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hb h
  rw [eval_tmul, one_mul, Int.cast_eq_zero] at h
  exact hmu b hb h

/-- The filtration span of the empty set of roots is trivial. -/
theorem rootFiltrationSpan_empty (x : B.Apartment) (r : ℝ) :
    B.rootFiltrationSpan x ∅ r = ⊥ :=
  le_bot_iff.mp (iSup₂_le fun _ hb => absurd hb (Set.notMem_empty _))

/-- **Clause 4 at depth zero.** From `U⁺(μ)(K) ∩ G(K)_{x,0} = U⁺_{x,0}` for every generic
`μ`: for a closed set `Ψ` of roots in an open half-space, `U_Ψ ∩ G(K)_{x,0} = U_{Ψ,x,0}`. -/
theorem rootIntersection_zero_of_depthZero
    (hDZa : ∀ (x : B.Apartment) (mu : cocharacterLattice B.S), IsGenericCocharacter B.i mu →
      B.rootGroupSpan (positiveRelativeRoots B.i mu) ⊓ B.moyPrasad hZ x 0 =
        B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) 0)
    (Ψ : Set (characterLattice B.S)) (ν : V B.S) (hΨc : B.IsClosedRootSet Ψ)
    (hΨ : ∀ b ∈ Ψ, 0 < eval B.S b ν) (x : B.Apartment) :
    B.rootGroupSpan Ψ ⊓ B.moyPrasad hZ x 0 = B.rootFiltrationSpan x Ψ 0 := by
  apply le_antisymm
  · rintro g ⟨hgΨ, hg⟩
    obtain ⟨_, mu, hmu, hsign⟩ := B.exists_sign_and_generic ν
    have hΨmu : ∀ b ∈ Ψ, 0 < latticePairing B.S b mu :=
      fun b hb => (hsign b (hΨc.1 hb)).2.2.1 (hΨ b hb)
    have hgplus : g ∈ B.rootGroupSpan (positiveRelativeRoots B.i mu) :=
      B.rootGroupSpan_mono (fun b hb =>
        (show b ∈ positiveRelativeRoots B.i mu from ⟨hΨc.1 hb, hΨmu b hb⟩)) hgΨ
    have hgv : g ∈ B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) 0 := by
      rw [← hDZa x mu hmu]
      exact ⟨hgplus, hg⟩
    exact B.mem_rootFiltrationSpan_of_mem_rootGroupSpan x le_rfl mu hΨc hΨmu hgΨ hgv
  · have h := B.rootFiltrationSpan_le_moyPrasad hZ x hΨc.1 0
    rw [NNReal.coe_zero] at h
    exact le_inf (B.rootFiltrationSpan_le_rootGroupSpan x Ψ 0) h

/-- **Clause 6 at depth zero.** From `M_ν(K) ∩ G(K)_{x,0} ⊆ j(Z(K)_0) · U_{Φ⁰(ν),x,0}`. -/
theorem leviIntersection_zero_of_depthZero
    (hDZb : ∀ (x : B.Apartment) (ν : V B.S),
      B.pairingLeviSpan ν ⊓ B.moyPrasad hZ x 0 ≤
        B.centralizerTorusImage hZ 0 ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) 0)
    (ν : V B.S) (x : B.Apartment) :
    B.pairingLeviSpan ν ⊓ B.moyPrasad hZ x 0 =
      B.centralizerTorusImage hZ 0 ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) 0 := by
  apply le_antisymm (hDZb x ν)
  have h₁ := B.leviFiltration_le_pairingLeviSpan hZ x 0 ν
  have h₂ := B.leviFiltration_le_moyPrasad hZ x 0 ν
  rw [NNReal.coe_zero] at h₁ h₂
  exact le_inf h₁ h₂

/-- **Clause 7 at depth zero.** From the Levi inclusion at a generic `ν`, where no relative
root vanishes: `j⁻¹(G(K)_{x,0}) = Z(K)_0`. -/
theorem comap_moyPrasad_zero_of_depthZero
    (hDZb : ∀ (x : B.Apartment) (ν : V B.S),
      B.pairingLeviSpan ν ⊓ B.moyPrasad hZ x 0 ≤
        B.centralizerTorusImage hZ 0 ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) 0)
    (x : B.Apartment) :
    (B.moyPrasad hZ x 0).comap (rationalPoints.map B.centralizer.j) =
      B.centralizerTorusFiltration hZ 0 := by
  apply le_antisymm
  · intro z hz
    obtain ⟨mu, hmu⟩ := B.exists_genericCocharacter
    have hM : rationalPoints.map B.centralizer.j z ∈ B.pairingLeviSpan ((1 : ℝ) ⊗ₜ[ℤ] mu) :=
      le_sup_left (a := (rationalPoints.map B.centralizer.j).range) ⟨z, rfl⟩
    have h := hDZb x ((1 : ℝ) ⊗ₜ[ℤ] mu) ⟨hM, hz⟩
    rw [B.zeroPairingRoots_tmul_eq_empty hmu, B.rootFiltrationSpan_empty, sup_bot_eq] at h
    obtain ⟨z', hz', hzz'⟩ := h
    rwa [← B.centralizer_map_injective hzz']
  · intro z hz
    exact B.map_mem_moyPrasad hZ x hz

/-- **Clause 4 at every depth**, from the sign product cover at positive depth and the
depth-zero intersection with `U⁺(μ)`. -/
theorem rootIntersection_of_covers
    (hPC : ∀ (x : B.Apartment) (r : ℝ≥0), 0 < r → ∀ mu : cocharacterLattice B.S,
      IsGenericCocharacter B.i mu →
        (B.moyPrasad hZ x r : Set (rationalPoints H)) =
          (B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r :
              Set (rationalPoints H)) *
            (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
              (B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r :
                Set (rationalPoints H)))
    (hDZa : ∀ (x : B.Apartment) (mu : cocharacterLattice B.S), IsGenericCocharacter B.i mu →
      B.rootGroupSpan (positiveRelativeRoots B.i mu) ⊓ B.moyPrasad hZ x 0 =
        B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) 0) :
    LocalMoyPrasadRootIntersection B hZ := by
  intro Ψ ν hΨc hΨ x r
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ r from zero_le) with hr | hr
  · subst hr
    rw [NNReal.coe_zero]
    exact B.rootIntersection_zero_of_depthZero hZ hDZa Ψ ν hΨc hΨ x
  · exact B.rootIntersection_of_productCover hZ hPC Ψ ν hΨc hΨ x hr

/-- **Clause 6 at every depth**, from the sign product cover at positive depth and the
depth-zero Levi inclusion. -/
theorem leviIntersection_of_covers
    (hPC : ∀ (x : B.Apartment) (r : ℝ≥0), 0 < r → ∀ mu : cocharacterLattice B.S,
      IsGenericCocharacter B.i mu →
        (B.moyPrasad hZ x r : Set (rationalPoints H)) =
          (B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r :
              Set (rationalPoints H)) *
            (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
              (B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r :
                Set (rationalPoints H)))
    (hDZb : ∀ (x : B.Apartment) (ν : V B.S),
      B.pairingLeviSpan ν ⊓ B.moyPrasad hZ x 0 ≤
        B.centralizerTorusImage hZ 0 ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) 0) :
    LocalMoyPrasadLeviIntersection B hZ := by
  intro ν x r
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ r from zero_le) with hr | hr
  · subst hr
    rw [NNReal.coe_zero]
    exact B.leviIntersection_zero_of_depthZero hZ hDZb ν x
  · exact B.leviIntersection_of_productCover hZ hPC ν x hr

/-- **Clause 7 at every depth**, from the sign product cover at positive depth and the
depth-zero Levi inclusion. -/
theorem centralizerIntersection_of_covers
    (hPC : ∀ (x : B.Apartment) (r : ℝ≥0), 0 < r → ∀ mu : cocharacterLattice B.S,
      IsGenericCocharacter B.i mu →
        (B.moyPrasad hZ x r : Set (rationalPoints H)) =
          (B.rootFiltrationSpan x (positiveRelativeRoots B.i (-mu)) r :
              Set (rationalPoints H)) *
            (B.centralizerTorusImage hZ r : Set (rationalPoints H)) *
              (B.rootFiltrationSpan x (positiveRelativeRoots B.i mu) r :
                Set (rationalPoints H)))
    (hDZb : ∀ (x : B.Apartment) (ν : V B.S),
      B.pairingLeviSpan ν ⊓ B.moyPrasad hZ x 0 ≤
        B.centralizerTorusImage hZ 0 ⊔ B.rootFiltrationSpan x (B.zeroPairingRoots ν) 0) :
    LocalMoyPrasadCentralizerIntersection B hZ := by
  intro x r
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ r from zero_le) with hr | hr
  · subst hr
    exact B.comap_moyPrasad_zero_of_depthZero hZ hDZb x
  · exact B.comap_moyPrasad_eq_of_productCover hZ hPC x hr

end Langlands.Geometry.Building.MaximalUnramified.BuildingData
