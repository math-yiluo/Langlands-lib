import Langlands.Representation.Whittaker.CompactLocalizationProof
import Langlands.AllField.Group.GL.CompactOpen
import Langlands.AllField.Representation.Whittaker.CompactLocalizationStatement
import Langlands.AllField.Group.GL.PadicUpperUnipotent
/-! # Character localization of compact induction

Inverse-character transport reduces the exact character quotient to ordinary
compact-induction coinvariants. Compact open subgroups of the upper-unipotent group,
obtained from the supplied data `T`, supply the topological and measure hypotheses of
the published integral bijectivity theorem.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding CompactLocalizationStatement compactLocalization
open Langlands.AllField.Whittaker

open MeasureTheory MeasureTheory.Measure

universe uF uV uG uW

variable {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem coinvariantKer_top (ρ : Representation ℂ G V) :
    Representation.Coinvariants.ker (ρ.comp (⊤ : Subgroup G).subtype) =
      Representation.Coinvariants.ker ρ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact Representation.Coinvariants.sub_mem_ker (ρ := ρ) g.val v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact Representation.Coinvariants.sub_mem_ker
      (ρ := ρ.comp (⊤ : Subgroup G).subtype) ⟨g, Subgroup.mem_top g⟩ v

private theorem characterRelations_top (ρ : Representation ℂ G V) (χ : G →* ℂˣ) :
    Jacquet.Localization.relations ρ (⊤ : Subgroup G)
        (χ.comp (⊤ : Subgroup G).subtype) =
      Representation.Coinvariants.ker (twist χ⁻¹ ρ) := by
  rw [Jacquet.Localization.relations_eq_twisted_ker]
  change Representation.Coinvariants.ker
    ((twist χ⁻¹ ρ).comp (⊤ : Subgroup G).subtype) = _
  exact coinvariantKer_top _

/-- Identity on representatives, using the already proved inverse-character relation equality. -/
private def characterCoinvariantsEquiv (ρ : Representation ℂ G V) (χ : G →* ℂˣ) :
    Jacquet.Localization.Coinvariants ρ (⊤ : Subgroup G)
        (χ.comp (⊤ : Subgroup G).subtype) ≃ₗ[ℂ]
      Representation.Coinvariants (twist χ⁻¹ ρ) :=
  Submodule.quotEquivOfEq _ _ (characterRelations_top ρ χ)

/-- Transport ordinary coinvariants through an actual representation equivalence. -/
private def coinvariantsEquiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) : Representation.Coinvariants ρ ≃ₗ[ℂ]
      Representation.Coinvariants σ :=
  LinearEquiv.ofLinearMap
    (Representation.Coinvariants.map ρ σ e.toIntertwiningMap)
    (Representation.Coinvariants.map σ ρ e.symm.toIntertwiningMap)
    (by
      apply Representation.Coinvariants.hom_ext
      ext v
      change Representation.Coinvariants.mk σ (e (e.symm v)) = _
      rw [e.apply_symm_apply]
      rfl)
    (by
      apply Representation.Coinvariants.hom_ext
      ext v
      change Representation.Coinvariants.mk ρ (e.symm (e v)) = _
      rw [e.symm_apply_apply]
      rfl)

variable [TopologicalSpace G] [IsTopologicalGroup G]

private def inverseSmoothCharacter (θ : Induction.SmoothCharacter ℂ G) :
    Induction.SmoothCharacter ℂ G where
  toMonoidHom := θ.toMonoidHom⁻¹
  isOpen_ker := by
    convert θ.isOpen_ker using 1
    ext g
    change (θ.toMonoidHom g)⁻¹ = 1 ↔ θ.toMonoidHom g = 1
    exact inv_eq_one

/-- The exact character quotient equivalence follows from ordinary localization of the inverse twist. -/
private def compactLocalizationOfOrdinary (H : Subgroup G)
    (σ : Representation ℂ H V) (θ : Induction.SmoothCharacter ℂ G)
    (eOrd : Representation.Coinvariants
        (Induction.compactInduced H (twist (θ.toMonoidHom.comp H.subtype)⁻¹ σ)) ≃ₗ[ℂ]
      Representation.Coinvariants (twist (θ.toMonoidHom.comp H.subtype)⁻¹ σ)) :
    Jacquet.Localization.Coinvariants (Induction.compactInduced H σ)
        (⊤ : Subgroup G) (θ.toMonoidHom.comp (⊤ : Subgroup G).subtype) ≃ₗ[ℂ]
      Jacquet.Localization.Coinvariants σ (⊤ : Subgroup H)
        ((θ.toMonoidHom.comp H.subtype).comp (⊤ : Subgroup H).subtype) :=
  (characterCoinvariantsEquiv (Induction.compactInduced H σ) θ.toMonoidHom).trans
    ((coinvariantsEquiv (Induction.compactInductionTwistEquiv H
      (inverseSmoothCharacter θ) σ)).trans
        (eOrd.trans (characterCoinvariantsEquiv σ (θ.toMonoidHom.comp H.subtype)).symm))

/-- Assembly using the proved bijectivity of the actual supplied quotient integral. -/
private theorem compactLocalizationOfCompatible
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (hBasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μG : Measure G) (μH : Measure H)
    [IsHaarMeasure μG] [μG.Regular] [IsMulRightInvariant μG]
    [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
    [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
    [BorelSpace (QuotientIntegration.LeftQuotient H)]
    (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
    (hν : QuotientIntegration.IsCompatible H μG μH ν)
    (σ : Representation ℂ H V) (hσ : IsSmooth σ)
    (θ : Induction.SmoothCharacter ℂ G) :
    Nonempty
      (Jacquet.Localization.Coinvariants (Induction.compactInduced H σ)
          (⊤ : Subgroup G) (θ.toMonoidHom.comp (⊤ : Subgroup G).subtype) ≃ₗ[ℂ]
        Jacquet.Localization.Coinvariants σ (⊤ : Subgroup H)
          ((θ.toMonoidHom.comp H.subtype).comp (⊤ : Subgroup H).subtype)) := by
  let τ := twist (θ.toMonoidHom.comp H.subtype)⁻¹ σ
  have hχ : IsOpen (((θ.toMonoidHom.comp H.subtype)⁻¹).ker : Set H) :=
    (inverseSmoothCharacter θ).isOpen_ker.preimage continuous_subtype_val
  have hτ : IsSmooth τ := (isSmooth_twist_iff _ σ hχ).mpr hσ
  exact ⟨compactLocalizationOfOrdinary H σ θ
    (LinearEquiv.ofBijective (Induction.compactCoinvariantDesc H τ ν hν.right_invariant)
      (Induction.compactCoinvariantIntegralBijective hBasis H hH μG μH ν hν V τ hτ))⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Compact induction from every closed subgroup of the upper-unipotent group over a
nonarchimedean local field preserves the full positive-character quotient as a complex
vector space. -/
theorem compactLocalization : CompactLocalizationStatement.{uF,uV} := by
  intro F _ T
  let := T.topology
  dsimp only
  intro n
  let := T.generalLinearTopologicalGroup (n + 1)
  let U : Type uF := GeneralLinear.upperUnipotent (n + 1) F
  let : T2Space U := T.upperUnipotentT2Space (n + 1)
  let : LocallyCompactSpace U := T.upperUnipotentLocallyCompactSpace (n + 1)
  have hBasis : ∀ O : Set U, IsOpen O → (1 : U) ∈ O →
      ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ (K : Set U) ⊆ O := by
    intro O hO h1
    exact ⟨(T.upperUnipotentCompactOpen (n + 1) O (hO.mem_nhds h1)).val,
      (T.upperUnipotentCompactOpen (n + 1) O (hO.mem_nhds h1)).property⟩
  have hCover : ∀ g : U, ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ g ∈ K := by
    let := T.valuativeRel
    let := T.localField
    exact RankinSelberg.unipotent_exists_compact_open F n
  intro H hH V _ _ σ hσ θ
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  borelize U
  borelize ↥H
  borelize (QuotientIntegration.LeftQuotient H)
  let μU : Measure U := haar
  let μH : Measure H := haar
  have hR := Haar.compactOpenCoverUnimodularity hCover
  let : IsMulRightInvariant μU := hR.1 μU
  let : IsMulRightInvariant μH := hR.2 H hH μH
  obtain ⟨ν, hν⟩ := QuotientIntegration.compatibleMeasureExists H hH μU μH
  let : ν.Regular := hν.regular
  exact compactLocalizationOfCompatible hBasis H hH μU μH ν hν σ hσ θ

end Langlands.AllField.Whittaker
