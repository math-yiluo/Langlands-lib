import Langlands.AlgebraicGeometry.Descent.AffineFpqcClosedLocusDescent

/-! # Descent of closed loci along fpqc covers -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- An fpqc-closed sieve that is represented by closed immersions over a
covering sieve has a global closed-immersion representative. -/
def FpqcClosedLocusDescentStatement : Prop :=
  ∀ (Y : Scheme.{u}) (E : Sieve Y), Scheme.fpqcTopology.IsClosed E →
    (∃ R ∈ Scheme.fpqcTopology Y, ∀ ⦃Y' : Scheme.{u}⦄ (f : Y' ⟶ Y), R f →
      ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y'), IsClosedImmersion ι ∧
        ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y'), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E (g ≫ f)) →
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y), IsClosedImmersion ι ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E g

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fpqcClosedLocusDescent_affine {Y : Scheme.{u}} [IsAffine Y] (E : Sieve Y)
    (hE : Scheme.fpqcTopology.IsClosed E) (R : Sieve Y) (hR : R ∈ Scheme.fpqcTopology Y)
    (h : ∀ ⦃Y' : Scheme.{u}⦄ (f : Y' ⟶ Y), R f →
      ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y'), IsClosedImmersion ι ∧
        ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y'), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E (g ≫ f)) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y), IsClosedImmersion ι ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E g := by
  obtain ⟨P, hP, hle⟩ := (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
    (J := Scheme.fpqcPrecoverage)).mp hR
  obtain ⟨(𝒰 : Scheme.Cover Scheme.fpqcPrecoverage Y), rfl⟩ :=
    Precoverage.mem_iff_exists_zeroHypercover.mp hP
  obtain ⟨𝒱, f, hfin, -⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
  classical
  let : Finite 𝒱.I₀ := hfin
  let : Fintype 𝒱.I₀ := Fintype.ofFinite _
  let 𝒱' : Scheme.Cover Scheme.fpqcPrecoverage Y := .ofQuasiCompactCover 𝒱.cover
  have hS : Sieve.generate 𝒱.cover.presieve₀ ∈ Scheme.fpqcTopology Y :=
    Precoverage.generate_mem_toGrothendieck 𝒱'.mem₀
  refine AffineFpqcClosedLocusDescent.finiteCover Scheme.fpqcTopology E hE
    (fun i => Spec (𝒱.X i)) 𝒱.f 𝒱.map_prop hS (fun i => h _ ?_)
  change R (𝒱.cover.f i)
  rw [← f.w₀ i]
  exact R.downward_closed (hle _ _ (Presieve.ofArrows.mk (f.s₀ i))) _

/-- Effective descent for closed loci, using finite affine fpqc refinements. -/
theorem fpqcClosedLocusDescent : FpqcClosedLocusDescentStatement.{u} := by
  intro Y E hE ⟨R, hR, hloc⟩
  refine closedLocusFromAffineCharts Y (fun _ g => E g) (fun _ _ f g hg => E.downward_closed hg f)
    (fun T g hg => ?_) (fun U => ?_)
  · refine hE g (Scheme.fpqcTopology.superset_covering ?_
      (Scheme.zariskiTopology_le_fpqcTopology T
        (Precoverage.generate_mem_toGrothendieck (R := Presieve.ofArrows
          (fun V : Y.affineOpens => (g ⁻¹ᵁ (V : Y.Opens)).toScheme)
          (fun V => (g ⁻¹ᵁ (V : Y.Opens)).ι)) ?_)))
    · rw [Sieve.generate_le_iff]
      rintro _ _ ⟨V⟩
      exact hg V
    · rw [Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨fun t => ?_, fun V => inferInstance⟩
      obtain ⟨V, hV, hgV, -⟩ := exists_isAffineOpen_mem_and_subset
        (show g t ∈ (⊤ : Y.Opens) from trivial)
      exact ⟨⟨V, hV⟩, ⟨t, hgV⟩, rfl⟩
  · have : IsAffine (U : Y.Opens) := U.2
    refine fpqcClosedLocusDescent_affine (E.pullback (U : Y.Opens).ι)
      (Scheme.fpqcTopology.isClosed_pullback _ _ hE) (R.pullback (U : Y.Opens).ι)
      (Scheme.fpqcTopology.pullback_stable _ hR) fun Y' f hf => ?_
    obtain ⟨Z, ι, hι, H⟩ := hloc (f ≫ (U : Y.Opens).ι) hf
    refine ⟨Z, ι, hι, fun T g => ?_⟩
    rw [H g]
    change E (g ≫ f ≫ _) ↔ E ((g ≫ f) ≫ _)
    rw [Category.assoc]

end Langlands.AlgebraicGeometry
