import Langlands.Global.AdelicSiegelChamberReduction

/-! # Positive coordinates on the norm-one part of a minimal parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- The actual adelic minimal-parabolic image, restricted to ambient norm-one points.
This uses the ambient norm-one condition, rather than all characters of the parabolic. -/
def standardParabolicNormOneImage : Subgroup (normOneSubgroup F G) :=
  (standardParabolicImage F G T i ν).subgroupOf (normOneSubgroup F G)

/-- A coordinate homeomorphism whose forward map is precisely the ordered product
`N(𝔸_F) × (M(𝔸_F)¹ × A_{T₀}) → P(𝔸_F) ∩ G(𝔸_F)¹`. No direct-product group law
is asserted for this semidirect product. -/
def HasMinimalParabolicNormCoordinates : Prop :=
  ∃ E :
      AdelicGroupPoints F (Standard.unipotentScheme i ν ∅) ×
          (normOneSubgroup F (Standard.leviScheme i ν ∅) ×
            PositiveRealTorus.intrinsicSubgroup F T₀) ≃ₜ
        standardParabolicNormOneImage F G T i ν,
    ∀ x, ((E x : normOneSubgroup F G) : AdelicGroupPoints F G) =
      map F _ G (Standard.unipotentHom i ν ∅) x.1 *
        map F _ G (Standard.leviHom i ν ∅) x.2.1 *
        positiveMap F G T i T₀ j x.2.2

/-- The actual minimal-parabolic coordinate theorem needed to pass between Springer's
torus/parabolic factors and intrinsic positive-torus Siegel factors. -/
def MinimalParabolicNormCoordinatesStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T)
        (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T),
        IsSiegelAlgebraicSetup F G T i ν T₀ j →
          HasMinimalParabolicNormCoordinates F G T i ν T₀ j

/-- Coordinates give the exact factorization of each ambient norm-one parabolic point. -/
theorem HasMinimalParabolicNormCoordinates.exists_factors
    (h : HasMinimalParabolicNormCoordinates F G T i ν T₀ j)
    (p : normOneSubgroup F G) (hp : (p : AdelicGroupPoints F G) ∈
      standardParabolicImage F G T i ν) :
    ∃ (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
      (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (a : PositiveRealTorus.intrinsicSubgroup F T₀),
      map F _ G (Standard.unipotentHom i ν ∅) n *
        map F _ G (Standard.leviHom i ν ∅) m *
        positiveMap F G T i T₀ j a = p := by
  obtain ⟨E, hE⟩ := h
  let p' : standardParabolicNormOneImage F G T i ν := ⟨p, hp⟩
  refine ⟨(E.symm p').1, (E.symm p').2.1, (E.symm p').2.2, ?_⟩
  simpa only [Homeomorph.apply_symm_apply] using (hE (E.symm p')).symm

/-- Iwasawa coverage and coordinates supply the unrestricted `n m a k` factorization.
There is no simple-root bound here: obtaining one uniform threshold still requires reduction
theory and rational translation. -/
theorem HasMinimalParabolicNormCoordinates.exists_iwasawa_factors
    (h : HasMinimalParabolicNormCoordinates F G T i ν T₀ j)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅) K)
    (g : normOneSubgroup F G) :
    ∃ (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
      (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (a : PositiveRealTorus.intrinsicSubgroup F T₀),
      ∃ k ∈ K, map F _ G (Standard.unipotentHom i ν ∅) n *
        map F _ G (Standard.leviHom i ν ∅) m *
        positiveMap F G T i T₀ j a * k = g := by
  have hg : (g : AdelicGroupPoints F G) ∈
      Set.range (map F (Standard.parabolicScheme i ν ∅) G
        (Standard.parabolicHom i ν ∅)) * (K : Set (AdelicGroupPoints F G)) := by
    rw [hK.2]
    exact Set.mem_univ _
  obtain ⟨_, ⟨p, rfl⟩, k, hk, hpk⟩ := hg
  have hkone := compactSubgroup_le_normOneSubgroup F G K hK.1.1 hk
  have hpone : map F _ G (Standard.parabolicHom i ν ∅) p ∈ normOneSubgroup F G := by
    have hp : map F _ G (Standard.parabolicHom i ν ∅) p =
        (g : AdelicGroupPoints F G) * k⁻¹ := by
      rw [← hpk, mul_inv_cancel_right]
    rw [hp]
    exact (normOneSubgroup F G).mul_mem g.2 ((normOneSubgroup F G).inv_mem hkone)
  obtain ⟨n, m, a, hma⟩ := h.exists_factors F G T i ν T₀ j
    ⟨_, hpone⟩ ⟨p, rfl⟩
  exact ⟨n, m, a, k, hk, by rw [hma]; exact hpk⟩

/-- A compact set in the norm-one parabolic has compact sets of all three coordinates.
This is the compact-control consequence used when changing compact factors. -/
theorem HasMinimalParabolicNormCoordinates.compact_coordinate_covers
    (h : HasMinimalParabolicNormCoordinates F G T i ν T₀ j)
    (C : Set (standardParabolicNormOneImage F G T i ν)) (hC : IsCompact C) :
    ∃ (C_N : Set (AdelicGroupPoints F (Standard.unipotentScheme i ν ∅)))
      (C_M : Set (normOneSubgroup F (Standard.leviScheme i ν ∅)))
      (C_A : Set (PositiveRealTorus.intrinsicSubgroup F T₀)),
      IsCompact C_N ∧ IsCompact C_M ∧ IsCompact C_A ∧
        ∀ p ∈ C, ∃ n ∈ C_N, ∃ m ∈ C_M, ∃ a ∈ C_A,
          map F _ G (Standard.unipotentHom i ν ∅) n *
            map F _ G (Standard.leviHom i ν ∅) m *
            positiveMap F G T i T₀ j a =
              ((p : normOneSubgroup F G) : AdelicGroupPoints F G) := by
  obtain ⟨E, hE⟩ := h
  refine ⟨(fun p => (E.symm p).1) '' C,
    (fun p => (E.symm p).2.1) '' C,
    (fun p => (E.symm p).2.2) '' C,
    hC.image (continuous_fst.comp E.symm.continuous),
    hC.image (continuous_fst.comp (continuous_snd.comp E.symm.continuous)),
    hC.image (continuous_snd.comp (continuous_snd.comp E.symm.continuous)), ?_⟩
  intro p hp
  refine ⟨_, ⟨p, hp, rfl⟩, _, ⟨p, hp, rfl⟩, _, ⟨p, hp, rfl⟩, ?_⟩
  simpa only [Homeomorph.apply_symm_apply] using (hE (E.symm p)).symm

end Langlands.Global.AdelicSiegelFactors
