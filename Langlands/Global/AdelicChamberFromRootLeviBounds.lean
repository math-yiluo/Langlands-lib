import Langlands.Global.AdelicRootLeviTorusBound
import Langlands.Global.AdelicHeightMinimumCompactTransport
import Langlands.Global.AdelicMinimalParabolicNormCoordinates
import Langlands.Global.AdelicEmptyRootChamberReduction
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Finite-root chamber assembly from arithmetic bounds and positive coordinates -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix NNReal

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)

/-- One positive unit bounds every actual simple-root norm on the given
family of original torus points. -/
def HasUniformSimpleRootBound (S : Set (AdelicGroupPoints F T.toGrp)) : Prop :=
  ∃ B : ℝ≥0ˣ, ∀ α ∈ simpleRelativeRoots i ν, ∀ s ∈ S,
    normCharacter F T α s ≤ B

/-- Finitely many character bounds give a single simultaneous bound,
including when the actual simple-root set is empty. -/
theorem hasUniformSimpleRootBound_of_character_bounds
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (S : Set (AdelicGroupPoints F T.toGrp))
    (h : ∀ α ∈ simpleRelativeRoots i ν, HasUniformCharacterBound F T α S) :
    HasUniformSimpleRootBound F G T i ν S := by
  classical
  let : Fintype (simpleRelativeRoots i ν) := hfinite.fintype
  choose B hB using fun α : simpleRelativeRoots i ν => h α α.property
  obtain ⟨C, hC⟩ := (Set.finite_range B).bddAbove
  refine ⟨C, fun α hα s hs => ?_⟩
  exact (hB ⟨α, hα⟩ s hs).trans (hC ⟨⟨α, hα⟩, rfl⟩)

/-- Inverting the uniformly bounded family supplies a common weak lower
bound on all actual simple-root norms. -/
theorem HasUniformSimpleRootBound.exists_lower_inv
    {S : Set (AdelicGroupPoints F T.toGrp)}
    (h : HasUniformSimpleRootBound F G T i ν S) :
    ∃ t : ℝ≥0ˣ, ∀ α ∈ simpleRelativeRoots i ν, ∀ s ∈ S,
      t ≤ normCharacter F T α s⁻¹ := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B⁻¹, fun α hα s hs => ?_⟩
  rw [map_inv]
  exact inv_le_inv_iff.mpr (hB α hα s hs)

end Langlands.Global.PositiveRealTorus

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)
  (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- The original torus and minimal-Levi adelic images commute, since this
Levi represents the whole-torus centralizer in the actual setup. -/
theorem IsSiegelAlgebraicSetup.commute_torus_minimalLevi
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (s : AdelicGroupPoints F T.toGrp)
    (m : AdelicGroupPoints F (Standard.leviScheme i ν ∅)) :
    Commute (map F T.toGrp G i s)
      (map F _ G (Standard.leviHom i ν ∅) m) := by
  have hc : IsCentral (torusToStandardLevi F G T i ν) := by
    apply isCentral_of_range_le_torusCentralizer
      (Standard.isRepresentedBy_leviHom i ν ∅).1
    rw [torusToStandardLevi_comp, (Standard.isRepresentedBy_leviHom i ν ∅).2,
      hS.2.2.2.2.2.1]
  have h := (commute_of_mem_center
    (hc _ s) m).map (map F _ G (Standard.leviHom i ν ∅)).toMonoidHom
  have he : map F _ G (Standard.leviHom i ν ∅)
      (map F _ _ (torusToStandardLevi F G T i ν) s) = map F T.toGrp G i s := by
    change (s ≫ (torusToStandardLevi F G T i ν).hom.hom) ≫
      (Standard.leviHom i ν ∅).hom.hom = s ≫ i.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, torusToStandardLevi_comp]
  change Commute (map F _ G (Standard.leviHom i ν ∅)
    (map F _ _ (torusToStandardLevi F G T i ν) s))
      (map F _ G (Standard.leviHom i ν ∅) m) at h
  rwa [he] at h

/-- Uniform rank-one arithmetic bounds and actual positive coordinates give
the chamber factorization for every supplied minimal-parabolic Iwasawa compact.
Both universal arithmetic and coordinate inputs remain explicit. -/
theorem hasWeakChamberReduction_of_rootLevi_height_and_coordinates
    [LocallyOfFiniteType G.X.hom]
    (harith : RankOneParabolicRationalOrbitHeightBoundStatement.{u})
    (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (hcoords : HasMinimalParabolicNormCoordinates F G T i ν T₀ j)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅) K) :
    HasWeakChamberReduction F G T i ν T₀ j K := by
  classical
  let Δ := simpleRelativeRoots i ν
  have hfinite : Δ.Finite := hS.1.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  let : Fintype Δ := hfinite.fintype
  let r := Fintype.card Δ
  let e : Fin r ≃ Δ := (Fintype.equivFin Δ).symm
  let α : ℕ → characterLattice T := fun l =>
    if h : l < r then (e ⟨l, h⟩).val else 0
  have hα (l : ℕ) (hl : l < r) : α l ∈ Δ := by
    simpa only [α, dite_eq_left hl] using (e ⟨l, hl⟩).property
  have hinj (a l : ℕ) (ha : a < r) (hl : l < r) (heq : α a = α l) : a = l := by
    simp only [α, dite_eq_left ha, dite_eq_left hl] at heq
    exact congrArg Fin.val (e.injective (Subtype.ext heq))
  have hcover (β : characterLattice T) (hβ : β ∈ Δ) :
      ∃ l, l < r ∧ α l = β := by
    let l := e.symm ⟨β, hβ⟩
    refine ⟨l.val, l.isLt, ?_⟩
    simp only [α, dite_eq_left l.isLt, Fin.eta]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨β, hβ⟩)
  let J : ℕ → Set (characterLattice T) := fun l => Δ \ {α l}
  have hJ (l : ℕ) : J l ⊆ simpleRelativeRoots i ν := fun _ h => h.1
  obtain ⟨d, b, ρ, hstab, _, hmin⟩ :=
    exists_adapted_standardParabolicPrefix_minima F G T i ν J
  let d' : ℕ → ℕ := fun l => d l + 1
  let Q := closedPrefixRationalSubgroup F G
    (fun l => Standard.parabolicScheme i ν (J l))
    (fun l => Standard.parabolicHom i ν (J l))
  have hv (l : ℕ) (_ : l < r) :
      (Pi.single (b l) 1 : Fin (d' l) → F) ≠ 0 := by
    intro hz
    have he := congrFun hz (b l)
    simp at he
  obtain ⟨D, hD, htransport⟩ := exists_pos_chainHeightMinimalSet_compact_transport
    F G r d' ρ (fun l _ => Nat.zero_lt_succ (d l)) hK.1.1
  let S : Set (AdelicGroupPoints F T.toGrp) := {s |
    ∃ (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (x : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅)),
      map F _ G (Standard.leviHom i ν ∅) m * map F _ G i s *
          map F _ G (Standard.unipotentHom i ν ∅) x ∈
        adelicChainHeightMinimalSet F G r d' ρ (fun l => Pi.single (b l) 1) Q D}
  have hbound : PositiveRealTorus.HasUniformSimpleRootBound F G T i ν S := by
    apply PositiveRealTorus.hasUniformSimpleRootBound_of_character_bounds
      F G T i ν hfinite S
    intro β hβ
    obtain ⟨l, hl, rfl⟩ := hcover β hβ
    apply hasUniformRootBound_of_minimal_coordinates_and_prefix_minima
      F G T i ν harith hG hS.1 hS.2.1 J hJ r d' ρ b l hl (hstab l)
        (α l) (hα l hl) (by simp [J]) (fun a ha => ?_) D hD S
    · exact fun _ hs => hs
    · refine ⟨hα l hl, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro heq
      have heq' := hinj l a hl (ha.trans hl) heq
      omega
  obtain ⟨t, ht⟩ := hbound.exists_lower_inv F G T i ν
  let s : PositiveRealTorus.intrinsicSubgroup F T₀ → AdelicGroupPoints F T.toGrp :=
    fun a => map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a
  have hs (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
      map F T.toGrp G i (s a) = positiveMap F G T i T₀ j a := by
    change (a.val ≫ (CommGroupScheme.groupHom j).hom.hom) ≫ i.hom.hom =
      a.val ≫ (CommGroupScheme.groupHom j ≫ i).hom.hom
    rw [Grp.comp_hom_hom, Category.assoc]
  refine ⟨t, fun g => ?_⟩
  obtain ⟨q, hq⟩ := hmin r g⁻¹
  let y : normOneSubgroup F G := g⁻¹ * rationalNormOne F G q
  let z : normOneSubgroup F G := rationalNormOne F G q⁻¹ * g
  have hzy : z⁻¹ = y := by
    simp only [z, y, mul_inv_rev, map_inv, inv_inv]
  obtain ⟨x, m, a, k, hk, heq⟩ := hcoords.exists_iwasawa_factors
    F G T i ν T₀ j K hK z
  let p₀ := map F _ G (Standard.unipotentHom i ν ∅) x *
    map F _ G (Standard.leviHom i ν ∅) m * positiveMap F G T i T₀ j a
  have hp₀ : p₀ = (z : AdelicGroupPoints F G) * k⁻¹ := by
    rw [← heq]
    simp only [p₀, mul_inv_cancel_right]
  have hpone : p₀⁻¹ ∈ normOneSubgroup F G := by
    rw [hp₀]
    exact (normOneSubgroup F G).inv_mem ((normOneSubgroup F G).mul_mem z.property
      ((normOneSubgroup F G).inv_mem
        (compactSubgroup_le_normOneSubgroup F G K hK.1.1 hk)))
  let p : normOneSubgroup F G := ⟨p₀⁻¹, hpone⟩
  let k' : normOneSubgroup F G := ⟨k⁻¹,
    compactSubgroup_le_normOneSubgroup F G K hK.1.1 (K.inv_mem hk)⟩
  have hk'p : k' * p = y := by
    apply Subtype.ext
    change k⁻¹ * p₀⁻¹ = (y : AdelicGroupPoints F G)
    rw [← mul_inv_rev]
    change (p₀ * k)⁻¹ = (y : AdelicGroupPoints F G)
    rw [heq]
    exact congrArg Subtype.val hzy
  have hpmin : p ∈ chainHeightMinimalSet F G r d' ρ
      (fun l => Pi.single (b l) 1) Q D := by
    have h := (htransport (fun l => Pi.single (b l) 1) hv Q k' (K.inv_mem hk)
      p 1 zero_le_one).2 (hk'p.symm ▸ hq)
    simpa only [mul_one] using h
  have hporder :
      map F _ G (Standard.leviHom i ν ∅) (m⁻¹ : normOneSubgroup F _) *
        map F _ G i (s a)⁻¹ * map F _ G (Standard.unipotentHom i ν ∅) x⁻¹ =
          (p : AdelicGroupPoints F G) := by
    have hc := (hS.commute_torus_minimalLevi F G T i ν T₀ j (s a) m).inv_inv
    simp only [hs] at hc
    change _ = p₀⁻¹
    simp only [p₀, mul_inv_rev, Subgroup.coe_inv, map_inv, hs]
    rw [← mul_assoc, hc.eq]
  have hsa : (s a)⁻¹ ∈ S := by
    refine ⟨m⁻¹, x⁻¹, ?_⟩
    rw [hporder]
    exact hpmin
  have ha : a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t := by
    intro β hβ
    have h := ht β hβ (s a)⁻¹ hsa
    rw [inv_inv] at h
    exact (PositiveRealTorus.normCharacter_pullback F T₀ T j β a).symm ▸ h
  refine ⟨q⁻¹, x, m, a, ha, k, hk, ?_⟩
  simpa only [z, Subgroup.coe_mul, rationalNormOne_val] using heq

/-- The full chamber proposition follows from the two remaining universal
inputs. This implication does not assert either premise. -/
theorem adelicSiegelChamberReduction_of_rankOne_height_and_coordinates
    (harith : RankOneParabolicRationalOrbitHeightBoundStatement.{u})
    (hcoords : MinimalParabolicNormCoordinatesStatement.{u}) :
    AdelicSiegelChamberReductionStatement.{u} := by
  intro F _ _ G _ _ hG T i ν T₀ j hS K hK
  exact hasWeakChamberReduction_of_rootLevi_height_and_coordinates F G T i ν T₀ j
    harith hG hS (hcoords F G hG T i ν T₀ j hS) K hK

end Langlands.Global.AdelicSiegelFactors
