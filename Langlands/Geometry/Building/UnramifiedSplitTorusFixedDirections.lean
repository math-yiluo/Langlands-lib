import Langlands.Geometry.Building.UnramifiedSpecialApartmentRegularDirectionReduction
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Coefficient-fixed directions from a prescribed split torus -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- A descended actual cocharacter gives a reduced real direction upstairs. -/
def baseChangeCocharacterDirection (ν : cocharacterLattice T) :
    TranslationSpace (S := T_K) i_K :=
  Submodule.Quotient.mk
    ((1 : ℝ) ⊗ₜ[ℤ] cocharacterLattice.baseChange b T ν)

/-- This direction is fixed by every actual coefficient automorphism. -/
theorem galoisTranslationAction_baseChangeCocharacterDirection
    (σ : K ≃ₐ[k] K) (ν : cocharacterLattice T) :
    galoisTranslationAction k K i σ (baseChangeCocharacterDirection k K i ν) =
      baseChangeCocharacterDirection k K i ν := by
  change Submodule.Quotient.mk
      (galoisCocharacterAction k K T σ
        ((1 : ℝ) ⊗ₜ[ℤ] cocharacterLattice.baseChange b T ν)) = _
  rw [galoisCocharacterAction_tmul, cocharacterLattice.galoisRepresentation_baseChange]
  rfl

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
  (hS : IsSplitTorus S.toGrp) (f : S ⟶ T)

local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "f_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) f

include hS

/-- A nonzero actual restriction to the supplied split torus is detected by
one of its descended cocharacters. -/
theorem exists_baseChangeCocharacterDirection_rootForm_ne_zero
    (a : relativeRoots (T := T_K) i_K)
    (ha : characterRestrict (CommGroupScheme.groupHom f_K) a.val ≠ 0) :
    ∃ ν : cocharacterLattice S,
      rootForm (S := T_K) i_K a
        (baseChangeCocharacterDirection k K i (ν ≫ f)) ≠ 0 := by
  let χ := characterRestrict (CommGroupScheme.groupHom f_K) a.val
  have hp := CocharacterUniformizer.latticePairing_isPerfPair K S_K (hS.baseChange b)
  have hν : ∃ ν' : cocharacterLattice S_K, latticePairing S_K χ ν' ≠ 0 := by
    by_contra! hn
    apply ha
    apply hp.bijective_left.injective
    ext ν'
    simpa only [map_zero, LinearMap.zero_apply] using hn ν'
  obtain ⟨ν', hpair⟩ := hν
  obtain ⟨ν, hν⟩ := (hS.cocharacterLattice_baseChange_bijective b S).surjective ν'
  refine ⟨ν, ?_⟩
  change eval T_K a.val
    ((1 : ℝ) ⊗ₜ[ℤ] cocharacterLattice.baseChange b T (ν ≫ f)) ≠ 0
  rw [cocharacterLattice.baseChange_comp, eval_tmul, one_mul, latticePairing_map, hν]
  exact_mod_cast hpair

/-- A root nonzero on the supplied split torus has nonzero derivative on a
common fixed vector of the actual reduced coefficient action. -/
theorem exists_galois_fixed_direction_of_root_restrict_ne_zero
    (a : relativeRoots (T := T_K) i_K)
    (ha : characterRestrict (CommGroupScheme.groupHom f_K) a.val ≠ 0) :
    ∃ v : TranslationSpace (S := T_K) i_K,
      (∀ σ : K ≃ₐ[k] K, galoisTranslationAction k K i σ v = v) ∧
        rootForm (S := T_K) i_K a v ≠ 0 := by
  obtain ⟨ν, hν⟩ := exists_baseChangeCocharacterDirection_rootForm_ne_zero
    k K i hS f a ha
  exact ⟨baseChangeCocharacterDirection k K i (ν ≫ f),
    fun σ => galoisTranslationAction_baseChangeCocharacterDirection k K i σ _, hν⟩

namespace KPApartmentData

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left] {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i) ω)

/-- Nonzero restriction of each incident derivative root supplies the full
direction hypothesis for this same apartment. -/
theorem hasIncidentGaloisDirections_of_root_restrict_ne_zero (p : D.Apartment)
    (hroot : ∀ a : relativeRoots (T := T_K) i_K,
      (∃ ψ ∈ D.affineRoots, ψ p = 0 ∧ ψ.linear = rootForm (S := T_K) i_K a) →
        characterRestrict (CommGroupScheme.groupHom f_K) a.val ≠ 0) :
    HasIncidentGaloisDirections k K i D p := by
  intro ψ hψ hp
  have hmem := hψ
  obtain ⟨a, hlin, _⟩ := hmem
  obtain ⟨v, hv, hne⟩ := exists_galois_fixed_direction_of_root_restrict_ne_zero
    k K i hS f a (hroot a ⟨ψ, hψ, hp, hlin⟩)
  exact ⟨v, hv, by simpa only [hlin] using hne⟩

end KPApartmentData

end Langlands.Geometry.Building
