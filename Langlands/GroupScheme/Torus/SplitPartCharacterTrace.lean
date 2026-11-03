import Langlands.GroupScheme.Absolute.CocharacterDescentLattice
import Langlands.GroupScheme.Torus.CocharacterDetection
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Rational.TorusSplitPart

/-! # Galois traces of characters vanishing on a split part -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

section Detection

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Rational cocharacters separate rational characters of an affine finite-type torus. -/
theorem IsTorus.latticePairing_injective
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hT : IsTorus T.toGrp) : Function.Injective (latticePairing T) := by
  rw [injective_iff_map_eq_zero]
  intro χ hχ
  by_contra hne
  obtain ⟨φ, hφ⟩ :=
    CocharacterDetection.exists_gm_characterRestrict_ne_zero_of_isTorus hT hne
  apply hφ
  apply (gmEndEquiv k).injective
  change latticePairing T χ (Additive.ofMul φ) = gmEndEquiv k 0
  rw [hχ, map_zero]
  rfl

end Detection

namespace CharacterAveraging

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [Fintype (K ≃ₐ[k] K)]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "T_K" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T

/-- The integral Galois orbit sum of an actual character over the extension field. -/
def galoisOrbitSum (χ : characterLattice T_K) : characterLattice T_K :=
  CocharacterAveraging.orbitSum (characterLattice.galoisRepresentation k K T) χ

/-- The character orbit sum is fixed by every automorphism of the extension. -/
theorem galoisOrbitSum_fixed (χ : characterLattice T_K) (σ : K ≃ₐ[k] K) :
    characterLattice.galoisRepresentation k K T σ (galoisOrbitSum k K T χ) =
      galoisOrbitSum k K T χ :=
  CocharacterAveraging.orbitSum_fixed _ _ _

/-- Under the invariant pairing, the character orbit sum is adjoint to the
cocharacter orbit sum. -/
theorem latticePairing_galoisOrbitSum (χ : characterLattice T_K)
    (ν : cocharacterLattice T_K) :
    latticePairing T_K (galoisOrbitSum k K T χ) ν =
      latticePairing T_K χ (CocharacterAveraging.galoisOrbitSum k K T ν) := by
  classical
  simp only [galoisOrbitSum, CocharacterAveraging.galoisOrbitSum,
    CocharacterAveraging.orbitSum, map_sum, LinearMap.sum_apply]
  symm
  calc
    ∑ σ : K ≃ₐ[k] K, latticePairing T_K χ
        (cocharacterLattice.galoisRepresentation k K T σ ν) =
      ∑ σ : K ≃ₐ[k] K, latticePairing T_K
        (characterLattice.galoisRepresentation k K T σ⁻¹ χ) ν := by
          apply Finset.sum_congr rfl
          intro σ _
          exact latticePairing_galoisRepresentation_right k K T σ χ ν
    _ = ∑ σ : K ≃ₐ[k] K, latticePairing T_K
        (characterLattice.galoisRepresentation k K T σ χ) ν :=
      Fintype.sum_equiv (Equiv.inv _) _ _ (fun _ => rfl)

end CharacterAveraging

section SplitPart

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : A ⟶ T} (hi : IsLargestSplitSubtorus (CommGroupScheme.groupHom i))

local notation "T_K" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T

include hi

/-- A character trivial on the extended split part annihilates every cocharacter
defined over the original field. -/
theorem IsLargestSplitSubtorus.latticePairing_baseChange_eq_zero
    (χ : characterLattice T_K)
    (hχ : (CommGroupScheme.baseChange (algebraBaseMap k K)).map i ≫ χ = 0)
    (ν : cocharacterLattice T) :
    latticePairing T_K χ (cocharacterLattice.baseChange (algebraBaseMap k K) T ν) = 0 := by
  obtain ⟨g, hg, _⟩ := hi.2 (Gm (Spec (CommRingCat.of k)))
    (CommGroupScheme.groupHom ν) isSplitTorus_gm
  let g' : Gm (Spec (CommRingCat.of k)) ⟶ A := Additive.ofMul g
  have he : g' ≫ i = ν := congrArg Additive.ofMul hg
  change gmEndEquiv K (((Gm.commBaseChangeIso (algebraBaseMap k K)).inv ≫
    (CommGroupScheme.baseChange (algebraBaseMap k K)).map ν) ≫ χ) = 0
  rw [← he, Functor.map_comp, Category.assoc, Category.assoc, hχ,
    Limits.comp_zero, Limits.comp_zero, map_zero]

/-- A character vanishing on the split part has zero finite-Galois trace, as an
actual character of the extended torus. -/
theorem IsLargestSplitSubtorus.galoisOrbitSum_character_eq_zero
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hT : IsTorus T.toGrp) (χ : characterLattice T_K)
    (hχ : (CommGroupScheme.baseChange (algebraBaseMap k K)).map i ≫ χ = 0) :
    CharacterAveraging.galoisOrbitSum k K T χ = 0 := by
  have : IsAffineHom (T_K).toGrp.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd T.X.hom (algebraBaseMap k K))
    infer_instance
  have : LocallyOfFiniteType (T_K).toGrp.X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd T.X.hom (algebraBaseMap k K))
    infer_instance
  apply (hT.baseChange (K := K)).latticePairing_injective
  rw [map_zero]
  apply LinearMap.ext
  intro ν
  change latticePairing T_K (CharacterAveraging.galoisOrbitSum k K T χ) ν = 0
  rw [CharacterAveraging.latticePairing_galoisOrbitSum,
    ← CocharacterAveraging.baseChange_descendedOrbitSum]
  exact hi.latticePairing_baseChange_eq_zero K χ hχ _

end SplitPart

end Langlands.GroupScheme
