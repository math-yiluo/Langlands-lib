import Langlands.GroupScheme.Rational.CentralCocharacterDescent

/-! # Positive central cocharacters and actual split components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Galois

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Fintype (K ≃ₐ[k] K)]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "b" => algebraBaseMap k K
local notation "T_K" => Functor.obj (CommGroupScheme.baseChange b) T

namespace CocharacterAveraging

/-- Strict positivity on a Galois-stable character family is preserved by
the integral Galois orbit sum. -/
theorem latticePairing_galoisOrbitSum_pos
    (Φ : Set (characterLattice T_K))
    (hΦ : ∀ (σ : K ≃ₐ[k] K) (χ : characterLattice T_K),
      χ ∈ Φ → characterLattice.galoisRepresentation k K T σ χ ∈ Φ)
    (ν : cocharacterLattice T_K)
    (hpos : ∀ χ ∈ Φ, 0 < latticePairing T_K χ ν)
    (χ : characterLattice T_K) (hχ : χ ∈ Φ) :
    0 < latticePairing T_K χ (galoisOrbitSum k K T ν) := by
  classical
  change 0 < latticePairing T_K χ
    (∑ σ : K ≃ₐ[k] K, cocharacterLattice.galoisRepresentation k K T σ ν)
  rw [map_sum]
  apply Finset.sum_pos
  · intro σ _
    rw [latticePairing_galoisRepresentation_right]
    exact hpos _ (hΦ σ⁻¹ χ hχ)
  · exact Finset.univ_nonempty

variable [FiniteDimensional k K] [IsGalois k K] [IsAffineHom T.X.hom]

/-- Extending the actual descended cocharacter retains strict positivity
on the original Galois-stable character family. -/
theorem latticePairing_baseChange_descendedOrbitSum_pos
    (Φ : Set (characterLattice T_K))
    (hΦ : ∀ (σ : K ≃ₐ[k] K) (χ : characterLattice T_K),
      χ ∈ Φ → characterLattice.galoisRepresentation k K T σ χ ∈ Φ)
    (ν : cocharacterLattice T_K)
    (hpos : ∀ χ ∈ Φ, 0 < latticePairing T_K χ ν)
    (χ : characterLattice T_K) (hχ : χ ∈ Φ) :
    0 < latticePairing T_K χ
      (cocharacterLattice.baseChange b T (descendedOrbitSum k K T ν)) := by
  rw [baseChange_descendedOrbitSum]
  exact latticePairing_galoisOrbitSum_pos k K T Φ hΦ ν hpos χ hχ

end CocharacterAveraging

variable [FiniteDimensional k K] [IsGalois k K] [IsAffineHom T.X.hom]
    {M : GroupScheme (Spec (CommRingCat.of k))} (t : T.toGrp ⟶ M)

/-- A central positive direction over a finite Galois extension gives an
actual central cocharacter over the original field, positive after extension. -/
theorem exists_centralCocharacter_positive_of_galois_stable
    (Φ : Set (characterLattice T_K))
    (hΦ : ∀ (σ : K ≃ₐ[k] K) (χ : characterLattice T_K),
      χ ∈ Φ → characterLattice.galoisRepresentation k K T σ χ ∈ Φ)
    (ν : cocharacterLattice T_K)
    (hν : ν ∈ centralCocharacters ((GroupScheme.baseChange b).map t))
    (hpos : ∀ χ ∈ Φ, 0 < latticePairing T_K χ ν) :
    ∃ νc : cocharacterLattice T, νc ∈ centralCocharacters t ∧
      ∀ χ ∈ Φ, 0 < latticePairing T_K χ (cocharacterLattice.baseChange b T νc) :=
  ⟨CocharacterAveraging.descendedOrbitSum k K T ν,
    centralCocharacters_descendedOrbitSum_mem k K T t ν hν,
    CocharacterAveraging.latticePairing_baseChange_descendedOrbitSum_pos
      k K T Φ hΦ ν hpos⟩

section SplitComponent

variable [IsAffineHom M.X.hom] [Mono t.hom.hom.left]
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ M} (ha : IsSplitComponent a)
    (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ t = a)

include ha hf in
/-- The positive central orbit sum factors integrally through the specified
split component, retaining its lift into the original torus. -/
theorem IsSplitComponent.exists_positiveCocharacter_factor
    (Φ : Set (characterLattice T_K))
    (hΦ : ∀ (σ : K ≃ₐ[k] K) (χ : characterLattice T_K),
      χ ∈ Φ → characterLattice.galoisRepresentation k K T σ χ ∈ Φ)
    (ν : cocharacterLattice T_K)
    (hν : ν ∈ centralCocharacters ((GroupScheme.baseChange b).map t))
    (hpos : ∀ χ ∈ Φ, 0 < latticePairing T_K χ ν) :
    ∃ ζ : cocharacterLattice A,
      RealTorusSpace.cocharacterMapInt f ζ =
        CocharacterAveraging.descendedOrbitSum k K T ν ∧
      ∀ χ ∈ Φ, 0 < latticePairing T_K χ
        (cocharacterLattice.baseChange b T (RealTorusSpace.cocharacterMapInt f ζ)) := by
  have hdesc := centralCocharacters_descendedOrbitSum_mem k K T t ν hν
  rw [← ha.range_cocharacterMapInt_eq_centralCocharacters f hf] at hdesc
  obtain ⟨ζ, hζ⟩ := hdesc
  refine ⟨ζ, hζ, ?_⟩
  intro χ hχ
  rw [hζ]
  exact CocharacterAveraging.latticePairing_baseChange_descendedOrbitSum_pos
    k K T Φ hΦ ν hpos χ hχ

include ha hf in
/-- A chosen actual integral factor of the positive central orbit sum through
the specified split component. -/
def IsSplitComponent.positiveCocharacterFactor
    (Φ : Set (characterLattice T_K))
    (hΦ : ∀ (σ : K ≃ₐ[k] K) (χ : characterLattice T_K),
      χ ∈ Φ → characterLattice.galoisRepresentation k K T σ χ ∈ Φ)
    (ν : cocharacterLattice T_K)
    (hν : ν ∈ centralCocharacters ((GroupScheme.baseChange b).map t))
    (hpos : ∀ χ ∈ Φ, 0 < latticePairing T_K χ ν) :
    cocharacterLattice A :=
  Classical.choose (ha.exists_positiveCocharacter_factor k K T t f hf Φ hΦ ν hν hpos)

set_option backward.isDefEq.respectTransparency true in
include ha hf in
/-- The chosen factor maps to the actual descended orbit sum, and its
extended image pairs strictly positively with the original character family. -/
theorem IsSplitComponent.positiveCocharacterFactor_spec
    (Φ : Set (characterLattice T_K))
    (hΦ : ∀ (σ : K ≃ₐ[k] K) (χ : characterLattice T_K),
      χ ∈ Φ → characterLattice.galoisRepresentation k K T σ χ ∈ Φ)
    (ν : cocharacterLattice T_K)
    (hν : ν ∈ centralCocharacters ((GroupScheme.baseChange b).map t))
    (hpos : ∀ χ ∈ Φ, 0 < latticePairing T_K χ ν) :
    let ζ : cocharacterLattice A := @IsSplitComponent.positiveCocharacterFactor
      k K _ _ _ ‹Fintype (K ≃ₐ[k] K)› T ‹FiniteDimensional k K› ‹IsGalois k K›
      ‹IsAffineHom T.X.hom› M t ‹IsAffineHom M.X.hom› ‹Mono t.hom.hom.left›
      A a ha f hf Φ hΦ ν (by assumption) (by assumption)
    RealTorusSpace.cocharacterMapInt f ζ =
      CocharacterAveraging.descendedOrbitSum k K T ν ∧
    ∀ χ ∈ Φ, 0 < latticePairing T_K χ
      (cocharacterLattice.baseChange b T (RealTorusSpace.cocharacterMapInt f ζ)) :=
  Classical.choose_spec
    (ha.exists_positiveCocharacter_factor k K T t f hf Φ hΦ ν hν hpos)

include ha hf in
/-- Every character of a stable positive family restricts nontrivially to
the extended specified split component. -/
theorem IsSplitComponent.characterRestriction_ne_zero_of_central_positive
    (Φ : Set (characterLattice T_K))
    (hΦ : ∀ (σ : K ≃ₐ[k] K) (χ : characterLattice T_K),
      χ ∈ Φ → characterLattice.galoisRepresentation k K T σ χ ∈ Φ)
    (ν : cocharacterLattice T_K)
    (hν : ν ∈ centralCocharacters ((GroupScheme.baseChange b).map t))
    (hpos : ∀ χ ∈ Φ, 0 < latticePairing T_K χ ν)
    (χ : characterLattice T_K) (hχ : χ ∈ Φ) :
    (CommGroupScheme.baseChange b).map f ≫ χ ≠ 0 := by
  intro hzero
  have hz := ha.latticePairing_centralOrbitSum_eq_zero f hf χ hzero ν hν
  have hp := CocharacterAveraging.latticePairing_galoisOrbitSum_pos
    k K T Φ hΦ ν hpos χ hχ
  omega

end SplitComponent
end Galois

end Langlands.GroupScheme
