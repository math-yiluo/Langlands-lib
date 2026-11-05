import Langlands.Geometry.Building.RootReflectionConjugation
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence

/-! # The actual normalizer action on affine roots without AS 5 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

section DoubleRoots

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- Conjugation preserves the actual double-root subgroup, including the convention
that it is trivial when the double is not a root. -/
theorem conj_doubleRootGroupPoints (n : normalizerPoints i) (a : characterLattice S) :
    (doubleRootGroupPoints i a).map (MulAut.conj (n : rationalPoints G)).toMonoidHom =
      doubleRootGroupPoints i (weylAction i n a) := by
  classical
  have h2 : 2 • weylAction i n a ∈ relativeRoots i ↔ 2 • a ∈ relativeRoots i := by
    rw [← map_nsmul]
    exact weylAction_mem_roots_iff n (2 • a)
  by_cases ha : 2 • a ∈ relativeRoots i
  · rw [doubleRootGroupPoints, ite_eq_left ha, doubleRootGroupPoints,
      ite_eq_left (h2.mpr ha), conj_rootGroupPoints, map_nsmul]
  · rw [doubleRootGroupPoints, ite_eq_right ha, doubleRootGroupPoints,
      ite_eq_right (fun hroot => ha (h2.mp hroot)), Subgroup.map_bot]

end DoubleRoots

namespace KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The derivative of the transported functional is the Weyl transform of its root. -/
theorem conjugateAffineFunctional_linear_eq_rootForm (n : normalizerPoints i)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} {a : relativeRoots i}
    (hψ : ψ.linear = rootForm i a) :
    (D.conjugateAffineFunctional n ψ).linear =
      rootForm i ⟨weylAction i n a, weylAction_mapsTo_relativeRoots i n a.property⟩ := by
  apply LinearMap.ext
  intro v
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  change ψ.linear (translationAction i n⁻¹ (Submodule.Quotient.mk w)) = _
  rw [hψ, translationAction_mk, rootForm_mk, rootForm_mk,
    eval_normalizer_smul, inv_inv]

/-- The noncontainment test defining ordinary affine roots is invariant under
actual normalizer conjugation. -/
theorem affineRootGroup_subset_mul_conjugate_iff (n : normalizerPoints i)
    (a : characterLattice S) (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    (D.affineRootGroup (weylAction i n a) (D.conjugateAffineFunctional n ψ) :
        Set (rationalPoints G)) ⊆
      (D.affineRootGroupPlus (weylAction i n a) (D.conjugateAffineFunctional n ψ) :
        Set (rationalPoints G)) *
        (doubleRootGroupPoints i (weylAction i n a) : Set (rationalPoints G)) ↔
    (D.affineRootGroup a ψ : Set (rationalPoints G)) ⊆
      (D.affineRootGroupPlus a ψ : Set (rationalPoints G)) *
        (doubleRootGroupPoints i a : Set (rationalPoints G)) := by
  conv_rhs =>
    rw [← Set.image_subset_image_iff (MulAut.conj (n : rationalPoints G)).injective,
      Set.image_mul]
  change _ ↔
    ((D.affineRootGroup a ψ).map (MulAut.conj (n : rationalPoints G)).toMonoidHom :
        Set (rationalPoints G)) ⊆
      ((D.affineRootGroupPlus a ψ).map
          (MulAut.conj (n : rationalPoints G)).toMonoidHom : Set (rationalPoints G)) *
        ((doubleRootGroupPoints i a).map
          (MulAut.conj (n : rationalPoints G)).toMonoidHom : Set (rationalPoints G))
  rw [D.conj_affineRootGroup, D.conj_affineRootGroupPlus, conj_doubleRootGroupPoints]

/-- Actual normalizer conjugation takes each ordinary affine root to an ordinary
affine root. No apartment-axiom predicate is needed. -/
theorem conjugateAffineFunctional_mem_affineRoots (n : normalizerPoints i)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.affineRoots) :
    D.conjugateAffineFunctional n ψ ∈ D.affineRoots := by
  obtain ⟨a, ha, hnot⟩ := hψ
  refine ⟨⟨weylAction i n a, weylAction_mapsTo_relativeRoots i n a.property⟩,
    D.conjugateAffineFunctional_linear_eq_rootForm n ha, ?_⟩
  exact fun hs => hnot ((D.affineRootGroup_subset_mul_conjugate_iff n a ψ).mp hs)

/-- Ordinary affine-root membership is preserved and reflected. -/
theorem conjugateAffineFunctional_mem_affineRoots_iff (n : normalizerPoints i)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    D.conjugateAffineFunctional n ψ ∈ D.affineRoots ↔ ψ ∈ D.affineRoots := by
  constructor
  · intro hψ
    simpa only [D.conjugateAffineFunctional_inv] using
      D.conjugateAffineFunctional_mem_affineRoots n⁻¹ hψ
  · exact D.conjugateAffineFunctional_mem_affineRoots n

/-- The actual apartment action preserves ordinary affine roots, without AS 5. -/
theorem normalizerAffineEquiv_mem_rootStabilizer (n : normalizerPoints i) :
    D.normalizerAffineEquiv n ∈ AffineRootSystem.rootStabilizer D.affineRoots := by
  intro ψ
  simpa only [conjugateAffineFunctional, inv_inv] using
    D.conjugateAffineFunctional_mem_affineRoots_iff n⁻¹ ψ

/-- The actual normalizer action, with its codomain restricted to the stabilizer
of the affine roots. This construction requires no apartment axioms. -/
def normalizerAffineRootAction :
    normalizerPoints i →* AffineRootSystem.rootStabilizer D.affineRoots where
  toFun n := ⟨D.normalizerAffineEquiv n, D.normalizerAffineEquiv_mem_rootStabilizer n⟩
  map_one' := Subtype.ext (map_one D.normalizerAffineEquiv)
  map_mul' n m := Subtype.ext (map_mul D.normalizerAffineEquiv n m)

@[simp]
theorem normalizerAffineRootAction_coe (n : normalizerPoints i) :
    (D.normalizerAffineRootAction n : D.Apartment ≃ᵃ[ℝ] D.Apartment) =
      D.normalizerAffineEquiv n := rfl

/-- The whole actual action has root-preserving image. -/
theorem normalizerAffineEquiv_range_le_rootStabilizer :
    D.normalizerAffineEquiv.range ≤ AffineRootSystem.rootStabilizer D.affineRoots := by
  rintro _ ⟨n, rfl⟩
  exact D.normalizerAffineEquiv_mem_rootStabilizer n

end KPApartmentData

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    {a : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- The coroot of any actual opposite pair preserves the affine roots. Neither
AS 5 nor an affine-root-system hypothesis is needed here. -/
theorem isCoroot_reflectionCoroot_without_apartment_axioms
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p) :
    AffineRootSystem.IsCoroot B.affineRoots (B.reflectionFunctional a g)
      (B.reflectionCoroot hg hg1 hp) := by
  refine ⟨B.rootForm_reflectionCoroot hg hg1 hp, fun f hf => ?_⟩
  have hm := B.apartment.normalizerAffineEquiv_mem_rootStabilizer (B.reflectionElement hp)
  rw [B.normalizerAffineEquiv_reflectionElement hg hg1 hp] at hm
  have hf' := (hm f).2 hf
  change f.comp (AffineRootSystem.affineReflection (B.reflectionFunctional a g)
    (B.rootForm_reflectionCoroot hg hg1 hp) : B.Apartment →ᵃ[ℝ] B.Apartment) ∈
      B.affineRoots at hf'
  exact (AffineRootSystem.comp_affineReflection (B.reflectionFunctional a g)
    (B.rootForm_reflectionCoroot hg hg1 hp) f) ▸ hf'

/-- An explicit affine-root-system hypothesis suffices to identify every coroot
of an actual point functional with the integral coroot of its opposite pair. -/
theorem reflectionCoroot_eq_of_isCoroot_of_isAffineRootSystem
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p)
    {v : TranslationSpace B.i}
    (hv : AffineRootSystem.IsCoroot B.affineRoots (B.reflectionFunctional a g) v) :
    B.reflectionCoroot hg hg1 hp = v :=
  hΨ.isCoroot_unique (B.isCoroot_reflectionCoroot_without_apartment_axioms hg hg1 hp) hv

/-- Any system coroot for the point functional gives the actual reflection action,
with only the affine-root-system hypothesis. -/
theorem normalizerAffineEquiv_reflectionElement_eq_of_isAffineRootSystem
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p)
    {v : TranslationSpace B.i}
    (hv : AffineRootSystem.IsCoroot B.affineRoots (B.reflectionFunctional a g) v) :
    B.apartment.normalizerAffineEquiv (B.reflectionElement hp) =
      AffineRootSystem.affineReflection (B.reflectionFunctional a g) hv.1 := by
  have hv' := B.reflectionCoroot_eq_of_isCoroot_of_isAffineRootSystem hΨ hg hg1 hp hv
  simpa only [hv'] using B.normalizerAffineEquiv_reflectionElement hg hg1 hp

/-- Existence of actual opposite pairs realizes every affine Weyl generator.
This lower inclusion assumes only that the actual affine roots form a system. -/
theorem affineWeylGroup_le_reflectionNormalizer_map_of_isAffineRootSystem
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) :
    AffineRootSystem.affineWeylGroup B.affineRoots ≤
      B.reflectionNormalizer.map B.apartment.normalizerAffineEquiv := by
  refine (Subgroup.closure_le _).2 ?_
  rintro e ⟨ψ, hψ, v, hv, rfl⟩
  have hψ' := B.apartment.affineRoots_subset_extendedAffineRoots hψ
  rw [← B.reflectionAffineRoots_eq] at hψ'
  obtain ⟨a, g, hg, hg1, rfl⟩ := hψ'
  obtain ⟨p, hp⟩ := hF a a.property g hg hg1
  refine ⟨B.reflectionElement hp,
    B.reflectionElement_mem_reflectionNormalizer hg hg1 hp, ?_⟩
  exact B.normalizerAffineEquiv_reflectionElement_eq_of_isAffineRootSystem
    hΨ hg hg1 hp hv

/-- In particular, the actual normalizer image contains the affine Weyl group,
without any AS 5 premise. -/
theorem affineWeylGroup_le_normalizerAffineEquiv_range_of_isAffineRootSystem
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) :
    AffineRootSystem.affineWeylGroup B.affineRoots ≤ B.apartment.normalizerAffineEquiv.range := by
  intro w hw
  obtain ⟨n, _, hn⟩ := B.affineWeylGroup_le_reflectionNormalizer_map_of_isAffineRootSystem
    hΨ hF hw
  exact ⟨n, hn⟩

end ValuationBuildingData

end Langlands.Geometry.Building
