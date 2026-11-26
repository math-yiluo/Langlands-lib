import Langlands.BruhatTits.IntegralModels.UnramifiedModelFamily
import Langlands.BruhatTits.IntegralModels.GeneralMorphismAxiomsUnramified
import Langlands.BruhatTits.IntegralModels.SimplyConnectedZeroPoints
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusClauseStatement
import Langlands.Geometry.Building.UnramifiedApartmentDescentStatement
import Langlands.Geometry.Building.UnramifiedOneFixerClosureStatement
import Langlands.Geometry.Building.UnramifiedZeroFixerAffineRootStatement
import Langlands.Geometry.Building.UnramifiedStabilizerDescent
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof

/-! # KP Axiom 4.1.20 for a model family built over the maximal unramified extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Geometry.Building LocalGalois.Separable GaloisPointComparison IntegralModel

section Generic

/-- The identity homomorphism acts trivially on rational points. -/
theorem rationalPoints_map_id_apply {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))} (y : rationalPoints H) :
    rationalPoints.map (𝟙 H) y = y := by
  simp [rationalPoints.map_apply]

/-- Two composites of generic-identity morphisms of integral models agree. -/
theorem comp_hom_eq_of_generic {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] {G : GroupScheme (Spec (CommRingCat.of K))}
    {M₁ M₂ M₃ M₄ : IntegralModel R K G}
    (φ₁ : M₁.Hom M₂ (𝟙 G)) (φ₂ : M₂.Hom M₄ (𝟙 G))
    (ψ₁ : M₁.Hom M₃ (𝟙 G)) (ψ₂ : M₃.Hom M₄ (𝟙 G)) :
    φ₁.hom ≫ φ₂.hom = ψ₁.hom ≫ ψ₂.hom := by
  apply hom_eq_of_generic
  apply (cancel_mono M₄.genericIso.hom).mp
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Category.assoc, φ₂.generic_comm, ψ₂.generic_comm, Category.comp_id, Category.comp_id,
    φ₁.generic_comm, ψ₁.generic_comm]

/-- A generic-identity morphism with a generic-identity morphism back is an isomorphism. -/
theorem isIso_hom_of_hom {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] {G : GroupScheme (Spec (CommRingCat.of K))}
    {M N : IntegralModel R K G} (φ : M.Hom N (𝟙 G)) (ψ : N.Hom M (𝟙 G)) : IsIso φ.hom := by
  have h : IsIso (IntegralModel.Iso.ofHoms (f := CategoryTheory.Iso.refl G) φ ψ).iso.hom :=
    inferInstance
  exact h

/-- Intersections with a smaller subgroup inherit inclusions of intersections. -/
theorem inf_le_inf_of_le_of_inf_le {H : Type*} [Group H] {E G₁ X Y : Subgroup H}
    (hE : E ≤ G₁) (h : G₁ ⊓ X ≤ G₁ ⊓ Y) : E ⊓ X ≤ E ⊓ Y :=
  fun _ hx => ⟨hx.1, (h ⟨hE hx.1, hx.2⟩).2⟩

/-- Intersections with a smaller subgroup inherit equalities of intersections. -/
theorem inf_eq_inf_of_le_of_inf_eq {H : Type*} [Group H] {E G₁ X Y : Subgroup H}
    (hE : E ≤ G₁) (h : G₁ ⊓ X = G₁ ⊓ Y) : E ⊓ X = E ⊓ Y :=
  le_antisymm (inf_le_inf_of_le_of_inf_le hE h.le) (inf_le_inf_of_le_of_inf_le hE h.ge)

end Generic

section Facets

open AffineRootSystem

variable {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- An affine root has the same sign at two points of one facet. -/
theorem nonneg_iff_of_mem_facet {x y : A} (h : y ∈ facet Ψ x) {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ Ψ) : 0 ≤ ψ x ↔ 0 ≤ ψ y := by
  rw [← sign_nonneg_iff, (mem_facet.mp h) ψ hψ, sign_nonneg_iff]

/-- Two nonempty subsets of one facet have the same nonnegative affine roots. -/
theorem forall_nonneg_iff_of_subset_facet {x : A} {Y Y' : Set A} (hY : Y ⊆ facet Ψ x)
    (hY' : Y' ⊆ facet Ψ x) (hne : Y.Nonempty) (hne' : Y'.Nonempty) (ψ : A →ᵃ[ℝ] ℝ)
    (hψ : ψ ∈ Ψ) : (∀ y ∈ Y, 0 ≤ ψ y) ↔ (∀ y ∈ Y', 0 ≤ ψ y) := by
  have key : ∀ Z : Set A, Z ⊆ facet Ψ x → Z.Nonempty → ((∀ y ∈ Z, 0 ≤ ψ y) ↔ 0 ≤ ψ x) := by
    intro Z hZ hne
    constructor
    · intro h
      obtain ⟨z, hz⟩ := hne
      exact (nonneg_iff_of_mem_facet (hZ hz) hψ).2 (h z hz)
    · intro h z hz
      exact (nonneg_iff_of_mem_facet (hZ hz) hψ).1 h
  rw [key Y hY hne, key Y' hY' hne']

end Facets

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

section Presentations

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B : ValuationBuildingData G}

/-- Every index of a model family has a presentation in a translated apartment chart. -/
theorem BuildingModelIndex.exists_eq_translatedApartmentMap (Ω : BuildingModelIndex B) :
    ∃ (g : rationalPoints G) (Ωa : Set B.Apartment),
      Ω.val = B.translatedApartmentMap g '' Ωa := by
  rcases Ω.property with ⟨g, Ωa, -, -, h⟩ | ⟨g, Fa, -, h⟩
  · exact ⟨g, Ωa, h⟩
  · exact ⟨g, Fa, h⟩

/-- Every apartment presentation of an index is nonempty. -/
theorem BuildingModelIndex.nonempty_of_eq_translatedApartmentMap {Ω : BuildingModelIndex B}
    {g : rationalPoints G} {Ωa : Set B.Apartment}
    (h : Ω.val = B.translatedApartmentMap g '' Ωa) : Ωa.Nonempty := by
  have hne := Ω.nonempty
  rw [h] at hne
  exact hne.of_image

variable {C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G)}

/-- Pointwise fixers over the maximal unramified extension are antitone. -/
theorem unramifiedPointwiseFixer_anti {Y Y' : Set C.ReducedBuilding} (h : Y ⊆ Y') :
    C.pointwiseFixer Y' ≤ C.pointwiseFixer Y := by
  intro x hx
  rw [IntegerValuationBuildingData.pointwiseFixer, KPApartmentData.mem_pointwiseFixer] at hx ⊢
  exact fun y hy => hx y (h hy)

variable (e : B.ReducedBuilding → C.ReducedBuilding) (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (he_smul : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (he_apt : ∀ w : B.Apartment, e (B.apartmentMap w) = C.apartmentMap (a w))
  (hbdd : ∀ (Ω : BuildingModelIndex B) (g : rationalPoints G) (Ωa : Set B.Apartment),
    Ω.val = B.translatedApartmentMap g '' Ωa → B.IsBoundedSubset Ωa)

include he_smul he_apt hbdd in
/-- The image of an index in the building over the maximal unramified extension is a translate
of a nonempty bounded subset of the apartment of `C`. -/
theorem exists_unramified_presentation (Ω : BuildingModelIndex B) :
    ∃ (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (Ya : Set C.Apartment),
      Ya.Nonempty ∧ (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ya)) ∧
        e '' Ω.val = (fun x => g • C.apartmentMap x) '' Ya := by
  obtain ⟨g, Ωa, h⟩ := Ω.exists_eq_translatedApartmentMap
  refine ⟨rationalExtend F (inertiaFixedField F) G g, a '' Ωa,
    (BuildingModelIndex.nonempty_of_eq_translatedApartmentMap h).image a,
    bddAbove_image_image a (hbdd Ω g Ωa h), ?_⟩
  rw [h, image_translatedApartmentMap e a he_smul he_apt]

include he_smul he_apt hbdd in
set_option maxHeartbeats 1000000 in
/-- **Inclusion of one-fixers along a required morphism.** Granting the closure statement for
`G(K)^1`, the one-fixer of the larger index lies in the one-fixer of the smaller one. -/
theorem one_inf_pointwiseFixer_le (hclos : UnramifiedOneFixerClosureStatement.{u})
    (hface : ∀ Fa Fa' : Set B.Apartment,
      AffineRootSystem.IsFaceOf B.affineRoots Fa Fa' → Fa ⊆ apartmentClosure B Fa')
    {Ω Ω' : BuildingModelIndex B} (h : ModelMorphismRequired B Ω Ω') :
    characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓ C.pointwiseFixer (e '' Ω'.val) ≤
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓ C.pointwiseFixer (e '' Ω.val) := by
  obtain ⟨g, Ωa, Ωa', hΩ, hΩ', hcl⟩ :=
    BuildingModelFamily.exists_chart_of_modelMorphismRequired hface h
  have e1 : e '' Ω.val = (fun x => rationalExtend F (inertiaFixedField F) G g •
      C.apartmentMap x) '' (a '' Ωa) := by
    rw [hΩ]
    exact image_translatedApartmentMap e a he_smul he_apt g Ωa
  have e2 : e '' Ω'.val = (fun x => rationalExtend F (inertiaFixedField F) G g •
      C.apartmentMap x) '' (a '' Ωa') := by
    rw [hΩ']
    exact image_translatedApartmentMap e a he_smul he_apt g Ωa'
  have hsub : (fun x => rationalExtend F (inertiaFixedField F) G g •
        C.apartmentMap x) '' (a '' Ωa) ⊆
      (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) ''
        @closure C.Apartment (unramifiedApartmentTopology C) (a '' Ωa') :=
    Set.image_mono (image_subset_closure_image a hcl)
  have hc := hclos F G C (rationalExtend F (inertiaFixedField F) G g) (a '' Ωa')
    ((BuildingModelIndex.nonempty_of_eq_translatedApartmentMap hΩ').image a)
    (bddAbove_image_image a (hbdd Ω' g Ωa' hΩ'))
  rw [e1, e2, hc]
  exact inf_le_inf_left _ (unramifiedPointwiseFixer_anti hsub)

end Presentations

/-- `G(K)^0` lies in `G(K)^1`, for the integer-normalized valuation of the maximal unramified
extension. -/
theorem UnramifiedZeroDatum.zeroPoints_le_unramifiedCharacterValuationKernel
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G)) :
    E.zeroPoints ≤ characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) G) := by
  rw [characterValuationKernel_eq_of_isEquiv (MaximalUnramified.valuation_isEquiv F)]
  exact E.zeroPoints_le_characterValuationKernel

/-- A generic-identity morphism between models over `𝒪[F]` exists as soon as the integral
points of the unramified base changes are included (KP Corollary 2.10.10). -/
theorem nonempty_hom_of_unramified_le (hext : UnramifiedSmoothHomExtensionStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of F))} (M N : IntegralModel ↥𝒪[F] F G)
    (hM : M.IsSmooth)
    (h : M.baseChangeUnramified.integralPoints ≤ N.baseChangeUnramified.integralPoints) :
    Nonempty (M.Hom N (𝟙 G)) := by
  refine hext F G G (𝟙 G) M N hM fun x hx => ?_
  rw [CategoryTheory.Functor.map_id, rationalPoints_map_id_apply]
  exact h hx

/-- Neutral models with equal unramified integral points are isomorphic over the identity. -/
theorem exists_isIso_neutral_of_unramified_eq (hext : UnramifiedSmoothHomExtensionStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of F))} (D D' : RelativeComponentModelData ↥𝒪[F] F G)
    (h : D.neutral.baseChangeUnramified.integralPoints =
      D'.neutral.baseChangeUnramified.integralPoints) :
    ∃ φ : D.neutral.Hom D'.neutral (𝟙 G), IsIso φ.hom := by
  obtain ⟨φ⟩ := nonempty_hom_of_unramified_le hext D.neutral D'.neutral D.neutral_smooth h.le
  obtain ⟨ψ⟩ := nonempty_hom_of_unramified_le hext D'.neutral D.neutral D'.neutral_smooth h.ge
  exact ⟨φ, isIso_hom_of_hom φ ψ⟩

end Langlands.BruhatTits.IntegralModels
