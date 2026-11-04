import Langlands.Geometry.Building.KPCentralFactor
import Langlands.Geometry.Building.ValuationBuildingApartmentCharts
import Mathlib.Algebra.Group.Action.Prod

/-! # The canonical-dual enlarged product over supplied KP building data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The enlarged product of the same supplied reduced building and the actual central dual. -/
abbrev EnlargedBuilding : Type u := B.ReducedBuilding × CentralFactor G

/-- The enlarged base apartment, carrying the product normalizer action. -/
abbrev EnlargedApartment : Type u := B.Apartment × CentralFactor G

/-- The product map from the enlarged base apartment into the enlarged building. -/
def enlargedApartmentMap (x : B.EnlargedApartment) : B.EnlargedBuilding :=
  (B.apartmentMap x.1, x.2)

@[simp] theorem enlargedApartmentMap_fst (x : B.EnlargedApartment) :
    (B.enlargedApartmentMap x).1 = B.apartmentMap x.1 := rfl

@[simp] theorem enlargedApartmentMap_snd (x : B.EnlargedApartment) :
    (B.enlargedApartmentMap x).2 = x.2 := rfl

/-- Equivariance for the actual normalizer, using its existing reduced apartment action. -/
theorem normalizer_smul_enlargedApartmentMap (n : normalizerPoints B.i)
    (x : B.EnlargedApartment) :
    (n : rationalPoints G) • B.enlargedApartmentMap x =
      B.enlargedApartmentMap (n • x) := by
  exact Prod.ext (B.normalizer_smul_apartmentMap n x.1) rfl

/-- An injective reduced base chart gives an injective enlarged base chart. -/
theorem enlargedApartmentMap_injective (hB : Function.Injective B.apartmentMap) :
    Function.Injective B.enlargedApartmentMap := by
  intro x y hxy
  have h₁ : B.apartmentMap x.1 = B.apartmentMap y.1 :=
    congrArg (fun z : B.EnlargedBuilding => z.1) hxy
  have h₂ : x.2 = y.2 := congrArg (fun z : B.EnlargedBuilding => z.2) hxy
  exact Prod.ext (hB h₁) h₂

/-- The enlarged base apartment as the actual range of its product map. -/
def enlargedApartmentImage : Set B.EnlargedBuilding := Set.range B.enlargedApartmentMap

/-- The actual translate of the enlarged base apartment subset. -/
def enlargedTranslatedApartment (g : rationalPoints G) : Set B.EnlargedBuilding :=
  g • B.enlargedApartmentImage

/-- The translated product apartment map, using the actual product action. -/
def enlargedTranslatedApartmentMap (g : rationalPoints G) (x : B.EnlargedApartment) :
    B.EnlargedBuilding := g • B.enlargedApartmentMap x

theorem range_enlargedTranslatedApartmentMap (g : rationalPoints G) :
    Set.range (B.enlargedTranslatedApartmentMap g) = B.enlargedTranslatedApartment g := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨B.enlargedApartmentMap x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

/-- Every translated enlarged apartment has the entire central factor. -/
theorem enlargedTranslatedApartment_eq_prod (g : rationalPoints G) :
    B.enlargedTranslatedApartment g =
      (g • B.apartmentImage) ×ˢ (Set.univ : Set (CentralFactor G)) := by
  rw [← B.range_enlargedTranslatedApartmentMap, ← B.range_translatedApartmentMap]
  ext y
  constructor
  · rintro ⟨⟨x, v⟩, rfl⟩
    exact ⟨⟨x, rfl⟩, Set.mem_univ _⟩
  · rintro ⟨⟨x, hx⟩, _⟩
    refine ⟨(x, g⁻¹ • y.2), ?_⟩
    exact Prod.ext hx (smul_inv_smul g y.2)

theorem enlargedApartmentImage_eq_prod :
    B.enlargedApartmentImage =
      B.apartmentImage ×ˢ (Set.univ : Set (CentralFactor G)) := by
  simpa only [enlargedTranslatedApartment, one_smul] using
    B.enlargedTranslatedApartment_eq_prod 1

/-- Projection to the same supplied reduced building. -/
def enlargedProjection (x : B.EnlargedBuilding) : B.ReducedBuilding := x.1

/-- The zero section of the central factor. -/
def enlargedZeroSection (y : B.ReducedBuilding) : B.EnlargedBuilding := (y, 0)

@[simp] theorem enlargedProjection_smul (g : rationalPoints G) (x : B.EnlargedBuilding) :
    B.enlargedProjection (g • x) = g • B.enlargedProjection x := rfl

@[simp] theorem enlargedProjection_zeroSection (y : B.ReducedBuilding) :
    B.enlargedProjection (B.enlargedZeroSection y) = y := rfl

theorem enlargedProjection_surjective : Function.Surjective B.enlargedProjection :=
  fun y => ⟨B.enlargedZeroSection y, rfl⟩

/-- The zero section is equivariant for the actual norm-kernel subgroup. -/
theorem enlargedZeroSection_smul (g : rationalCommonNormKernel G) (y : B.ReducedBuilding) :
    B.enlargedZeroSection (g • y) = g • B.enlargedZeroSection y := by
  apply Prod.ext
  · rfl
  · exact ((CentralFactor.smul_eq_self_iff G (g : rationalPoints G) 0).mpr g.property).symm

/-- Translation by a central vector, with the reduced coordinate unchanged. -/
def centralTranslate (v : CentralFactor G) (x : B.EnlargedBuilding) : B.EnlargedBuilding :=
  (x.1, x.2 + v)

@[simp] theorem centralTranslate_zero (x : B.EnlargedBuilding) :
    B.centralTranslate 0 x = x := by
  exact Prod.ext rfl (add_zero x.2)

theorem centralTranslate_add (v w : CentralFactor G) (x : B.EnlargedBuilding) :
    B.centralTranslate (v + w) x = B.centralTranslate w (B.centralTranslate v x) := by
  exact Prod.ext rfl (add_assoc x.2 v w).symm

@[simp] theorem enlargedProjection_centralTranslate (v : CentralFactor G)
    (x : B.EnlargedBuilding) :
    B.enlargedProjection (B.centralTranslate v x) = B.enlargedProjection x := rfl

/-- Central translations commute with the actual rational-point action. -/
theorem centralTranslate_smul (v : CentralFactor G) (g : rationalPoints G)
    (x : B.EnlargedBuilding) :
    B.centralTranslate v (g • x) = g • B.centralTranslate v x := by
  apply Prod.ext
  · rfl
  · change g • x.2 + v = g • (x.2 + v)
    exact sub_add_eq_add_sub _ _ _

/-- Fibers of projection are exactly the central translation orbits. -/
theorem enlargedProjection_eq_iff (x y : B.EnlargedBuilding) :
    B.enlargedProjection x = B.enlargedProjection y ↔
      ∃ v : CentralFactor G, B.centralTranslate v x = y := by
  constructor
  · intro h
    refine ⟨y.2 - x.2, Prod.ext h ?_⟩
    change x.2 + (y.2 - x.2) = y.2
    abel
  · rintro ⟨v, rfl⟩
    rfl

/-- The full stabilizer under the actual product action. -/
def enlargedStabilizer (x : B.EnlargedBuilding) : Subgroup (rationalPoints G) :=
  MulAction.stabilizer (rationalPoints G) x

/-- The actual pointwise stabilizer of an enlarged subset. -/
def enlargedPointwiseFixer (Y : Set B.EnlargedBuilding) : Subgroup (rationalPoints G) :=
  fixingSubgroup (rationalPoints G) Y

theorem mem_enlargedStabilizer {x : B.EnlargedBuilding} {g : rationalPoints G} :
    g ∈ B.enlargedStabilizer x ↔
      g ∈ rationalCommonNormKernel G ∧ g • B.enlargedProjection x = B.enlargedProjection x := by
  change g • x = x ↔ _
  rw [Prod.ext_iff]
  change (g • x.1 = x.1 ∧ g • x.2 = x.2) ↔ _
  rw [CentralFactor.smul_eq_self_iff]
  exact and_comm

theorem enlargedStabilizer_eq_compactStabilizer (x : B.EnlargedBuilding) :
    B.enlargedStabilizer x = B.compactStabilizer (B.enlargedProjection x) := by
  ext g
  rw [B.mem_enlargedStabilizer, B.mem_compactStabilizer]

/-- A subgroup equality only; no topological compactness is asserted. -/
theorem enlargedStabilizer_eq_inf (x : B.EnlargedBuilding) :
    B.enlargedStabilizer x =
      rationalCommonNormKernel G ⊓ B.fixer (B.enlargedProjection x) := by
  ext g
  rw [B.mem_enlargedStabilizer, Subgroup.mem_inf, B.mem_fixer]

theorem enlargedStabilizer_central_independent (y : B.ReducedBuilding)
    (v w : CentralFactor G) :
    B.enlargedStabilizer (y, v) = B.enlargedStabilizer (y, w) := by
  rw [B.enlargedStabilizer_eq_compactStabilizer, B.enlargedStabilizer_eq_compactStabilizer]
  rfl

theorem mem_enlargedPointwiseFixer {Y : Set B.EnlargedBuilding} {g : rationalPoints G} :
    g ∈ B.enlargedPointwiseFixer Y ↔ ∀ x ∈ Y, g • x = x :=
  mem_fixingSubgroup_iff (rationalPoints G)

/-- Nonemptiness is necessary: one central coordinate detects the norm kernel. -/
theorem enlargedPointwiseFixer_eq_inf {Y : Set B.EnlargedBuilding} (hY : Y.Nonempty) :
    B.enlargedPointwiseFixer Y =
      rationalCommonNormKernel G ⊓ B.pointwiseFixer (B.enlargedProjection '' Y) := by
  ext g
  rw [B.mem_enlargedPointwiseFixer, Subgroup.mem_inf, B.apartment.mem_pointwiseFixer]
  constructor
  · intro hg
    obtain ⟨x, hx⟩ := hY
    refine ⟨(CentralFactor.smul_eq_self_iff G g x.2).mp (congrArg Prod.snd (hg x hx)), ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact congrArg Prod.fst (hg z hz)
  · rintro ⟨hk, hr⟩ x hx
    exact Prod.ext (hr _ ⟨x, hx, rfl⟩) ((CentralFactor.smul_eq_self_iff G g x.2).mpr hk)

theorem enlargedProjection_image_prod (Ω : Set B.ReducedBuilding) :
    B.enlargedProjection '' (Ω ×ˢ (Set.univ : Set (CentralFactor G))) = Ω := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.1
  · intro hy
    exact ⟨(y, 0), ⟨hy, Set.mem_univ _⟩, rfl⟩

/-- The pointwise fixer of a product over a nonempty reduced subset. -/
theorem enlargedPointwiseFixer_prod {Ω : Set B.ReducedBuilding} (hΩ : Ω.Nonempty) :
    B.enlargedPointwiseFixer (Ω ×ˢ (Set.univ : Set (CentralFactor G))) =
      rationalCommonNormKernel G ⊓ B.pointwiseFixer Ω := by
  obtain ⟨y, hy⟩ := hΩ
  have hY : (Ω ×ˢ (Set.univ : Set (CentralFactor G))).Nonempty :=
    ⟨(y, 0), hy, Set.mem_univ _⟩
  rw [B.enlargedPointwiseFixer_eq_inf hY, B.enlargedProjection_image_prod]

@[simp] theorem enlargedPointwiseFixer_empty :
    B.enlargedPointwiseFixer ∅ = ⊤ := fixingSubgroup_empty _ _

end Langlands.Geometry.Building.ValuationBuildingData
