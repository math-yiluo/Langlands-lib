import Langlands.Geometry.Building.CrossTorusApartment

/-! # Affine roots under actual cross-torus apartment transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {ω : kˣ → ℝ}
  (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
  (D : KPApartmentData i ω)

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
private theorem pointMap_bijective : Function.Bijective (rationalPoints.map f.hom) :=
  (isoPointsEquiv f (Over.mk (𝟙 _))).bijective

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
private theorem subgroupMap_injective :
    Function.Injective (Subgroup.map (rationalPoints.map f.hom)) := by
  intro K L hKL
  apply SetLike.coe_injective
  apply (pointMap_bijective f).injective.image_injective
  exact congrArg (fun P : Subgroup (rationalPoints H) => (P : Set (rationalPoints H))) hKL

/-- Transport affine functionals by the inverse of the actual apartment affine map. -/
def affineFunctionalTransportEquiv :
    (D.Apartment →ᵃ[ℝ] ℝ) ≃ₗ[ℝ] ((D.transport e f h).Apartment →ᵃ[ℝ] ℝ) :=
  (D.apartmentTransportAffineEquiv e f h).congrLeftₗ ℝ ℝ

/-- The transported functional has the same value at the transported point. -/
@[simp] theorem affineFunctionalTransportEquiv_apply_map
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (x : D.Apartment) :
    D.affineFunctionalTransportEquiv e f h ψ (D.apartmentTransportEquiv e f h x) = ψ x := by
  change ψ ((D.apartmentTransportAffineEquiv e f h).symm
    (D.apartmentTransportAffineEquiv e f h x)) = ψ x
  rw [AffineEquiv.symm_apply_apply]

/-- The original derivative is evaluated on the original vector. -/
theorem affineFunctionalTransportEquiv_linear_apply
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (v : TranslationSpace i) :
    (D.affineFunctionalTransportEquiv e f h ψ).linear
        (translationSpaceTransportEquiv e f h v) = ψ.linear v := by
  change ψ.linear ((translationSpaceTransportEquiv e f h).symm
    (translationSpaceTransportEquiv e f h v)) = ψ.linear v
  rw [LinearEquiv.symm_apply_apply]

/-- Being the form of an actual root is preserved and reflected. -/
theorem affineFunctionalTransportEquiv_linear_eq_rootForm_iff
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (a : relativeRoots i) :
    (D.affineFunctionalTransportEquiv e f h ψ).linear =
        rootForm j (relativeRootsTransportEquiv e f h a) ↔
      ψ.linear = rootForm i a := by
  constructor
  · intro hψ
    apply LinearMap.ext
    intro v
    rw [← D.affineFunctionalTransportEquiv_linear_apply e f h ψ v, hψ,
      rootForm_translationSpaceTransportEquiv]
  · intro hψ
    apply LinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := (translationSpaceTransportEquiv e f h).surjective v
    rw [D.affineFunctionalTransportEquiv_linear_apply, hψ,
      rootForm_translationSpaceTransportEquiv]

/-- Adding the same real constant commutes with actual functional transport. -/
theorem affineFunctionalTransportEquiv_add_const (ψ : D.Apartment →ᵃ[ℝ] ℝ) (c : ℝ) :
    D.affineFunctionalTransportEquiv e f h (ψ + AffineMap.const ℝ D.Apartment c) =
      D.affineFunctionalTransportEquiv e f h ψ +
        AffineMap.const ℝ (D.transport e f h).Apartment c := by
  apply AffineMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (D.apartmentTransportEquiv e f h).surjective y
  simp only [affineFunctionalTransportEquiv_apply_map,
    AffineMap.coe_add, Pi.add_apply, AffineMap.coe_const, Function.const_apply]

/-- Membership in every affine root group is preserved and reflected. -/
theorem mem_affineRootGroup_transport_iff (a : characterLattice S)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈
        (D.transport e f h).affineRootGroup (characterLattice.congr e a)
          (D.affineFunctionalTransportEquiv e f h ψ) ↔
      g ∈ D.affineRootGroup a ψ := by
  simp only [affineRootGroup, Subgroup.mem_iInf]
  constructor
  · intro hg x
    have hx := hg (D.apartmentTransportEquiv e f h x)
    rw [affineFunctionalTransportEquiv_apply_map] at hx
    exact (D.mem_filtration_apartmentTransport_iff e f h x a (ψ x) g).mp hx
  · intro hg y
    obtain ⟨x, rfl⟩ := (D.apartmentTransportEquiv e f h).surjective y
    rw [affineFunctionalTransportEquiv_apply_map]
    exact (D.mem_filtration_apartmentTransport_iff e f h x a (ψ x) g).mpr (hg x)

/-- The ambient map carries the entire affine root group onto the target group. -/
theorem map_affineRootGroup_transport (a : characterLattice S)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    (D.affineRootGroup a ψ).map (rationalPoints.map f.hom) =
      (D.transport e f h).affineRootGroup (characterLattice.congr e a)
        (D.affineFunctionalTransportEquiv e f h ψ) := by
  apply Subgroup.ext
  intro y
  obtain ⟨g, rfl⟩ := (pointMap_bijective f).surjective y
  rw [Subgroup.mem_map_iff_mem (pointMap_bijective f).injective,
    D.mem_affineRootGroup_transport_iff]

/-- Strict affine root-group membership is also preserved and reflected. -/
theorem mem_affineRootGroupPlus_transport_iff (a : characterLattice S)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈
        (D.transport e f h).affineRootGroupPlus (characterLattice.congr e a)
          (D.affineFunctionalTransportEquiv e f h ψ) ↔
      g ∈ D.affineRootGroupPlus a ψ := by
  rw [mem_affineRootGroupPlus, mem_affineRootGroupPlus]
  constructor
  · rintro ⟨c, hc, hg⟩
    refine ⟨c, hc, ?_⟩
    rw [← affineFunctionalTransportEquiv_add_const] at hg
    exact (D.mem_affineRootGroup_transport_iff e f h a _ g).mp hg
  · rintro ⟨c, hc, hg⟩
    refine ⟨c, hc, ?_⟩
    rw [← affineFunctionalTransportEquiv_add_const]
    exact (D.mem_affineRootGroup_transport_iff e f h a _ g).mpr hg

/-- The entire strict affine root group has the corresponding actual image. -/
theorem map_affineRootGroupPlus_transport (a : characterLattice S)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    (D.affineRootGroupPlus a ψ).map (rationalPoints.map f.hom) =
      (D.transport e f h).affineRootGroupPlus (characterLattice.congr e a)
        (D.affineFunctionalTransportEquiv e f h ψ) := by
  apply Subgroup.ext
  intro y
  obtain ⟨g, rfl⟩ := (pointMap_bijective f).surjective y
  rw [Subgroup.mem_map_iff_mem (pointMap_bijective f).injective,
    D.mem_affineRootGroupPlus_transport_iff]

omit [Mono i.hom.hom.left] [Mono j.hom.hom.left] in
include h in
/-- The convention for a nonexistent double root is preserved by the actual map. -/
theorem map_doubleRootGroupPoints_transport (a : characterLattice S) :
    (doubleRootGroupPoints i a).map (rationalPoints.map f.hom) =
      doubleRootGroupPoints j (characterLattice.congr e a) := by
  classical
  have h2 : 2 • characterLattice.congr e a ∈ relativeRoots j ↔
      2 • a ∈ relativeRoots i := by
    rw [← map_nsmul]
    exact roots_mem_of_transport_iff e f h (2 • a)
  by_cases ha : 2 • a ∈ relativeRoots i
  · rw [doubleRootGroupPoints, ite_eq_left ha, doubleRootGroupPoints,
      ite_eq_left (h2.mpr ha)]
    apply SetLike.ext'
    change rationalPoints.map f.hom '' (rootGroupPoints i (2 • a) : Set (rationalPoints G)) =
      (rootGroupPoints j (2 • characterLattice.congr e a) : Set (rationalPoints H))
    rw [← map_nsmul]
    exact image_rootGroupPoints_transport e f h (2 • a)
  · rw [doubleRootGroupPoints, ite_eq_right ha, doubleRootGroupPoints,
      ite_eq_right (fun hroot => ha (h2.mp hroot)), Subgroup.map_bot]

/-- The noncontainment test defining ordinary affine roots is invariant. -/
theorem affineRootGroup_subset_mul_transport_iff (a : characterLattice S)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    ((D.transport e f h).affineRootGroup (characterLattice.congr e a)
          (D.affineFunctionalTransportEquiv e f h ψ) : Set (rationalPoints H)) ⊆
        ((D.transport e f h).affineRootGroupPlus (characterLattice.congr e a)
          (D.affineFunctionalTransportEquiv e f h ψ) : Set (rationalPoints H)) *
        (doubleRootGroupPoints j (characterLattice.congr e a) : Set (rationalPoints H)) ↔
      (D.affineRootGroup a ψ : Set (rationalPoints G)) ⊆
        (D.affineRootGroupPlus a ψ : Set (rationalPoints G)) *
          (doubleRootGroupPoints i a : Set (rationalPoints G)) := by
  rw [← Set.image_subset_image_iff (pointMap_bijective f).injective, Set.image_mul]
  change _ ↔
    ((D.affineRootGroup a ψ).map (rationalPoints.map f.hom) : Set (rationalPoints H)) ⊆
      ((D.affineRootGroupPlus a ψ).map (rationalPoints.map f.hom) : Set (rationalPoints H)) *
        ((doubleRootGroupPoints i a).map (rationalPoints.map f.hom) : Set (rationalPoints H))
  rw [D.map_affineRootGroup_transport e f h, D.map_affineRootGroupPlus_transport e f h,
    map_doubleRootGroupPoints_transport e f h]

/-- Extended affine roots are preserved and reflected by the actual functional map. -/
theorem mem_extendedAffineRoots_transport_iff (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    D.affineFunctionalTransportEquiv e f h ψ ∈ (D.transport e f h).extendedAffineRoots ↔
      ψ ∈ D.extendedAffineRoots := by
  constructor
  · rintro ⟨a', hψ, hne⟩
    obtain ⟨a, rfl⟩ := (relativeRootsTransportEquiv e f h).surjective a'
    refine ⟨a, (D.affineFunctionalTransportEquiv_linear_eq_rootForm_iff e f h ψ a).mp hψ,
      fun heq => hne ?_⟩
    change (D.transport e f h).affineRootGroupPlus (characterLattice.congr e a)
        (D.affineFunctionalTransportEquiv e f h ψ) =
      (D.transport e f h).affineRootGroup (characterLattice.congr e a)
        (D.affineFunctionalTransportEquiv e f h ψ)
    rw [← D.map_affineRootGroupPlus_transport e f h a ψ,
      ← D.map_affineRootGroup_transport e f h a ψ, heq]
  · rintro ⟨a, hψ, hne⟩
    refine ⟨relativeRootsTransportEquiv e f h a,
      (D.affineFunctionalTransportEquiv_linear_eq_rootForm_iff e f h ψ a).mpr hψ, ?_⟩
    intro heq
    apply hne
    apply subgroupMap_injective f
    rwa [D.map_affineRootGroupPlus_transport e f h a ψ,
      D.map_affineRootGroup_transport e f h a ψ]

/-- Ordinary affine roots, with the original double-root test, are preserved and reflected. -/
theorem mem_affineRoots_transport_iff (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    D.affineFunctionalTransportEquiv e f h ψ ∈ (D.transport e f h).affineRoots ↔
      ψ ∈ D.affineRoots := by
  constructor
  · rintro ⟨a', hψ, hnot⟩
    obtain ⟨a, rfl⟩ := (relativeRootsTransportEquiv e f h).surjective a'
    refine ⟨a, (D.affineFunctionalTransportEquiv_linear_eq_rootForm_iff e f h ψ a).mp hψ, ?_⟩
    exact fun hs => hnot ((D.affineRootGroup_subset_mul_transport_iff e f h a ψ).mpr hs)
  · rintro ⟨a, hψ, hnot⟩
    refine ⟨relativeRootsTransportEquiv e f h a,
      (D.affineFunctionalTransportEquiv_linear_eq_rootForm_iff e f h ψ a).mpr hψ, ?_⟩
    exact fun hs => hnot ((D.affineRootGroup_subset_mul_transport_iff e f h a ψ).mp hs)

/-- The actual functional map restricts to a bijection of extended affine roots. -/
def extendedAffineRootsTransportEquiv :
    D.extendedAffineRoots ≃ (D.transport e f h).extendedAffineRoots :=
  (D.affineFunctionalTransportEquiv e f h).toEquiv.subtypeEquiv
    (fun ψ => (D.mem_extendedAffineRoots_transport_iff e f h ψ).symm)

/-- The actual functional map restricts to a bijection of ordinary affine roots. -/
def affineRootsTransportEquiv :
    D.affineRoots ≃ (D.transport e f h).affineRoots :=
  (D.affineFunctionalTransportEquiv e f h).toEquiv.subtypeEquiv
    (fun ψ => (D.mem_affineRoots_transport_iff e f h ψ).symm)

end Langlands.Geometry.Building.KPApartmentData
