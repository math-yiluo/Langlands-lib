import Langlands.Geometry.Building.CrossTorusApartment
import Langlands.Geometry.Building.KPBuilding

/-! # Actual reduced quotient transport between torus embeddings -/

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

/-- Root fixers of every subset use the same actual character and point transport. -/
theorem mem_rootFixer_transport_iff (a : characterLattice S) (Ω : Set D.Apartment)
    (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈
        (D.transport e f h).rootFixer (characterLattice.congr e a)
          (D.apartmentTransportEquiv e f h '' Ω) ↔
      g ∈ D.rootFixer a Ω := by
  rw [mem_rootFixer, mem_rootFixer, rootGroupPoints_transport_iff e f h]
  constructor
  · rintro ⟨hg, hΩ⟩
    refine ⟨hg, fun x hx => ?_⟩
    exact (D.mem_filtration_apartmentTransport_iff e f h x a 0 g).mp
      (hΩ _ ⟨x, hx, rfl⟩)
  · rintro ⟨hg, hΩ⟩
    refine ⟨hg, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (D.mem_filtration_apartmentTransport_iff e f h x a 0 g).mpr (hΩ x hx)

/-- The entire root fixer has exactly its actual ambient image, also for the empty subset. -/
theorem map_rootFixer_transport (a : characterLattice S) (Ω : Set D.Apartment) :
    (D.rootFixer a Ω).map (rationalPoints.map f.hom) =
      (D.transport e f h).rootFixer (characterLattice.congr e a)
        (D.apartmentTransportEquiv e f h '' Ω) := by
  apply Subgroup.ext
  intro y
  obtain ⟨g, rfl⟩ := (pointMap_bijective f).surjective y
  rw [Subgroup.mem_map_iff_mem (pointMap_bijective f).injective,
    D.mem_rootFixer_transport_iff]

/-- The actual ambient homomorphism carries the whole generated sharp fixer onto it. -/
theorem map_sharpFixer_transport (Ω : Set D.Apartment) :
    (D.sharpFixer Ω).map (rationalPoints.map f.hom) =
      (D.transport e f h).sharpFixer (D.apartmentTransportEquiv e f h '' Ω) := by
  simp only [sharpFixer, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun a => ?_
    rw [D.map_rootFixer_transport e f h]
    exact le_iSup (fun a' : relativeRoots j => (D.transport e f h).rootFixer a'
      (D.apartmentTransportEquiv e f h '' Ω)) (relativeRootsTransportEquiv e f h a)
  · refine iSup_le fun a' => ?_
    obtain ⟨a, rfl⟩ := (relativeRootsTransportEquiv e f h).surjective a'
    change (D.transport e f h).rootFixer (characterLattice.congr e a)
      (D.apartmentTransportEquiv e f h '' Ω) ≤ _
    rw [← D.map_rootFixer_transport e f h]
    exact le_iSup (fun a : relativeRoots i =>
      (D.rootFixer a Ω).map (rationalPoints.map f.hom)) a

/-- Membership in the original generated sharp fixer is preserved and reflected. -/
theorem mem_sharpFixer_transport_iff (Ω : Set D.Apartment) (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈
        (D.transport e f h).sharpFixer (D.apartmentTransportEquiv e f h '' Ω) ↔
      g ∈ D.sharpFixer Ω := by
  rw [← D.map_sharpFixer_transport e f h Ω,
    Subgroup.mem_map_iff_mem (pointMap_bijective f).injective]

/-- The sharp-fixer condition at each actual point uses the same ambient point map. -/
theorem mem_sharpFixer_singleton_transport_iff (x : D.Apartment) (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈
        (D.transport e f h).sharpFixer {D.apartmentTransportEquiv e f h x} ↔
      g ∈ D.sharpFixer {x} := by
  simpa only [Set.image_singleton] using D.mem_sharpFixer_transport_iff e f h {x} g

/-- The exact defining quotient relation is preserved and reflected on actual representatives. -/
theorem apartmentRel_transport_iff (g g' : rationalPoints G) (x y : D.Apartment) :
    apartmentRel (normalizerPoints j) (D.transport e f h).sharpFixerFamily
        (rationalPoints.map f.hom g, D.apartmentTransportEquiv e f h x)
        (rationalPoints.map f.hom g', D.apartmentTransportEquiv e f h y) ↔
      apartmentRel (normalizerPoints i) D.sharpFixerFamily (g, x) (g', y) := by
  constructor
  · rintro ⟨n', hn, hmem⟩
    obtain ⟨n, rfl⟩ := (normalizerPointsTransportEquiv e f h).surjective n'
    refine ⟨n, (D.apartmentTransportEquiv e f h).injective ?_, ?_⟩
    · rw [D.apartmentTransportEquiv_smul]
      exact hn
    · change (rationalPoints.map f.hom g)⁻¹ * rationalPoints.map f.hom g' *
        rationalPoints.map f.hom (n : rationalPoints G) ∈
          (D.transport e f h).sharpFixer {D.apartmentTransportEquiv e f h x} at hmem
      rw [← map_inv, ← map_mul, ← map_mul] at hmem
      exact (D.mem_sharpFixer_singleton_transport_iff e f h x _).mp hmem
  · rintro ⟨n, hn, hmem⟩
    refine ⟨normalizerPointsTransportEquiv e f h n, ?_, ?_⟩
    · rw [← D.apartmentTransportEquiv_smul, hn]
    · change (rationalPoints.map f.hom g)⁻¹ * rationalPoints.map f.hom g' *
        rationalPoints.map f.hom (n : rationalPoints G) ∈
          (D.transport e f h).sharpFixer {D.apartmentTransportEquiv e f h x}
      rw [← map_inv, ← map_mul, ← map_mul]
      exact (D.mem_sharpFixer_singleton_transport_iff e f h x _).mpr hmem

/-- The actual product map descends to an equivalence of the existing reduced quotient types. -/
def reducedBuildingTransportEquiv :
    D.ReducedBuilding ≃ (D.transport e f h).ReducedBuilding :=
  Quotient.congr
    (Equiv.prodCongr (isoPointsEquiv f (Over.mk (𝟙 _))).toEquiv
      (D.apartmentTransportEquiv e f h))
    (fun a b => (D.apartmentRel_transport_iff e f h a.1 b.1 a.2 b.2).symm)

/-- On each quotient representative the map is actual ambient and apartment transport. -/
@[simp] theorem reducedBuildingTransportEquiv_mk (g : rationalPoints G) (x : D.Apartment) :
    D.reducedBuildingTransportEquiv e f h (ApartmentQuotient.mk D.sharpFixerFamily (g, x)) =
      ApartmentQuotient.mk (D.transport e f h).sharpFixerFamily
        (rationalPoints.map f.hom g, D.apartmentTransportEquiv e f h x) := rfl

/-- The map carries the original canonical apartment chart to the transported chart. -/
@[simp] theorem reducedBuildingTransportEquiv_apartmentMap (x : D.Apartment) :
    D.reducedBuildingTransportEquiv e f h (D.apartmentMap x) =
      (D.transport e f h).apartmentMap (D.apartmentTransportEquiv e f h x) := by
  change ApartmentQuotient.mk _ (rationalPoints.map f.hom 1, _) =
    ApartmentQuotient.mk _ (1, _)
  rw [map_one]

/-- The equivalence intertwines the existing rational-point actions through the actual map. -/
theorem reducedBuildingTransportEquiv_smul (g : rationalPoints G) (q : D.ReducedBuilding) :
    D.reducedBuildingTransportEquiv e f h (g • q) =
      rationalPoints.map f.hom g • D.reducedBuildingTransportEquiv e f h q := by
  induction q using ApartmentQuotient.ind with
  | h g' x =>
    change ApartmentQuotient.mk _
        (rationalPoints.map f.hom (g * g'), D.apartmentTransportEquiv e f h x) =
      ApartmentQuotient.mk _
        (rationalPoints.map f.hom g * rationalPoints.map f.hom g',
          D.apartmentTransportEquiv e f h x)
    rw [map_mul]

/-- Full point stabilizers are preserved and reflected as full stabilizers. -/
theorem mem_reducedFixer_transport_iff (q : D.ReducedBuilding) (g : rationalPoints G) :
    rationalPoints.map f.hom g ∈
        (D.transport e f h).reducedFixer (D.reducedBuildingTransportEquiv e f h q) ↔
      g ∈ D.reducedFixer q := by
  rw [mem_reducedFixer, mem_reducedFixer,
    ← D.reducedBuildingTransportEquiv_smul]
  exact (D.reducedBuildingTransportEquiv e f h).injective.eq_iff

/-- The entire full stabilizer has exactly its actual ambient subgroup image. -/
theorem map_reducedFixer_transport (q : D.ReducedBuilding) :
    (D.reducedFixer q).map (rationalPoints.map f.hom) =
      (D.transport e f h).reducedFixer (D.reducedBuildingTransportEquiv e f h q) := by
  apply Subgroup.ext
  intro y
  obtain ⟨g, rfl⟩ := (pointMap_bijective f).surjective y
  rw [Subgroup.mem_map_iff_mem (pointMap_bijective f).injective,
    D.mem_reducedFixer_transport_iff]

/-- Injectivity of the canonical apartment chart is preserved and reflected. -/
theorem apartmentMap_injective_transport_iff :
    Function.Injective (D.transport e f h).apartmentMap ↔
      Function.Injective D.apartmentMap := by
  constructor
  · intro hE x y hxy
    apply (D.apartmentTransportEquiv e f h).injective
    apply hE
    rw [← D.reducedBuildingTransportEquiv_apartmentMap,
      ← D.reducedBuildingTransportEquiv_apartmentMap, hxy]
  · intro hD x' y' hxy
    obtain ⟨x, rfl⟩ := (D.apartmentTransportEquiv e f h).surjective x'
    obtain ⟨y, rfl⟩ := (D.apartmentTransportEquiv e f h).surjective y'
    apply congrArg (D.apartmentTransportEquiv e f h)
    apply hD
    apply (D.reducedBuildingTransportEquiv e f h).injective
    rwa [D.reducedBuildingTransportEquiv_apartmentMap,
      D.reducedBuildingTransportEquiv_apartmentMap]

end Langlands.Geometry.Building.KPApartmentData
