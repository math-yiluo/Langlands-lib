import Langlands.Group.LeftQuotientInversion
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement
import Langlands.Group.LeftQuotient

/-!
# Iwasawa and Cartan decompositions of the standard family of `G(F)`

A compact coset cover `G = P K` is equivalent to compactness of `P \ G` for a
locally compact group. For the actual standard family of a connected reductive
group over a nonarchimedean local field, the conjuncts of the published
`JointSpecialCompactBasisExistenceStatement` give:

* `G(F) = P_∅ K₀` with `K₀` compact (Renard V.5.1 (1));
* for every finite set `I` of simple roots, `M_I(F) = K_I Λ_I K_I` with
  `K_I = K₀ ∩ M_I(F)` compact and `Λ_I` the image in `G(F)` of the dominant
  part `C₀ F₀ ∩ Z_dom` of a full lattice transversal, a countable subset of
  `M_I(F)` (Renard V.5.1 (4), applied to `M_I`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Induction

section CosetCover

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- `G = P K` for a compact set `K`: every right coset `P * g` meets `K`. -/
def HasCompactCosetCover (P : Subgroup G) : Prop :=
  ∃ K : Set G, IsCompact K ∧ ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k

/-- A compact coset cover makes `P \ G` compact. -/
theorem compactSpace_of_hasCompactCosetCover {P : Subgroup G} (h : HasCompactCosetCover P) :
    CompactSpace (LeftQuotient P) := by
  obtain ⟨K, hK, hcov⟩ := h
  exact compactSpace_leftQuotient_of_compact_representatives P hK hcov

/-- If `P \ G` is compact and `G` is locally compact, then `G = P K` for a
compact set `K`. -/
theorem hasCompactCosetCover_of_compactSpace [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] (P : Subgroup G) [CompactSpace (LeftQuotient P)] :
    HasCompactCosetCover P := by
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : G)
  have hopen : IsOpenMap (quotientMap P) :=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : G => quotientMap P '' ((fun k => i * k) '' interior V))
    (fun i => hopen _ (isOpenMap_mul_left i _ isOpen_interior))
    (by
      intro y _
      induction y using Quotient.inductionOn with
      | h x =>
        exact Set.mem_iUnion.mpr ⟨x, x, ⟨1, mem_interior_iff_mem_nhds.mpr hV1, mul_one x⟩, rfl⟩)
  refine ⟨⋃ i ∈ t, (fun k => i * k) '' V,
    t.isCompact_biUnion fun i _ => hV.image (continuous_const.mul continuous_id), fun x => ?_⟩
  have hx := ht (Set.mem_univ (quotientMap P x))
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, _, ⟨k, hk, rfl⟩, hy⟩ := hx
  have hp : x * (i * k)⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact hy)
  exact ⟨_, hp, i * k, Set.mem_biUnion hi ⟨k, interior_subset hk, rfl⟩,
    (inv_mul_cancel_right x (i * k)).symm⟩

/-- For a locally compact group, `P \ G` is compact iff `G = P K` for a compact
set `K`. -/
theorem hasCompactCosetCover_iff_compactSpace [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] (P : Subgroup G) :
    HasCompactCosetCover P ↔ CompactSpace (LeftQuotient P) :=
  ⟨compactSpace_of_hasCompactCosetCover, fun _ => hasCompactCosetCover_of_compactSpace P⟩

end CosetCover

end Langlands.Induction

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Geometry.Building Langlands.BruhatTits.Cartan
open Langlands.Plancherel.RenardCartan Langlands.BruhatTits.SpecialCompact

/-- Rational points are functorial: `(f ≫ g)(y) = g (f y)`. -/
theorem rationalPoints_map_comp_apply {k : Type u} [CommRing k]
    {H M G : GroupScheme (Spec (CommRingCat.of k))}
    (f : H ⟶ M) (g : M ⟶ G) (y : rationalPoints H) :
    rationalPoints.map (f ≫ g) y = rationalPoints.map g (rationalPoints.map f y) := by
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

section Iwasawa

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- If a compact subgroup `K` satisfies `G(k) = P_J K` for every standard
parabolic `P_J`, then `G(k) = P_∅ K` is a compact coset cover of the minimal
standard parabolic. -/
theorem hasCompactCosetCover_parabolic_empty_of_products {K : Subgroup (rationalPoints G)}
    (hK : haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
      IsCompact (K : Set (rationalPoints G)))
    (hP : Langlands.BruhatTits.Iwasawa.StandardParabolicProducts i ν K) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
    Langlands.Induction.HasCompactCosetCover (parabolic i ν ∅) := by
  refine ⟨K, hK, fun g => ?_⟩
  have hg : g ∈ (standardParabolicPoints i ν ∅ : Set (rationalPoints G)) *
      (K : Set (rationalPoints G)) :=
    (hP ∅ (Set.empty_subset _)).1 ▸ Set.mem_univ g
  obtain ⟨p, hp, c, hc, rfl⟩ := hg
  refine ⟨p, ?_, c, hc, rfl⟩
  rw [parabolic, rootSet_empty]
  exact hp

/-- The Iwasawa covering `G(F) = P_∅ K₀` for a subgroup `K₀` with the special
compact properties and the actual parabolic product family. -/
theorem hasCompactCosetCover_parabolic_empty_of_specialCompactProperties
    [ValuativeRel k] {K : Subgroup (rationalPoints G)}
    (hK : SpecialCompactProperties k i ν K)
    (hP : Langlands.BruhatTits.Iwasawa.ParabolicPointProductFamily i ν K) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint k G.X) := rationalPointTopology k G.X
    Langlands.Induction.HasCompactCosetCover (parabolic i ν ∅) :=
  hasCompactCosetCover_parabolic_empty_of_products i ν hK.2.1.1 hP.2.2.1

end Iwasawa

section Cartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
  (ν : cocharacterLattice S) {j : Z ⟶ G} {s : S.toGrp ⟶ Z}
  {h : Function.Bijective (restrictionEvaluation s)}

local instance (J : Set (characterLattice S)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom

omit [Mono i.hom.hom.left] in
/-- The intersection of a compact subgroup with a standard Levi subgroup is
compact. -/
theorem isCompact_inf_levi {K : Subgroup (rationalPoints G)}
    (hK : haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (K : Set (rationalPoints G)))
    (I : Finset (SimpleRoot i ν)) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    IsCompact ((K ⊓ levi i ν I : Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  rw [Subgroup.coe_inf]
  exact hK.inter_right (isClosed_levi_of_isNonarchimedeanLocalField i ν I)

/-- The cocharacter lattice of a split torus is countable. -/
theorem countable_cocharacterLattice {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp) :
    Countable (cocharacterLattice T) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  have := hI
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  exact ((cocharacterLattice.congr eC).trans
    (splitTorus.cocharacterLatticeEquiv k I)).injective.countable

omit [Mono i.hom.hom.left] [IsAffineHom G.X.hom] in
/-- The dominant part `C₀ F₀ ∩ Z_dom` of a finite transversal is countable. -/
theorem countable_tildeC0Plus (hS : IsSplitTorus S.toGrp) {F0 : Set (rationalPoints Z)}
    (hF0 : F0.Finite) (dominant : Set (rationalPoints Z)) :
    (tildeC0Plus s F0 dominant).Countable := by
  have := countable_cocharacterLattice hS
  have : Countable (Multiplicative (cocharacterLattice S)) :=
    inferInstanceAs (Countable (cocharacterLattice S))
  have hC0 : (C0 S s : Set (rationalPoints Z)).Countable := by
    rw [C0, MonoidHom.coe_range]
    exact Set.countable_range _
  refine Set.Countable.mono Set.inter_subset_left ?_
  rw [tildeC0, ← Set.image2_mul]
  exact hC0.image2 hF0.countable _

/-- The rational points of the represented torus centralizer lie in every
standard Levi subgroup. -/
theorem map_mem_levi (hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j)
    (I : Finset (SimpleRoot i ν)) (a : rationalPoints Z) :
    rationalPoints.map j a ∈ levi i ν I := by
  obtain ⟨jM, -, -, hjM, -⟩ := hcompat (rootSet i ν I) (rootSet_subset i ν I)
  rw [← hjM, rationalPoints_map_comp_apply]
  exact (Standard.leviPointsEquiv i ν _ (rationalPoints.map jM a)).property

/-- The Cartan middle set `j(C₀ F₀ ∩ Z_dom)` lies in `M_I(F)`. -/
theorem image_tildeC0Plus_subset_levi
    (hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j)
    (F0 dominant : Set (rationalPoints Z)) (I : Finset (SimpleRoot i ν)) :
    rationalPoints.map j '' tildeC0Plus s F0 dominant ⊆ levi i ν I := by
  rintro _ ⟨a, -, rfl⟩
  exact map_mem_levi D x ν hcompat I a

omit [Mono i.hom.hom.left] [IsAffineHom G.X.hom] in
/-- The Cartan middle set `j(C₀ F₀ ∩ Z_dom)` is countable. -/
theorem countable_image_tildeC0Plus (hS : IsSplitTorus S.toGrp) {F0 : Set (rationalPoints Z)}
    (hF0 : F0.Finite) (dominant : Set (rationalPoints Z)) :
    (rationalPoints.map j '' tildeC0Plus s F0 dominant).Countable :=
  (countable_tildeC0Plus hS hF0 dominant).image _

/-- A finite lattice transversal of the torus centralizer exists. -/
theorem exists_isFiniteLatticeTransversal
    (hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j) :
    ∃ F0 : Set (rationalPoints Z), IsFiniteLatticeTransversal s F0 := by
  obtain ⟨jM, -, -, -, -, -, -, hlat⟩ := hcompat ∅ (Set.empty_subset _)
  obtain ⟨F0, hF0, -⟩ := hlat.2.2.2.1
  exact ⟨F0, hF0⟩

/-- **Cartan decomposition of a standard Levi subgroup.** Every `m ∈ M_I(F)` is
`k₁ t k₂` with `k₁, k₂ ∈ K₀ ∩ M_I(F)` and `t` the image of a point of the
dominant part `C₀ F₀ ∩ Z_dom` (for the positive roots of `M_I`) of a finite
lattice transversal `F₀`. -/
theorem exists_cartan_levi (hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j)
    {F0 : Set (rationalPoints Z)} (hF0 : IsFiniteLatticeTransversal s F0)
    (I : Finset (SimpleRoot i ν)) :
    ∀ m ∈ levi i ν I,
      ∃ k₁ ∈ ((D.specialCompactSubgroup x ⊓ levi i ν I : Subgroup (rationalPoints G)) :
          Set (rationalPoints G)),
        ∃ t ∈ rationalPoints.map j '' tildeC0Plus s F0
            (dominantCentralizer (Standard.leviTorusHom i ν (rootSet i ν I)) ν s h),
          ∃ k₂ ∈ ((D.specialCompactSubgroup x ⊓ levi i ν I : Subgroup (rationalPoints G)) :
              Set (rationalPoints G)),
            m = k₁ * t * k₂ := by
  intro m hm
  set J := rootSet i ν I
  obtain ⟨jM, -, -, hjM, -, -, hc, hlat⟩ := hcompat J (rootSet_subset i ν I)
  have hA := (hlat.2.2.2.2.1 F0 hF0).1
  obtain ⟨m', hm'⟩ := (Standard.leviPointsEquiv i ν J).surjective ⟨m, hm⟩
  have hm'v : rationalPoints.map (Standard.leviHom i ν J) m' = m :=
    congrArg Subtype.val hm'
  obtain ⟨⟨a, ha⟩, hq⟩ := (sameCompactLeviSectionMap_bijective D x ν J jM s h hc _ hA).2
    (DoubleCoset.mk (D.specialCompactLeviSubgroup ν J x) (D.specialCompactLeviSubgroup ν J x) m')
  obtain ⟨k₁, hk₁, k₂, hk₂, hm'eq⟩ := DoubleCoset.eq.mp hq
  have hsub : ∀ k ∈ D.specialCompactLeviSubgroup ν J x,
      rationalPoints.map (Standard.leviHom i ν J) k ∈ D.specialCompactSubgroup x ⊓ levi i ν I :=
    fun k hk => ⟨hk, (Standard.leviPointsEquiv i ν J k).property⟩
  refine ⟨_, hsub k₁ hk₁, rationalPoints.map j a, ⟨a, ha, rfl⟩, _, hsub k₂ hk₂, ?_⟩
  rw [← hjM, rationalPoints_map_comp_apply, ← map_mul, ← map_mul, ← hm'eq, hm'v]

end Cartan

end Langlands.Aubert.General.RationalPointFamily
