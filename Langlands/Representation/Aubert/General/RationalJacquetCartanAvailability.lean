import Langlands.Representation.Aubert.General.RationalUniformizerContraction
import Langlands.Representation.Aubert.General.RationalJacquetCartanDatum
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.BruhatTits.SpecialCompact.ValidTorusRebasingProof
import Langlands.BruhatTits.SpecialCompact.AvailableSpecialVertexProof
import Langlands.BruhatTits.Iwasawa.AvailableProof
import Langlands.Geometry.Building.BruhatTitsAvailabilityStatement
import Langlands.Representation.Plancherel.AvailableRenardCartanStatement

/-!
# Jacquet–Cartan data on `G(F)` from Bruhat–Tits availability and Levi Cartan compatibility

`rationalStandardParabolicSystemOfCompact` builds the standard parabolic system of `G(F)`
from a compact subgroup `K₀ = D.specialCompactSubgroup x` with the parabolic product family
and the standard Levi compatibility: it needs neither the full special compact properties
nor a simultaneous basis of compact open subgroups (the wall contraction comes from
`isCartanLatticeModel_rational_of_standard`).

`rationalPointsJacquetCartanDatum_of_validLeviCompatibility` proves
`RationalPointsJacquetCartanDatumStatement` from `BruhatTitsAvailabilityStatement` and the
standard Levi compatibility at the special vertices of valid assignments; the published
torus rebasing, special vertex existence and Iwasawa results supply everything else.
`rationalPointsJacquetCartanDatum_of_availability_of_renardCartan` takes that compatibility
from `AvailableRenardCartanStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits.Cartan Langlands.BruhatTits.SpecialCompact
open Langlands.Geometry.Building Langlands.Plancherel.RenardCartan
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General

open RationalPointFamily

section System

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- **The standard parabolic system of `G(F)` from a compact subgroup.** For a maximal split
torus `i : S → G` with a generic cocharacter `ν`, a vertex `x` whose subgroup
`K₀ = D.specialCompactSubgroup x` is compact and has the parabolic product family and the
standard Levi compatibility, a represented torus centralizer `j : Z → G` with `s ≫ j = i`,
and a finite lattice transversal `F₀` of `Z(F)`: the simple roots of `(i, ν)`, the
standard parabolic, Levi and unipotent subgroups, the Iwasawa decomposition `G = P_∅ K₀`,
the Cartan decompositions `M_I = (K₀ ∩ M_I) Λ_I (K₀ ∩ M_I)` with
`Λ_I = rationalCartanSet i ν j s h F₀ I`, and their wall contraction. -/
def rationalStandardParabolicSystemOfCompact (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
    {j : Z ⟶ G} {s : S.toGrp ⟶ Z} {h : Function.Bijective (restrictionEvaluation s)}
    (hrep : (torusCentralizer i).IsRepresentedBy j) (hsj : s ≫ j = i)
    (hK : haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact ((D.specialCompactSubgroup x : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)))
    (hP : Langlands.BruhatTits.Iwasawa.ParabolicPointProductFamily i ν
      (D.specialCompactSubgroup x))
    (hcompat : SpecialCompactStandardLeviCompatibility D x ν s h j)
    {F0 : Set (rationalPoints Z)} (hF0 : IsFiniteLatticeTransversal s F0) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    StandardParabolicSystem.{u, u} (RationalPoint F G.X) :=
  haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  { Δ := SimpleRoot i ν
    decEq := Classical.decEq _
    parabolic := parabolic i ν
    levi := levi i ν
    unipotent := unipotent i ν
    parabolic_mono := fun _ _ hIJ => parabolic_mono hG hi hν standardParabolicOrder hIJ
    levi_mul_unipotent := fun I _ hp =>
      exists_mul_of_mem_parabolic hG hi hν standardCocharacter I hp
    levi_le_normalizer := levi_le_normalizer i ν
    isClosed_levi := isClosed_levi_of_isNonarchimedeanLocalField i ν
    top := (exists_unipotent_eq_bot hG hi ν).choose
    unipotent_top := (exists_unipotent_eq_bot hG hi ν).choose_spec.2
    unipotent_descent := fun _ _ hJI _ hn =>
      exists_mul_of_mem_unipotent hG hi hν standardCocharacter standardParabolicOrder hJI hn
    iwasawa := hasCompactCosetCover_parabolic_empty_of_products i ν hK hP.2.2.1
    cartanCompact := fun I =>
      ((D.specialCompactSubgroup x ⊓ levi i ν I : Subgroup (rationalPoints G)) :
        Set (rationalPoints G))
    cartanSet := rationalCartanSet i ν j s h F0
    isCompact_cartanCompact := isCompact_inf_levi ν hK
    cartanCompact_subset := fun _ _ hm => hm.2
    countable_cartanSet := fun _ =>
      countable_image_tildeC0Plus hi.isSplitSubtorus.1 hF0.1 _
    cartanSet_subset := fun I => image_tildeC0Plus_subset_levi D x ν hcompat F0 _ I
    cartan := exists_cartan_levi D x ν hcompat hF0
    contraction := by
      have : Smooth G.X.hom := hG.smooth
      have : IsTopologicalGroup (RationalPoint F G.X) := rationalPoint_isTopologicalGroup F G
      have : Finite (SimpleRoot i ν) := finite_simpleRoot hG hi ν
      let : Fintype (SimpleRoot i ν) := Fintype.ofFinite _
      have hfinite : (simpleRelativeRoots i ν).Finite := Set.finite_coe_iff.mp ‹_›
      have hexists : ∀ I : Finset (SimpleRoot i ν),
          ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ :=
        fun I => (standardCocharacter F G hG S i hi ν hν (rootSet i ν I)
          (rootSet_subset i ν I)).1
      obtain ⟨-, -, -, -, -, -, -, hlat⟩ := hcompat ∅ (Set.empty_subset _)
      exact (isCartanLatticeModel_rational_of_standard i ν j s h hi hfinite hexists hrep hsj
        hlat.1 hF0.1).hasWallContraction }

end System

section Data

/-- The compact Iwasawa and Levi Cartan data at the given torus from the conclusions at
every special vertex of building data whose torus is the given one. -/
theorem compactLeviData_of_valuationBuildingData {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (V : ValuationBuildingData G)
    (hx : ∃ x : V.Apartment, V.apartment.IsSpecialApartmentVertex x)
    (hI : ∀ ν : cocharacterLattice V.S, IsGenericCocharacter V.i ν →
      ∀ x : V.Apartment, V.apartment.IsSpecialApartmentVertex x →
        Langlands.BruhatTits.Iwasawa.ParabolicPointProductFamily V.i ν
            (V.apartment.specialCompactSubgroup x) ∧
          IsCompactOpenMaximal F (V.apartment.specialCompactSubgroup x))
    (hC : ∀ ν : cocharacterLattice V.S, IsGenericCocharacter V.i ν →
      ∀ x : V.Apartment, V.apartment.IsSpecialApartmentVertex x →
        SpecialCompactStandardLeviCompatibility V.apartment x ν
          V.centralizer.s V.centralizer.bijective V.centralizer.j)
    {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (hS : V.S = S) (hVi : HEq V.i i)
    (ν : cocharacterLattice S) :
    haveI : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∃ (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
        (Z : GroupScheme (Spec (CommRingCat.of F))) (j : Z ⟶ G)
        (s : S.toGrp ⟶ Z),
        (torusCentralizer i).IsRepresentedBy j ∧ s ≫ j = i ∧
          ∃ h : Function.Bijective (restrictionEvaluation s),
            Langlands.BruhatTits.Iwasawa.ParabolicPointProductFamily i ν
                (D.specialCompactSubgroup x) ∧
              IsCompactOpenMaximal F (D.specialCompactSubgroup x) ∧
              SpecialCompactStandardLeviCompatibility D x ν s h j := by
  intro hν
  obtain ⟨_, SV, iV, hiV, AV, CV, _⟩ := V
  subst hS
  obtain rfl := eq_of_heq hVi
  obtain ⟨x, hx⟩ := hx
  obtain ⟨hP, hK⟩ := hI ν hν x hx
  exact ⟨AV, x, CV.Z, CV.j, CV.s, CV.isRepresentedBy, CV.comp_eq, CV.bijective, hP, hK,
    hC ν hν x hx⟩

end Data

/-- **Jacquet–Cartan data on `G(F)` from Bruhat–Tits availability and Levi compatibility.**
If some corrected KP assignment is valid (`BruhatTitsAvailabilityStatement`) and the
standard Levi compatibility holds at every special vertex of every valid assignment, then
`RationalPointsJacquetCartanDatumStatement` holds. -/
theorem rationalPointsJacquetCartanDatum_of_validLeviCompatibility
    (hAvailability : BruhatTitsAvailabilityStatement.{u})
    (hCompat : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
      (hG : IsConnectedReductive G),
      haveI : IsAffineHom G.X.hom := hG.isAffineHom
      ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid →
        let B := (𝔅.datum F G hG).base
        ∀ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν →
          ∀ x : B.Apartment, B.apartment.IsSpecialApartmentVertex x →
            SpecialCompactStandardLeviCompatibility B.apartment x ν
              B.centralizer.s B.centralizer.bijective B.centralizer.j) :
    RationalPointsJacquetCartanDatumStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  obtain ⟨S, i, ν, hi, hν⟩ := exists_maximalSplitTorus_genericCocharacter hG
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨𝔅₀, h𝔅₀⟩ := hAvailability
  obtain ⟨𝔅, h𝔅, hS, hVi⟩ := validAssignmentTorusRebasing 𝔅₀ h𝔅₀ F G hG S i hi
  have hA : 𝔅.IsAvailableFor F G hG := h𝔅.isAvailableFor
  obtain ⟨D, x, Z, j, s, hrep, hsj, h, hP, hK, hcompat⟩ :=
    compactLeviData_of_valuationBuildingData (𝔅.datum F G hG).base.toValuationBuildingData
      (availableSpecialVertexExistence F G hG 𝔅 hA)
      (fun ν hν x hx =>
        ⟨((Langlands.BruhatTits.Iwasawa.availableIwasawa F G hG 𝔅 hA ν hν).1 x hx).2.2.1,
          ((Langlands.BruhatTits.Iwasawa.availableIwasawa F G hG 𝔅 hA ν hν).1 x hx).2.2.2⟩)
      (hCompat F G hG 𝔅 h𝔅) hi hS hVi ν hν
  obtain ⟨F0, hF0⟩ := exists_isFiniteLatticeTransversal D x ν hcompat
  exact (rationalStandardParabolicSystemOfCompact hG hi hν D x hrep hsj hK.1 hP hcompat
    hF0).nonempty_jacquetCartanDatum

/-- **Jacquet–Cartan data on `G(F)`, conditionally on two building statements.**
`BruhatTitsAvailabilityStatement` and `AvailableRenardCartanStatement` imply
`RationalPointsJacquetCartanDatumStatement`; no simultaneous basis statement is used. -/
theorem rationalPointsJacquetCartanDatum_of_availability_of_renardCartan
    (hAvailability : BruhatTitsAvailabilityStatement.{u})
    (hCartan : AvailableRenardCartanStatement.{u}) :
    RationalPointsJacquetCartanDatumStatement.{u} := by
  refine rationalPointsJacquetCartanDatum_of_validLeviCompatibility hAvailability ?_
  intro F _ _ _ _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  intro 𝔅 h𝔅 _ ν hν x hx
  exact (hCartan F G hG 𝔅 h𝔅.isAvailableFor ν hν x hx).2

end Langlands.Aubert.General
