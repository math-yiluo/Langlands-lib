import Langlands.Representation.Plancherel.RenardCartanAlgebraicComparison
import Langlands.Representation.Plancherel.RenardParahoricCompactTransport
import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.GroupScheme.Rational.RootSubgroupConjugation

/-! # The same centralizer on a restricted standard-Levi apartment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.BruhatTits.Cartan Langlands.BruhatTits.SpecialCompact

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] (i : S.toGrp ⟶ G)
  (C : CentralizerDatum i) (ν : cocharacterLattice S)
  (J : Set (characterLattice S))

local instance : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom

/-- The ambient centralizer, with its unchanged torus map and character valuation,
is the whole centralizer of the same torus in the actual standard Levi. -/
def standardLeviCentralizerDatum : CentralizerDatum (Standard.leviTorusHom i ν J) where
  Z := C.Z
  j := standardLeviCentralizerFactor i ν J C.j C.isRepresentedBy
  s := C.s
  isClosedSubgroup :=
    isClosedSubgroup_standardLeviCentralizerFactor i ν J C.j C.isRepresentedBy
      C.isClosedSubgroup
  isRepresentedBy :=
    isRepresentedBy_standardLeviCentralizerFactor i ν J C.j C.isRepresentedBy
  comp_eq :=
    comp_standardLeviCentralizerFactor i ν J C.j C.isRepresentedBy C.s C.comp_eq
  bijective := C.bijective

section Restriction

variable [Mono i.hom.hom.left]
  [Mono (Standard.leviTorusHom i ν J).hom.hom.left]
  (D : KPApartmentData i (localFieldOrder F))
  (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F))

/-- Literal restriction of every valuation point transfers full V6 on the
unchanged actual centralizer; it does not require a Levi building realization. -/
theorem isOmegaCompatible_standardLevi_of_restriction
    (hD : D.IsOmegaCompatible C)
    (hres : ∀ yM : DM.Apartment, ∃ y : D.Apartment,
      IsLeviRestriction (Standard.leviHom i ν J) y yM) :
    DM.IsOmegaCompatible (standardLeviCentralizerDatum i C ν J) := by
  change DM.IsCentralizerCompatible
    (standardLeviCentralizerFactor i ν J C.j C.isRepresentedBy) C.s C.bijective
  intro φ hφ
  obtain ⟨y, hy⟩ := hres ⟨φ, hφ⟩
  intro a ha z m hm
  have haG : a ∈ relativeRoots i :=
    relativeRoots_subset_of_factor (Standard.isRepresentedBy_leviHom i ν J)
      (Standard.leviTorusHom i ν J) (Standard.leviTorusHom_comp i ν J) ha
  have hmG : rationalPoints.map (Standard.leviHom i ν J) m ∈ rootGroupPoints i a := by
    simpa only [rootGroupPoints, rationalPoints.map_apply, Standard.leviTorusHom_comp] using
      RelativeRoot.comp_mem_subgroup (Standard.leviTorusHom i ν J) a
        (Standard.leviHom i ν J) hm
  have hfactor : rationalPoints.map (Standard.leviHom i ν J)
      (rationalPoints.map (standardLeviCentralizerFactor i ν J C.j C.isRepresentedBy) z) =
        rationalPoints.map C.j z := by
    simpa only [rationalPoints.map_apply, Category.assoc, Grp.comp_hom_hom] using
      congrArg (fun f : C.Z ⟶ G => z ≫ f.hom.hom)
        (standardLeviCentralizerFactor_comp i ν J C.j C.isRepresentedBy)
  change φ a ((rationalPoints.map
      (standardLeviCentralizerFactor i ν J C.j C.isRepresentedBy) z)⁻¹ *
      m * rationalPoints.map
        (standardLeviCentralizerFactor i ν J C.j C.isRepresentedBy) z) =
    φ a m + _
  rw [hy a ha, hy a ha, map_mul, map_mul, map_inv, hfactor]
  exact (hD y.val y.mem) a haG z _ hmG

end Restriction

section CompactIntersection

open Langlands.AlgebraicGeometry.PointTopology

variable {i}
  (B : ParahoricBuildingData G) (ν : cocharacterLattice B.S)
  (J : Set (characterLattice B.S)) (x : B.Apartment)

/-- The preimage of the same ambient compact subgroup is compact in the
canonical rational-point topology of the actual standard Levi. -/
theorem isCompact_specialCompactLeviSubgroup
    (hK : let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (B.apartment.specialCompactSubgroup x : Set (rationalPoints G))) :
    let : IsAffineHom (Standard.leviScheme B.i ν J).X.hom :=
      (Standard.isClosedSubgroup_leviHom B.i ν J).isAffineHom
    let : IsAffine (Standard.leviScheme B.i ν J).X.left :=
      isAffine_of_isAffineHom (Standard.leviScheme B.i ν J).X.hom
    let : TopologicalSpace (rationalPoints (Standard.leviScheme B.i ν J)) :=
      rationalPointTopology F (Standard.leviScheme B.i ν J).X
    IsCompact (B.apartment.specialCompactLeviSubgroup ν J x :
      Set (rationalPoints (Standard.leviScheme B.i ν J))) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsAffineHom (Standard.leviScheme B.i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom B.i ν J).isAffineHom
  let : IsAffine (Standard.leviScheme B.i ν J).X.left :=
    isAffine_of_isAffineHom (Standard.leviScheme B.i ν J).X.hom
  let : TopologicalSpace (rationalPoints (Standard.leviScheme B.i ν J)) :=
    rationalPointTopology F (Standard.leviScheme B.i ν J).X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let : IsClosedImmersion (Standard.leviHom B.i ν J).hom.hom.left :=
    Standard.isClosedSubgroup_leviHom B.i ν J
  exact (isClosedEmbedding_rationalPointMap F
    (Standard.leviHom B.i ν J).hom.hom).isCompact_preimage hK

/-- The centralizer preimage in the same Levi compact intersection is still
the ambient centralizer's actual character norm kernel. -/
theorem specialCompactLeviCentralizer_comap
    (hK : let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (B.apartment.specialCompactSubgroup x : Set (rationalPoints G))) :
    (B.apartment.specialCompactLeviSubgroup ν J x).comap
      (rationalPoints.map (standardLeviCentralizerDatum B.i B.centralizer ν J).j) =
        rationalCommonNormKernel B.centralizer.Z := by
  change (B.apartment.specialCompactLeviSubgroup ν J x).comap
    (rationalPoints.map (standardLeviCentralizerFactor B.i ν J B.centralizer.j
      B.centralizer.isRepresentedBy)) = rationalCommonNormKernel B.centralizer.Z
  have hcomp :
      (B.apartment.specialCompactLeviSubgroup ν J x).comap
        (rationalPoints.map (standardLeviCentralizerFactor B.i ν J B.centralizer.j
          B.centralizer.isRepresentedBy)) =
      (B.apartment.specialCompactSubgroup x).comap
        (rationalPoints.map B.centralizer.j) := by
    ext z
    change rationalPoints.map (Standard.leviHom B.i ν J)
        (rationalPoints.map
          (standardLeviCentralizerFactor B.i ν J B.centralizer.j
            B.centralizer.isRepresentedBy) z) ∈ B.apartment.specialCompactSubgroup x ↔ _
    have hpoint := congrArg (fun f : B.centralizer.Z ⟶ G => z ≫ f.hom.hom)
      (standardLeviCentralizerFactor_comp B.i ν J B.centralizer.j
        B.centralizer.isRepresentedBy)
    simp only [Grp.comp_hom_hom] at hpoint
    change z ≫
        (standardLeviCentralizerFactor B.i ν J B.centralizer.j
          B.centralizer.isRepresentedBy).hom.hom ≫
        (Standard.leviHom B.i ν J).hom.hom ∈ B.apartment.specialCompactSubgroup x ↔ _
    rw [hpoint]
    rfl
  rw [hcomp, specialCompactCentralizer_comap B x hK]

end CompactIntersection

end Langlands.Plancherel.RenardCartan
