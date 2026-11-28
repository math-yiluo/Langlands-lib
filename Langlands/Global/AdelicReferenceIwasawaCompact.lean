import Langlands.Global.AdelicGoodPositionIwasawaCompactProof
import Langlands.Global.AdelicPositiveTorusCompatibility

/-! # A reference compact for characteristic Eisenstein truncation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Opposite
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints AdelicSiegelFactors CoordinateCompactAssembly CoordinateCompactPatching

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

/-- For a fixed standard family, a maximal adelic compact gives minimal Iwasawa coverage,
is maximal on inverse images in all standard Levis, and its intersection with the
minimal parabolic centralizes the positive torus. -/
def ReferenceIwasawaCompactStatement : Prop :=
  ∃ K : Subgroup (AdelicGroupPoints F G),
    IsParabolicIwasawaCompact F G (fam.P fam.minimalIndex) (fam.p fam.minimalIndex) K ∧
    (∀ J, IsMaximalCompactSubgroup F (fam.M J)
      (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) ∧
    IsPositiveTorusCompatible F G fam.T fam.i fam.ν fam.T (𝟙 fam.T) K

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem pointRange_eq_of_subgroupRange_eq
    {P Q : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G} {q : Q ⟶ G}
    (h : SubgroupFunctor.range p = SubgroupFunctor.range q) (A : CommAlgCat (CommRingCat.of F)) :
    Set.range (P.affinePointsTarget p A) = Set.range (Q.affinePointsTarget q A) := by
  let X := (algSpec (CommRingCat.of F)).obj (op A)
  change ((SubgroupFunctor.range p).carrier X : Set (G.affinePoints A)) =
    (SubgroupFunctor.range q).carrier X
  rw [h]

theorem referenceIwasawaCompact : ReferenceIwasawaCompactStatement fam := by
  let I := fam.minimalIndex
  let good (v : Place F) (L : Subgroup (PlaceGroupPoints F G v)) : Prop :=
    match v with
    | .inl w => fam.IsStandardLeviCompact (.inl w) L ∧
        InfinitePlaceGroupPoints.IsLeviCompatibleIwasawaCompact F G
          (fam.P I) (fam.p I) (fam.M I) (fam.l I) w L
    | .inr w => fam.IsStandardLeviCompact (.inr w) L
  have hBT : Geometry.Building.BruhatTitsAvailabilityStatement.{u} :=
    Geometry.Building.bruhatTitsAvailabilityReduction
      (Geometry.Building.groupAxiomsExistenceReduction
        Geometry.Building.rootValuationBuildingConstruction
        Geometry.Building.rootGroupActionAxiom
        Geometry.Building.iwahoriDecompositionAxiom
        Geometry.Building.integralModelAxioms)
  have hex : ∀ v, ∃ L, good v L := by
    rintro (v | v)
    · exact InfinitePlaceGroupPoints.exists_standardLeviCompatibleCompact F G fam v
    · exact FinitePlaceGroupPoints.finitePlaceStandardLeviCompactReduction hBT F G fam v
  let K₀ := extendFinite F G (FiniteTypeIntegralFamily.subgroup F G)
  let Kloc := patchFamily good hex K₀
  have hlocal (v : Place F) : good v (Kloc v) := good_patchFamily good hex K₀ v
  have hstandard (v : Place F) : fam.IsStandardLeviCompact v (Kloc v) := by
    cases v with
    | inl v => exact (hlocal (.inl v)).1
    | inr v => exact hlocal (.inr v)
  have heq : ∀ᶠ v : Place F in cofinite, Kloc v = K₀ v :=
    patchFamily_eventually_eq good hex K₀
      (eventually_place_of_finite F fam.eventually_isStandardLeviCompact_integral)
  let K := coordinateSubgroup (fun v => (atPlace F G v).toMonoidHom) Kloc
  have hK := fam.standardLeviCompact_of_coordinateFamily Kloc hstandard heq
  refine ⟨K, hK.1, hK.2, ?_⟩
  let T := fam.T
  have hT := fam.maximalSplit.isSplitSubtorus.1
  have hMin := standardLevi_empty_eq_torusCentralizer_of_generic fam.i fam.ν
    fam.connectedReductive fam.maximalSplit fam.generic
  intro k hk hkP a
  change k * positiveMap F G T fam.i T (𝟙 T) a = positiveMap F G T fam.i T (𝟙 T) a * k
  apply ext_atPlace F G
  intro v
  rw [map_mul, map_mul]
  cases v with
  | inl v =>
      let A := CommAlgCat.of F v.Completion
      have hP := pointRange_eq_of_subgroupRange_eq
        ((fam.isCompatible I).parabolic_eq.trans
          (Standard.isRepresentedBy_parabolicHom fam.i fam.ν ∅).2.symm) A
      have hM := pointRange_eq_of_subgroupRange_eq
        ((fam.isCompatible I).levi_eq.trans
          (Standard.isRepresentedBy_leviHom fam.i fam.ν ∅).2.symm) A
      have hkP' : atInfinitePlace F G v k ∈ Set.range
          ((fam.P I).affinePointsTarget (fam.p I) A) := by
        rw [hP]
        obtain ⟨p, rfl⟩ := hkP
        exact ⟨atInfinitePlace F (Standard.parabolicScheme fam.i fam.ν ∅) v p,
          (atPlace_map F _ (Standard.parabolicHom fam.i fam.ν ∅) (.inl v) p).symm⟩
      have hm := (hlocal (.inl v)).2.mem_levi F G hkP' (hk (.inl v))
      rw [hM] at hm
      have hc := commute_of_mem_standardLevi_image F G T fam.i fam.ν T (𝟙 T) hMin A
        (atInfinitePlace F G v k) hm (atInfinitePlace F T.toGrp v a.val)
      change atPlace F G (.inl v) k *
          atPlace F G (.inl v) (map F T.toGrp G (CommGroupScheme.groupHom (𝟙 T) ≫ fam.i) a.val) =
        atPlace F G (.inl v) (map F T.toGrp G (CommGroupScheme.groupHom (𝟙 T) ≫ fam.i) a.val) *
          atPlace F G (.inl v) k
      rw [atPlace_map]
      exact hc.eq
  | inr v =>
      have hfin := atFinitePlace_positiveMap F G T fam.i T (𝟙 T) hT v a
      change atFinitePlace F G v k * atFinitePlace F G v (positiveMap F G T fam.i T (𝟙 T) a) =
        atFinitePlace F G v (positiveMap F G T fam.i T (𝟙 T) a) * atFinitePlace F G v k
      rw [hfin, mul_one, one_mul]

end Langlands.Global.StandardParabolicFamily
