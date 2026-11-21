import Langlands.Global.AdelicIwasawaAssembly
import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.IntegralIwasawaFamilyProof
import Langlands.GroupScheme.Rational.IdentityParabolic

/-! # Adelic compact assembly with simultaneous standard Levi intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter NumberField
open scoped CategoryTheory.MonObj Pointwise ValuativeRel

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints CoordinateCompactAssembly CoordinateCompactPatching

namespace FiniteTypeIntegralFamily

variable {F : Type u} [Field F] [NumberField F]
  {G H P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- The fixed integral families are compatible with a closed immersion after discarding
finitely many places. Restriction of the ambient embedding provides the same integrality
conditions on the smaller group. -/
theorem eventually_comap_eq (j : H ⟶ G) (hj : IsClosedSubgroup j) :
    ∀ᶠ v : FinitePlace F in cofinite,
      (subgroup F G v).comap (H.affinePointsTarget j (placeCompletion F (.inr v))) =
        subgroup F H v := by
  let rho := representation F G
  have hrho : IsClosedSubgroup (rho.restrict j) := hj.comp (isClosed_representation F G)
  filter_upwards [eventually_subgroup_eq F H (rho.restrict j) hrho] with v hv
  rw [hv]
  ext x
  let L := Langlands.GeneralLinearGroup.integralSubgroup (Fin (dimension F G))
    (v.adicCompletionIntegers F).toSubring
  change rho.affineMatrix _ (H.affinePointsTarget j (placeCompletion F (.inr v)) x) ∈ L ↔
    (rho.restrict j).affineMatrix _ x ∈ L
  rw [MatrixRepresentation.affineMatrix_restrict, GroupScheme.affinePointsTarget_apply]

omit [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] in
/-- The published good integral models give the Iwasawa properties for the
fixed representation family itself. -/
theorem isIntegralIwasawaFamily (hG : IsConnectedReductive G) (p : P ⟶ G)
    (hp : IsParabolicSubgroup p) :
    IntegralIwasawaFamily.IsIntegralIwasawaFamily F G P p (subgroup F G) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let D := IntegralIwasawaFamily.goodModelData F G hG P p hp
  apply IntegralIwasawaFamily.isIntegralIwasawaFamily_of_models F G P p D.1 D.2.ambient
  apply IntegralIwasawaFamily.ModelLocalConditions.of_quotientStatement F D.1
    IntegralIwasawaFamily.relativeParabolicQuotient D.2
  intro v
  let : ValuativeRel (FiniteCompletion F v.1) := FiniteCompletion.valuativeRel v.1
  let : IsNonarchimedeanLocalField (FiniteCompletion F v.1) :=
    FiniteCompletion.isNonarchimedeanLocalField v.1
  exact (IntegralModel.maximalCompactStatement _ _
    (connectedReductiveFieldExtensionStatement F (FiniteCompletion F v.1) G hG)
    (IntegralModelCompletions.canonicalModel F D.1 v D.2.ambient)
    (IntegralModelCompletions.canonicalModelData_specialFibre F D.1 v D.2).1).2

end FiniteTypeIntegralFamily

namespace AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

/-- A closed embedding pulls a uniformly integral family back to a uniformly
integral family. Use surjectivity on affine global functions before taking
the exceptional finite set. -/
theorem IsUniformlyIntegral.comap_of_closedSubgroup
    {K : ∀ v : Place F, Subgroup (PlaceGroupPoints F G v)}
    (hK : IsUniformlyIntegral F G K) (j : H ⟶ G) (hj : IsClosedSubgroup j) :
    IsUniformlyIntegral F H (fun v => (K v).comap (H.affinePointsTarget j (placeCompletion F v))) := by
  let : IsClosedImmersion j.hom.hom.left := hj
  intro a
  obtain ⟨b, rfl⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine j.hom.hom.left).2 a
  filter_upwards [hK b] with v hv x hx
  rw [← GroupScheme.affinePointEvaluation_postcomp]
  exact hv _ hx

end AdelicGroupPoints

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

/-- The empty set of Levi roots indexes the minimal standard parabolic. -/
abbrev minimalIndex : StandardIndex F G fam.i fam.ν := ⟨∅, Set.empty_subset _⟩

local notation "I₀" => fam.minimalIndex

/-- A local compact serves the minimal parabolic and has maximal compact
inverse images in every actual standard Levi. -/
def IsStandardLeviCompact (v : Place F) (K : Subgroup (PlaceGroupPoints F G v)) : Prop :=
  IsLocalIwasawaCompact ((fam.P I₀).affinePointsTarget (fam.p I₀) (placeCompletion F v)) K ∧
    ∀ J : StandardIndex F G fam.i fam.ν,
      let T := PlaceGroupPoints F (fam.M J) v
      let L := K.comap ((fam.M J).affinePointsTarget (fam.l J ≫ fam.p J) (placeCompletion F v))
      IsCompact (L : Set T) ∧
        ∀ L' : Subgroup T, IsCompact (L' : Set T) → L ≤ L' → L' = L

/-- The fixed integral family serves the whole standard family away from a
single finite set. The standard indices are finite, so one can intersect the
eventual conditions for all Levi embeddings. -/
theorem eventually_isStandardLeviCompact_integral :
    ∀ᶠ v : FinitePlace F in cofinite,
      fam.IsStandardLeviCompact (.inr v) (FiniteTypeIntegralFamily.subgroup F G v) := by
  let : Finite (StandardIndex F G fam.i fam.ν) :=
    (fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν).finite_subsets.to_subtype
  have hMin := (FiniteTypeIntegralFamily.isIntegralIwasawaFamily fam.connectedReductive
    (fam.p I₀) (fam.isCompatible I₀).parabolic).1
  have hLevi (J : StandardIndex F G fam.i fam.ν) :
      ∀ᶠ v : FinitePlace F in cofinite,
        let T := PlaceGroupPoints F (fam.M J) (.inr v)
        let L := (FiniteTypeIntegralFamily.subgroup F G v).comap
          ((fam.M J).affinePointsTarget (fam.l J ≫ fam.p J) (placeCompletion F (.inr v)))
        IsCompact (L : Set T) ∧
          ∀ L' : Subgroup T, IsCompact (L' : Set T) → L ≤ L' → L' = L := by
    have hM := (fam.isCompatible J).levi.isConnectedReductive
    let : IsAffineHom (fam.M J).X.hom := hM.isAffineHom
    have hL : IsClosedSubgroup (fam.l J ≫ fam.p J) :=
      (fam.isCompatible J).levi.isClosedSubgroup.comp (fam.isCompatible J).parabolic.isClosedSubgroup
    have hModel := (FiniteTypeIntegralFamily.isIntegralIwasawaFamily hM _
      hM.isParabolicSubgroup_id).1
    filter_upwards [FiniteTypeIntegralFamily.eventually_comap_eq (F := F) _ hL, hModel]
      with v heq hv
    dsimp only
    rw [heq]
    exact ⟨hv.1, hv.2.1⟩
  filter_upwards [hMin, eventually_all.mpr hLevi] with v hv hL
  exact ⟨⟨⟨hv.1, hv.2.1⟩, hv.2.2⟩, hL⟩

/-- Local existence at each place implies existence of one adelic maximal
compact serving the minimal parabolic and all standard Levis. -/
def StandardLeviCompactAssemblyStatement : Prop :=
  (∀ v : Place F, ∃ L : Subgroup (PlaceGroupPoints F G v), fam.IsStandardLeviCompact v L) →
    ∃ K : Subgroup (AdelicGroupPoints F G),
      IsParabolicIwasawaCompact F G (fam.P I₀) (fam.p I₀) K ∧
      ∀ J : StandardIndex F G fam.i fam.ν, IsMaximalCompactSubgroup F (fam.M J)
        (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)

theorem standardLeviCompactAssembly : fam.StandardLeviCompactAssemblyStatement := by
  intro hlocal
  let K₀ := extendFinite F G (FiniteTypeIntegralFamily.subgroup F G)
  let Kloc := patchFamily fam.IsStandardLeviCompact hlocal K₀
  have hKloc (v : Place F) : fam.IsStandardLeviCompact v (Kloc v) :=
    good_patchFamily _ hlocal K₀ v
  have heq : ∀ᶠ v : Place F in cofinite, Kloc v = K₀ v :=
    patchFamily_eventually_eq _ hlocal K₀
      (eventually_place_of_finite F fam.eventually_isStandardLeviCompact_integral)
  have hF := FiniteTypeIntegralFamily.isIntegralIwasawaFamily fam.connectedReductive
    (fam.p I₀) (fam.isCompatible I₀).parabolic
  have hint : IsUniformlyIntegral F G K₀ := hF.2.2
  have hint' := hint.of_eventuallyEq heq
  have habsorb (a : AdelicGroupPoints F G) : ∀ᶠ v : Place F in cofinite, atPlace F G v a ∈ Kloc v := by
    filter_upwards [heq, eventually_atPlace_mem_of_finite F G (K := K₀) hF.2.1 a] with v hv ha
    rwa [hv]
  let K := coordinateSubgroup (fun v => (atPlace F G v).toMonoidHom) Kloc
  refine ⟨K, ⟨?_, ?_⟩, ?_⟩
  · exact compact_maximal_coordinateSubgroup hint'.compactProductLift
      (fun _ _ h => ext_atPlace F G h) (fun v => (atPlace F G v).continuous)
      (fun v => (hKloc v).1.1.1) (fun v => (hKloc v).1.1.2)
  · exact range_mul_coordinateSubgroup_eq_univ (map F (fam.P I₀) G (fam.p I₀)).toMonoidHom
      (fun v => (atPlace F (fam.P I₀) v).toMonoidHom)
      (fun v => (fam.P I₀).affinePointsTarget (fam.p I₀) (placeCompletion F v))
      (fun v x => atPlace_map F (fam.P I₀) (fam.p I₀) v x) habsorb
      (fun q hq => exists_atPlace_eq_of_eventually_one F (fam.P I₀) q hq)
      (fun v => (hKloc v).1.2)
  · intro J
    let j := fam.l J ≫ fam.p J
    have hj : IsClosedSubgroup j :=
      (fam.isCompatible J).levi.isClosedSubgroup.comp (fam.isCompatible J).parabolic.isClosedSubgroup
    let Lloc (v : Place F) := (Kloc v).comap ((fam.M J).affinePointsTarget j (placeCompletion F v))
    have hL : K.comap (map F (fam.M J) G j).toMonoidHom =
        coordinateSubgroup (fun v => (atPlace F (fam.M J) v).toMonoidHom) Lloc := by
      ext x
      change (∀ v, atPlace F G v (map F (fam.M J) G j x) ∈ Kloc v) ↔
        ∀ v, (fam.M J).affinePointsTarget j (placeCompletion F v) (atPlace F (fam.M J) v x) ∈ Kloc v
      simp only [atPlace_map]
    rw [hL]
    exact compact_maximal_coordinateSubgroup (hint'.comap_of_closedSubgroup j hj).compactProductLift
      (fun _ _ h => ext_atPlace F (fam.M J) h) (fun v => (atPlace F (fam.M J) v).continuous)
      (fun v => ((hKloc v).2 J).1) (fun v => ((hKloc v).2 J).2)

end StandardParabolicFamily

end Langlands.Global
