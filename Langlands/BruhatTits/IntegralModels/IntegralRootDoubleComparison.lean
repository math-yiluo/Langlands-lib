import Langlands.BruhatTits.IntegralModels.IntegralTorusRootSupport
import Langlands.GroupScheme.Rational.RelativeRootMultiples
import Langlands.GroupScheme.Rational.RootNonmultipliableFactors
import Langlands.GroupScheme.Rational.AbsentRootDoubleComparison

/-! # Root-multiple support and doubled-root comparison for integral models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp)

include hS

/-- If every positive integral multiple of a nonzero character is absent
from the actual root support, its intrinsic root functor is trivial. -/
theorem subgroup_eq_bot_of_noPositiveRoots
    {a : characterLattice S} (ha : a ≠ 0)
    (hroots : ∀ n : ℕ, 0 < n → n • a ∉ relativeRoots i) :
    subgroup i a = ⊥ := by
  rw [← weightFiltration_one_eq_subgroup hS i a ha]
  apply semigroupSubgroup_eq_bot_of_ambientWeights_vanish _ hS
  rintro χ ⟨n, hn, hn0, rfl⟩ hχ
  exact hroots n hn0
    ((mem_actionWeightSupport_conjugation_iff i
      (hS.nsmul_ne_zero ha hn0.ne')).mp hχ)

variable [Mono i.hom.hom.left]

/-- For an actual root, an absent double has trivial intrinsic root
functor; the root-system bound excludes every later multiple. -/
theorem subgroup_double_eq_bot_of_noDoubleRoot
    (hroot : HasRelativeRootSystem i)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (h2 : 2 • a ∉ relativeRoots i) :
    subgroup i (2 • a) = ⊥ := by
  apply subgroup_eq_bot_of_noPositiveRoots i hS
    (hS.nsmul_ne_zero ha.1 (by decide : (2 : ℕ) ≠ 0))
  intro n hn
  rw [← mul_smul]
  by_cases hn1 : n = 1
  · simpa only [hn1, one_mul] using h2
  · exact hroot.nsmul_not_mem_of_three_le ha (by omega)

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building

open GroupScheme

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- For an actual root of a supplied relative root system, the intrinsic
doubled root group agrees with KP's conditional doubled-root convention. -/
theorem rootGroupPoints_double_eq_doubleRootGroupPoints
    (hS : IsSplitTorus S.toGrp) (hroot : HasRelativeRootSystem i)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    rootGroupPoints i (2 • a) = doubleRootGroupPoints i a := by
  classical
  by_cases h2 : 2 • a ∈ relativeRoots i
  · simp only [doubleRootGroupPoints, h2, ite_true]
  · rw [doubleRootGroupPoints, ite_eq_right h2]
    change (RelativeRoot.subgroup i (2 • a)).carrier _ = ⊥
    rw [RelativeRoot.subgroup_double_eq_bot_of_noDoubleRoot i hS hroot ha h2]
    rfl

end Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom]
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}

namespace IntegralTorusData

variable (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)

include hT hQ in
/-- Quotient-root membership reflects to the original generic character
through the canonical specialization of the supplied integral split torus. -/
theorem mem_relativeRoots_of_specialized_quotient_root
    {a : characterLattice S}
    (ha : T.characterSpecialization hT a ∈
      relativeRoots (T.specialFibreInclusion ≫ Q.projection)) :
    a ∈ relativeRoots i :=
  (T.mem_relativeRoots_characterSpecialization_iff hT a).mp
    (Q.relativeRoots_subset_specialFibre hQ T hT ha)

include hT hQ in
/-- Every natural multiplier surviving in the actual quotient already
occurs among the original generic root multipliers. -/
theorem relativeRootMultipliers_quotient_subset
    (a : characterLattice S) :
    relativeRootMultipliers (T.specialFibreInclusion ≫ Q.projection)
        (T.characterSpecialization hT a) ⊆ relativeRootMultipliers i a := by
  intro n hn
  change n • T.characterSpecialization hT a ∈
    relativeRoots (T.specialFibreInclusion ≫ Q.projection) at hn
  apply T.mem_relativeRoots_of_specialized_quotient_root hT Q hQ
  simpa only [map_nsmul] using hn

variable [Mono i.hom.hom.left]

include hT hQ in
/-- No third or later multiple of an original actual root survives in
the reductive quotient, whether or not the first root survives. -/
theorem nsmul_specialization_not_mem_quotient_roots_of_three_le
    (hroot : HasRelativeRootSystem i)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {n : ℕ} (hn : 3 ≤ n) :
    n • T.characterSpecialization hT a ∉
      relativeRoots (T.specialFibreInclusion ≫ Q.projection) := by
  intro hna
  exact hroot.nsmul_not_mem_of_three_le ha hn
    (T.relativeRootMultipliers_quotient_subset hT Q hQ a hna)

include hT hQ in
/-- If the specialization of an original root is absent from the actual
quotient support, its intrinsic quotient-root functor equals its double. -/
theorem quotient_subgroup_eq_double_of_absent_root
    (hroot : HasRelativeRootSystem i)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (hfirst : T.characterSpecialization hT a ∉
      relativeRoots (T.specialFibreInclusion ≫ Q.projection)) :
    RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
        (T.characterSpecialization hT a) =
      RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
        (T.characterSpecialization hT (2 • a)) := by
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  have ha0 : T.characterSpecialization hT a ≠ 0 := by
    intro h
    apply ha.1
    exact (T.characterSpecialization hT).injective (h.trans (map_zero _).symm)
  rw [map_nsmul]
  exact RelativeRoot.subgroup_eq_double_of_absent_roots
    (T.specialFibreInclusion ≫ Q.projection)
    (hT.baseChange (IntegralModel.residueBaseMap R))
    (T.characterSpecialization hT a) ha0 hfirst
    (fun n hn => T.nsmul_specialization_not_mem_quotient_roots_of_three_le
      hT Q hQ hroot ha hn)

/-- Actual representatives of the two quotient-root functors are
isomorphic over their original quotient group. -/
def absentQuotientRootDoubleIso
    (hroot : HasRelativeRootSystem i)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (hfirst : T.characterSpecialization hT a ∉
      relativeRoots (T.specialFibreInclusion ≫ Q.projection))
    {U V : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    {jU : U ⟶ Q.quotient} {jV : V ⟶ Q.quotient}
    (hU : (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
      (T.characterSpecialization hT a)).IsRepresentedBy jU)
    (hV : (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
      (T.characterSpecialization hT (2 • a))).IsRepresentedBy jV) : U ≅ V :=
  hU.isoOfIsRepresentedBy
    ⟨hV.1, hV.2.trans
      (T.quotient_subgroup_eq_double_of_absent_root hT Q hQ hroot ha hfirst).symm⟩

/-- The representative comparison preserves the supplied ambient inclusion. -/
theorem absentQuotientRootDoubleIso_hom_comp
    (hroot : HasRelativeRootSystem i)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (hfirst : T.characterSpecialization hT a ∉
      relativeRoots (T.specialFibreInclusion ≫ Q.projection))
    {U V : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    {jU : U ⟶ Q.quotient} {jV : V ⟶ Q.quotient}
    (hU : (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
      (T.characterSpecialization hT a)).IsRepresentedBy jU)
    (hV : (RelativeRoot.subgroup (T.specialFibreInclusion ≫ Q.projection)
      (T.characterSpecialization hT (2 • a))).IsRepresentedBy jV) :
    (T.absentQuotientRootDoubleIso hT Q hQ hroot ha hfirst hU hV).hom ≫ jV = jU := by
  unfold absentQuotientRootDoubleIso
  apply SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp

end IntegralTorusData
end Langlands.BruhatTits.IntegralModels
