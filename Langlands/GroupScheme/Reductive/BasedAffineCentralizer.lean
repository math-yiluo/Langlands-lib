import Langlands.GroupScheme.Reductive.AffineRegularCentralizer

/-! # Canonical based cocharacters have the prescribed split centralizer -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace RelativeCocharacterCentralizerNeighbourhood

variable {S : Scheme.{u}} {G : GroupScheme S} {T : CommGroupScheme S}
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [Smooth T.toGrp.X.hom]
    (t : T.toGrp ⟶ G) (ν : cocharacterLattice T) (ht : IsClosedSubgroup t)

include ht in
/-- Equality on every residue fibre identifies the actual global centralizer
with a smooth commutative subgroup. The empty base is included. -/
theorem centralizer_eq_range_of_residueFibres
    (hs : ∀ s : S, Dynamic.centralizer
        (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s)
          (CommGroupScheme.groupHom ν ≫ t)) =
      SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map t)) :
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t) =
      SubgroupFunctor.range t := by
  obtain ⟨Z, z, _, hZfp, hz⟩ :=
    (dynamicBaseRepresentability S G (CommGroupScheme.groupHom ν ≫ t)).2.2
  let f := comparison t ν z hz
  let : LocallyOfFinitePresentation Z.X.hom := hZfp
  have : IsIso f := by
    apply SmoothIsomorphismLocus.isIso_of_group_residueField_fibres
    intro s
    have := isIso_comparison_residueFiber t ν z hz ht s (hs s)
    exact TorusIsomorphismLocus.isIso_of_underlying _
  calc
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t) =
        SubgroupFunctor.range z := hz.2.symm
    _ = SubgroupFunctor.range (f ≫ z) :=
      (SubgroupFunctor.range_iso_comp (asIso f) z).symm
    _ = SubgroupFunctor.range t := by rw [comparison_comp]

end RelativeCocharacterCentralizerNeighbourhood

namespace AffineRegularBorel

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I] [Fintype J]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hG : IsReductive G) (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)

include hP hG hi hmax in
/-- The positive-coroot cocharacter has exactly the original split maximal
torus as its centralizer over every ring, including the zero ring. -/
theorem centralizer_eq_range_positiveCorootSum :
    Dynamic.centralizer (cocharacter i (BasedBorelExponent.positiveCorootSum P b)) =
      SubgroupFunctor.range i := by
  let S := Spec (CommRingCat.of R)
  let n := BasedBorelExponent.positiveCorootSum P b
  let ν := splitTorus.exponentCocharacter S I n
  let : Smooth G.X.hom := hG.smooth
  let : Smooth (splitTorus S I).X.hom := (isSplitTorus_splitTorus (S := S) I).smooth
  apply RelativeCocharacterCentralizerNeighbourhood.centralizer_eq_range_of_residueFibres
    (T := splitTorus.commGroupScheme S I) i ν hi
  intro s
  let φ := Spec.preimage (S.fromSpecResidueField s)
  let : Algebra R (S.residueField s) := φ.hom.toAlgebra
  have hb : algebraBaseMap R (S.residueField s) = S.fromSpecResidueField s :=
    Spec.map_preimage _
  change Dynamic.centralizer
      (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s) (cocharacter i n)) = _
  rw [← hb, cocharacter_baseChange]
  have hn := positiveCorootExponent_regular i P b hP (S.residueField s)
  have ht := centralizer_comp_eq_range_of_isRegular
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of (S.residueField s))) I)
    (hG.isConnectedReductive_algebraMap (S.residueField s))
    (isSplitTorus_splitTorus I)
    (splitTorus.baseChangeHom (K := S.residueField s) G I i)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax (S.residueField s))
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of (S.residueField s))) I n)
    (isRegular_field i n P hP hn (S.residueField s))
  have hr : SubgroupFunctor.range (splitTorus.baseChangeHom
      (K := S.residueField s) G I i) =
      SubgroupFunctor.range ((baseChange (algebraBaseMap R (S.residueField s))).map i) :=
    SubgroupFunctor.range_iso_comp
      (splitTorus.baseChangeIso (algebraBaseMap R (S.residueField s)) I).symm _
  rwa [hr] at ht

/-- Any actual canonical-cocharacter centralizer representative is identified
with the prescribed coordinate torus. -/
def centralizerIso_positiveCorootSum {Z : GroupScheme (Spec (CommRingCat.of R))}
    (z : Z ⟶ G)
    (hz : (Dynamic.centralizer
      (cocharacter i (BasedBorelExponent.positiveCorootSum P b))).IsRepresentedBy z) :
    Z ≅ splitTorus (Spec (CommRingCat.of R)) I := by
  have : Mono i.hom.hom.left := hi.mono
  exact hz.isoOfIsRepresentedBy
    ⟨Over.mono_of_mono_left _,
      (centralizer_eq_range_positiveCorootSum i P b hP hG hi hmax).symm⟩

/-- The canonical representative comparison respects the actual inclusion. -/
theorem centralizerIso_positiveCorootSum_hom_comp
    {Z : GroupScheme (Spec (CommRingCat.of R))} (z : Z ⟶ G)
    (hz : (Dynamic.centralizer
      (cocharacter i (BasedBorelExponent.positiveCorootSum P b))).IsRepresentedBy z) :
    (centralizerIso_positiveCorootSum i P b hP hG hi hmax z hz).hom ≫ i = z :=
  hz.isoOfIsRepresentedBy_hom_comp _

end AffineRegularBorel

end Langlands.GroupScheme
