import Langlands.GroupScheme.Reductive.BasedAffineBorel
import Langlands.GroupScheme.RelativeLevi.CentralizerNeighbourhood
import Langlands.GroupScheme.SmoothIsomorphismLocus

/-! # The centralizer of a fibrewise regular split-torus cocharacter -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffineRegularBorel

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (n : I → ℤ)
  (P : RootDatum J (I → ℤ) (I → ℤ))
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hn : ∀ a : J, ∑ j, P.root a j * n j ≠ 0)
  (hG : IsReductive G) (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)

include hP hn hG hi hmax in
/-- Fibrewise regularity identifies the actual centralizer with the original
split maximal torus, even over a nonreduced ring. -/
theorem centralizer_eq_range :
    Dynamic.centralizer (cocharacter i n) = SubgroupFunctor.range i := by
  let S := Spec (CommRingCat.of R)
  let ν := splitTorus.exponentCocharacter S I n
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨Z, z, _, hZfp, hz⟩ :=
    (dynamicBaseRepresentability S G (cocharacter i n)).2.2
  let f := RelativeCocharacterCentralizerNeighbourhood.comparison
    (T := splitTorus.commGroupScheme S I) i ν z hz
  have : Smooth (splitTorus S I).X.hom := (isSplitTorus_splitTorus (S := S) I).smooth
  have : LocallyOfFinitePresentation Z.X.hom := hZfp
  have : IsIso f := by
    apply SmoothIsomorphismLocus.isIso_of_group_residueField_fibres
    intro s
    let φ := Spec.preimage (S.fromSpecResidueField s)
    let : Algebra R (S.residueField s) := φ.hom.toAlgebra
    have hb : algebraBaseMap R (S.residueField s) = S.fromSpecResidueField s :=
      Spec.map_preimage _
    have hs : Dynamic.centralizer
        (Dynamic.baseChangeCocharacter (S.fromSpecResidueField s) (cocharacter i n)) =
        SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i) := by
      rw [← hb, cocharacter_baseChange]
      have ht := centralizer_comp_eq_range_of_isRegular
        (T := splitTorus.commGroupScheme (Spec (CommRingCat.of (S.residueField s))) I)
        (hG.isConnectedReductive_algebraMap (S.residueField s))
        (isSplitTorus_splitTorus I)
        (splitTorus.baseChangeHom (K := S.residueField s) G I i)
        (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax
          (S.residueField s))
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of (S.residueField s))) I n)
        (isRegular_field i n P hP hn (S.residueField s))
      have hr : SubgroupFunctor.range (splitTorus.baseChangeHom
          (K := S.residueField s) G I i) =
          SubgroupFunctor.range ((baseChange (algebraBaseMap R (S.residueField s))).map i) :=
        SubgroupFunctor.range_iso_comp
          (splitTorus.baseChangeIso (algebraBaseMap R (S.residueField s)) I).symm _
      rwa [hr] at ht
    have := RelativeCocharacterCentralizerNeighbourhood.isIso_comparison_residueFiber
      (T := splitTorus.commGroupScheme S I) i ν z hz hi s hs
    exact TorusIsomorphismLocus.isIso_of_underlying _
  calc
    Dynamic.centralizer (cocharacter i n) = SubgroupFunctor.range z := hz.2.symm
    _ = SubgroupFunctor.range (f ≫ z) :=
      (SubgroupFunctor.range_iso_comp (asIso f) z).symm
    _ = SubgroupFunctor.range i := by
      rw [RelativeCocharacterCentralizerNeighbourhood.comparison_comp]

/-- Any actual representative of this centralizer is canonically identified
with the supplied split maximal torus. -/
def centralizerIso {Z : GroupScheme (Spec (CommRingCat.of R))} (z : Z ⟶ G)
    (hz : (Dynamic.centralizer (cocharacter i n)).IsRepresentedBy z) :
    Z ≅ splitTorus (Spec (CommRingCat.of R)) I := by
  have : Mono i.hom.hom.left := hi.mono
  exact hz.isoOfIsRepresentedBy
    ⟨Over.mono_of_mono_left _, (centralizer_eq_range i n P hP hn hG hi hmax).symm⟩

/-- The isomorphism respects the given inclusion in the ambient group. -/
theorem centralizerIso_hom_comp {Z : GroupScheme (Spec (CommRingCat.of R))}
    (z : Z ⟶ G) (hz : (Dynamic.centralizer (cocharacter i n)).IsRepresentedBy z) :
    (centralizerIso i n P hP hn hG hi hmax z hz).hom ≫ i = z :=
  hz.isoOfIsRepresentedBy_hom_comp _

end Langlands.GroupScheme.AffineRegularBorel
