import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope
import Langlands.GroupScheme.Rational.SplitTorusImage
import Langlands.GroupScheme.Dynamic.ClosedSubgroup

/-! # Cocharacters factor through the fixed torus envelope -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Every homomorphism from a split torus has all-test image in the fixed
closed envelope, even when the homomorphism is not a closed immersion. -/
theorem IsSplitTorus.range_le_closedTorusEnvelope
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (f : T.toGrp ⟶ G) :
    SubgroupFunctor.range f ≤ closedTorusEnvelope G := by
  obtain ⟨T', p, i, hi, hp, -⟩ := hT.exists_factor_isSplitSubtorus f
  intro U x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  apply closedTorusEnvelope_containsTori G T' i hi.1.isTorus hi.2 U
  refine SubgroupFunctor.mem_range.mpr ⟨t ≫ p.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, hp]

namespace TorusGeneratedEnvelope

variable (D : TorusGeneratedEnvelope G)

/-- Factor an arbitrary split-torus homomorphism through its torus envelope. -/
def splitTorusFactor {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (f : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) : T.toGrp ⟶ D.group :=
  D.represents.factorHom f (hT.range_le_closedTorusEnvelope f)

theorem splitTorusFactor_comp {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (f : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) :
    D.splitTorusFactor f hT ≫ D.inclusion = f :=
  D.represents.factorHom_comp _ _

theorem splitTorusFactor_unique {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (f : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (a : T.toGrp ⟶ D.group) (ha : a ≫ D.inclusion = f) :
    a = D.splitTorusFactor f hT :=
  D.represents.hom_ext (ha.trans (D.splitTorusFactor_comp f hT).symm)

/-- The actual cocharacter in the envelope inducing a supplied ambient cocharacter. -/
def cocharacterFactor (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D.group :=
  D.splitTorusFactor χ isSplitTorus_gm

theorem cocharacterFactor_comp (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    D.cocharacterFactor χ ≫ D.inclusion = χ :=
  D.splitTorusFactor_comp χ isSplitTorus_gm

theorem cocharacterFactor_unique (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (a : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D.group)
    (ha : a ≫ D.inclusion = χ) :
    a = D.cocharacterFactor χ :=
  D.splitTorusFactor_unique χ isSplitTorus_gm a ha

/-- Dynamic parabolics restrict to the envelope on every relative test. -/
theorem parabolic_cocharacterFactor (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    Dynamic.parabolic (D.cocharacterFactor χ) =
      (Dynamic.parabolic χ).comap D.inclusion := by
  simpa only [D.cocharacterFactor_comp] using
    Dynamic.parabolic_eq_comap_of_isClosedSubgroup
      (D.cocharacterFactor χ) D.inclusion D.closed

/-- Dynamic unipotent functors restrict to the envelope on every relative test. -/
theorem unipotent_cocharacterFactor (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    Dynamic.unipotent (D.cocharacterFactor χ) =
      (Dynamic.unipotent χ).comap D.inclusion := by
  simpa only [D.cocharacterFactor_comp] using
    Dynamic.unipotent_eq_comap_of_isClosedSubgroup
      (D.cocharacterFactor χ) D.inclusion D.closed

/-- Dynamic centralizers restrict to the envelope on every relative test. -/
theorem centralizer_cocharacterFactor (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    Dynamic.centralizer (D.cocharacterFactor χ) =
      (Dynamic.centralizer χ).comap D.inclusion := by
  simpa only [D.cocharacterFactor_comp] using
    Dynamic.centralizer_eq_comap_of_isClosedSubgroup
      (D.cocharacterFactor χ) D.inclusion D.closed

end TorusGeneratedEnvelope

end Langlands.GroupScheme
