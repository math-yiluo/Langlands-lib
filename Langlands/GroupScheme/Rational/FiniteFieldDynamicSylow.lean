import Langlands.Group.SplitTitsSylow
import Langlands.GroupScheme.Rational.RelativeTitsSystemProof
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsProof
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.TorusPointsPSubgroups
import Langlands.GroupScheme.Rational.UnipotentPointsPGroup
import Langlands.GroupScheme.Rational.ParabolicFunctor
import Langlands.GroupScheme.Dynamic.SplitContractingSubgroup
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteFieldPoints

/-! # Sylow subgroups from generic contracting subgroups over finite fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- Actual rational points of an affine finite type group over a finite field are finite. -/
theorem finite_rationalPoints_of_finite_field {k : Type u} [Field k] [Finite k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] : Finite (rationalPoints G) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Finite (RingPoint k G.X k) :=
    Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteFieldPoints.finite_ringPoint k
  exact Finite.of_equiv _ (rationalPointEquiv k G.X).symm

section Limit

variable {k : Type u} [Field k] {G C : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom C.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (c : C ⟶ G) (hc : (Dynamic.centralizer χ).IsRepresentedBy c)
    (hC : IsTorus C) (p : ℕ) [Fact p.Prime] [CharP k p]

include hc hC in
/-- With torus Levi, every defining-characteristic p-subgroup of the dynamic
parabolic lies in the contracting subgroup. -/
theorem pSubgroup_le_unipotent_of_torus_levi
    (P : Subgroup (rationalPoints G)) (hPB : P ≤ RationalPoint.parabolic χ)
    (hP : IsPGroup p P) : P ≤ RationalPoint.unipotent χ := by
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let e : rationalPoints C ≃* RationalPoint.levi χ := hc.rationalPointsEquiv
  intro x hx
  let b : RationalPoint.parabolic χ := ⟨x, hPB hx⟩
  obtain ⟨r, hr⟩ := hP.exists_pow_pow_eq_one (⟨x, hx⟩ : P)
  have hxpow : x ^ p ^ r = (1 : rationalPoints G) :=
    congrArg (fun y : P => (y : rationalPoints G)) hr
  have hb : b ^ p ^ r = 1 := Subtype.ext hxpow
  have hz : e.symm (RationalPoint.limitHom χ b) = 1 := by
    apply (pow_prime_pow_eq_one_iff_of_isTorus p hC r _).mp
    rw [← map_pow, ← map_pow, hb, map_one, map_one]
  have hl : RationalPoint.limitHom χ b = 1 := by
    apply e.symm.injective
    simpa only [map_one] using hz
  have hbker : b ∈ (RationalPoint.limitHom χ).ker := hl
  rw [RationalPoint.ker_limitHom] at hbker
  exact hbker

end Limit

section Generic

variable {k : Type u} [Field k] [Finite k]
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G)
    (ha : IsMaximalSplitTorus a) (ν : cocharacterLattice A)
    (c : C ⟶ G) (hc : (torusCentralizer a).IsRepresentedBy c)
    (hclosed : IsClosedSubgroup c) (hC : IsTorus C)

/-- The actual contracting points of a generic cocharacter are a Sylow subgroup
when the whole maximal-split-torus centralizer is a torus. -/
def genericUnipotentSylowOfTorusCentralizer
    (hν : haveI := hG.isAffineHom; IsGenericCocharacter a ν) :
    Sylow (ringChar k) (rationalPoints G) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Mono a.hom.hom.left := ha.isSplitSubtorus.mono
  let : IsAffineHom C.X.hom := hclosed.isAffineHom
  let : Finite (rationalPoints G) := finite_rationalPoints_of_finite_field G
  let : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  let χ := CommGroupScheme.groupHom ν ≫ a
  have hgen : Dynamic.centralizer χ = torusCentralizer a :=
    genericCentralizer k G hG A a ha ν hν
  have hcχ : (Dynamic.centralizer χ).IsRepresentedBy c := hgen.symm ▸ hc
  have hB : standardParabolicPoints a ν ∅ = RationalPoint.parabolic χ := by
    change (standardParabolic a ν ∅).carrier _ = _
    rw [(standardParabolicEndpoints k G hG A a ha ν hν).1]
  have htits := (relativeTitsSystem k G hG A a ha ν hν).isTitsSystem
  rw [hB] at htits
  have hUB := RationalPoint.unipotent_le_parabolic χ
  have hBU := (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mp
    (RationalPoint.unipotent_normal χ)
  have hsplit : ∀ b ∈ RationalPoint.parabolic χ,
      ∃ u ∈ RationalPoint.unipotent χ, ∃ t : normalizerPoints a,
        QuotientGroup.mk' ((centralizerPoints a).subgroupOf (normalizerPoints a)) t = 1 ∧
          b = u * t := by
    intro b hb
    obtain ⟨⟨u, l⟩, ⟨hu, hl, hbl⟩, _⟩ :=
      RationalPoint.existsUnique_unipotent_mul_levi χ hb
    have hlZ : l ∈ centralizerPoints a := by
      rw [← torusCentralizer_carrier_base a, ← hgen]
      exact hl
    let t : normalizerPoints a := ⟨l, centralizerPoints_le_normalizerPoints a hlZ⟩
    refine ⟨u, hu, t, ?_, hbl⟩
    change t ∈ (QuotientGroup.mk'
      ((centralizerPoints a).subgroupOf (normalizerPoints a))).ker
    rw [QuotientGroup.ker_mk']
    exact hlZ
  have hU : IsPGroup (ringChar k) (RationalPoint.unipotent χ) := by
    let U := Dynamic.Affine.unipotentScheme χ
    let j : U ⟶ G := Dynamic.Affine.unipotentHom χ
    have hj := Dynamic.Affine.isRepresentedBy_unipotentHom χ
    have hjc := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
    let : IsAffineHom U.X.hom := hjc.isAffineHom
    let : Smooth U.X.hom := (dynamicSmooth k G χ U j).2.2 hj
    have hu := Dynamic.isUnipotent_of_isRepresentedBy_unipotent χ hj hjc
    change IsPGroup (ringChar k) ((Dynamic.unipotent χ).carrier _)
    rw [← hj.2]
    exact isPGroup_range_testPoints_of_isUnipotent (ringChar k) hu j _
  exact htits.sylowOfSplit hUB hBU hsplit hU
    (fun P hPB hP => pSubgroup_le_unipotent_of_torus_levi χ c hcχ hC _ P hPB hP)

/-- The constructed Sylow subgroup is literally the contracting subgroup. -/
@[simp] theorem genericUnipotentSylowOfTorusCentralizer_toSubgroup
    (hν : haveI := hG.isAffineHom; IsGenericCocharacter a ν) :
    (genericUnipotentSylowOfTorusCentralizer hG A a ha ν c hc hclosed hC hν).toSubgroup =
      RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ a) := rfl

end Generic

end Langlands.GroupScheme
