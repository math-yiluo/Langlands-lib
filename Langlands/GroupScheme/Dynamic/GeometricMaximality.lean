import Langlands.GroupScheme.Dynamic.SubgroupMaximality
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.SemistandardIntersection

/-! # Geometric maximality from a reductive dynamic centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {k : Type u} [Field k]
    {G Z P U : GroupScheme (Spec (CommRingCat.of k))}
    [hGaff : IsAffineHom G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (z : Z ⟶ G) (p : P ⟶ G) (r : U ⟶ P)
    (hP : (parabolic χ).IsRepresentedBy p) (hpc : IsClosedSubgroup p)
    (hU : (unipotent χ).IsRepresentedBy (r ≫ p))
    (hz : (centralizer χ).IsRepresentedBy z) (hzc : IsClosedSubgroup z)

local instance instGeometricMaximality1 :
    IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (toAlgebraicClosure k))
  infer_instance

include χ z p hP hpc hU hz hzc hGaff

/-- Factor a smooth connected normal unipotent closed subgroup of `P(χ)`
through an arbitrary compatible representative of `U(χ)`. -/
def normalUnipotentFactor
    {V : GroupScheme (Spec (CommRingCat.of k))} (v : V ⟶ P)
    (hvc : IsClosedSubgroup v) (hsm : Smooth V.X.hom)
    (hc : ConnectedSpace V.X.left) (hu : IsUnipotent V)
    (hn : (SubgroupFunctor.range v).IsNormal)
    (hZ : HasTrivialUnipotentRadical Z) : V ⟶ U :=
  hU.factorHom (v ≫ p)
    (normal_subgroup_range_comp_le_unipotent (χ := χ) (z := z) p hP hpc
      v hvc hn hz hzc hsm hc hu hZ)

/-- The factor has the prescribed inclusion into the actual parabolic. -/
theorem normalUnipotentFactor_comp
    {V : GroupScheme (Spec (CommRingCat.of k))} (v : V ⟶ P)
    (hvc : IsClosedSubgroup v) (hsm : Smooth V.X.hom)
    (hc : ConnectedSpace V.X.left) (hu : IsUnipotent V)
    (hn : (SubgroupFunctor.range v).IsNormal)
    (hZ : HasTrivialUnipotentRadical Z) :
    normalUnipotentFactor χ z p r hP hpc hU hz hzc v hvc hsm hc hu hn hZ ≫ r = v := by
  apply hP.hom_ext
  rw [Category.assoc]
  exact hU.factorHom_comp (v ≫ p) _

/-- Every such subgroup lies in the represented identity-limit subgroup
on every test scheme. -/
theorem normal_subgroup_range_le_unipotentRepresentative
    {V : GroupScheme (Spec (CommRingCat.of k))} (v : V ⟶ P)
    (hvc : IsClosedSubgroup v) (hsm : Smooth V.X.hom)
    (hc : ConnectedSpace V.X.left) (hu : IsUnipotent V)
    (hn : (SubgroupFunctor.range v).IsNormal)
    (hZ : HasTrivialUnipotentRadical Z) :
    SubgroupFunctor.range v ≤ SubgroupFunctor.range r := by
  let f := normalUnipotentFactor χ z p r hP hpc hU hz hzc v hvc hsm hc hu hn hZ
  have hf : f ≫ r = v :=
    normalUnipotentFactor_comp χ z p r hP hpc hU hz hzc v hvc hsm hc hu hn hZ
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  refine SubgroupFunctor.mem_range.mpr ⟨y ≫ f.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, hf]

/-- Over the algebraic closure, reductivity of the represented centralizer
supplies the radical hypothesis for the canonical factorization. -/
def geometricNormalUnipotentFactor
    (hZ : IsConnectedReductive Z)
    {V : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
    (v : V ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj P)
    (hvc : IsClosedSubgroup v) (hsm : Smooth V.X.hom)
    (hc : ConnectedSpace V.X.left) (hu : IsUnipotent V)
    (hn : (SubgroupFunctor.range v).IsNormal) :
    V ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj U := by
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  have hPb : (parabolic (baseChangeCocharacter b χ)).IsRepresentedBy (B.map p) := by
    rw [parabolic_baseChange]
    exact hP.baseChange b
  have hUb : (unipotent (baseChangeCocharacter b χ)).IsRepresentedBy
      (B.map r ≫ B.map p) := by
    rw [unipotent_baseChange, ← B.map_comp]
    exact hU.baseChange b
  exact normalUnipotentFactor (baseChangeCocharacter b χ) (B.map z) (B.map p) (B.map r)
    hPb (hpc.baseChange b) hUb (isRepresentedBy_centralizer_baseChange b χ hz)
    (hzc.baseChange b) v hvc hsm hc hu hn hZ.hasTrivialGeometricUnipotentRadical

/-- The geometric factorization commutes with inclusion into the base-changed
parabolic. -/
theorem geometricNormalUnipotentFactor_comp
    (hZ : IsConnectedReductive Z)
    {V : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k)))}
    (v : V ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj P)
    (hvc : IsClosedSubgroup v) (hsm : Smooth V.X.hom)
    (hc : ConnectedSpace V.X.left) (hu : IsUnipotent V)
    (hn : (SubgroupFunctor.range v).IsNormal) :
    geometricNormalUnipotentFactor χ z p r hP hpc hU hz hzc hZ v hvc hsm hc hu hn ≫
      (GroupScheme.baseChange (toAlgebraicClosure k)).map r = v := by
  unfold geometricNormalUnipotentFactor
  apply normalUnipotentFactor_comp

/-- The full geometric greatestness clause for an arbitrary compatible
representative of `U(χ)`, under connected reductivity of `Z(χ)`. -/
theorem geometric_normal_subgroup_range_le_unipotentRepresentative
    (hZ : IsConnectedReductive Z)
    (V : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))))
    (v : V ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj P)
    (hvc : IsClosedSubgroup v) (hsm : Smooth V.X.hom)
    (hc : ConnectedSpace V.X.left) (hu : IsUnipotent V)
    (hn : (SubgroupFunctor.range v).IsNormal) :
    SubgroupFunctor.range v ≤
      SubgroupFunctor.range ((GroupScheme.baseChange (toAlgebraicClosure k)).map r) := by
  let f := geometricNormalUnipotentFactor χ z p r hP hpc hU hz hzc hZ v hvc hsm hc hu hn
  have hf : f ≫ (GroupScheme.baseChange (toAlgebraicClosure k)).map r = v :=
    geometricNormalUnipotentFactor_comp χ z p r hP hpc hU hz hzc hZ v hvc hsm hc hu hn
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  refine SubgroupFunctor.mem_range.mpr ⟨y ≫ f.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, hf]

/-- Assemble the geometric radical predicate from its structural clauses and
the greatestness supplied by the reductive dynamic centralizer. -/
theorem isGeometricUnipotentRadical_of_reductive_centralizer
    (hZ : IsConnectedReductive Z)
    (hrc : IsClosedSubgroup r) (hsm : Smooth U.X.hom)
    (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (hn : (SubgroupFunctor.range r).IsNormal)
    (hcg : ConnectedSpace ((GroupScheme.baseChange (toAlgebraicClosure k)).obj U).X.left)
    (hug : IsUnipotent ((GroupScheme.baseChange (toAlgebraicClosure k)).obj U)) :
    IsGeometricUnipotentRadical r := by
  refine ⟨hrc, hsm, hc, hu, hn, hcg, hug, ?_, ?_⟩
  · rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange _
  · exact geometric_normal_subgroup_range_le_unipotentRepresentative χ z p r
      hP hpc hU hz hzc hZ

end Langlands.GroupScheme.Dynamic
