import Langlands.GroupScheme.Rational.ParabolicBoundaryCocharacter
import Langlands.GroupScheme.Rational.CommonCocharacterLeviIntersection
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization

/-! # Actual boundary parabolics with the original inner Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Actual outer and inner decompositions for a proper coarsening of a
specified parabolic, retaining the specified original Levi source. -/
structure NestedProperParabolicModel
    {k : Type u} [Field k]
    {G P M : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (m : M ⟶ P)
    (chi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) where
  Q : GroupScheme (Spec (CommRingCat.of k))
  L : GroupScheme (Spec (CommRingCat.of k))
  U : GroupScheme (Spec (CommRingCat.of k))
  PL : GroupScheme (Spec (CommRingCat.of k))
  NL : GroupScheme (Spec (CommRingCat.of k))
  q : Q ⟶ G
  l : L ⟶ Q
  r : U ⟶ Q
  pL : PL ⟶ L
  mL : M ⟶ PL
  nL : NL ⟶ PL
  hq : IsParabolicSubgroup q
  hl : IsRationalLeviSubgroup l
  hr : LeviSubgroup.IsGeometricUnipotentRadical r
  hmulQ : IsIso (subgroupMultiplication l r)
  hpL : IsParabolicSubgroup pL
  hmL : IsRationalLeviSubgroup mL
  hnL : LeviSubgroup.IsGeometricUnipotentRadical nL
  hmulL : IsIso (subgroupMultiplication mL nL)
  proper : ¬ IsIso q
  parabolic_range : SubgroupFunctor.range q = Dynamic.parabolic chi
  levi_range : SubgroupFunctor.range (l ≫ q) = Dynamic.centralizer chi
  radical_range : SubgroupFunctor.range (r ≫ q) = Dynamic.unipotent chi
  hP : SubgroupFunctor.range p ≤ SubgroupFunctor.range q
  hM : (mL ≫ pL) ≫ l ≫ q = m ≫ p
  hPL : SubgroupFunctor.range (pL ≫ l ≫ q) =
    SubgroupFunctor.range (l ≫ q) ⊓ SubgroupFunctor.range p

namespace ParabolicRootPresentation

open RealTorusSpace
open RepresentedParabolicLeviIntersection

variable {k : Type u} [Field k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {B : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {m : M ⟶ P} {b : B.toGrp ⟶ M}
  (fine : ParabolicRootPresentation p m b)

/-- The constructed torus cocharacter is the original component cocharacter
followed by the original maps into the ambient group. -/
theorem boundaryCocharacterInTorus_comp {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    CommGroupScheme.groupHom (fine.boundaryCocharacterInTorus hx hstrict) ≫ fine.data.i =
      CommGroupScheme.groupHom (fine.boundarySplitComponentCocharacter hx hstrict) ≫
        b ≫ m ≫ p := by
  change (CommGroupScheme.groupHom (fine.boundarySplitComponentCocharacter hx hstrict) ≫
    CommGroupScheme.groupHom fine.data.f) ≫ fine.data.i = _
  rw [Category.assoc, fine.isCompatible.factor_comp]

/-- Centrality of the supplied split component places the original Levi in
the boundary centralizer on every test scheme. -/
theorem levi_le_boundaryCentralizer {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    SubgroupFunctor.range (m ≫ p) ≤
      Dynamic.centralizer
        (CommGroupScheme.groupHom (fine.boundaryCocharacterInTorus hx hstrict) ≫
          fine.data.i) := by
  rw [fine.boundaryCocharacterInTorus_comp hx hstrict]
  exact (isCentral_comp_iff_le_dynamicCentralizer
    (F := SubgroupFunctor.range (m ≫ p))
    ⟨mono_of_isClosedSubgroup
      (fine.isCompatible.levi.isClosedSubgroup.comp
        fine.isCompatible.parabolic.isClosedSubgroup), rfl⟩
    b rfl (fine.boundarySplitComponentCocharacter hx hstrict)).mp
    (fine.isCompatible.splitComponent.isCentralSplitTorus.isCentral.comp _)

/-- The boundary dynamic functors have actual proper outer parabolic,
rational Levi and geometric radical models, together with an actual inner
intersection whose Levi is the original supplied `M`. -/
def boundaryParabolicModels (hG : IsConnectedReductive G) {x : Vstar B}
    (hx : x ∈ fine.nonnegCone) (hstrict : x ∉ fine.positiveCone) :
    NestedProperParabolicModel p m
      (CommGroupScheme.groupHom (fine.boundaryCocharacterInTorus hx hstrict) ≫
        fine.data.i) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let eta := fine.boundaryCocharacterInTorus hx hstrict
  let chi := CommGroupScheme.groupHom eta ≫ fine.data.i
  let d := Dynamic.affineDecompositionModel chi
  have hqc := d.parabolic_closed
  have : IsAffineHom d.parabolic.X.hom := hqc.isAffineHom
  have hjc : IsClosedSubgroup (d.leviHom ≫ d.parabolicHom) :=
    d.levi_closed.comp hqc
  have hL : IsConnectedReductive d.levi :=
    dynamicCentralizerReductive k G hG chi d.levi (d.leviHom ≫ d.parabolicHom)
      hjc d.levi_rep
  have hrad : LeviSubgroup.IsGeometricUnipotentRadical d.unipotentHom :=
    (dynamicGeometricUnipotentRadical k G hG chi d.parabolic d.unipotent
      d.parabolicHom d.unipotentHom d.parabolic_rep d.unipotent_rep).leviSubgroup_of_unipotentFieldExtension
        unipotentFieldExtensionStatement
  have hlevi : IsRationalLeviSubgroup d.leviHom :=
    ⟨inferInstance, d.levi_closed, hL,
      d.unipotent, d.unipotentHom, hrad, d.multiplication_isIso⟩
  have hML : SubgroupFunctor.range (m ≫ p) ≤
      SubgroupFunctor.range (d.leviHom ≫ d.parabolicHom) := by
    rw [d.levi_rep.2]
    exact fine.levi_le_boundaryCentralizer hx hstrict
  let zeta := fine.isCompatible.realization.choose
  have hzP := fine.isCompatible.realization.choose_spec.2.1
  have hzM := fine.isCompatible.realization.choose_spec.2.2
  let inner := commonCocharacterLeviIntersection hL fine.data.i eta zeta hjc d.levi_rep
  have heq : SubgroupFunctor.range
      (inner.l' ≫ inner.p' ≫ d.leviHom ≫ d.parabolicHom) =
      SubgroupFunctor.range (m ≫ p) := by
    rw [inner.levi_eq, ← hzM]
    apply SubgroupFunctor.ext
    intro V
    apply Subgroup.ext
    intro y
    exact ⟨fun hy => hy.2, fun hy => ⟨hML V hy, hy⟩⟩
  have hmc : IsClosedSubgroup (m ≫ p) :=
    fine.isCompatible.levi.isClosedSubgroup.comp fine.isCompatible.parabolic.isClosedSubgroup
  have hinnerc : IsClosedSubgroup
      (inner.l' ≫ inner.p' ≫ d.leviHom ≫ d.parabolicHom) :=
    inner.hl'.isClosedSubgroup.comp (inner.hp'.isClosedSubgroup.comp hjc)
  let hrepM : (SubgroupFunctor.range (m ≫ p)).IsRepresentedBy (m ≫ p) :=
    ⟨mono_of_isClosedSubgroup hmc, rfl⟩
  let hrepInner : (SubgroupFunctor.range (m ≫ p)).IsRepresentedBy
      (inner.l' ≫ inner.p' ≫ d.leviHom ≫ d.parabolicHom) :=
    ⟨mono_of_isClosedSubgroup hinnerc, heq⟩
  let e : M ≅ inner.M' := hrepM.isoOfIsRepresentedBy hrepInner
  refine
    { Q := d.parabolic
      L := d.levi
      U := d.unipotent
      PL := inner.P'
      NL := inner.N'
      q := d.parabolicHom
      l := d.leviHom
      r := d.unipotentHom
      pL := inner.p'
      mL := e.hom ≫ inner.l'
      nL := inner.r'
      hq := isParabolicSubgroup_of_range_eq_dynamicParabolic hG d.parabolicHom hqc
        chi d.parabolic_rep.2
      hl := hlevi
      hr := hrad
      hmulQ := d.multiplication_isIso
      hpL := inner.hp'
      hmL := inner.hl'.iso_comp e
      hnL := inner.hr'
      hmulL := isIso_subgroupMultiplication_iso_comp e inner.hmul'
      proper := ?_
      parabolic_range := d.parabolic_rep.2
      levi_range := d.levi_rep.2
      radical_range := d.unipotent_rep.2
      hP := ?_
      hM := ?_
      hPL := ?_ }
  · intro hqiso
    let := hqiso
    apply fine.boundaryCocharacter_parabolic_ne_top hG hx hstrict
    change Dynamic.parabolic chi = ⊤
    rw [← d.parabolic_rep.2]
    calc
      SubgroupFunctor.range d.parabolicHom =
          SubgroupFunctor.range ((asIso d.parabolicHom).hom ≫ 𝟙 G) := by simp
      _ = SubgroupFunctor.range (𝟙 G) := SubgroupFunctor.range_iso_comp _ _
      _ = ⊤ := (SubgroupFunctor.top_isRepresentedBy_id G).2
  · rw [d.parabolic_rep.2]
    exact fine.parabolic_le_boundaryCocharacter hG hx hstrict
  · simpa only [Category.assoc] using
      hrepM.isoOfIsRepresentedBy_hom_comp hrepInner
  · rw [inner.parabolic_eq, ← hzP]

end ParabolicRootPresentation

end Langlands.GroupScheme
