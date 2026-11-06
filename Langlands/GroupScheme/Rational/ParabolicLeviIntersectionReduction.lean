import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Rational.ParabolicLeviIntersectionStatement
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination

/-! # Levi intersections along a common maximal split torus from the dynamic description -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RepresentedParabolicLeviIntersection

section Base

variable {S : Scheme.{u}} {H G K : GroupScheme S}

/-- The range of a composite is the image of the range of its first factor. -/
theorem range_comp_eq_map (f : H ⟶ G) (j : G ⟶ K) :
    SubgroupFunctor.range (f ≫ j) = (SubgroupFunctor.range f).map j :=
  SubgroupFunctor.ext fun _ => Subgroup.ext fun _ => by
    rw [SubgroupFunctor.mem_map, SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y ≫ f.hom.hom, SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩,
        by rw [Grp.comp_hom_hom, Category.assoc]⟩
    · rintro ⟨_, hy, rfl⟩
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hy
      exact ⟨y, by rw [Grp.comp_hom_hom, Category.assoc]⟩

/-- The range of a composite lies in the range of its last factor. -/
theorem range_comp_le (f : H ⟶ G) (j : G ⟶ K) :
    SubgroupFunctor.range (f ≫ j) ≤ SubgroupFunctor.range j := by
  rw [range_comp_eq_map]
  exact SubgroupFunctor.map_le_range j _

/-- The image under `j` of a subgroup represented as a preimage under `j`. -/
theorem range_comp_eq_inf_of_range_eq_comap (f : H ⟶ G) (j : G ⟶ K)
    {F : SubgroupFunctor K} (hf : SubgroupFunctor.range f = F.comap j) :
    SubgroupFunctor.range (f ≫ j) = SubgroupFunctor.range j ⊓ F := by
  rw [range_comp_eq_map, hf, SubgroupFunctor.map_comap]

/-- A closed subgroup homomorphism is a monomorphism of schemes over the base. -/
theorem mono_of_isClosedSubgroup {j : H ⟶ G} (hj : IsClosedSubgroup j) : Mono j.hom.hom :=
  hj.mono_overHom

end Base

section Field

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A cocharacter whose dynamic centralizer contains a maximal split torus factors
through that torus. -/
theorem exists_factor_of_range_le_centralizer [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (h : SubgroupFunctor.range i ≤ Dynamic.centralizer ψ) :
    ∃ α : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp, α ≫ i = ψ :=
  hi.exists_factor_of_commute isSplitTorus_gm ψ fun U x y =>
    (Dynamic.commute_cocharacter_of_mem_centralizer ψ (h U ⟨y, rfl⟩) x).symm

/-- **Levi intersections along a common maximal split torus** (Renard V.4.6 (ii)
and V.4.7). Let `P = MN` and `Q = LU` be parabolic subgroups of a connected
reductive group `G` over a field with rational Levi subgroups `M` and `L`, and suppose
that `M` and `L` contain a common maximal split torus `T` of `G`. Then `M ∩ Q` is
represented by a parabolic subgroup `P'` of `M` with rational Levi subgroup
`M' = M ∩ L` and geometric unipotent radical `N' = M ∩ U`, whose multiplication
`M' × N' → P'` is an isomorphism, and `T` lies in `M'`. The intersections are equalities
of subgroup functors on every test scheme. The proof assumes that parabolic subgroups
are the dynamic parabolics and that dynamic centralizers are connected reductive. -/
theorem exists_leviIntersection_of_commonMaximalSplitTorus
    (hPD : ParabolicDynamicStatement.{u})
    (hDCR : DynamicCentralizerReductiveStatement.{u})
    {P M Q L U : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {tM : T.toGrp ⟶ M} (htM : tM ≫ l ≫ p = i)
    {tL : T.toGrp ⟶ L} (htL : tL ≫ lQ ≫ q = i) :
    ∃ (P' M' N' : GroupScheme (Spec (CommRingCat.of k)))
      (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : N' ⟶ P'),
      IsParabolicSubgroup p' ∧ LeviSubgroup.IsGeometricUnipotentRadical r' ∧
      IsRationalLeviSubgroup l' ∧ IsIso (subgroupMultiplication l' r') ∧
      SubgroupFunctor.range (p' ≫ l ≫ p) =
        SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range q ∧
      SubgroupFunctor.range (l' ≫ p' ≫ l ≫ p) =
        SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (lQ ≫ q) ∧
      SubgroupFunctor.range (r' ≫ p' ≫ l ≫ p) =
        SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (rQ ≫ q) ∧
      ∃ t : T.toGrp ⟶ M', t ≫ l' ≫ p' ≫ l ≫ p = i := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have hGUR := dynamicGeometricUnipotentRadical_of_centralizer hDCR
  have hM : IsConnectedReductive M := hl.isConnectedReductive
  have hqc : IsClosedSubgroup q := hq.isClosedSubgroup
  have hjc : IsClosedSubgroup (l ≫ p) := hl.isClosedSubgroup.comp hp.isClosedSubgroup
  have : IsAffineHom M.X.hom := hjc.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  -- Cocharacters realizing both parabolics together with their Levi subgroups.
  obtain ⟨ψP, -, hψPZ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi hPD hGUR hG hp hl
  obtain ⟨ψQ, hψQP, hψQZ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi hPD hGUR hG hq hlQ
  -- Both cocharacters factor through the common maximal split torus.
  obtain ⟨α, hα⟩ := exists_factor_of_range_le_centralizer hi ψP (by
    rw [← hψPZ, ← htM]
    exact range_comp_le tM (l ≫ p))
  obtain ⟨β, hβ⟩ := exists_factor_of_range_le_centralizer hi ψQ (by
    rw [← hψQZ, ← htL]
    exact range_comp_le tL (lQ ≫ q))
  have hj : (Dynamic.centralizer (α ≫ i)).IsRepresentedBy (l ≫ p) :=
    ⟨mono_of_isClosedSubgroup hjc, by rw [hα, hψPZ]⟩
  -- The cocharacter of `M` whose dynamic subgroups are the three intersections.
  let χM := Dynamic.intersectionCocharacter i α β hj
  have hχM := Dynamic.intersection_dynamic_eq_comap i α β hj hjc
  rw [hβ] at hχM
  let d := Dynamic.affineDecompositionModel χM
  have hPc : IsClosedSubgroup d.parabolicHom := d.parabolic_closed
  have : IsAffineHom d.parabolic.X.hom := hPc.isAffineHom
  have hrad : LeviSubgroup.IsGeometricUnipotentRadical d.unipotentHom :=
    (hGUR k M hM χM d.parabolic d.unipotent d.parabolicHom d.unipotentHom
      d.parabolic_rep d.unipotent_rep).leviSubgroup_of_unipotentFieldExtension
      unipotentFieldExtensionStatement
  have hUQ : SubgroupFunctor.range (rQ ≫ q) = Dynamic.unipotent ψQ :=
    Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer ψQ
      ⟨mono_of_isClosedSubgroup hqc, hψQP⟩
      ⟨mono_of_isClosedSubgroup (hlQ.isClosedSubgroup.comp hqc), hψQZ⟩
      hlQ.isConnectedReductive hrQ
  have hlevi : SubgroupFunctor.range ((d.leviHom ≫ d.parabolicHom) ≫ l ≫ p) =
      SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (lQ ≫ q) := by
    rw [hψQZ]
    exact range_comp_eq_inf_of_range_eq_comap _ _ (d.levi_rep.2.trans hχM.2.1)
  refine ⟨d.parabolic, d.levi, d.unipotent, d.parabolicHom, d.leviHom, d.unipotentHom,
    (hPD k M hM d.parabolic d.parabolicHom hPc).mpr ⟨χM, d.parabolic_rep.2⟩, hrad,
    ⟨inferInstance, d.levi_closed,
      hDCR k M hM χM d.levi (d.leviHom ≫ d.parabolicHom) (d.levi_closed.comp hPc) d.levi_rep,
      ⟨d.unipotent, d.unipotentHom, hrad, d.multiplication_isIso⟩⟩,
    d.multiplication_isIso, ?_, ?_, ?_, ?_⟩
  · rw [hψQP]
    exact range_comp_eq_inf_of_range_eq_comap _ _ (d.parabolic_rep.2.trans hχM.1)
  · simpa only [Category.assoc] using hlevi
  · have h := range_comp_eq_inf_of_range_eq_comap _ (l ≫ p)
      ((d.unipotent_rep.2.trans hχM.2.2 :
        SubgroupFunctor.range (d.unipotentHom ≫ d.parabolicHom) = _))
    rw [hUQ]
    simpa only [Category.assoc] using h
  · have hrep : (SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (lQ ≫ q)).IsRepresentedBy
        ((d.leviHom ≫ d.parabolicHom) ≫ l ≫ p) :=
      ⟨mono_of_isClosedSubgroup ((d.levi_closed.comp hPc).comp hjc), hlevi⟩
    have hle : SubgroupFunctor.range i ≤
        SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (lQ ≫ q) := by
      intro V x hx
      refine ⟨?_, ?_⟩
      · rw [← htM] at hx
        exact range_comp_le tM (l ≫ p) V hx
      · rw [← htL] at hx
        exact range_comp_le tL (lQ ≫ q) V hx
    exact ⟨hrep.factorHom i hle, by simpa only [Category.assoc] using hrep.factorHom_comp i hle⟩

end Field

end RepresentedParabolicLeviIntersection

/-- Levi intersections along a common maximal split torus follow from the dynamic
description of parabolic subgroups and the reductivity of dynamic centralizers. -/
def RepresentedParabolicLeviIntersectionFromDynamicStatement : Prop :=
  ParabolicDynamicStatement.{u} → DynamicCentralizerReductiveStatement.{u} →
    RepresentedParabolicLeviIntersectionStatement.{u}

/-- The reduction holds: the common-torus theorem gives the intersections, and its extra
factorization of the torus through `M'` is discarded. -/
theorem representedParabolicLeviIntersection_of_dynamic :
    RepresentedParabolicLeviIntersectionFromDynamicStatement.{u} := by
  intro hPD hDCR k _ G hG P M Q L U p l hp hl q lQ rQ hq hlQ hrQ _ T i hi ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨P', M', N', p', l', r', hp', hr', hl', hmul', hP', hM', hN', -⟩ :=
    RepresentedParabolicLeviIntersection.exists_leviIntersection_of_commonMaximalSplitTorus
      hPD hDCR hG hp hl hq hlQ hrQ hi ha hb
  exact ⟨P', M', N', p', l', r', hp', hr', hl', hmul', hP', hM', hN'⟩

end Langlands.GroupScheme
