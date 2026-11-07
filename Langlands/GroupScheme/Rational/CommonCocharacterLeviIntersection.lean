import Langlands.GroupScheme.Rational.ParabolicLeviIntersectionReduction
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # Actual Levi intersections for supplied common cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RepresentedParabolicLeviIntersection

/-- Actual models for the intersections of a represented subgroup with the
three dynamic subgroups of a supplied common cocharacter. -/
structure CommonCocharacterLeviIntersection
    {k : Type u} [Field k]
    {G M : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (β : cocharacterLattice T) (j : M ⟶ G) where
  P' : GroupScheme (Spec (CommRingCat.of k))
  M' : GroupScheme (Spec (CommRingCat.of k))
  N' : GroupScheme (Spec (CommRingCat.of k))
  p' : P' ⟶ M
  l' : M' ⟶ P'
  r' : N' ⟶ P'
  hp' : IsParabolicSubgroup p'
  hr' : LeviSubgroup.IsGeometricUnipotentRadical r'
  hl' : IsRationalLeviSubgroup l'
  hmul' : IsIso (subgroupMultiplication l' r')
  parabolic_eq : SubgroupFunctor.range (p' ≫ j) =
    SubgroupFunctor.range j ⊓ Dynamic.parabolic (CommGroupScheme.groupHom β ≫ i)
  levi_eq : SubgroupFunctor.range (l' ≫ p' ≫ j) =
    SubgroupFunctor.range j ⊓ Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i)
  radical_eq : SubgroupFunctor.range (r' ≫ p' ≫ j) =
    SubgroupFunctor.range j ⊓ Dynamic.unipotent (CommGroupScheme.groupHom β ≫ i)
  torusMap : T.toGrp ⟶ M'
  torusMap_comp : torusMap ≫ l' ≫ p' ≫ j = i

/-- The three intersections inside a represented centralizer of one common
cocharacter have actual parabolic, rational Levi and geometric radical models.
The original common commutative group factors through the common Levi. -/
theorem exists_leviIntersection_of_commonCocharacters
    {k : Type u} [Field k]
    {G M : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hM : IsConnectedReductive M) (i : T.toGrp ⟶ G)
    (α β : cocharacterLattice T) {j : M ⟶ G}
    (hjc : IsClosedSubgroup j)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i)).IsRepresentedBy j) :
    ∃ (P' M' N' : GroupScheme (Spec (CommRingCat.of k)))
      (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : N' ⟶ P'),
      IsParabolicSubgroup p' ∧ LeviSubgroup.IsGeometricUnipotentRadical r' ∧
      IsRationalLeviSubgroup l' ∧ IsIso (subgroupMultiplication l' r') ∧
      SubgroupFunctor.range (p' ≫ j) =
        SubgroupFunctor.range j ⊓ Dynamic.parabolic (CommGroupScheme.groupHom β ≫ i) ∧
      SubgroupFunctor.range (l' ≫ p' ≫ j) =
        SubgroupFunctor.range j ⊓ Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i) ∧
      SubgroupFunctor.range (r' ≫ p' ≫ j) =
        SubgroupFunctor.range j ⊓ Dynamic.unipotent (CommGroupScheme.groupHom β ≫ i) ∧
      ∃ t : T.toGrp ⟶ M', t ≫ l' ≫ p' ≫ j = i := by
  have := hM.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let χ := Dynamic.intersectionCocharacter i (CommGroupScheme.groupHom α)
    (CommGroupScheme.groupHom β) hj
  have hχ := Dynamic.intersection_dynamic_eq_comap i (CommGroupScheme.groupHom α)
    (CommGroupScheme.groupHom β) hj hjc
  let d := Dynamic.affineDecompositionModel χ
  have hPc : IsClosedSubgroup d.parabolicHom := d.parabolic_closed
  have : IsAffineHom d.parabolic.X.hom := hPc.isAffineHom
  have hrad : LeviSubgroup.IsGeometricUnipotentRadical d.unipotentHom :=
    (dynamicGeometricUnipotentRadical k M hM χ d.parabolic d.unipotent
      d.parabolicHom d.unipotentHom d.parabolic_rep d.unipotent_rep).leviSubgroup_of_unipotentFieldExtension
        unipotentFieldExtensionStatement
  have hlevi : SubgroupFunctor.range ((d.leviHom ≫ d.parabolicHom) ≫ j) =
      SubgroupFunctor.range j ⊓ Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i) :=
    range_comp_eq_inf_of_range_eq_comap _ _ (d.levi_rep.2.trans hχ.2.1)
  refine ⟨d.parabolic, d.levi, d.unipotent, d.parabolicHom, d.leviHom, d.unipotentHom,
    isParabolicSubgroup_of_range_eq_dynamicParabolic hM d.parabolicHom hPc χ
      d.parabolic_rep.2, hrad,
    ⟨inferInstance, d.levi_closed,
      dynamicCentralizerReductive k M hM χ d.levi (d.leviHom ≫ d.parabolicHom)
        (d.levi_closed.comp hPc) d.levi_rep,
      ⟨d.unipotent, d.unipotentHom, hrad, d.multiplication_isIso⟩⟩,
    d.multiplication_isIso, ?_, ?_, ?_, ?_⟩
  · exact range_comp_eq_inf_of_range_eq_comap _ _ (d.parabolic_rep.2.trans hχ.1)
  · simpa only [Category.assoc] using hlevi
  · simpa only [Category.assoc] using
      range_comp_eq_inf_of_range_eq_comap _ j (d.unipotent_rep.2.trans hχ.2.2)
  · have hrep : (SubgroupFunctor.range j ⊓
        Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i)).IsRepresentedBy
          ((d.leviHom ≫ d.parabolicHom) ≫ j) :=
      ⟨mono_of_isClosedSubgroup ((d.levi_closed.comp hPc).comp hjc), hlevi⟩
    have hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range j ⊓
        Dynamic.centralizer (CommGroupScheme.groupHom β ≫ i) := by
      intro V x hx
      refine ⟨?_, range_le_centralizer_groupHom_comp i β V hx⟩
      rw [hj.2]
      exact range_le_centralizer_groupHom_comp i α V hx
    exact ⟨hrep.factorHom i hle, by
      simpa only [Category.assoc] using hrep.factorHom_comp i hle⟩

/-- Choose actual intersection models from the proved common-cocharacter
construction, retaining their structural proofs and all-test identities. -/
def commonCocharacterLeviIntersection
    {k : Type u} [Field k]
    {G M : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hM : IsConnectedReductive M) (i : T.toGrp ⟶ G)
    (α β : cocharacterLattice T) {j : M ⟶ G}
    (hjc : IsClosedSubgroup j)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i)).IsRepresentedBy j) :
    CommonCocharacterLeviIntersection i β j :=
  Classical.choice <| by
    obtain ⟨P', M', N', p', l', r', hp', hr', hl', hmul', hpar, hlevi, hrad, t, ht⟩ :=
      exists_leviIntersection_of_commonCocharacters hM i α β hjc hj
    exact ⟨{ P' := P', M' := M', N' := N', p' := p', l' := l', r' := r'
             hp' := hp', hr' := hr', hl' := hl', hmul' := hmul'
             parabolic_eq := hpar, levi_eq := hlevi, radical_eq := hrad
             torusMap := t, torusMap_comp := ht }⟩

end Langlands.GroupScheme
