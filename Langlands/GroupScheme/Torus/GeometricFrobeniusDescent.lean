import Langlands.GroupScheme.Torus.FrobeniusDescent

/-! # Recovery over the original algebraic extension after Frobenius descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

@[reassoc]
private theorem recovery_baseChange_map_fst {S S' : Scheme.{u}}
    (b : S' ⟶ S) {G H : GroupScheme S} (f : G ⟶ H) :
    ((baseChange b).map f).hom.hom.left ≫ pullback.fst H.X.hom b =
      pullback.fst G.X.hom b ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

private theorem recovery_tower_hom_ext {B S S' : Scheme.{u}}
    (b : S ⟶ B) (c : S' ⟶ S) (H : GroupScheme B)
    {G : GroupScheme S'}
    {f g : G ⟶ (baseChange c).obj ((baseChange b).obj H)}
    (h : f.hom.hom.left ≫ pullback.fst ((baseChange b).obj H).X.hom c ≫
        pullback.fst H.X.hom b =
      g.hom.hom.left ≫ pullback.fst ((baseChange b).obj H).X.hom c ≫
        pullback.fst H.X.hom b) : f = g := by
  apply (cancel_mono (Descent.pullbackComparison b c (c ≫ b) rfl H).hom).mp
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      Descent.pullbackComparison_hom_fst] using h
  · exact (Over.w
      (f ≫ (Descent.pullbackComparison b c (c ≫ b) rfl H).hom).hom.hom).trans
      (Over.w
        (g ≫ (Descent.pullbackComparison b c (c ≫ b) rfl H).hom).hom.hom).symm

private theorem recovery_tower_naturality {B S S' : Scheme.{u}}
    (b : S ⟶ B) (c : S' ⟶ S) (d : S' ⟶ B)
    {G H : GroupScheme B} (f : G ⟶ H)
    (eG : (baseChange d).obj G ≅ (baseChange c).obj ((baseChange b).obj G))
    (eH : (baseChange d).obj H ≅ (baseChange c).obj ((baseChange b).obj H))
    (hG : eG.hom.hom.hom.left ≫
      pullback.fst ((baseChange b).obj G).X.hom c ≫ pullback.fst G.X.hom b =
        pullback.fst G.X.hom d)
    (hH : eH.hom.hom.hom.left ≫
      pullback.fst ((baseChange b).obj H).X.hom c ≫ pullback.fst H.X.hom b =
        pullback.fst H.X.hom d) :
    (baseChange d).map f ≫ eH.hom =
      eG.hom ≫ (baseChange c).map ((baseChange b).map f) := by
  apply recovery_tower_hom_ext b c H
  simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc, hH,
    recovery_baseChange_map_fst, recovery_baseChange_map_fst_assoc]
  simpa only [Category.assoc] using
    congrArg (fun z => z ≫ f.hom.hom.left) hG.symm

private theorem recovery_finiteStage_projection
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (E : Langlands.AlgebraicGeometry.Picard.FinIntermediateField k Ω)
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    (Descent.FiniteStage.comparison k Ω E G).hom.hom.hom.left ≫
        pullback.fst ((baseChange (algebraBaseMap k E.1)).obj G).X.hom
          (algebraBaseMap E.1 Ω) ≫ pullback.fst G.X.hom (algebraBaseMap k E.1) =
      pullback.fst G.X.hom (algebraBaseMap k Ω) := by
  change (Descent.FiniteStage.comparison k Ω E G).hom.hom.hom.left ≫
    pullback.fst (pullback.snd G.X.hom (algebraBaseMap k E.1))
      (algebraBaseMap E.1 Ω) ≫ pullback.fst G.X.hom (algebraBaseMap k E.1) = _
  rw [← Category.assoc, Descent.FiniteStage.comparison_hom_fst]
  simp [Langlands.AlgebraicGeometry.Picard.baseChangeCone]

namespace Descent.FiniteStage

/-- The finite-stage tower comparison is natural in the original group. -/
@[reassoc]
theorem comparison_naturality
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (E : Langlands.AlgebraicGeometry.Picard.FinIntermediateField k Ω)
    {G H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H) :
    (baseChange (algebraBaseMap k Ω)).map f ≫ (comparison k Ω E H).hom =
      (comparison k Ω E G).hom ≫
        (baseChange (algebraBaseMap E.1 Ω)).map
          ((baseChange (algebraBaseMap k E.1)).map f) := by
  exact recovery_tower_naturality
    (algebraBaseMap k E.1) (algebraBaseMap E.1 Ω) (algebraBaseMap k Ω) f
    (comparison k Ω E G) (comparison k Ω E H)
    (recovery_finiteStage_projection k Ω E G)
    (recovery_finiteStage_projection k Ω E H)

end Descent.FiniteStage

namespace TorusFiniteModel

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
variable {G : GroupScheme (Spec (CommRingCat.of k))}
variable {T : CommGroupScheme (Spec (CommRingCat.of Ω))}
variable {i : T.toGrp ⟶ (baseChange (algebraBaseMap k Ω)).obj G}

/-- Compose finite-model and finite-field descent recovery over the original
algebraic extension. -/
def Model.recoverDescent (D : Model k Ω i) (D₀ : TorusDescent D.inclusion) :
    TorusDescent i where
  torus := D₀.torus
  inclusion := D₀.inclusion
  recovery := Descent.FiniteStage.comparison k Ω D.fieldOfDefinition D₀.torus.toGrp ≪≫
    (baseChange (algebraBaseMap D.fieldOfDefinition.1 Ω)).mapIso D₀.recovery ≪≫
      D.recovery
  isTorus := D₀.isTorus
  isClosedSubgroup := D₀.isClosedSubgroup
  comparison := by
    apply (cancel_mono
      (Descent.FiniteStage.comparison k Ω D.fieldOfDefinition G).hom).mp
    rw [Descent.FiniteStage.comparison_naturality, D₀.comparison,
      Functor.map_comp, D.comparison]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]

/-- Geometric Frobenius invariance yields descent with recovery of the
specified inclusion over the original algebraic extension. -/
def Model.geometricDescentOfFrobenius [Fintype k] [Algebra.IsAlgebraic k Ω]
    [IsAffineHom G.X.hom] (D : Model k Ω i)
    (h : SubgroupFunctor.galoisTransport k Ω G
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) (SubgroupFunctor.range i) =
        SubgroupFunctor.range i) : TorusDescent i :=
  D.recoverDescent (D.descentOfFrobenius h)

end TorusFiniteModel

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
variable [Fintype k] [Algebra.IsAlgebraic k Ω]
variable {G : GroupScheme (Spec (CommRingCat.of k))}
variable [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom]
variable {T : CommGroupScheme (Spec (CommRingCat.of Ω))}
variable {i : T.toGrp ⟶ (baseChange (algebraBaseMap k Ω)).obj G}

/-- A specified Frobenius-invariant closed split torus over an algebraic
extension descends with recovery over that extension. -/
def geometricTorusDescentOfFrobenius
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (h : SubgroupFunctor.galoisTransport k Ω G
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) (SubgroupFunctor.range i) =
        SubgroupFunctor.range i) : TorusDescent i :=
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  (TorusFiniteModel.model k Ω i hT hi).geometricDescentOfFrobenius h

/-- A Frobenius-invariant geometric maximal torus descends to a maximal
torus whose specified original-extension pullback is maximal. -/
theorem IsMaximalTorus.exists_descent_of_frobenius_range_eq
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (h : SubgroupFunctor.galoisTransport k Ω G
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) (SubgroupFunctor.range i) =
        SubgroupFunctor.range i) :
    ∃ (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j : T₀.toGrp ⟶ G)
      (e : (baseChange (algebraBaseMap k Ω)).obj T₀.toGrp ≅ T.toGrp),
      IsMaximalTorus j ∧
        IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k Ω)).obj T₀)
          ((baseChange (algebraBaseMap k Ω)).map j) ∧
        (baseChange (algebraBaseMap k Ω)).map j = e.hom ≫ i := by
  let D := geometricTorusDescentOfFrobenius hT hi.2.1 h
  exact ⟨D.torus, D.inclusion, D.recovery,
    D.isMaximalTorus hi, D.isMaximalTorus_baseChange hi, D.comparison⟩

end Langlands.GroupScheme
