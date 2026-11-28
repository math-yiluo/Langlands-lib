import Langlands.AbelianScheme.PotentialSemistableReductionStatement
import Langlands.AbelianScheme.BaseChangeCoherence
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AbelianScheme.SemistableReductionConstruction
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange
import Langlands.GroupScheme.RelativeIdentityComponent.SmoothExistenceProof
import Langlands.GroupScheme.RelativeIdentityComponentProperties
import Langlands.BruhatTits.IntegralModels.RelativeComponentModelLemmas

/-! # Geometric semiabelian reduction under base change of the valuation ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AbelianScheme

namespace GeometricSemiabelianDescent

variable {S S' S'' : Scheme.{u}}

/-- Direct pullback of a commutative group scheme is canonically isomorphic to successive
pullback. -/
def commBaseChangeCompIso (b : S' ⟶ S) (c : S'' ⟶ S') (G : CommGroupScheme S) :
    (CommGroupScheme.baseChange (c ≫ b)).obj G ≅
      (CommGroupScheme.baseChange c).obj ((CommGroupScheme.baseChange b).obj G) where
  hom := Additive.ofMul (GroupScheme.baseChangeCompIso b c G.toGrp).hom
  inv := Additive.ofMul (GroupScheme.baseChangeCompIso b c G.toGrp).inv
  hom_inv_id := congrArg Additive.ofMul (GroupScheme.baseChangeCompIso b c G.toGrp).hom_inv_id
  inv_hom_id := congrArg Additive.ofMul (GroupScheme.baseChangeCompIso b c G.toGrp).inv_hom_id

/-- Pullbacks along equal morphisms are isomorphic. -/
def commBaseChangeEqIso {b b' : S' ⟶ S} (h : b = b') (G : CommGroupScheme S) :
    (CommGroupScheme.baseChange b).obj G ≅ (CommGroupScheme.baseChange b').obj G :=
  eqToIso (by rw [h])

/-- The isomorphism of underlying group schemes. -/
def groupIso {G H : CommGroupScheme S} (e : G ≅ H) : G.toGrp ≅ H.toGrp where
  hom := CommGroupScheme.groupHom e.hom
  inv := CommGroupScheme.groupHom e.inv
  hom_inv_id := congrArg Additive.toMul e.hom_inv_id
  inv_hom_id := congrArg Additive.toMul e.inv_hom_id

end GeometricSemiabelianDescent

open GeometricSemiabelianDescent

/-- Pullback of a split semiabelian presentation to an algebraically closed field. -/
def SplitSemiabelianPresentation.baseChange {k k' : Type u} [Field k] [Field k'] [IsAlgClosed k']
    {G : CommGroupScheme (Spec (CommRingCat.of k))} (P : SplitSemiabelianPresentation G)
    (b : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) :
    SplitSemiabelianPresentation ((CommGroupScheme.baseChange b).obj G) := by
  let f := CommGroupScheme.groupHom P.quotientMap
  have hsm : Smooth (CommGroupScheme.hom ((CommGroupScheme.baseChange b).map P.quotientMap)) :=
    MorphismProperty.of_isPullback
      (RelativeIdentityComponent.overPullback_isPullback b f.hom.hom).flip P.smooth
  have hsurj :
      Surjective (CommGroupScheme.hom ((CommGroupScheme.baseChange b).map P.quotientMap)) :=
    MorphismProperty.of_isPullback
      (RelativeIdentityComponent.overPullback_isPullback b f.hom.hom).flip P.surjective
  have hsplit : IsSplitTorus (GroupScheme.kernel f) :=
    IsSplitTorus.of_iso (groupIso P.torusIso).symm (isSplitTorus_splitTorus _)
  have hT : IsTorus (CommGroupScheme.kernel
      ((CommGroupScheme.baseChange b).map P.quotientMap)).toGrp :=
    (IsSplitTorus.of_iso (kernelBaseChangeIso b f).symm (hsplit.baseChange b)).isTorus
  exact SplitSemiabelianPresentation.ofTorusKernel ((AbelianScheme.baseChange b).obj P.quotient)
    ((CommGroupScheme.baseChange b).map P.quotientMap) hsm hsurj hT

/-- Geometric semiabelian reduction descends along a local homomorphism of discrete valuation
rings with algebraic residue extension: if a model over `W` whose group scheme is isomorphic
to the base change of `N` has semiabelian geometric special identity component, so has `N`. -/
theorem NeronModel.hasGeometricSemiabelianReduction_of_baseChange
    {V K W L : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra V W] [IsLocalHom (algebraMap V W)]
    [Algebra.IsAlgebraic (ResidueField V) (ResidueField W)]
    {B : AbelianScheme (Spec (CommRingCat.of K))} (N : NeronModel V K B)
    {B' : AbelianScheme (Spec (CommRingCat.of L))} (N' : NeronModel W L B')
    (e : N'.group ≅ (CommGroupScheme.baseChange (Spec.algebraMap V W)).obj N.group)
    (h : N'.HasGeometricSemiabelianReduction) : N.HasGeometricSemiabelianReduction := by
  obtain ⟨J', i', hi', ⟨P'⟩⟩ := h
  let σ : AlgebraicClosure (ResidueField W) ≃ₐ[ResidueField V]
      AlgebraicClosure (ResidueField V) :=
    IsAlgClosure.equivOfAlgebraic (ResidueField V) (ResidueField W) _ _
  let φ : Spec (CommRingCat.of (AlgebraicClosure (ResidueField W))) ⟶
      Spec (CommRingCat.of (AlgebraicClosure (ResidueField V))) :=
    Spec.map (CommRingCat.ofHom (σ.symm : AlgebraicClosure (ResidueField V) →+*
      AlgebraicClosure (ResidueField W)))
  let ψ : Spec (CommRingCat.of (AlgebraicClosure (ResidueField V))) ⟶
      Spec (CommRingCat.of (AlgebraicClosure (ResidueField W))) :=
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure (ResidueField W) →+*
      AlgebraicClosure (ResidueField V)))
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    simp only [ψ, φ, ← Spec.map_comp]
    rw [← Spec.map_id]
    congr 1
    ext x
    simp
  have hsq : geometricSpecialPoint W ≫ Spec.algebraMap V W = φ ≫ geometricSpecialPoint V := by
    simp only [geometricSpecialPoint, φ, Spec.algebraMap, Category.assoc, ← Spec.map_comp]
    congr 1
    ext v
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply, RingHom.coe_coe]
    rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply (ResidueField V) (ResidueField W)
      (AlgebraicClosure (ResidueField W)), IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ResidueField.algebraMap_residue]
  let α : N'.geometricSpecialFibre ≅
      (CommGroupScheme.baseChange φ).obj N.geometricSpecialFibre :=
    (CommGroupScheme.baseChange (geometricSpecialPoint W)).mapIso e ≪≫
      (commBaseChangeCompIso _ _ N.group).symm ≪≫ commBaseChangeEqIso hsq N.group ≪≫
      commBaseChangeCompIso _ _ N.group
  let β : (CommGroupScheme.baseChange ψ).obj N'.geometricSpecialFibre ≅
      N.geometricSpecialFibre :=
    (CommGroupScheme.baseChange ψ).mapIso α ≪≫ (commBaseChangeCompIso _ _ _).symm ≪≫
      commBaseChangeEqIso hψφ _ ≪≫ Langlands.GroupScheme.CommGroupScheme.baseChangeIdIso _
  have : Smooth N'.group.X.hom := N'.property.smooth
  have hsmooth : Smooth N'.geometricSpecialFibre.X.hom := by
    change Smooth (Limits.pullback.snd N'.group.X.hom (geometricSpecialPoint W))
    infer_instance
  obtain ⟨H, j, hj, -, hconn⟩ :=
    RelativeIdentityComponent.smoothExistence _ N'.geometricSpecialFibre.toGrp hsmooth
  have : GeometricallyConnected H.X.hom := hconn
  have : GeometricallyConnected J'.X.hom := hi'.geometricallyConnected hj
  refine ⟨(CommGroupScheme.baseChange ψ).obj J', (CommGroupScheme.baseChange ψ).map i' ≫ β.hom,
    ?_, ⟨P'.baseChange ψ⟩⟩
  exact (hi'.baseChange ψ).comp_iso (groupIso β)

end Langlands.AbelianScheme
