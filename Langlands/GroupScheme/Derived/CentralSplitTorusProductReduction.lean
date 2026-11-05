import Langlands.GroupScheme.Derived.CentralSplitTorusProductKernel
import Langlands.GroupScheme.Derived.CentralSplitTorusProductStatement
import Langlands.GroupScheme.CentralIsogeny.ProjectionCentralIsogeny

/-! # Reduction of the derived and central split product to surjectivity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

section Centrality

variable {B : Scheme.{u}} (X Y : CommGroupScheme B)
    {M : GroupScheme B} (f : X.toGrp ⊗ Y.toGrp ⟶ M)

/-- The full kernel of a map from a product of commutative group schemes is central. -/
theorem isCentral_kernel_of_commutative_product : IsCentral (kernelι f) := by
  apply (isCentral_kernelι_iff f).mpr
  intro T x _
  rw [mem_center]
  intro T' a y
  change (a ≫ x) * y = y * (a ≫ x)
  apply (productPointsEquiv X.toGrp Y.toGrp T').injective
  rw [map_mul, map_mul]
  exact Prod.ext (mul_comm _ _) (mul_comm _ _)

end Centrality

section Field

variable {k : Type u} [Field k]
    {G D : GroupScheme (Spec (CommRingCat.of k))}
    {S S_D A : CommGroupScheme (Spec (CommRingCat.of k))}
    {d : D ⟶ G} (i : S.toGrp ⟶ G) (j : S_D.toGrp ⟶ D)
    (e : S_D ⟶ S) (a : A.toGrp ⟶ G) (c : A ⟶ S)

/-- Surjectivity is the only further condition needed for compatible closed split factors
to give a central isogeny. -/
theorem isCentralIsogeny_derivedCentralSplitTorusProduct_of_surjective
    (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (hS : IsSplitTorus S.toGrp) (hSD : IsSplitTorus S_D.toGrp)
    (hA : IsSplitTorus A.toGrp) (hj : IsClosedSubgroup j)
    (ha : IsClosedSubgroup a) (hacent : IsCentral a)
    (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hc : CommGroupScheme.groupHom c ≫ i = a)
    (hsurj : Surjective
      (prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
        (fun _ _ _ => Commute.all _ _)).hom.hom.left) :
    IsCentralIsogeny
      (prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
        (fun _ _ _ => Commute.all _ _)) := by
  let f := prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
    (fun _ _ _ => Commute.all _ _)
  have : Surjective f.hom.hom.left := hsurj
  have : IsAffineHom (S_D.toGrp ⊗ A.toGrp).X.hom := (hSD.tensor hA).isAffineHom
  have : Smooth (S_D.toGrp ⊗ A.toGrp).X.hom := (hSD.tensor hA).smooth
  have : IsAffineHom S.X.hom := hS.isAffineHom
  have : Smooth S.X.hom := hS.smooth
  have : QuasiCompact f.hom.hom.left := by
    have : QuasiCompact (f.hom.hom.left ≫ S.X.hom) := by
      rw [Over.w]
      infer_instance
    exact QuasiCompact.of_comp _ S.X.hom
  have : Flat f.hom.hom.left := flat_of_surjective f
  have : IsFinite (kernel f).X.hom :=
    isFinite_kernel_derivedCentralSplitTorusProduct i j e a c hG hd hS hSD hA
      hj ha hacent he hc
  have hfin : IsFinite f.hom.hom.left := isFinite_of_finite_kernel f
  have : LocallyOfFiniteType (f.hom.hom.left ≫ S.X.hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType f.hom.hom.left :=
    locallyOfFiniteType_of_comp _ S.X.hom
  have : IsLocallyNoetherian S.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian S.X.hom
  exact ⟨⟨hfin, inferInstance, hsurj⟩, inferInstance,
    isCentral_kernel_of_commutative_product S_D A f⟩

end Field

/-- For the exact supplied factors, central isogeny is equivalent to scheme surjectivity. -/
def DerivedCentralSplitTorusProductReductionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
    IsConnectedReductive G → IsDerivedSubgroup d →
    ∀ (S S_D A : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : S.toGrp ⟶ G) (j : S_D.toGrp ⟶ D) (e : S_D ⟶ S)
      (a : A.toGrp ⟶ G) (c : A ⟶ S),
      IsMaximalSplitTorus i → IsMaximalSplitTorus j →
      IsClosedSubgroup (CommGroupScheme.groupHom e) →
      j ≫ d = CommGroupScheme.groupHom e ≫ i →
      IsSplitComponent a → CommGroupScheme.groupHom c ≫ i = a →
      (Surjective
        (prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
          (fun _ _ _ => Commute.all _ _)).hom.hom.left ↔
        IsCentralIsogeny
          (prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
            (fun _ _ _ => Commute.all _ _)))

/-- All the isogeny conditions other than surjectivity follow from published results. -/
theorem derivedCentralSplitTorusProductReduction :
    DerivedCentralSplitTorusProductReductionStatement.{u} := by
  intro k _ G D d hG hd S S_D A i j e a c hi hj _ he ha hc
  constructor
  · exact isCentralIsogeny_derivedCentralSplitTorusProduct_of_surjective i j e a c hG hd
      hi.1.1 hj.1.1 ha.1.1.1 hj.1.2 ha.1.1.2 ha.1.2 he hc
  · exact IsCentralIsogeny.surjective

end Langlands.GroupScheme
