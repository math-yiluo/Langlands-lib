import Langlands.GroupScheme.Derived.CentralIntersectionProof
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-! # The full kernel of compatible derived and central split factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

section ProductKernel

variable {B : Scheme.{u}} {X Y M : GroupScheme B}
    (e : X ⟶ M) (c : Y ⟶ M)
    (hec : ∀ (T : Over B) (x : T ⟶ X.X) (y : T ⟶ Y.X),
      Commute (x ≫ e.hom.hom) (y ≫ c.hom.hom))

/-- If the second factor is monic, the first coordinate embeds the actual product kernel. -/
theorem mono_prodKernel_fst [Mono c.hom.hom] :
    Mono (kernelι (prodHom e c hec) ≫ fst X Y).hom.hom := by
  constructor
  intro T x y hxy
  apply (cancel_mono (kernelι (prodHom e c hec)).hom.hom).mp
  apply (productPointsEquiv X Y T).injective
  have hfst : (productPointsEquiv X Y T
      (x ≫ (kernelι (prodHom e c hec)).hom.hom)).1 =
      (productPointsEquiv X Y T
        (y ≫ (kernelι (prodHom e c hec)).hom.hom)).1 := by
    simpa only [productPointsEquiv_fst, Grp.comp_hom_hom, Grp.fst_hom_hom,
      Category.assoc] using hxy
  refine Prod.ext hfst ?_
  apply (cancel_mono c.hom.hom).mp
  have hx := (kernelPointsEquiv (prodHom e c hec) T x).property
  have hy := (kernelPointsEquiv (prodHom e c hec) T y).property
  change (x ≫ (kernelι (prodHom e c hec)).hom.hom) ≫
    (prodHom e c hec).hom.hom = 1 at hx
  change (y ≫ (kernelι (prodHom e c hec)).hom.hom) ≫
    (prodHom e c hec).hom.hom = 1 at hy
  rw [comp_prodHom] at hx hy
  rw [hfst] at hx
  exact mul_left_cancel (hx.trans hy.symm)

end ProductKernel

section Field

variable {k : Type u} [Field k]
    {G D : GroupScheme (Spec (CommRingCat.of k))}
    {S S_D A : CommGroupScheme (Spec (CommRingCat.of k))}
    {d : D ⟶ G} (i : S.toGrp ⟶ G) (j : S_D.toGrp ⟶ D)
    (e : S_D ⟶ S) (a : A.toGrp ⟶ G) (c : A ⟶ S)

/-- Compatible split factors from an actual derived subgroup and a closed central subgroup
have finite full multiplication kernel. Maximality is not needed for this assertion. -/
theorem isFinite_kernel_derivedCentralSplitTorusProduct
    (hG : IsConnectedReductive G) (hd : IsDerivedSubgroup d)
    (hS : IsSplitTorus S.toGrp) (hSD : IsSplitTorus S_D.toGrp)
    (hA : IsSplitTorus A.toGrp) (hj : IsClosedSubgroup j)
    (ha : IsClosedSubgroup a) (hacent : IsCentral a)
    (he : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hc : CommGroupScheme.groupHom c ≫ i = a) :
    IsFinite (kernel
      (prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
        (fun _ _ _ => Commute.all _ _))).X.hom := by
  let f := prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
    (fun _ _ _ => Commute.all _ _)
  let r : kernel f ⟶ D := kernelι f ≫ fst S_D.toGrp A.toGrp ≫ j
  have : IsClosedImmersion a.hom.hom.left := ha
  have : Mono a.hom.hom := Over.mono_of_mono_left _
  have : Mono (CommGroupScheme.groupHom c).hom.hom :=
    mono_of_mono_fac (congrArg (fun z => z.hom.hom) hc)
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : Mono (kernelι f ≫ fst S_D.toGrp A.toGrp).hom.hom :=
    mono_prodKernel_fst _ _ _
  have : Mono r.hom.hom := by
    change Mono ((kernelι f ≫ fst S_D.toGrp A.toGrp).hom.hom ≫ j.hom.hom)
    infer_instance
  have hrange : SubgroupFunctor.range r ≤ (center G).comap d := by
    rintro T z ⟨x, rfl⟩
    let p := x ≫ (kernelι f).hom.hom
    let xD := (productPointsEquiv S_D.toGrp A.toGrp T p).1
    let xA := (productPointsEquiv S_D.toGrp A.toGrp T p).2
    have hx : (xD ≫ (CommGroupScheme.groupHom e).hom.hom) *
        (xA ≫ (CommGroupScheme.groupHom c).hom.hom) = 1 := by
      exact (comp_prodHom _ _ _ T p).symm.trans
        (kernelPointsEquiv f T x).property
    have hcoord : xD ≫ (CommGroupScheme.groupHom e).hom.hom =
        (xA ≫ (CommGroupScheme.groupHom c).hom.hom)⁻¹ :=
      eq_inv_of_mul_eq_one_left hx
    have hmap : (x ≫ r.hom.hom) ≫ d.hom.hom = (xA ≫ a.hom.hom)⁻¹ := by
      change xD ≫ (j ≫ d).hom.hom = _
      rw [he, Grp.comp_hom_hom, ← Category.assoc, hcoord, GrpObj.inv_comp,
        Category.assoc, ← Grp.comp_hom_hom, hc]
    change (x ≫ r.hom.hom) ≫ d.hom.hom ∈ (center G).carrier T
    rw [hmap]
    exact (center G).carrier T |>.inv_mem (hacent T xA)
  obtain ⟨C, b, hb, hbrange, hbfin⟩ := derivedCentralIntersectionFiniteness k G D d hG hd
  have : IsClosedImmersion b.hom.hom.left := hb
  have hbRep : ((center G).comap d).IsRepresentedBy b :=
    ⟨Over.mono_of_mono_left _, hbrange⟩
  let q : kernel f ⟶ C := hbRep.factorHom r hrange
  have hq : q ≫ b = r := hbRep.factorHom_comp r hrange
  have : Mono q.hom.hom :=
    mono_of_mono_fac (congrArg (fun z => z.hom.hom) hq)
  have : Mono q.hom.hom.left := inferInstance
  have : IsAffineHom (S_D.toGrp ⊗ A.toGrp).X.hom := (hSD.tensor hA).isAffineHom
  have : Smooth (S_D.toGrp ⊗ A.toGrp).X.hom := (hSD.tensor hA).smooth
  have : IsAffineHom S.X.hom := hS.isAffineHom
  have : IsClosedImmersion (kernelι f).hom.hom.left := inferInstance
  have : LocallyOfFiniteType (kernel f).X.hom := by
    rw [← Over.w (kernelι f).hom.hom]
    infer_instance
  have : QuasiCompact (kernel f).X.hom := by
    rw [← Over.w (kernelι f).hom.hom]
    infer_instance
  have : LocallyOfFiniteType (q.hom.hom.left ≫ C.X.hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType q.hom.hom.left :=
    locallyOfFiniteType_of_comp q.hom.hom.left C.X.hom
  have : LocallyQuasiFinite q.hom.hom.left := inferInstance
  have : IsFinite C.X.hom := hbfin
  have : LocallyQuasiFinite (kernel f).X.hom := by
    rw [← Over.w q.hom.hom]
    infer_instance
  have : IsLocallyArtinian (Spec (CommRingCat.of k)) := by
    rw [Scheme.isLocallyArtinianScheme_Spec]
    change IsArtinianRing k
    infer_instance
  exact IsFinite.of_locallyQuasiFinite (kernel f).X.hom

end Field

/-- Full-kernel finiteness for compatible derived and central closed split factors. -/
def DerivedCentralSplitTorusProductKernelFinitenessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
    IsConnectedReductive G → IsDerivedSubgroup d →
    ∀ (S S_D A : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : S.toGrp ⟶ G) (j : S_D.toGrp ⟶ D) (e : S_D ⟶ S)
      (a : A.toGrp ⟶ G) (c : A ⟶ S),
      IsSplitTorus S.toGrp → IsSplitTorus S_D.toGrp → IsSplitTorus A.toGrp →
      IsClosedSubgroup j → IsClosedSubgroup a → IsCentral a →
      j ≫ d = CommGroupScheme.groupHom e ≫ i →
      CommGroupScheme.groupHom c ≫ i = a →
      IsFinite (kernel
        (prodHom (CommGroupScheme.groupHom e) (CommGroupScheme.groupHom c)
          (fun _ _ _ => Commute.all _ _))).X.hom

/-- The finite-kernel proposition holds over every field and in every universe. -/
theorem derivedCentralSplitTorusProductKernelFiniteness :
    DerivedCentralSplitTorusProductKernelFinitenessStatement.{u} := by
  intro k _ G D d hG hd S S_D A i j e a c hS hSD hA hj ha hacent he hc
  exact isFinite_kernel_derivedCentralSplitTorusProduct i j e a c hG hd hS hSD hA
    hj ha hacent he hc

end Langlands.GroupScheme
