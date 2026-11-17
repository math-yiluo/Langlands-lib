import Langlands.GroupScheme.Torus.MultiplicativeTypeFieldExtensionStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeGeometry
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Langlands.GroupScheme.LinearAdditiveExtension.DiagonalizableAverage
import Langlands.GroupScheme.VectorScalarKernel
import Langlands.GroupScheme.FppfQuotientComparison

/-! # Reductions for extensions of multiplicative-type groups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot.IsFppfQuotient

variable {S : Scheme.{u}} {H G K : GroupScheme S} (i : H ⟶ G) [Mono i.hom.hom]
    {p : G ⟶ K} (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p)

include i hq

/-- An fppf quotient with affine represented kernel is an affine morphism. -/
theorem isAffineHom_of_kernel [IsAffineHom H.X.hom] : IsAffineHom p.hom.hom.left := by
  have hpb := (QuotientCell.multiplication_isPullback i (𝟙 G.X) p.hom.hom
    (hq.fibers_iff ⟨inferInstance, rfl⟩)).map (Over.forget S)
  change IsPullback (QuotientCell.multiplication i (𝟙 G.X)).left
    (fst G.X H.X).left p.hom.hom.left ((𝟙 G.X) ≫ p.hom.hom).left at hpb
  simp only [Category.id_comp] at hpb
  have hsource : IsAffineHom (fst G.X H.X).left := by
    change IsAffineHom (Limits.pullback.fst G.X.hom H.X.hom)
    exact MorphismProperty.pullback_fst G.X.hom H.X.hom
      (inferInstanceAs (IsAffineHom H.X.hom))
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    hpb.flip ⟨⟨hq.2.1, hq.1⟩, hq.2.2.1⟩ hsource

/-- A represented fppf extension of affine finite-type groups has affine finite-type source. -/
theorem affine_finiteType_source [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]
    [LocallyOfFiniteType K.X.hom] : IsAffineHom G.X.hom ∧ LocallyOfFiniteType G.X.hom := by
  have : IsAffineHom p.hom.hom.left := hq.isAffineHom_of_kernel i
  have : LocallyOfFinitePresentation p.hom.hom.left := hq.2.2.1
  rw [← Over.w p.hom.hom]
  exact ⟨inferInstance, inferInstance⟩

/-- Maps out of a represented fpqc quotient are maps killing its represented kernel. -/
def quotientHomEquiv {V : GroupScheme S} [QuasiCompact p.hom.hom.left] :
    (K ⟶ V) ≃ {f : G ⟶ V // i ≫ f = 0} := by
  let e := hq.kernelIso (show (SubgroupFunctor.range i).IsRepresentedBy i from
    ⟨inferInstance, rfl⟩)
  have hip : i ≫ p = 0 := by
    rw [← hq.kernelIso_hom_comp
      (show (SubgroupFunctor.range i).IsRepresentedBy i from ⟨inferInstance, rfl⟩),
      Category.assoc]
    have hk : kernelι p ≫ p = 0 := by
      apply Grp.hom_ext
      exact (kernel_isPullback p).w
    rw [hk, comp_zero]
  have hk (f : {f : G ⟶ V // i ≫ f = 0}) : kernelι p ≫ f.1 = 0 := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, hq.kernelIso_hom_comp, f.2, comp_zero]
  let : Flat p.hom.hom.left := hq.1
  let : Surjective p.hom.hom.left := hq.2.1
  refine
    { toFun := fun d => ⟨p ≫ d, by rw [← Category.assoc, hip, zero_comp]⟩
      invFun := fun f => FpqcHomDescent.hom p f.1 (hk f)
      left_inv := ?_
      right_inv := ?_ }
  · intro d
    exact (FpqcHomDescent.unique p (p ≫ d) (hk ⟨p ≫ d, by
      rw [← Category.assoc, hip, zero_comp]⟩) d rfl).symm
  · intro f
    exact Subtype.ext (FpqcHomDescent.fac p f.1 (hk f))

/-- Vanishing of homomorphisms to a fixed group is preserved by represented fpqc extensions. -/
theorem hom_eq_zero_of_kernel_quotient {V : GroupScheme S}
    [QuasiCompact p.hom.hom.left] [Subsingleton (H ⟶ V)] [Subsingleton (K ⟶ V)]
    (f : G ⟶ V) : f = 0 := by
  let e := hq.kernelIso (show (SubgroupFunctor.range i).IsRepresentedBy i from
    ⟨inferInstance, rfl⟩)
  have hi : i ≫ f = 0 := Subsingleton.elim _ _
  have hk : kernelι p ≫ f = 0 := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, hq.kernelIso_hom_comp, hi, comp_zero]
  let : Flat p.hom.hom.left := hq.1
  let : Surjective p.hom.hom.left := hq.2.1
  have hd : FpqcHomDescent.hom p f hk = 0 := Subsingleton.elim _ _
  rw [← FpqcHomDescent.fac p f hk, hd, comp_zero]

end RelativeRoot.IsFppfQuotient

namespace Diagonalizable

open PointedCoordinateWeights DiagonalizableAverage

variable {k : Type u} [Field k] (Λ : Type u) [AddCommGroup Λ]

/-- Every homomorphism from a diagonalizable group to the additive group is zero. -/
theorem hom_vector_eq_zero
    (f : (groupScheme (CommRingCat.of k) Λ).toGrp ⟶
      VectorGroup.groupScheme (CommRingCat.of k) 1) : f = 0 := by
  apply Grp.hom_ext
  apply affine_hom_ext
  intro A _ _ d
  have ht := congrArg
    (fun x => coord (x ≫ f.hom.hom))
    (pmap_translation_univPoint (k := k) Λ d)
  rw [pmap_comp_hom, coord_pmap, MonObj.mul_comp, coord_mul,
    pmap_comp_hom, coord_pmap] at ht
  have hc := congrArg (fun x : AddMonoidAlgebra A Λ => x.coeff 0) ht
  rw [coeff_zero_translation, AddMonoidAlgebra.coeff_add] at hc
  change (coord (univPoint k Λ A ≫ f.hom.hom)).coeff 0 =
    (coord (univPoint k Λ A ≫ f.hom.hom)).coeff 0 +
      (const k Λ A (coord (d ≫ f.hom.hom))).coeff 0 at hc
  have hconst : (const k Λ A (coord (d ≫ f.hom.hom))).coeff 0 =
      coord (d ≫ f.hom.hom) := by
    change (AddMonoidAlgebra.single 0 _).coeff 0 = _
    simp
  rw [hconst] at hc
  have hd : coord (d ≫ f.hom.hom) = 0 := (add_eq_left.mp hc.symm)
  change d ≫ f.hom.hom = d ≫ (0 : (groupScheme (CommRingCat.of k) Λ).toGrp ⟶
    VectorGroup.groupScheme (CommRingCat.of k) 1).hom.hom
  change d ≫ f.hom.hom = d ≫ (1 : _ ⟶ _)
  rw [MonObj.comp_one]
  apply coord_injective
  simpa only [coord_one] using hd

end Diagonalizable

end Langlands.GroupScheme
