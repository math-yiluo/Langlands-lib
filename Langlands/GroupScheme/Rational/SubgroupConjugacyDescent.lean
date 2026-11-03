import Langlands.GroupScheme.Rational.SubgroupConjugacy
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.GaloisPointRational

/-! # Descending rational subgroup conjugacy and its source isomorphism -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section BaseChange

variable {S S' : Scheme.{u}} {G H H' : GroupScheme S}

/-- Base change carries an inner automorphism to the inner automorphism of
its pulled-back rational point. -/
theorem baseChange_innerIso_hom (b : S' ⟶ S) (g : Over.mk (𝟙 S) ⟶ G.X) :
    (GroupScheme.baseChange b).map (G.innerIso g).hom =
      (((GroupScheme.baseChange b).obj G).innerIso (baseChangeBasePoint b G g)).hom := by
  apply hom_ext_points
  intro T x
  apply (baseChangePointsEquiv b G T).injective
  rw [baseChangePointsEquiv_comp, comp_innerIso_hom, comp_innerIso_hom,
    map_mul, map_mul, map_inv, baseChangePointsEquiv_constantPoint]

private theorem range_iso_precomp (e : H ≅ H') (i' : H' ⟶ G) :
    SubgroupFunctor.range (e.hom ≫ i') = SubgroupFunctor.range i' := by
  ext T x
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ e.hom.hom.hom, ?_⟩
    simp only [Grp.comp_hom_hom, Category.assoc]
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ e.inv.hom.hom, ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : H' ⟶ G => y ≫ f.hom.hom) (e.inv_hom_id_assoc i')

variable (b : S' ⟶ S) [QuasiCompact b] [Flat b] [Surjective b]
variable (i : H ⟶ G) (i' : H' ⟶ G) [Mono i.hom.hom] [Mono i'.hom.hom]
variable (g : Over.mk (𝟙 S) ⟶ G.X)
variable (e : (GroupScheme.baseChange b).obj H ≅ (GroupScheme.baseChange b).obj H')
variable (he : (GroupScheme.baseChange b).map i ≫
    (((GroupScheme.baseChange b).obj G).innerIso (baseChangeBasePoint b G g)).hom =
      e.hom ≫ (GroupScheme.baseChange b).map i')

include he

local instance : Mono (i ≫ (G.innerIso g).hom).hom.hom := by
  change Mono (i.hom.hom ≫ (G.innerIso g).hom.hom.hom)
  infer_instance

/-- A geometric source isomorphism conjugating by the pullback of `g` gives
equality of the represented conjugate subgroups over the original base. -/
theorem range_eq_of_baseChange_conjugacy :
    SubgroupFunctor.range (i ≫ (G.innerIso g).hom) = SubgroupFunctor.range i' := by
  apply SubgroupFunctor.range_eq_of_baseChange_eq b
  rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom,
    Functor.map_comp, baseChange_innerIso_hom, he]
  exact range_iso_precomp e _

/-- Construct the source isomorphism over the original base from an fpqc
conjugacy witness by the pullback of a supplied rational conjugator. -/
def subgroupConjugacyIsoOfBaseChange : H ≅ H' :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (show (SubgroupFunctor.range (i ≫ (G.innerIso g).hom)).IsRepresentedBy
      (i ≫ (G.innerIso g).hom) from ⟨inferInstance, rfl⟩)
    (show (SubgroupFunctor.range (i ≫ (G.innerIso g).hom)).IsRepresentedBy i' from
      ⟨inferInstance, (range_eq_of_baseChange_conjugacy b i i' g e he).symm⟩)

@[reassoc]
theorem subgroupConjugacyIsoOfBaseChange_hom_comp :
    (subgroupConjugacyIsoOfBaseChange b i i' g e he).hom ≫ i' =
      i ≫ (G.innerIso g).hom :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- Rational subgroup conjugacy descends if the conjugating point is already
rational over the original base; the source isomorphism is constructed. -/
theorem subgroupConjugate_of_baseChange_conjugacy : SubgroupConjugate i i' := by
  exact ⟨g, subgroupConjugacyIsoOfBaseChange b i i' g e he,
    (subgroupConjugacyIsoOfBaseChange_hom_comp b i i' g e he).symm⟩

end BaseChange

section Field

open GaloisPointComparison
open Langlands.AlgebraicGeometry.PointTopology

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
variable (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Coefficient extension and geometric pullback give the same rational point. -/
theorem rationalExtend_eq_baseChangeBasePoint
    (g : rationalPoints G) :
    rationalExtend k L G g = baseChangeBasePoint (baseMap k L) G g := by
  apply (baseChangeCoeffEquiv k L G).injective
  apply Over.OverMorphism.ext
  rw [baseChangeCoeffEquiv_left, baseChangeCoeffEquiv_left,
    rationalExtend_fst, baseChangeBasePoint_fst]

variable [IsAffine G.X.left] [FiniteDimensional k L] [IsGalois k L]

/-- Construct the original-field rational point represented by a Galois-fixed
rational point of the actual base change. -/
def rationalPointOfGaloisFixed
    (g : rationalPoints (baseChanged k L G))
    (hg : ∀ σ : L ≃ₐ[k] L, rationalConjugate k L G σ g = g) : rationalPoints G :=
  (rationalCoeffEquiv k G).symm (GaloisPoint.descend k L G
    ⟨baseChangeCoeffEquiv k L G g, fun σ => by
      simpa only [baseChangeCoeffEquiv_rationalConjugate] using
        congrArg (baseChangeCoeffEquiv k L G) (hg σ)⟩)

/-- The constructed rational point pulls back to the supplied fixed point. -/
theorem baseChangeBasePoint_rationalPointOfGaloisFixed
    (g : rationalPoints (baseChanged k L G))
    (hg : ∀ σ : L ≃ₐ[k] L, rationalConjugate k L G σ g = g) :
    baseChangeBasePoint (baseMap k L) G (rationalPointOfGaloisFixed k L G g hg) = g := by
  rw [← rationalExtend_eq_baseChangeBasePoint]
  apply (baseChangeCoeffEquiv k L G).injective
  rw [baseChangeCoeffEquiv_rationalExtend]
  simp only [rationalPointOfGaloisFixed, MulEquiv.apply_symm_apply,
    GaloisPoint.extend_descend]

variable {H H' : GroupScheme (Spec (CommRingCat.of k))}
variable (i : H ⟶ G) (i' : H' ⟶ G) [Mono i.hom.hom] [Mono i'.hom.hom]

/-- A finite-Galois conjugacy witness with a fixed conjugator descends,
including an actual source-group isomorphism over the original field. -/
theorem subgroupConjugate_of_galois_fixed_conjugator
    (g : rationalPoints (baseChanged k L G))
    (hg : ∀ σ : L ≃ₐ[k] L, rationalConjugate k L G σ g = g)
    (e : (GroupScheme.baseChange (baseMap k L)).obj H ≅
      (GroupScheme.baseChange (baseMap k L)).obj H')
    (he : (GroupScheme.baseChange (baseMap k L)).map i ≫
      ((baseChanged k L G).innerIso g).hom =
        e.hom ≫ (GroupScheme.baseChange (baseMap k L)).map i') :
    SubgroupConjugate i i' := by
  have hfpqc := fieldExtension_fpqc k L
  let : Surjective (baseMap k L) := hfpqc.1
  let : Flat (baseMap k L) := hfpqc.2.1
  let : QuasiCompact (baseMap k L) := hfpqc.2.2
  apply subgroupConjugate_of_baseChange_conjugacy (baseMap k L) i i'
    (rationalPointOfGaloisFixed k L G g hg) e
  simpa only [baseChangeBasePoint_rationalPointOfGaloisFixed] using he

end Field

end Langlands.GroupScheme
