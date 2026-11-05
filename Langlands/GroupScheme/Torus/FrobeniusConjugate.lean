import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.FiniteFieldTorsorPoint.LangGroupScheme
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Frobenius-stable conjugates from Lang's theorem -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Descent

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
  (G : GroupScheme B)

/-- Pull back a rational point and identify the ambient group by its canonical
descent isomorphism. -/
def descentBasePoint
    (g : Over.mk (𝟙 S) ⟶ ((baseChange b).obj G).X) :
    Over.mk (𝟙 S) ⟶ ((baseChange b).obj G).X :=
  baseChangeBasePoint a ((baseChange b).obj G) g ≫
    (descentBaseChangeIso b a ha G).hom.hom.hom

/-- Transport of a point is coefficient pullback after projection to the
original group. -/
theorem descentBasePoint_fst
    (g : Over.mk (𝟙 S) ⟶ ((baseChange b).obj G).X) :
    (descentBasePoint b a ha G g).left ≫ pullback.fst G.X.hom b =
      a ≫ g.left ≫ pullback.fst G.X.hom b := by
  change (_ ≫ (descentBaseChangeIso b a ha G).hom.hom.hom.left) ≫ _ = _
  rw [Category.assoc, descentBaseChangeIso_hom_fst, ← Category.assoc]
  have h := baseChangeBasePoint_fst a ((baseChange b).obj G) g
  change (baseChangeBasePoint a ((baseChange b).obj G) g).left ≫
    pullback.fst (pullback.snd G.X.hom b) a = a ≫ g.left at h
  exact (congrArg (fun z => z ≫ pullback.fst G.X.hom b) h).trans
    (Category.assoc _ _ _)

/-- Canonical descent transport commutes with inner automorphisms. -/
theorem descentBasePoint_innerIso
    (g : Over.mk (𝟙 S) ⟶ ((baseChange b).obj G).X) :
    (baseChange a).map (((baseChange b).obj G).innerIso g).hom ≫
        (descentBaseChangeIso b a ha G).hom =
      (descentBaseChangeIso b a ha G).hom ≫
        (((baseChange b).obj G).innerIso (descentBasePoint b a ha G g)).hom := by
  rw [baseChange_innerIso_hom]
  exact innerIso_hom_comp (descentBaseChangeIso b a ha G).hom _

variable {H : GroupScheme S} (i : H ⟶ (baseChange b).obj G)

/-- The transported conjugate inclusion is conjugated by the transported
point. -/
theorem descent_conjugate_inclusion
    (g : Over.mk (𝟙 S) ⟶ ((baseChange b).obj G).X) :
    (baseChange a).map (i ≫ (((baseChange b).obj G).innerIso g).hom) ≫
        (descentBaseChangeIso b a ha G).hom =
      ((baseChange a).map i ≫ (descentBaseChangeIso b a ha G).hom) ≫
        (((baseChange b).obj G).innerIso (descentBasePoint b a ha G g)).hom := by
  rw [Functor.map_comp, Category.assoc, descentBasePoint_innerIso,
    ← Category.assoc]

end Descent

section FiniteField

variable (k Ω : Type u) [Field k] [Fintype k]
  [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Lang's equation on rational points of the actual geometric pullback,
using the canonical descent point transport. -/
theorem exists_eq_inv_mul_descentBasePoint
    (x : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange (algebraBaseMap k Ω)).obj G).X) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange (algebraBaseMap k Ω)).obj G).X,
      x = g⁻¹ * descentBasePoint (algebraBaseMap k Ω)
        (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))
        (galoisBaseMap_over k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) G g := by
  let e := baseChangeBasePointsEquiv (algebraBaseMap k Ω) G
  obtain ⟨g, hg⟩ :=
    FiniteFieldTorsorPoint.exists_eq_inv_mul_frobenius G Ω (e x)
  refine ⟨e.symm g, ?_⟩
  apply e.injective
  rw [map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [hg]
  congr 1
  apply Over.OverMorphism.ext
  rw [baseChangeBasePointsEquiv_left, descentBasePoint_fst]
  symm
  change (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) ≫
      (e.symm g).left ≫ pullback.fst G.X.hom (algebraBaseMap k Ω) =
    (Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgHom k Ω).toRingHom)) ≫
      g.left
  have he := congrArg (fun z => z.left) (e.apply_symm_apply g)
  rw [baseChangeBasePointsEquiv_left] at he
  rw [he]
  rfl

variable {H : GroupScheme (Spec (CommRingCat.of Ω))}
  (i : H ⟶ (baseChange (algebraBaseMap k Ω)).obj G)
  (hc : SubgroupConjugate
    ((baseChange (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))).map i ≫
      (descentBaseChangeIso (algebraBaseMap k Ω)
          (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))
          (galoisBaseMap_over k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) G).hom) i)

include hc in
/-- A subgroup conjugate to its Frobenius transform has a conjugate whose
all-test range is Frobenius invariant. -/
theorem exists_frobeniusStableConjugator :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange (algebraBaseMap k Ω)).obj G).X,
      SubgroupFunctor.range
        ((baseChange (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))).map
          (i ≫ (((baseChange (algebraBaseMap k Ω)).obj G).innerIso g).hom) ≫
          (descentBaseChangeIso (algebraBaseMap k Ω)
          (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))
          (galoisBaseMap_over k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) G).hom) =
        SubgroupFunctor.range (i ≫ (((baseChange (algebraBaseMap k Ω)).obj G).innerIso g).hom) := by
  obtain ⟨x, e, he⟩ := hc
  obtain ⟨g, hg⟩ := exists_eq_inv_mul_descentBasePoint k Ω G x
  have hfg : descentBasePoint (algebraBaseMap k Ω)
        (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))
        (galoisBaseMap_over k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) G g = g * x := by
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using
      (congrArg (fun z => g * z) hg).symm
  refine ⟨g, ?_⟩
  rw [descent_conjugate_inclusion, hfg, innerIso_mul_hom, ← Category.assoc,
    he, Category.assoc, SubgroupFunctor.range_iso_comp]

/-- Choose a point whose conjugate of the specified subgroup has
Frobenius-invariant all-test range. -/
def frobeniusStableConjugatingPoint :
    Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ ((baseChange (algebraBaseMap k Ω)).obj G).X :=
  Classical.choose (exists_frobeniusStableConjugator k Ω G i hc)

/-- The actual inclusion of a chosen Frobenius-stable conjugate. -/
def frobeniusStableConjugate : H ⟶ (baseChange (algebraBaseMap k Ω)).obj G :=
  i ≫ (((baseChange (algebraBaseMap k Ω)).obj G).innerIso
    (frobeniusStableConjugatingPoint k Ω G i hc)).hom

/-- The chosen conjugate is conjugate to the specified original subgroup. -/
theorem subgroupConjugate_frobeniusStableConjugate :
    SubgroupConjugate i (frobeniusStableConjugate k Ω G i hc) :=
  SubgroupConjugate.conjugate i _

/-- The range of the chosen actual inclusion is fixed by Frobenius transport
on every test scheme. -/
theorem frobeniusStableConjugate_range_eq :
    SubgroupFunctor.range
      ((baseChange (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))).map
        (frobeniusStableConjugate k Ω G i hc) ≫
        (descentBaseChangeIso (algebraBaseMap k Ω)
          (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))
          (galoisBaseMap_over k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) G).hom) =
      SubgroupFunctor.range (frobeniusStableConjugate k Ω G i hc) :=
  Classical.choose_spec (exists_frobeniusStableConjugator k Ω G i hc)

/-- Conjugation preserves maximality of the chosen torus inclusion. -/
theorem IsMaximalTorus.frobeniusStableConjugate
    {T : CommGroupScheme (Spec (CommRingCat.of Ω))}
    {i : T.toGrp ⟶ (baseChange (algebraBaseMap k Ω)).obj G} (hi : IsMaximalTorus i)
    (hc : SubgroupConjugate
      ((baseChange (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))).map i ≫
      (descentBaseChangeIso (algebraBaseMap k Ω)
          (galoisBaseMap k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω))
          (galoisBaseMap_over k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) G).hom) i) :
    IsMaximalTorus (frobeniusStableConjugate k Ω G i hc) :=
  hi.comp_iso _

end FiniteField

end Langlands.GroupScheme
