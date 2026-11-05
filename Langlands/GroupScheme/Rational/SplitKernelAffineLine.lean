import Langlands.GroupScheme.Rational.AffineLineExtensions
import Langlands.GroupScheme.Products

/-! # Pointed affine-line capture and constant split kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H Q : GroupScheme (Spec (CommRingCat.of k))}

local notation "A" => AffineLine.scheme (Spec (CommRingCat.of k))
local notation "z" => AffineLine.zeroSection (Spec (CommRingCat.of k))

/-- Every affine-line map taking zero to the identity factors through the
supplied group homomorphism as a morphism of relative schemes. -/
def CapturesPointedAffineLineMaps (s : H ⟶ G) : Prop :=
  ∀ a : A ⟶ G.X, z ≫ a = 1 →
    a ∈ (SubgroupFunctor.range s).carrier A

namespace HasConstantAffineLineMaps

/-- A pointed affine-line map to a constant target is the identity map. -/
theorem pointed_eq_one (hG : HasConstantAffineLineMaps G) (a : A ⟶ G.X)
    (ha : z ≫ a = 1) : a = 1 := by
  rw [hG.eq_to_zeroSection a, ha]
  exact MonObj.comp_one _

end HasConstantAffineLineMaps

namespace CapturesPointedAffineLineMaps

/-- In an actual product with a constant second factor, the first-factor
inclusion captures every pointed affine-line map. -/
theorem of_productIso {V W : GroupScheme (Spec (CommRingCat.of k))}
    (e : G ≅ V ⊗ W) (hW : HasConstantAffineLineMaps W) :
    CapturesPointedAffineLineMaps (lift (𝟙 V) (0 : V ⟶ W) ≫ e.inv) := by
  intro a ha
  have hw : (a ≫ e.hom.hom.hom) ≫ snd V.X W.X = 1 := by
    have hp : z ≫ (a ≫ (e.hom ≫ snd V W).hom.hom) = 1 := by
      rw [← Category.assoc, ha]
      exact MonObj.one_comp _
    exact hW.pointed_eq_one _ hp
  refine SubgroupFunctor.mem_range.mpr
    ⟨(a ≫ e.hom.hom.hom) ≫ fst V.X W.X, ?_⟩
  apply (cancel_mono e.hom.hom.hom).mp
  simp only [Category.assoc, ← Grp.comp_hom_hom,
    e.inv_hom_id, Category.comp_id]
  apply (productPointsEquiv V W A).injective
  apply Prod.ext
  · simp only [productPointsEquiv_fst, Category.assoc, Grp.lift_hom,
      Mon.lift_hom, lift_fst, Grp.id_hom_hom, Category.comp_id]
  · simp only [productPointsEquiv_snd, Category.assoc, Grp.lift_hom,
      Mon.lift_hom, lift_snd]
    change (a ≫ e.hom.hom.hom) ≫ fst V.X W.X ≫ (1 : V.X ⟶ W.X) = _
    rw [MonObj.comp_one, MonObj.comp_one]
    exact hw.symm

/-- Capture in a subgroup applies to every pointed ambient map which factors
through its monic inclusion. -/
theorem mem_range_comp (s : H ⟶ G) (hcap : CapturesPointedAffineLineMaps s)
    (j : G ⟶ Q) [Mono j.hom.hom] (a : A ⟶ Q.X)
    (ha : z ≫ a = 1) (haj : a ∈ (SubgroupFunctor.range j).carrier A) :
    a ∈ (SubgroupFunctor.range (s ≫ j)).carrier A := by
  obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp haj
  have hb0 : z ≫ b = 1 := by
    apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, hb, ha, MonObj.one_comp]
  obtain ⟨c, hc⟩ := SubgroupFunctor.mem_range.mp (hcap b hb0)
  refine SubgroupFunctor.mem_range.mpr ⟨c, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hc, hb]

/-- A constant quotient captures every pointed map in its full kernel, and
hence in any supplied homomorphism covering that kernel on all scheme tests. -/
theorem of_constant_quotient (q : G ⟶ Q) (s : H ⟶ G)
    (hker : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range s)
    (hQ : HasConstantAffineLineMaps Q) : CapturesPointedAffineLineMaps s := by
  intro a ha
  apply hker A
  apply (mem_range_kernelι_iff q a).mpr
  apply hQ.pointed_eq_one
  rw [← Category.assoc, ha]
  exact MonObj.one_comp _

/-- If a homomorphic section captures all pointed affine-line maps, its
complementary full kernel has only constant affine-line maps. -/
theorem kernel_hasConstantAffineLineMaps (q : G ⟶ H) (s : H ⟶ G)
    (hs : s ≫ q = 𝟙 H) (hcap : CapturesPointedAffineLineMaps s) :
    HasConstantAffineLineMaps (kernel q) := by
  intro a
  let d := affineLineDifference a
  have hd0 : z ≫ (d ≫ (kernelι q).hom.hom) = 1 := by
    rw [← Category.assoc, zeroSection_comp_affineLineDifference]
    exact MonObj.one_comp _
  obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp (hcap _ hd0)
  have hbq : b = 1 := by
    calc
      b = (b ≫ s.hom.hom) ≫ q.hom.hom := by
        rw [Category.assoc, ← Grp.comp_hom_hom, hs,
          Grp.id_hom_hom, Category.comp_id]
      _ = (d ≫ (kernelι q).hom.hom) ≫ q.hom.hom := by rw [hb]
      _ = 1 := (kernelPointsEquiv q A d).property
  have hd : d = 1 := by
    apply (cancel_mono (kernelι q).hom.hom).mp
    rw [← hb, hbq, MonObj.one_comp, MonObj.one_comp]
  exact ⟨z ≫ a, (affineLineDifference_eq_one_iff a).mp hd⟩

end CapturesPointedAffineLineMaps

end Langlands.GroupScheme
