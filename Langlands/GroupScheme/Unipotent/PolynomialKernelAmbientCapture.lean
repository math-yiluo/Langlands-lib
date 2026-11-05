import Langlands.GroupScheme.Torus.Products
import Langlands.GroupScheme.Unipotent.PolynomialKernelAmbientFactor
import Langlands.GroupScheme.Rational.SplitKernelAffineLine

/-! # Pointed affine-line capture by ambient polynomial-kernel factors -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme

section BaseChangeProducts

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (V W : GroupScheme S)

@[reassoc (attr := simp)]
theorem baseChangeTensorIso_inv_fst :
    (baseChangeTensorIso b V W).inv ≫ (baseChange b).map (fst V W) = fst _ _ := by
  exact Functor.Monoidal.μ_fst (baseChange b) V W

@[reassoc (attr := simp)]
theorem baseChangeTensorIso_inv_snd :
    (baseChangeTensorIso b V W).inv ≫ (baseChange b).map (snd V W) = snd _ _ := by
  exact Functor.Monoidal.μ_snd (baseChange b) V W

/-- The product comparison preserves the actual first-factor inclusion. -/
@[reassoc (attr := simp)]
theorem baseChangeTensorIso_section :
    lift (𝟙 ((baseChange b).obj V)) (0 : (baseChange b).obj V ⟶ (baseChange b).obj W) ≫
      (baseChangeTensorIso b V W).inv =
        (baseChange b).map (lift (𝟙 V) (0 : V ⟶ W)) := by
  simpa only [(baseChange b).map_id, Functor.map_zero, baseChangeTensorIso, Iso.symm_inv, Functor.Monoidal.μIso_hom] using
    Functor.Monoidal.lift_μ (baseChange b) (𝟙 V) (0 : V ⟶ W)

end BaseChangeProducts

namespace Unipotent

open OneDimensional RelativeRoot

variable {k : Type u} [Field k] {n r m : ℕ}
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (g : Fin m → k[X]) (hg : ∀ i, IsAdditive (g i))
    (e : VectorGroup.groupScheme (CommRingCat.of k) n ≅
      VectorGroup.groupScheme (CommRingCat.of k) r ⊗
        VectorGroup.groupScheme (CommRingCat.of k) m)
    (he : e.hom ≫ snd _ _ ≫ polynomialRow g hg = polynomialRow f hf)
    {S' : Scheme.{u}} (b : S' ⟶ Spec (CommRingCat.of k))

/-- The compatible kernel decomposition after actual scheme base change. -/
def polynomialKernelAmbientBaseChangeIso :
    kernel ((baseChange b).map (polynomialRow f hf)) ≅
      (baseChange b).obj (VectorGroup.groupScheme (CommRingCat.of k) r) ⊗
        (baseChange b).obj (kernel (polynomialRow g hg)) :=
  (kernelBaseChangeIso b (polynomialRow f hf)).symm ≪≫
    (baseChange b).mapIso (polynomialKernelAmbientKernelIso f hf g hg e he) ≪≫
      baseChangeTensorIso b _ _

/-- The first-factor inclusion in the changed kernel is the changed ambient
section, after the actual kernel inclusion. -/
@[reassoc (attr := simp)]
theorem polynomialKernelAmbientBaseChangeIso_section_ι :
    lift (𝟙 _) 0 ≫ (polynomialKernelAmbientBaseChangeIso f hf g hg e he b).inv ≫
      kernelι ((baseChange b).map (polynomialRow f hf)) =
        (baseChange b).map (polynomialKernelAmbientSection e) := by
  simp only [polynomialKernelAmbientBaseChangeIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Category.assoc, kernelBaseChangeIso_hom_ι]
  rw [← Category.assoc, baseChangeTensorIso_section, ← Functor.map_comp,
    ← Functor.map_comp, polynomialKernelAmbientKernelIso_section_ι]

/-- A pointed map killed by the changed row factors through the changed
ambient section whenever the changed residual kernel is constant. -/
theorem mem_range_baseChange_polynomialKernelAmbientSection
    (he : e.hom ≫ snd _ _ ≫ polynomialRow g hg = polynomialRow f hf)
    {K : Type u} [Field K] (c : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (hconst : HasConstantAffineLineMaps
      ((baseChange c).obj (kernel (polynomialRow g hg))))
    (a : AffineLine.scheme (Spec (CommRingCat.of K)) ⟶
      ((baseChange c).obj (VectorGroup.groupScheme (CommRingCat.of k) n)).X)
    (ha : AffineLine.zeroSection (Spec (CommRingCat.of K)) ≫ a = 1)
    (hrow : a ≫ ((baseChange c).map (polynomialRow f hf)).hom.hom = 1) :
    a ∈ (SubgroupFunctor.range
      ((baseChange c).map (polynomialKernelAmbientSection e))).carrier _ := by
  have hcap := CapturesPointedAffineLineMaps.of_productIso
    (polynomialKernelAmbientBaseChangeIso f hf g hg e he c) hconst
  have hmem := CapturesPointedAffineLineMaps.mem_range_comp _ hcap
    (kernelι ((baseChange c).map (polynomialRow f hf))) a ha
    ((mem_range_kernelι_iff _ a).mpr hrow)
  simpa only [Category.assoc, polynomialKernelAmbientBaseChangeIso_section_ι] using hmem

/-- Every nonzero additive row admits a closed ambient vector subgroup of
strictly smaller rank, a retraction, and capture of all pointed affine-line
maps over the separable closure which are killed by the changed row. -/
theorem exists_polynomialKernelAmbientCapture (n : ℕ)
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) (hf0 : f ≠ 0) :
    ∃ (r : ℕ)
      (s : VectorGroup.groupScheme (CommRingCat.of k) r ⟶
        VectorGroup.groupScheme (CommRingCat.of k) n)
      (q : VectorGroup.groupScheme (CommRingCat.of k) n ⟶
        VectorGroup.groupScheme (CommRingCat.of k) r),
      r < n ∧ IsClosedSubgroup s ∧ s ≫ q = 𝟙 _ ∧ s ≫ polynomialRow f hf = 0 ∧
        ∀ a : AffineLine.scheme (Spec (CommRingCat.of (SeparableClosure k))) ⟶
            ((baseChange (algebraBaseMap k (SeparableClosure k))).obj
              (VectorGroup.groupScheme (CommRingCat.of k) n)).X,
          AffineLine.zeroSection (Spec (CommRingCat.of (SeparableClosure k))) ≫ a = 1 →
          a ≫ ((baseChange (algebraBaseMap k (SeparableClosure k))).map
            (polynomialRow f hf)).hom.hom = 1 →
          a ∈ (SubgroupFunctor.range
            ((baseChange (algebraBaseMap k (SeparableClosure k))).map s)).carrier _ := by
  obtain ⟨r, m, g, hg, _hrm, hrn, _hc, hcs, e, he⟩ :=
    exists_polynomialKernelAmbientFactor_of_ne_zero n f hf hf0
  refine ⟨r, polynomialKernelAmbientSection e, polynomialKernelAmbientRetraction e,
    hrn, polynomialKernelAmbientSection_isClosedSubgroup e,
    polynomialKernelAmbientSection_comp_retraction e,
    polynomialKernelAmbientSection_comp_row f hf g hg e he, ?_⟩
  intro a ha hrow
  exact mem_range_baseChange_polynomialKernelAmbientSection f hf g hg e he
    (algebraBaseMap k (SeparableClosure k)) hcs a ha hrow

end Unipotent
end Langlands.GroupScheme
