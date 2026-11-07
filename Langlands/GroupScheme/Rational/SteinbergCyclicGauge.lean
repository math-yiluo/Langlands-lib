import Langlands.GroupScheme.Rational.SteinbergRepresentativeComparison
import Langlands.GroupScheme.Rational.SteinbergCoxeterTorus
import Langlands.GroupScheme.SchemeActionRationalOrbit
import Langlands.GroupScheme.HomConjugacy

/-! # Cyclic comparison gauges over algebraically closed fields -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private def successiveGaugePath {B : Type*} :
    (r : ℕ) → (Fin r → B → B) → B → Fin (r + 1) → B
  | 0, _, t => fun _ => t
  | r + 1, f, t => Fin.cons t
      (successiveGaugePath r (fun j => f j.succ) (f 0 t))

private theorem successiveGaugePath_zero {B : Type*} (r : ℕ)
    (f : Fin r → B → B) (t : B) : successiveGaugePath r f t 0 = t := by
  cases r <;> rfl

private theorem successiveGaugePath_step {B : Type*} (r : ℕ)
    (f : Fin r → B → B) (t : B) (j : Fin r) :
    successiveGaugePath r f t j.succ = f j (successiveGaugePath r f t j.castSucc) := by
  induction r generalizing t with
  | zero => exact j.elim0
  | succ r ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.castSucc_zero, successiveGaugePath, Fin.cons_zero, Fin.cons_succ,
        successiveGaugePath_zero]
    · simpa only [← Fin.succ_castSucc, successiveGaugePath, Fin.cons_succ] using
        ih (fun j => f j.succ) (f 0 t) j

private theorem gaugeProduct_telescope {A : Type*} [Group A] (r : ℕ)
    (a : Fin r → A) (b : Fin (r + 1) → A) :
    (List.ofFn fun j => b j.castSucc * a j * (b j.succ)⁻¹).prod =
      b 0 * (List.ofFn a).prod * (b (Fin.last r))⁻¹ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    have ht := ih (fun j => a j.succ) (fun j => b j.succ)
    simp only [Fin.succ_castSucc] at ht
    rw [ht]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    group

private theorem exists_cyclicGaugePath {A B : Type*} [Group A] {r : ℕ}
    (i : B → A) (hi : Function.Injective i) (n m : Fin r → A)
    (hstep : ∀ j t, ∃ s, i s = (m j)⁻¹ * i t * n j)
    (t : B) (hprod : (List.ofFn m).prod = i t * (List.ofFn n).prod * (i t)⁻¹) :
    ∃ v : Fin (r + 1) → B, v (Fin.last r) = v 0 ∧
      ∀ j, m j = i (v j.castSucc) * n j * (i (v j.succ))⁻¹ := by
  choose f hf using hstep
  let v := successiveGaugePath r f t
  have hv0 : v 0 = t := successiveGaugePath_zero r f t
  have hfactor (j : Fin r) :
      m j = i (v j.castSucc) * n j * (i (v j.succ))⁻¹ := by
    have hs : i (v j.succ) = (m j)⁻¹ * i (v j.castSucc) * n j := by
      dsimp only [v]
      rw [successiveGaugePath_step]
      exact hf j _
    rw [hs]
    group
  refine ⟨v, ?_, hfactor⟩
  have htel := gaugeProduct_telescope r n (fun j => i (v j))
  have hm : (List.ofFn m).prod =
      i (v 0) * (List.ofFn n).prod * (i (v (Fin.last r)))⁻¹ := by
    rw [funext hfactor]
    exact htel
  rw [hv0] at hm
  have he := mul_left_cancel (hm.symm.trans hprod)
  exact hi ((inv_injective he).trans (congrArg i hv0).symm)

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G}

local instance : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono
local instance : Mono p.inclusion.hom.hom := Over.mono_of_mono_left _

/-- Two actual normalizer points with equal full Weyl action differ by a torus point. -/
theorem exists_torus_mul_of_weylAction_eq (n m : normalizerPoints p.inclusion)
    (h : weylAction p.inclusion n = weylAction p.inclusion m) :
    ∃ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X,
      n.val = (t ≫ p.inclusion.hom.hom) * m.val := by
  have hz : weylAction p.inclusion (n * m⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hc := (p.isSplitTorus.weylAction_eq_one_iff p.inclusion (n * m⁻¹)).mp hz
  have hc' : n.val * m.val⁻¹ ∈
      (torusCentralizer p.inclusion).carrier (Over.mk (𝟙 _)) := by
    rw [torusCentralizer_carrier_base]
    exact hc
  rw [maximalTorusCentralizer k G p.isConnectedReductive p.torus p.inclusion
    p.isMaximalTorus, SubgroupFunctor.mem_range] at hc'
  obtain ⟨t, ht⟩ := hc'
  refine ⟨t, ?_⟩
  rw [ht, mul_assoc, inv_mul_cancel, mul_one]

variable {r : ℕ} (e : Fin r ≃ p.base.support)
    (n m : p.SimpleReflectionRepresentatives)

@[simp]
theorem coxeterNormalizer_val :
    (coxeterNormalizer e n).val = (List.ofFn fun j => (n (e j)).point).prod := by
  change (normalizerPoints p.inclusion).subtype (coxeterNormalizer e n) = _
  rw [coxeterNormalizer, map_list_prod, List.map_ofFn]
  rfl

/-- A rational conjugacy of the full ordered products gives an actual cyclic gauge. -/
theorem nonempty_cyclicTorusGauge_of_conjugate
    (t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X)
    (ht : (coxeterNormalizer e m).val =
      (t ≫ p.inclusion.hom.hom) * (coxeterNormalizer e n).val *
        (t ≫ p.inclusion.hom.hom)⁻¹) :
    Nonempty (p.CyclicTorusGauge e n m) := by
  have hstep (j : Fin r)
      (v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X) :
      ∃ w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X,
        w ≫ p.inclusion.hom.hom =
          (m (e j)).point⁻¹ * (v ≫ p.inclusion.hom.hom) * (n (e j)).point := by
    let q := SimpleReflectionRepresentative.torusRatio (m (e j)) (n (e j))
    have hq := SimpleReflectionRepresentative.point_eq_torusRatio_mul (m (e j)) (n (e j))
    let v' := q⁻¹ * v
    let w := v' ≫ (CommGroupScheme.groupHom (n (e j)).torusAut.inv).hom.hom
    refine ⟨w, ?_⟩
    have hn := congrArg (fun f : p.torus.toGrp ⟶ G => v' ≫ f.hom.hom)
      (n (e j)).normalizes.inv
    simp only [Grp.comp_hom_hom] at hn
    rw [← Category.assoc, comp_innerIso_hom, constantPoint_self] at hn
    calc
      w ≫ p.inclusion.hom.hom =
          (n (e j)).point⁻¹ * (v' ≫ p.inclusion.hom.hom) * (n (e j)).point := by
        simpa only [w, Iso.symm_hom, inv_inv, Category.assoc] using hn.symm
      _ = (m (e j)).point⁻¹ * (v ≫ p.inclusion.hom.hom) * (n (e j)).point := by
        dsimp only [v', q]
        rw [MonObj.mul_comp, GrpObj.inv_comp, hq]
        group
  obtain ⟨v, hv, hf⟩ := exists_cyclicGaugePath
    (fun z => z ≫ p.inclusion.hom.hom)
    (fun _ _ h => (cancel_mono p.inclusion.hom.hom).mp h)
    (fun j => (n (e j)).point) (fun j => (m (e j)).point) hstep t
    (by simpa only [coxeterNormalizer_val] using ht)
  exact ⟨⟨v, hv, hf⟩⟩

variable [IsAlgClosed k]

/-- Over an algebraically closed field the actual surjective Coxeter map lifts rational points. -/
theorem exists_comp_eq_coxeterTorusEnd (hG : IsSemisimple G)
    (q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X) :
    ∃ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X,
      t ≫ (CommGroupScheme.groupHom (coxeterTorusEnd e n)).hom.hom = q := by
  let f := CommGroupScheme.groupHom (coxeterTorusEnd e n)
  have := p.isSplitTorus.smooth
  have : LocallyOfFiniteType (f.hom.hom.left ≫ p.torus.X.hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType f.hom.hom.left :=
    locallyOfFiniteType_of_comp f.hom.hom.left p.torus.X.hom
  have hs := (coxeterTorusEnd_flat_and_surjective e n hG).2
  have : Surjective f.hom.hom.left := hs
  obtain ⟨z, hz⟩ := exists_rationalPoint_lift_of_mem_range f.hom.hom.left q.left
    (f.hom.hom.left.surjective (q.left (IsLocalRing.closedPoint k)))
  refine ⟨Over.homMk z ?_, Over.OverMorphism.ext hz⟩
  rw [← Over.w f.hom.hom, ← Category.assoc, hz]
  exact Over.w q

/-- Every two supplied ordered representative products are conjugate by a rational torus point
when the field is algebraically closed and the actual group is semisimple. -/
theorem exists_coxeter_conjugating_torus (hG : IsSemisimple G) :
    ∃ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X,
      (coxeterNormalizer e m).val =
        (t ≫ p.inclusion.hom.hom) * (coxeterNormalizer e n).val *
          (t ≫ p.inclusion.hom.hom)⁻¹ := by
  obtain ⟨q, hq⟩ := exists_torus_mul_of_weylAction_eq
    (coxeterNormalizer e m) (coxeterNormalizer e n)
    (by rw [weylAction_coxeterNormalizer, weylAction_coxeterNormalizer])
  obtain ⟨t, ht⟩ := exists_comp_eq_coxeterTorusEnd e n hG q⁻¹
  have hc := comp_torusCommutatorEnd p.inclusion (coxeterNormalizer e n) t
  dsimp only [coxeterTorusEnd] at ht
  rw [← Category.assoc, ht, GrpObj.inv_comp, constantPoint_self] at hc
  have hq' : q ≫ p.inclusion.hom.hom =
      (t ≫ p.inclusion.hom.hom) * (coxeterNormalizer e n).val *
        (t ≫ p.inclusion.hom.hom)⁻¹ * (coxeterNormalizer e n).val⁻¹ := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv hc
  refine ⟨t, ?_⟩
  rw [hq, hq']
  group

/-- A cyclic comparison gauge exists for every supplied family over an algebraically closed
field, without restricting the representatives or the ordering. -/
theorem nonempty_cyclicTorusGauge (hG : IsSemisimple G) :
    Nonempty (p.CyclicTorusGauge e n m) := by
  obtain ⟨t, ht⟩ := exists_coxeter_conjugating_torus e n m hG
  exact nonempty_cyclicTorusGauge_of_conjugate e n m t ht

/-- A chosen actual cyclic comparison, whose existence was proved from semisimplicity. -/
def cyclicTorusGauge (hG : IsSemisimple G) : p.CyclicTorusGauge e n m :=
  Classical.choice (nonempty_cyclicTorusGauge e n m hG)

/-- Over an algebraically closed field, the canonical-quotient isomorphism property is
independent of the arbitrary supplied reflection representatives. -/
theorem isIso_quotient_iff_representatives (hG : IsSemisimple G)
    (x : p.NormalizedSimpleRootParametrizations) :
    IsIso (steinbergProduct e x m ≫ ClassFunctions.rho G) ↔
      IsIso (steinbergProduct e x n ≫ ClassFunctions.rho G) :=
  (cyclicTorusGauge e n m hG).isIso_quotient_iff x

end SplitPinning

end Langlands.GroupScheme
