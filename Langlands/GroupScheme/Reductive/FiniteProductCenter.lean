import Langlands.GroupScheme.Reductive.ProductCenter
import Langlands.GroupScheme.Adjoint.GeometricBaseChange
import Langlands.GroupScheme.Reductive.AlmostSimple

/-! # Trivial centres of finite products and their factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G G' : GroupScheme S}

/-- An isomorphism reflects a trivial full centre over an arbitrary base. -/
theorem center_eq_bot_of_iso (e : G ≅ G') (h : center G' = ⊥) : center G = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  apply le_antisymm ?_ bot_le
  intro x hx
  have hx' := mem_center_comp_iso e hx
  rw [h, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx'
  have hm := congrArg (fun y => y ≫ e.inv.hom.hom) hx'
  change x = 1
  simpa only [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id,
    Grp.id_hom_hom, Category.comp_id, MonObj.one_comp] using hm

variable {I : Type u} [Finite I] (H : I → GroupScheme S)

/-- A point of the finite product is central on all test schemes exactly when
each of its actual coordinates is central on all test schemes. -/
theorem mem_center_pi_iff {T : Over S} (x : T ⟶ (pi H).X) :
    x ∈ (center (pi H)).carrier T ↔
      ∀ i, piPointsEquiv H T x i ∈ (center (H i)).carrier T := by
  classical
  constructor
  · intro hx i T' a y
    let v : ∀ j, T' ⟶ (H j).X := Pi.mulSingle i y
    have h := (hx T' a ((piPointsEquiv H T').symm v)).map (piPointsEquiv H T')
    have hi := congrArg (fun z => z i) h.eq
    have ha := congrFun (piPointsEquiv_naturality H a x) i
    change Commute (a ≫ piPointsEquiv H T x i) y
    apply (commute_iff_eq _ _).mpr
    simpa only [Pi.mul_apply, MulEquiv.apply_symm_apply, v,
      Pi.mulSingle_eq_same, ha] using hi
  · intro hx T' a y
    apply (commute_iff_eq _ _).mpr
    apply (piPointsEquiv H T').injective
    funext i
    have ha := congrFun (piPointsEquiv_naturality H a x) i
    simpa only [map_mul, Pi.mul_apply, ha] using
      (hx i T' a (piPointsEquiv H T' y i)).eq

/-- The full centre of a finite product, multiplicatively on every actual
relative test scheme. -/
def centerPiPointsEquiv (T : Over S) :
    (center (pi H)).carrier T ≃* (∀ i, (center (H i)).carrier T) where
  toFun x i := ⟨piPointsEquiv H T x.val i, (mem_center_pi_iff H x.val).mp x.property i⟩
  invFun x := ⟨(piPointsEquiv H T).symm (fun i => (x i).val), by
    apply (mem_center_pi_iff H _).mpr
    intro i
    simpa only [MulEquiv.apply_symm_apply] using (x i).property⟩
  left_inv x := by
    apply Subtype.ext
    exact (piPointsEquiv H T).symm_apply_apply x.val
  right_inv x := by
    funext i
    apply Subtype.ext
    exact congrFun ((piPointsEquiv H T).apply_symm_apply (fun j => (x j).val)) i
  map_mul' x y := by
    funext i
    apply Subtype.ext
    exact congrFun ((piPointsEquiv H T).map_mul x.val y.val) i

/-- The full centre of a finite product is trivial exactly when every
factor's full centre is trivial, over an arbitrary base scheme. -/
theorem center_pi_eq_bot_iff :
    center (pi H) = ⊥ ↔ ∀ i, center (H i) = ⊥ := by
  classical
  constructor
  · intro hc i
    apply SubgroupFunctor.ext
    intro T
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 1
    let v : ∀ j, T ⟶ (H j).X := Pi.mulSingle i x
    let y := (piPointsEquiv H T).symm v
    have hy : y ∈ (center (pi H)).carrier T := by
      apply (mem_center_pi_iff H y).mpr
      intro j
      rw [show piPointsEquiv H T y = v from (piPointsEquiv H T).apply_symm_apply v]
      by_cases hji : j = i
      · subst j
        simpa only [v, Pi.mulSingle_eq_same] using hx
      · have hv : v j = 1 :=
          Pi.mulSingle_eq_of_ne (M := fun j => T ⟶ (H j).X) hji x
        rw [hv]
        exact (center (H j)).carrier T |>.one_mem
    rw [hc, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hy
    have hi := congrArg (fun z => piPointsEquiv H T z i) hy
    simpa only [y, MulEquiv.apply_symm_apply, v, Pi.mulSingle_eq_same, map_one,
      Pi.one_apply] using hi
  · intro hc
    apply SubgroupFunctor.ext
    intro T
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 1
    apply (piPointsEquiv H T).injective
    funext i
    have hi := (mem_center_pi_iff H x).mp hx i
    rw [hc i, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hi
    simpa only [map_one, Pi.one_apply] using hi

/-- A factor of an actual product with trivial full centre also has trivial
full centre. -/
theorem center_factor_eq_bot_of_productIso
    (e : G ≅ pi H) (hc : center G = ⊥) (i : I) : center (H i) = ⊥ :=
  (center_pi_eq_bot_iff H).mp (center_eq_bot_of_iso e.symm hc) i

/-- Almost-simple geometric factors of a centre-free product have adjoint
geometric fibres. The centre condition concerns the original relative groups. -/
theorem isAdjoint_geometricFactor_of_productIso
    (e : G ≅ pi H) (hc : center G = ⊥)
    (hAS : ∀ i, ∀ s : S, IsAlmostSimple (geometricFiber (H i) s))
    (i : I) (s : S) : IsAdjoint (geometricFiber (H i) s) :=
  ⟨(hAS i s).isSemisimple,
    center_eq_bot_baseChange (geometricPoint S s)
      (center_factor_eq_bot_of_productIso H e hc i)⟩

end Langlands.GroupScheme
