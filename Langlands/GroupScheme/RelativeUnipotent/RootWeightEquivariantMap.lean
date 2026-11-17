import Langlands.GroupScheme.RelativeUnipotent.RootWeightPositiveIntrinsic
import Langlands.GroupScheme.Rational.AffineIntrinsicWeight
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Actual equivariant maps of positive root-weight filtrations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

open LocalSplitCell Corepresented Langlands.GroupTheory

section PositiveInclusion

variable {R : Type u} [CommRing R] {U : GroupScheme (Spec (CommRingCat.of R))}
  {C : RootHeightChart U} (W : RootWeightData C)

private theorem range_inclusion_le_zero (d : ℕ) :
    SubgroupFunctor.range (W.inclusion d) ≤ W.subgroup 0 := by
  rw [(W.isRepresentedBy_inclusion d).2]
  intro T x hx
  exact HeightFiltration.antitone_level (rootFactor C.roots ULift.up T)
    W.weight (Nat.succ_le_succ (Nat.zero_le d)) hx

/-- The actual inclusion of any weight term into the represented positive group. -/
def toPositive (d : ℕ) : W.groupScheme d ⟶ W.groupScheme 0 :=
  (W.isRepresentedBy_inclusion 0).factorHom (W.inclusion d) (W.range_inclusion_le_zero d)

/-- The positive inclusion retains the original ambient term inclusion. -/
theorem toPositive_comp (d : ℕ) : W.toPositive d ≫ W.inclusion 0 = W.inclusion d :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- An original term point, read inside the positive group, is in the restricted
term functor on every test. -/
theorem toPositive_mem (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (W.groupScheme d).X) :
    x ≫ (W.toPositive d).hom.hom ∈
      ((W.subgroup d).comap (W.inclusion 0)).carrier T := by
  rw [SubgroupFunctor.mem_comap, Category.assoc, ← Grp.comp_hom_hom, W.toPositive_comp]
  rw [← (W.isRepresentedBy_inclusion d).2]
  exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩

end PositiveInclusion

section Equivariant

variable {R : Type u} [CommRing R]
  {I J I' J' : Type u} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
  {U G U' G' : GroupScheme (Spec (CommRingCat.of R))}
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {t' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ G'}
  {ch : J → I → ℤ} {ch' : J' → I' → ℤ}
  {fam : J → (Ga R ⟶ G)} {fam' : J' → (Ga R ⟶ G')}
  {C : RootHeightChart U} {C' : RootHeightChart U'}
  (W : RootWeightData C) (W' : RootWeightData C')
  (j : U ⟶ G) (j' : U' ⟶ G') [Mono j.hom.hom] [Mono j'.hom.hom]
  {index : Fin C.dimension → J} {index' : Fin C'.dimension → J'}
  (hroot : ∀ k, C.roots (ULift.up k) ≫ j = fam (index k))
  (hroot' : ∀ k, C'.roots (ULift.up k) ≫ j' = fam' (index' k))
  (hu : TorusEquivariant t ch fam) (hu' : TorusEquivariant t' ch' fam')
  (v : I → ℤ) (v' : I' → ℤ)
  (f : W.groupScheme 0 ⟶ W'.groupScheme 0)
  (hf : TorusAction.IsEquivariant
    ((W.termPolynomialTorusAction j hroot hu 0).alongCocharacter v)
    ((W'.termPolynomialTorusAction j' hroot' hu' 0).alongCocharacter v')
    (affinePointsTransformation f))
  (q : ℕ) (hq : 0 < q)
  (hw : ∀ k, coPairing (ch (index k)) v = q * W.weight k)
  (hw' : ∀ k, coPairing (ch' (index' k)) v' = q * W'.weight k)

include hf hq hw hw' in
/-- Actual equivariance on coefficient algebras forces preservation of every
original unscaled filtration term on ALL scheme tests, allowing different tori,
root data, root charts and dimensions. -/
theorem map_mem_positiveTerm (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (W.groupScheme 0).X)
    (hx : x ∈ ((W.subgroup d).comap (W.inclusion 0)).carrier T) :
    x ≫ f.hom.hom ∈ ((W'.subgroup d).comap (W'.inclusion 0)).carrier T := by
  rw [← W.positiveIntrinsicCutoff_eq_comap j hroot hu v q hq hw d] at hx
  have h := AffineCorepresentation.map_mem_intrinsicWeightSubgroup
    (W.termChart 0) (W'.termChart 0) f
    ((W.termPolynomialTorusAction j hroot hu 0).alongCocharacter v)
    ((W'.termPolynomialTorusAction j' hroot' hu' 0).alongCocharacter v')
    hf (cyclicTail (fun _ : PUnit => (1 : ℤ)) (q * (d + 1))) hx
  change x ≫ f.hom.hom ∈
    (W'.positiveIntrinsicCutoff j' hroot' hu' v' (q * (d + 1))).carrier T at h
  rw [W'.positiveIntrinsicCutoff_eq_comap j' hroot' hu' v' q hq hw' d] at h
  exact h

include hf hq hw hw' in
private theorem range_toPositive_map_le (d : ℕ) :
    SubgroupFunctor.range (W.toPositive d ≫ f ≫ W'.inclusion 0) ≤ W'.subgroup d := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have h := map_mem_positiveTerm W W' j j' hroot hroot' hu hu' v v' f hf q hq hw hw'
    d T (y ≫ (W.toPositive d).hom.hom) (W.toPositive_mem d T y)
  exact h

/-- The actual induced homomorphism on every represented filtration term. No
termwise map or equality is supplied as a premise. -/
def equivariantTermMap (d : ℕ) : W.groupScheme d ⟶ W'.groupScheme d :=
  (W'.isRepresentedBy_inclusion d).factorHom
    (W.toPositive d ≫ f ≫ W'.inclusion 0)
      (range_toPositive_map_le W W' j j' hroot hroot' hu hu' v v' f hf q hq hw hw' d)

/-- The induced term map preserves the actual maps into the target chart group. -/
theorem equivariantTermMap_comp (d : ℕ) :
    equivariantTermMap W W' j j' hroot hroot' hu hu' v v' f hf q hq hw hw' d ≫
      W'.inclusion d = W.toPositive d ≫ f ≫ W'.inclusion 0 :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

end Equivariant

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData
