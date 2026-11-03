import Langlands.GroupScheme.Dynamic.LeviParabolicDefinitions
import Langlands.GroupScheme.Dynamic.Uniqueness
import Langlands.GroupScheme.Reductive.Basic

/-! # Inverse image and exact extension for a represented dynamic centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section Generic

variable {S : Scheme.{u}} {G L : GroupScheme S}
  (χ : (Gm S).toGrp ⟶ G) (j : L ⟶ G)
  (hj : (centralizer χ).IsRepresentedBy j)

/-- The ambient unipotent functor lies in every extension. -/
theorem unipotent_le_extendFromCentralizer (F : SubgroupFunctor L) :
    unipotent χ ≤ extendFromCentralizer χ j hj F := fun T n hn =>
  (mem_extendFromCentralizer χ j hj F T n).2
    ⟨1, (F.carrier T).one_mem, n, hn, by rw [MonObj.one_comp, one_mul]⟩

/-- The image of `F` lies in its extension. -/
theorem map_le_extendFromCentralizer (F : SubgroupFunctor L) :
    F.map j ≤ extendFromCentralizer χ j hj F := by
  rintro T _ ⟨l, hl, rfl⟩
  exact (mem_extendFromCentralizer χ j hj F T _).2
    ⟨l, hl, 1, ((unipotent χ).carrier T).one_mem, mul_one _⟩

variable [IsSeparated G.X.hom]

/-- Over a separated group scheme, the inverse image of the exact extension
`j(F) U(χ)` along the represented centralizer is `F` again. -/
theorem comap_extendFromCentralizer (F : SubgroupFunctor L) :
    (extendFromCentralizer χ j hj F).comap j = F := by
  have : Mono j.hom.hom := hj.1
  refine SubgroupFunctor.ext fun T => Subgroup.ext fun x => ?_
  rw [SubgroupFunctor.mem_comap, mem_extendFromCentralizer]
  constructor
  · rintro ⟨l, hl, n, hn, h⟩
    have hn' : (l⁻¹ * x) ≫ j.hom.hom = n := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, ← h, inv_mul_cancel_left]
    have hz : n ∈ (centralizer χ).carrier T := by
      rw [← hj.2]
      exact ⟨_, hn'⟩
    have h1 : n = 1 := eq_one_of_mem_centralizer_of_mem_unipotent χ
      (fun _ _ _ _ hl hl' => hl.unique χ hl') hz hn
    rw [h1, mul_one] at h
    rw [← (cancel_mono j.hom.hom).mp h]
    exact hl
  · intro hx
    exact ⟨x, hx, 1, ((unipotent χ).carrier T).one_mem, mul_one _⟩

/-- Over a separated group scheme, a subgroup functor between `U(χ)` and
`P(χ)` is the exact extension of its inverse image along the represented
centralizer. -/
theorem extendFromCentralizer_comap {Q : SubgroupFunctor G}
    (hUQ : unipotent χ ≤ Q) (hQP : Q ≤ parabolic χ) :
    extendFromCentralizer χ j hj (Q.comap j) = Q := by
  refine le_antisymm ?_ ?_
  · refine SubgroupFunctor.normalizedProduct_le _ ?_ hUQ
    rw [SubgroupFunctor.map_comap]
    exact fun _ _ hx => hx.2
  · intro T q hq
    obtain ⟨l, hl⟩ := exists_hasLimit χ (hQP T hq)
    have hz : l ∈ (centralizer χ).carrier T := hl.mem_centralizer χ
    have hn : l⁻¹ * q ∈ (unipotent χ).carrier T := by
      have h := (hasLimit_of_mem_centralizer χ hz).inv.mul χ hl
      rwa [inv_mul_cancel] at h
    rw [← hj.2] at hz
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hz
    refine (mem_extendFromCentralizer χ j hj _ T q).2
      ⟨y, ?_, _, hn, mul_inv_cancel_left _ _⟩
    rw [SubgroupFunctor.mem_comap]
    have h := (Q.carrier T).mul_mem hq ((Q.carrier T).inv_mem (hUQ T hn))
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h

/-- Over a separated group scheme, exact extension reflects inclusion. -/
theorem extendFromCentralizer_le_iff {F F' : SubgroupFunctor L} :
    extendFromCentralizer χ j hj F ≤ extendFromCentralizer χ j hj F' ↔ F ≤ F' := by
  refine ⟨fun h => ?_, extendFromCentralizer_mono χ j hj⟩
  rw [← comap_extendFromCentralizer χ j hj F, ← comap_extendFromCentralizer χ j hj F']
  exact SubgroupFunctor.comap_mono h

end Generic

section Field

variable {k : Type u} [Field k] {G L : GroupScheme (Spec (CommRingCat.of k))}
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : L ⟶ G)
  (hj : (centralizer χ).IsRepresentedBy j) [IsSeparated G.X.hom]

/-- Over a field and a separated group scheme, assume that exact extension sends
actual parabolics of `L` to actual parabolics of `G`, and that every actual
parabolic of `G` below `P(χ)` is the exact extension of an actual parabolic of
`L`. Then exact extension is an order isomorphism, with inverse image along `j`
as its inverse. -/
def extendFromCentralizerOrderIso
    (hfwd : ∀ F : SubgroupFunctor L, IsParabolicFunctor F →
      IsParabolicFunctor (extendFromCentralizer χ j hj F))
    (hsurj : ∀ Q : SubgroupFunctor G, IsParabolicFunctor Q → Q ≤ parabolic χ →
      ∃ F : SubgroupFunctor L, IsParabolicFunctor F ∧ extendFromCentralizer χ j hj F = Q) :
    ParabolicFunctor L ≃o ParabolicFunctorBelow (parabolic χ) where
  toFun F := ⟨extendFromCentralizer χ j hj F.val, hfwd F.val F.2,
    extendFromCentralizer_le_parabolic χ j hj F.val⟩
  invFun Q := ⟨Q.val.comap j, by
    obtain ⟨F, hF, hFQ⟩ := hsurj Q.val Q.2.1 Q.2.2
    rw [← hFQ, comap_extendFromCentralizer]
    exact hF⟩
  left_inv F := Subtype.ext (comap_extendFromCentralizer χ j hj F.val)
  right_inv Q := Subtype.ext (by
    obtain ⟨F, -, hFQ⟩ := hsurj Q.val Q.2.1 Q.2.2
    change extendFromCentralizer χ j hj (Q.val.comap j) = Q.val
    rw [← hFQ, comap_extendFromCentralizer])
  map_rel_iff' := extendFromCentralizer_le_iff χ j hj

variable {χ j hj}

@[simp] theorem extendFromCentralizerOrderIso_apply_coe
    {hfwd : ∀ F : SubgroupFunctor L, IsParabolicFunctor F →
      IsParabolicFunctor (extendFromCentralizer χ j hj F)}
    {hsurj : ∀ Q : SubgroupFunctor G, IsParabolicFunctor Q → Q ≤ parabolic χ →
      ∃ F : SubgroupFunctor L, IsParabolicFunctor F ∧ extendFromCentralizer χ j hj F = Q}
    (F : ParabolicFunctor L) :
    (extendFromCentralizerOrderIso χ j hj hfwd hsurj F).val =
      extendFromCentralizer χ j hj F.val :=
  rfl

@[simp] theorem extendFromCentralizerOrderIso_symm_apply_coe
    {hfwd : ∀ F : SubgroupFunctor L, IsParabolicFunctor F →
      IsParabolicFunctor (extendFromCentralizer χ j hj F)}
    {hsurj : ∀ Q : SubgroupFunctor G, IsParabolicFunctor Q → Q ≤ parabolic χ →
      ∃ F : SubgroupFunctor L, IsParabolicFunctor F ∧ extendFromCentralizer χ j hj F = Q}
    (Q : ParabolicFunctorBelow (parabolic χ)) :
    ((extendFromCentralizerOrderIso χ j hj hfwd hsurj).symm Q).val = Q.val.comap j :=
  rfl

end Field

/-- Conditional assembly of the parabolic correspondence for a connected
reductive group over a field, in the exact form of the body of
`DynamicLeviParabolicCorrespondenceStatement`. -/
theorem exists_parabolicFunctor_orderIso_of_forward_of_surjective
    {k : Type u} [Field k] {G L : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (j : L ⟶ G) (hj : (centralizer χ).IsRepresentedBy j)
    (hfwd : ∀ F : SubgroupFunctor L, IsParabolicFunctor F →
      IsParabolicFunctor (extendFromCentralizer χ j hj F))
    (hsurj : ∀ Q : SubgroupFunctor G, IsParabolicFunctor Q → Q ≤ parabolic χ →
      ∃ F : SubgroupFunctor L, IsParabolicFunctor F ∧ extendFromCentralizer χ j hj F = Q) :
    ∃ e : ParabolicFunctor L ≃o ParabolicFunctorBelow (parabolic χ),
      (∀ F : ParabolicFunctor L, (e F).val = extendFromCentralizer χ j hj F.val) ∧
      (∀ Q : ParabolicFunctorBelow (parabolic χ), (e.symm Q).val = Q.val.comap j) := by
  have := hG.isAffineHom
  exact ⟨extendFromCentralizerOrderIso χ j hj hfwd hsurj, fun _ => rfl, fun _ => rfl⟩

end Langlands.GroupScheme.Dynamic
