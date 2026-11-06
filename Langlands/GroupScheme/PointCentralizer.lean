import Langlands.GroupScheme.StabilizerClosedSubgroup
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.CocharacterTransport
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.MaximalTorusParameterExistenceProof

/-! # The all-test centralizer of a section of a group scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- Conjugation of a group scheme on its own underlying scheme, as a scheme action. -/
@[instance_reducible]
def conjugationSchemeAction : SchemeAction G G.X :=
  schemeActionOfPointLaws (AutomorphicAction.conjugation (𝟙 G)).hom
    (fun g => (AutomorphicAction.conjugation (𝟙 G)).one_left g)
    (fun h h' g => (AutomorphicAction.conjugation (𝟙 G)).mul_left h h' g)

/-- The conjugation action is `h • g = h g h⁻¹` on every test scheme. -/
theorem conjugationSchemeAction_act {T : Over S} (h g : T ⟶ G.X) :
    (conjugationSchemeAction G).act h g = h * g * h⁻¹ := by
  have e := AutomorphicAction.conjugation_act (𝟙 G) h g
  simp only [Grp.id_hom_hom, Category.comp_id] at e
  exact e

/-- The all-test centralizer of a section `x` of `G` over the base: on a test scheme `T`, the
points of `G` commuting with the pullback of `x` to `T`. -/
def pointCentralizer (x : 𝟙_ (Over S) ⟶ G.X) : SubgroupFunctor G :=
  (conjugationSchemeAction G).stabilizer x

theorem mem_pointCentralizer (x : 𝟙_ (Over S) ⟶ G.X) {T : Over S} (c : T ⟶ G.X) :
    c ∈ (G.pointCentralizer x).carrier T ↔
      c * (toUnit T ≫ x) = (toUnit T ≫ x) * c := by
  rw [pointCentralizer, SchemeAction.mem_stabilizer, conjugationSchemeAction_act,
    mul_inv_eq_iff_eq_mul]

/-- Over a separated group scheme, the centralizer of a section is a closed subgroup scheme
on all tests. -/
theorem pointCentralizer_isClosedRepresentable [IsSeparated G.X.hom]
    (x : 𝟙_ (Over S) ⟶ G.X) : (G.pointCentralizer x).IsClosedRepresentable :=
  (conjugationSchemeAction G).stabilizer_isClosedRepresentable x

section BaseChange

variable {S' : Scheme.{u}} (b : S' ⟶ S)

/-- The pullback to a test scheme of the section of a base change corresponding to a point
over `S'` is that point restricted along the structure morphism. -/
theorem baseChangePointsEquiv_toUnit_comp_symm (y : Over.mk b ⟶ G.X) (T : Over S') :
    baseChangePointsEquiv b G T (toUnit T ≫ (baseChangeBasePointsEquiv b G).symm y) =
      Over.homMk (U := (Over.map b).obj T) (V := Over.mk b) T.hom (by simp) ≫ y := by
  have hy := (baseChangeBasePointsEquiv b G).apply_symm_apply y
  set y' := (baseChangeBasePointsEquiv b G).symm y
  apply Over.OverMorphism.ext
  have hl : y'.left ≫ pullback.fst G.X.hom b = y.left := by
    rw [← baseChangeBasePointsEquiv_left, hy]
  have ht : (toUnit T).left = T.hom := by simp
  rw [baseChangePointsEquiv_left, Over.comp_left, Over.comp_left, ← hl, ht]
  exact Category.assoc _ _ _

/-- Membership in the centralizer of the base-changed section, expressed through points of
the original group. -/
theorem mem_pointCentralizer_baseChange_iff (y : Over.mk b ⟶ G.X) {T : Over S'}
    (c : T ⟶ ((GroupScheme.baseChange b).obj G).X) :
    c ∈ (((GroupScheme.baseChange b).obj G).pointCentralizer
        ((baseChangeBasePointsEquiv b G).symm y)).carrier T ↔
      baseChangePointsEquiv b G T c *
          (Over.homMk (U := (Over.map b).obj T) (V := Over.mk b) T.hom (by simp) ≫ y) =
        (Over.homMk (U := (Over.map b).obj T) (V := Over.mk b) T.hom (by simp) ≫ y) *
          baseChangePointsEquiv b G T c := by
  rw [mem_pointCentralizer, ← baseChangePointsEquiv_toUnit_comp_symm,
    ← map_mul, ← map_mul]
  exact (baseChangePointsEquiv b G T).injective.eq_iff.symm

/-- Base change of the centralizer of a section over `S` is the centralizer of the pulled-back
section. -/
theorem pointCentralizer_baseChange (x : 𝟙_ (Over S) ⟶ G.X) :
    (G.pointCentralizer x).baseChange b =
      ((GroupScheme.baseChange b).obj G).pointCentralizer
        ((baseChangeBasePointsEquiv b G).symm (toUnit (Over.mk b) ≫ x)) := by
  ext T c
  rw [SubgroupFunctor.mem_baseChange, mem_pointCentralizer,
    mem_pointCentralizer_baseChange_iff, ← Category.assoc, toUnit_unique
      (Over.homMk (U := (Over.map b).obj T) (V := Over.mk b) T.hom (by simp) ≫
        toUnit (Over.mk b)) (toUnit _)]

/-- The base-changed point of a section, pulled back as a constant family, corresponds to the
original point restricted along the structure morphism. -/
theorem baseChangePointsEquiv_constantPoint_symm (y : Over.mk b ⟶ G.X) (T : Over S') :
    baseChangePointsEquiv b G T (((GroupScheme.baseChange b).obj G).constantPoint
        ((baseChangeBasePointsEquiv b G).symm y) T) =
      Over.homMk (U := (Over.map b).obj T) (V := Over.mk b) T.hom (by simp) ≫ y := by
  rw [← baseChangePointsEquiv_toUnit_comp_symm]
  unfold constantPoint
  rw [toUnit_unique (Over.homMk (U := T) (V := Over.mk (𝟙 S')) T.hom (by simp)) (toUnit T)]

end BaseChange

section Representative

variable {H : GroupScheme S} {j : H ⟶ G}

/-- A commutative subgroup containing a section and the centralizer of that section is equal
to the centralizer. -/
theorem range_eq_pointCentralizer [IsCommMonObj H.X] (x : 𝟙_ (Over S) ⟶ G.X)
    (h : G.pointCentralizer x ≤ SubgroupFunctor.range j) :
    SubgroupFunctor.range j = G.pointCentralizer x := by
  refine le_antisymm (fun T c hc => ?_) h
  obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hc
  have hx : toUnit T ≫ x ∈ (G.pointCentralizer x).carrier T := by
    rw [mem_pointCentralizer]
  obtain ⟨s₀, hs₀⟩ := SubgroupFunctor.mem_range.mp (h T hx)
  rw [mem_pointCentralizer, ← hs₀, ← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]

end Representative

section Conjugation

variable {S' S'' : Scheme.{u}} (b : S' ⟶ S) (c : S'' ⟶ S')

private theorem comp_iso_hom_comp_inv {G₁ G₂ : GroupScheme S''} (e : G₁ ≅ G₂) {V : Over S''}
    (w : V ⟶ G₁.X) : (w ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = w := by
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]

private theorem conj_comm_iff {T : Over S} (a y w : T ⟶ G.X) :
    (a * y * a⁻¹) * (a * w * a⁻¹) = (a * w * a⁻¹) * (a * y * a⁻¹) ↔ y * w = w * y := by
  have e₁ : (a * y * a⁻¹) * (a * w * a⁻¹) = a * (y * w) * a⁻¹ := by group
  have e₂ : (a * w * a⁻¹) * (a * y * a⁻¹) = a * (w * y) * a⁻¹ := by group
  rw [e₁, e₂, mul_left_inj, mul_right_inj]

/-- **Conjugation transports a represented centralizer.** Let `j` represent the centralizer
of a point `z` of `G` over `S'`, and let `g` be a point over `S''` conjugating the pullback
of a section `x` to the pullback of `z`. Then the base change of `j` to `S''`, followed by
the composite base-change comparison and conjugation by the inverse of `g`, represents the
base change of the centralizer of `x`. -/
theorem isRepresentedBy_pointCentralizer_baseChange_of_conj {x : 𝟙_ (Over S) ⟶ G.X}
    {z : Over.mk b ⟶ G.X} {H : GroupScheme S'} {j : H ⟶ (GroupScheme.baseChange b).obj G}
    (hj : (((GroupScheme.baseChange b).obj G).pointCentralizer
      ((baseChangeBasePointsEquiv b G).symm z)).IsRepresentedBy j)
    (g : Over.mk (c ≫ b) ⟶ G.X)
    (hg : g * (toUnit _ ≫ x) * g⁻¹ = Over.homMk (U := Over.mk (c ≫ b)) (V := Over.mk b) c ≫ z) :
    ((G.pointCentralizer x).baseChange (c ≫ b)).IsRepresentedBy
      (((GroupScheme.baseChange c).map j ≫ (baseChangeCompIso b c G).symm.hom) ≫
        (((GroupScheme.baseChange (c ≫ b)).obj G).innerIso
          ((baseChangeBasePointsEquiv (c ≫ b) G).symm g)⁻¹).hom) := by
  refine ⟨(((hj.baseChange c).comp_iso (baseChangeCompIso b c G).symm).comp_iso _).1, ?_⟩
  ext V y
  rw [MaximalTorusParameterExistence.mem_range_comp_innerIso_iff,
    MaximalTorusParameterExistence.mem_range_comp_iso_iff, SubgroupFunctor.range_baseChangeHom,
    hj.2, SubgroupFunctor.mem_baseChange, mem_pointCentralizer_baseChange_iff,
    SubgroupFunctor.mem_baseChange, mem_pointCentralizer, baseChangePointsEquiv_base_comp,
    Iso.symm_inv, comp_iso_hom_comp_inv, map_mul, map_mul, map_inv,
    ← map_inv (baseChangeBasePointsEquiv (c ≫ b) G).symm g,
    baseChangePointsEquiv_constantPoint_symm]
  set hV := Over.homMk (U := (Over.map (c ≫ b)).obj V) (V := Over.mk (c ≫ b)) V.hom (by simp)
  set m := (Over.mapComp c b).inv.app V
  have hm : Over.homMk (U := (Over.map b).obj ((Over.map c).obj V)) (V := Over.mk b)
      ((Over.map c).obj V).hom (by simp) =
      m ≫ hV ≫ Over.homMk (U := Over.mk (c ≫ b)) (V := Over.mk b) c := by
    apply Over.OverMorphism.ext
    simp [m, hV]
  have hz : Over.homMk (U := (Over.map b).obj ((Over.map c).obj V)) (V := Over.mk b)
      ((Over.map c).obj V).hom (by simp) ≫ z =
      m ≫ ((hV ≫ g) * (toUnit _ ≫ x) * (hV ≫ g)⁻¹) := by
    rw [hm, Category.assoc, Category.assoc, ← hg]
    congr 1
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc hV (toUnit _) x,
      toUnit_unique (hV ≫ toUnit _) (toUnit _)]
  rw [hz, GrpObj.comp_inv, inv_inv, ← MonObj.comp_mul, ← MonObj.comp_mul, cancel_epi,
    conj_comm_iff]

end Conjugation

end Langlands.GroupScheme
