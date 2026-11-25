import Langlands.GroupScheme.Rational.SteinbergRootFieldBaseChange
import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellUniversal
import Langlands.GroupScheme.Absolute.CocharacterDescentLattice

/-! # Base change of lines along a field extension

For a field extension `K / k` and a homomorphism `x : 𝔾ₐ ⟶ G` over `k`, `lineBaseChange K x`
is the homomorphism `𝔾ₐ ⟶ G_K` obtained by base change, with its source identified with `𝔾ₐ`
over `K`. Torus equivariance, the rank-one relation, monicity and commutation of lines pass to
the base change. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MaximalSplitSubgroup

open VectorGroup RootCell

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "bc" => algebraBaseMap k K

variable (K) in
/-- The base change of a line `x : 𝔾ₐ ⟶ G` along `Spec K ⟶ Spec k`, with its source identified
with `𝔾ₐ` over `K` by the published `VectorGroup.fieldBaseChangeIso`. -/
def lineBaseChange (x : Ga k ⟶ G) : Ga K ⟶ (GroupScheme.baseChange bc).obj G :=
  (VectorGroup.fieldBaseChangeIso k K 1).inv ≫ (GroupScheme.baseChange bc).map x

omit [Algebra k K] in
private theorem crd_scalarPoint_aux {Z : Over (Spec (CommRingCat.of k))} (c : Γ(Z.left, ⊤)) :
    crd (scalarPoint (CommRingCat.of k) Z c) = c :=
  coordinates_scalarPoint _ Z c 0

omit [Algebra k K] in
/-- Every point of `𝔾ₐ` is the scalar point of its coordinate. -/
theorem scalarPoint_crd {Z : Over (Spec (CommRingCat.of K))} (p : Z ⟶ (Ga K).X) :
    scalarPoint (CommRingCat.of K) Z (crd p) = p :=
  crd_injective (coordinates_scalarPoint _ Z _ 0)

/-- On points given by a scalar, the base-changed line is the original line. -/
theorem baseChangePointsEquiv_lineBaseChange (x : Ga k ⟶ G)
    (Z : Over (Spec (CommRingCat.of K))) (c : Γ(Z.left, ⊤)) :
    baseChangePointsEquiv bc G Z
        (scalarPoint (CommRingCat.of K) Z c ≫ (lineBaseChange K x).hom.hom) =
      scalarPoint (CommRingCat.of k) ((Over.map bc).obj Z) c ≫ x.hom.hom := by
  rw [lineBaseChange, Grp.comp_hom_hom, ← Category.assoc, baseChangePointsEquiv_comp,
    VectorGroup.baseChangePointsEquiv_scalarPoint_inv]

/-- On arbitrary points, the base-changed line is the original line at the same coordinate. -/
theorem baseChangePointsEquiv_comp_lineBaseChange (x : Ga k ⟶ G)
    {Z : Over (Spec (CommRingCat.of K))} (p : Z ⟶ (Ga K).X) :
    baseChangePointsEquiv bc G Z (p ≫ (lineBaseChange K x).hom.hom) =
      scalarPoint (CommRingCat.of k) ((Over.map bc).obj Z) (crd (k := K) p) ≫ x.hom.hom := by
  conv_lhs => rw [← scalarPoint_crd p]
  exact baseChangePointsEquiv_lineBaseChange x Z (crd (k := K) p)

/-- The base change of a monic line is monic. -/
theorem mono_lineBaseChange (x : Ga k ⟶ G) [Mono x.hom.hom] :
    Mono (lineBaseChange K x).hom.hom := by
  have : Mono ((GroupScheme.baseChange bc).map x).hom.hom := by
    change Mono ((Over.pullback bc).map x.hom.hom)
    infer_instance
  change Mono ((VectorGroup.fieldBaseChangeIso k K 1).inv.hom.hom ≫
    ((GroupScheme.baseChange bc).map x).hom.hom)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  infer_instance

/-- Torus equivariance passes to the base change, with the base-changed character. -/
theorem isTorusEquivariant_lineBaseChange {t : T.toGrp ⟶ G} {x : Ga k ⟶ G}
    {a : characterLattice T} (hx : IsTorusEquivariant t x a) :
    IsTorusEquivariant ((GroupScheme.baseChange bc).map t) (lineBaseChange K x)
      (characterLattice.baseChange bc T a) := by
  intro Z s c
  apply (baseChangePointsEquiv bc G Z).injective
  rw [map_mul, map_mul, map_inv, baseChangePointsEquiv_lineBaseChange,
    baseChangePointsEquiv_lineBaseChange, baseChangePointsEquiv_comp]
  rw [show VectorGroup.charValue (characterLattice.baseChange bc T a) Z s =
      VectorGroup.charValue a ((Over.map bc).obj Z) (baseChangePointsEquiv bc T.toGrp Z s) by
    exact congrArg Units.val (RelativeRoot.characterValue_baseChange bc a Z s)]
  exact hx ((Over.map bc).obj Z) (baseChangePointsEquiv bc T.toGrp Z s) c

/-- A unit point of `𝔾_m` over `K`, base changed back, is the same unit over `k`. -/
theorem baseChangePointsEquiv_gm (Z : Over (Spec (CommRingCat.of K))) (u : Γ(Z.left, ⊤)ˣ) :
    baseChangePointsEquiv bc (Gm (Spec (CommRingCat.of k))).toGrp Z
        ((Gm.pointsEquiv _ Z).symm u ≫ (Gm.baseChangeIso bc).inv.hom.hom) =
      (Gm.pointsEquiv _ ((Over.map bc).obj Z)).symm u := by
  apply (Gm.pointsEquiv _ _).injective
  rw [MulEquiv.apply_symm_apply, ← Gm.baseChangeUnitsEquiv_apply,
    Gm.baseChangeUnitsEquiv_baseChangeIso_inv, MulEquiv.apply_symm_apply]

/-- The cocharacter value at a unit, base changed back, is the original cocharacter value. -/
theorem baseChangePointsEquiv_cocharacter (t : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (Z : Over (Spec (CommRingCat.of K))) (u : Γ(Z.left, ⊤)ˣ) :
    baseChangePointsEquiv bc G Z
        ((Gm.pointsEquiv _ Z).symm u ≫
          (CommGroupScheme.groupHom (cocharacterLattice.baseChange bc T ν)).hom.hom ≫
            ((GroupScheme.baseChange bc).map t).hom.hom) =
      (Gm.pointsEquiv _ ((Over.map bc).obj Z)).symm u ≫
        (CommGroupScheme.groupHom ν).hom.hom ≫ t.hom.hom := by
  rw [cocharacterLattice.groupHom_baseChange, Grp.comp_hom_hom]
  simp only [← Category.assoc]
  rw [baseChangePointsEquiv_comp, baseChangePointsEquiv_comp, baseChangePointsEquiv_gm]

/-- The rank-one relation passes to the base change, with the base-changed cocharacter. -/
theorem relationOver_lineBaseChange {t : T.toGrp ⟶ G} {ν : cocharacterLattice T}
    {x y : Ga k ⟶ G} (h : ∀ Z, RelationOver t ν x y Z) (Z : Over (Spec (CommRingCat.of K))) :
    RelationOver ((GroupScheme.baseChange bc).map t) (cocharacterLattice.baseChange bc T ν)
      (lineBaseChange K x) (lineBaseChange K y) Z := by
  intro a b a' b' u hu ha hb
  unfold RelationAt
  apply (baseChangePointsEquiv bc G Z).injective
  rw [map_mul, map_mul, map_mul, baseChangePointsEquiv_comp_lineBaseChange,
    baseChangePointsEquiv_comp_lineBaseChange, baseChangePointsEquiv_comp_lineBaseChange,
    baseChangePointsEquiv_comp_lineBaseChange, baseChangePointsEquiv_cocharacter]
  have key := h ((Over.map bc).obj Z)
    (scalarPoint (CommRingCat.of k) ((Over.map bc).obj Z) (crd (k := K) a))
    (scalarPoint (CommRingCat.of k) ((Over.map bc).obj Z) (crd (k := K) b))
    (scalarPoint (CommRingCat.of k) ((Over.map bc).obj Z) (crd (k := K) a'))
    (scalarPoint (CommRingCat.of k) ((Over.map bc).obj Z) (crd (k := K) b')) u
    (by rw [crd_scalarPoint_aux, crd_scalarPoint_aux]; exact hu)
    (by rw [crd_scalarPoint_aux, crd_scalarPoint_aux]; exact ha)
    (by rw [crd_scalarPoint_aux, crd_scalarPoint_aux]; exact hb)
  exact key

/-- Lines whose points commute over `k` have base changes whose points commute over `K`. -/
theorem commute_lineBaseChange {x y : Ga k ⟶ G}
    (h : ∀ (Z : Over (Spec (CommRingCat.of k))) (c d : Γ(Z.left, ⊤)),
      Commute (scalarPoint (CommRingCat.of k) Z c ≫ x.hom.hom)
        (scalarPoint (CommRingCat.of k) Z d ≫ y.hom.hom))
    {Z : Over (Spec (CommRingCat.of K))} {g g' : Z ⟶ ((GroupScheme.baseChange bc).obj G).X}
    (hg : g ∈ (SubgroupFunctor.range (lineBaseChange K x)).carrier Z)
    (hg' : g' ∈ (SubgroupFunctor.range (lineBaseChange K y)).carrier Z) : Commute g g' := by
  obtain ⟨p, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  obtain ⟨q, rfl⟩ := SubgroupFunctor.mem_range.mp hg'
  apply (baseChangePointsEquiv bc G Z).injective
  rw [map_mul, map_mul, baseChangePointsEquiv_comp_lineBaseChange,
    baseChangePointsEquiv_comp_lineBaseChange]
  exact h _ _ _

/-- The base-changed line has the same range as the base change of the line. -/
theorem range_lineBaseChange (x : Ga k ⟶ G) :
    SubgroupFunctor.range (lineBaseChange K x) =
      SubgroupFunctor.range ((GroupScheme.baseChange bc).map x) :=
  SubgroupFunctor.range_iso_comp (VectorGroup.fieldBaseChangeIso k K 1).symm _

end Langlands.GroupScheme.MaximalSplitSubgroup
