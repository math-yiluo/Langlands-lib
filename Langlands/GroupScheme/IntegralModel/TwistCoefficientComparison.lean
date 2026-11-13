import Langlands.GroupScheme.IntegralModel.SemilinearGenericSolution
import Langlands.GroupScheme.IntegralModel.SemilinearExtension

/-! # Coefficient pullback and semilinear twisting -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Descent

@[reassoc] private theorem cube_map_fst {S T : Scheme.{u}} (b : T ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) :
    ((baseChange b).map f).hom.hom.left ≫ pullback.fst H.X.hom b =
      pullback.fst G.X.hom b ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- The inverse square comparison preserves the same original projection. -/
@[reassoc] theorem squareComparison_inv_fst_fst {B S U V : Scheme.{u}}
    (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) (G : GroupScheme B) :
    (squareComparison b c d e h G).inv.hom.hom.left ≫
        pullback.fst ((baseChange b).obj G).X.hom c ≫ pullback.fst G.X.hom b =
      pullback.fst ((baseChange d).obj G).X.hom e ≫ pullback.fst G.X.hom d := by
  simp only [squareComparison, Iso.trans_inv, Iso.symm_inv, Grp.comp_hom_hom,
    Over.comp_left, Category.assoc, pullbackComparison_inv_fst,
    pullbackComparison_hom_fst]

/-- The square comparisons around a commuting coefficient cube agree. -/
theorem squareComparison_cube {B S U V : Scheme.{u}}
    (p : S ⟶ B) (c : U ⟶ B) (q : V ⟶ S) (r : V ⟶ U) (h : q ≫ p = r ≫ c)
    (a : B ⟶ B) (a' : S ⟶ S) (v : U ⟶ U) (v' : V ⟶ V)
    (ha : a' ≫ p = p ≫ a) (hv : v' ≫ r = r ≫ v)
    (hvc : v ≫ c = c ≫ a) (hvq : v' ≫ q = q ≫ a') (G : GroupScheme B) :
    (baseChange q).map (squareComparison p a' a p ha G).hom ≫
        (squareComparison p q c r h ((baseChange a).obj G)).hom ≫
          (baseChange r).map (squareComparison c v a c hvc G).inv =
      (squareComparison q v' a' q hvq ((baseChange p).obj G)).inv ≫
        (baseChange v').map (squareComparison p q c r h G).hom ≫
          (squareComparison r v' v r hv ((baseChange c).obj G)).hom := by
  apply (cancel_mono ((baseChange r).map
    (pullbackComparison c v (v ≫ c) rfl G).hom)).mp
  apply hom_ext_pullback_tower (v ≫ c) r G
  simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc]
  simp only [cube_map_fst_assoc, pullbackComparison_hom_fst]
  conv_lhs =>
    rw [squareComparison_inv_fst_fst c v a c hvc G]
    erw [squareComparison_hom_fst_fst_assoc p q c r h ((baseChange a).obj G)
      (pullback.fst G.X.hom a)]
    erw [cube_map_fst_assoc q (squareComparison p a' a p ha G).hom
      (pullback.fst ((baseChange a).obj G).X.hom p ≫ pullback.fst G.X.hom a)]
    rw [squareComparison_hom_fst_fst p a' a p ha G]
  conv_rhs =>
    erw [squareComparison_hom_fst_fst_assoc r v' v r hv ((baseChange c).obj G)
      (pullback.fst G.X.hom c)]
    erw [cube_map_fst_assoc v' (squareComparison p q c r h G).hom
      (pullback.fst ((baseChange c).obj G).X.hom r ≫ pullback.fst G.X.hom c)]
    rw [squareComparison_hom_fst_fst p q c r h G]
    erw [squareComparison_inv_fst_fst_assoc q v' a' q hvq ((baseChange p).obj G)
      (pullback.fst G.X.hom p)]

end Langlands.GroupScheme.Descent

namespace Langlands.GroupScheme.IntegralModel
open Descent

@[reassoc] private theorem map_fst {S T : Scheme.{u}} (b : T ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) :
    ((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.fst H.X.hom b =
      pullback.fst G.X.hom b ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} (N : IntegralModel R K G)
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

/-- The model coefficient comparison expressed using the public
commuting-square comparison. -/
def baseChangeSquareIso :
    (GroupScheme.baseChange (Spec.algebraMap A L)).obj
        ((GroupScheme.baseChange (Spec.algebraMap R A)).obj N.group) ≅
      (GroupScheme.baseChange (Spec.algebraMap K L)).obj G :=
  squareComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
      (Spec.algebraMap R K) (Spec.algebraMap K L)
      (solutionCoefficientSquare (R := R) (K := K) (A := A) (L := L)) N.group ≪≫
    (GroupScheme.baseChange (Spec.algebraMap K L)).mapIso N.genericIso

omit [IsDomain A] [IsFractionRing A L] in
/-- The published coefficient base change has exactly this public square
comparison, including its prescribed generic identification. -/
theorem baseChangeGenericIso_eq_square :
    N.baseChangeGenericIso A L = N.baseChangeSquareIso A L := by
  apply Iso.ext
  apply (cancel_mono ((GroupScheme.baseChange (Spec.algebraMap K L)).map N.genericIso.inv)).mp
  change (N.baseChangeGenericIso A L).hom ≫
      (GroupScheme.baseChange (Spec.algebraMap K L)).map N.genericIso.inv =
    ((squareComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
      (Spec.algebraMap R K) (Spec.algebraMap K L)
      (solutionCoefficientSquare (R := R) (K := K) (A := A) (L := L)) N.group).hom ≫
        (GroupScheme.baseChange (Spec.algebraMap K L)).map N.genericIso.hom) ≫
          (GroupScheme.baseChange (Spec.algebraMap K L)).map N.genericIso.inv
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, N.genericIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  apply hom_ext_pullback_tower (Spec.algebraMap R K) (Spec.algebraMap K L) N.group
  simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc]
  erw [map_fst_assoc (Spec.algebraMap K L) N.genericIso.inv
    (pullback.fst N.group.X.hom (Spec.algebraMap R K))]
  exact (N.baseChangeGenericIso_hom_fst A L).trans
    (squareComparison_hom_fst_fst _ _ _ _ _ N.group).symm

section Twist

variable
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
  (v : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
  (hvc : v ≫ Spec.algebraMap R K = Spec.algebraMap R K ≫ a)
  (a' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A))
  (v' : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L))
  (hvq : v' ≫ Spec.algebraMap A L = Spec.algebraMap A L ≫ a')
  (ha : a' ≫ Spec.algebraMap R A = Spec.algebraMap R A ≫ a)
  (hv : v' ≫ Spec.algebraMap K L = Spec.algebraMap K L ≫ v)

/-- Coefficient pullback commutes with actual coefficient twisting, through
the exact integral and generic commuting-square comparisons. -/
def twistBaseChangeIso :
    ((N.baseChange A L).twist a' v' hvq).Iso
      ((N.twist a v hvc).baseChange A L)
      (squareComparison (Spec.algebraMap K L) v' v (Spec.algebraMap K L) hv G) where
  iso := squareComparison (Spec.algebraMap R A) a' a (Spec.algebraMap R A) ha N.group
  generic_comm := by
    change (GroupScheme.baseChange (Spec.algebraMap A L)).map
        (squareComparison (Spec.algebraMap R A) a' a (Spec.algebraMap R A) ha N.group).hom ≫
          ((N.twist a v hvc).baseChangeGenericIso A L).hom = _
    rw [baseChangeGenericIso_eq_square]
    change _ =
      ((squareComparison (Spec.algebraMap A L) v' a' (Spec.algebraMap A L) hvq
        ((GroupScheme.baseChange (Spec.algebraMap R A)).obj N.group)).inv ≫
          (GroupScheme.baseChange v').map (N.baseChangeGenericIso A L).hom) ≫
            (squareComparison (Spec.algebraMap K L) v' v (Spec.algebraMap K L) hv G).hom
    rw [baseChangeGenericIso_eq_square]
    simp only [baseChangeSquareIso, twist, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rw [squareComparison_naturality (Spec.algebraMap K L) v' v
      (Spec.algebraMap K L) hv N.genericIso.hom]
    have hc := congrArg
      (fun f => f ≫ (GroupScheme.baseChange (Spec.algebraMap K L)).map
        ((GroupScheme.baseChange v).map N.genericIso.hom))
      (squareComparison_cube (Spec.algebraMap R A) (Spec.algebraMap R K)
        (Spec.algebraMap A L) (Spec.algebraMap K L)
        (solutionCoefficientSquare (R := R) (K := K) (A := A) (L := L))
        a a' v v' ha hv hvc hvq N.group)
    simpa only [Category.assoc] using hc

end Twist

end Langlands.GroupScheme.IntegralModel
