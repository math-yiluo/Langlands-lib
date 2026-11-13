import Langlands.GroupScheme.IntegralModel.SemilinearCoefficientDescent

/-! # Exact transitivity of actual model coefficient extension -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Descent

@[reassoc] private theorem map_fst {S T : Scheme.{u}} (c : T ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) :
    ((baseChange c).map f).hom.hom.left ≫ pullback.fst H.X.hom c =
      pullback.fst G.X.hom c ≫ f.hom.hom.left := pullback.lift_fst _ _ _

/-- Two successive coefficient-square comparisons equal the composite square
comparison, with the actual integral and generic tower comparisons. -/
theorem squareComparison_pasting {R A B K L P : Scheme.{u}}
    (p : A ⟶ R) (q : B ⟶ A) (r : B ⟶ R) (hpq : q ≫ p = r)
    (i : L ⟶ K) (j : P ⟶ L) (k : P ⟶ K) (hij : j ≫ i = k)
    (c : K ⟶ R) (d : L ⟶ A) (e : P ⟶ B)
    (hdi : d ≫ p = i ≫ c) (hej : e ≫ q = j ≫ d) (hek : e ≫ r = k ≫ c)
    (G : GroupScheme R) :
    (baseChange e).map (pullbackComparison p q r hpq G).hom ≫
        (squareComparison r e c k hek G).hom =
      (squareComparison q e d j hej ((baseChange p).obj G)).hom ≫
        (baseChange j).map (squareComparison p d c i hdi G).hom ≫
          (pullbackComparison i j k hij ((baseChange c).obj G)).hom := by
  apply hom_ext_pullback_tower c k G
  simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc]
  conv_lhs =>
    rw [squareComparison_hom_fst_fst r e c k hek G]
    erw [map_fst_assoc e (pullbackComparison p q r hpq G).hom (pullback.fst G.X.hom r)]
    rw [pullbackComparison_hom_fst]
  conv_rhs =>
    erw [pullbackComparison_hom_fst_assoc i j k hij ((baseChange c).obj G)
      (pullback.fst G.X.hom c)]
    erw [map_fst_assoc j (squareComparison p d c i hdi G).hom
      (pullback.fst ((baseChange c).obj G).X.hom i ≫ pullback.fst G.X.hom c)]
    rw [squareComparison_hom_fst_fst p d c i hdi G]
    erw [squareComparison_hom_fst_fst_assoc q e d j hej ((baseChange p).obj G)
      (pullback.fst G.X.hom p)]

end Langlands.GroupScheme.Descent

namespace Langlands.GroupScheme.IntegralModel
open Descent

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {A L : Type u} [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  {B P : Type u} [CommRing B] [IsDomain B] [Field P]
  [Algebra A B] [Algebra B P] [IsFractionRing B P]
  [Algebra L P] [Algebra A P] [IsScalarTower A B P] [IsScalarTower A L P]
  [Algebra R B] [IsScalarTower R A B]
  [Algebra K P] [IsScalarTower K L P]
  [Algebra R P] [IsScalarTower R B P] [IsScalarTower R K P]
  {G : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)

omit [IsDomain R] [IsFractionRing R K] [IsDomain A] [IsFractionRing A L]
  [IsDomain B] [IsFractionRing B P] in
/-- Scalar towers give the exact contravariant composite of coefficient spectrum maps. -/
theorem coefficientSpec_comp :
    Spec.algebraMap A B ≫ Spec.algebraMap R A = Spec.algebraMap R B := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (IsScalarTower.algebraMap_eq R A B).symm

/-- The generic tower comparison for successive model coefficient extension. -/
def coefficientTowerGenericIso :
    (GroupScheme.baseChange (Spec.algebraMap L P)).obj
      ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G) ≅
        (GroupScheme.baseChange (Spec.algebraMap K P)).obj G :=
  pullbackComparison (Spec.algebraMap K L) (Spec.algebraMap L P) (Spec.algebraMap K P)
    (coefficientSpec_comp (R := K) (A := L) (B := P)) G

/-- Successive actual coefficient extensions recover direct extension,
with the canonical generic tower isomorphism. -/
def baseChangeTowerIso :
    ((M.baseChange A L).baseChange B P).Iso (M.baseChange B P) (coefficientTowerGenericIso (G := G)) where
  iso := pullbackComparison (Spec.algebraMap R A) (Spec.algebraMap A B) (Spec.algebraMap R B)
    (coefficientSpec_comp (R := R) (A := A) (B := B)) M.group
  generic_comm := by
    change (GroupScheme.baseChange (Spec.algebraMap B P)).map
        (pullbackComparison (Spec.algebraMap R A) (Spec.algebraMap A B) (Spec.algebraMap R B)
          (coefficientSpec_comp (R := R) (A := A) (B := B)) M.group).hom ≫
        (M.baseChangeGenericIso B P).hom =
      ((M.baseChange A L).baseChangeGenericIso B P).hom ≫ (coefficientTowerGenericIso (G := G)).hom
    rw [baseChangeGenericIso_eq_square, baseChangeGenericIso_eq_square]
    simp only [baseChangeSquareIso, Iso.trans_hom, Functor.mapIso_hom]
    rw [show (M.baseChange A L).genericIso = M.baseChangeSquareIso A L from
      M.baseChangeGenericIso_eq_square A L]
    simp only [baseChangeSquareIso, baseChange, Iso.trans_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc, coefficientTowerGenericIso]
    rw [pullbackComparison_naturality (Spec.algebraMap K L) (Spec.algebraMap L P)
      (Spec.algebraMap K P) (coefficientSpec_comp (R := K) (A := L) (B := P)) M.genericIso.hom]
    have h := congrArg
      (fun f => f ≫ (GroupScheme.baseChange (Spec.algebraMap K P)).map M.genericIso.hom)
      (squareComparison_pasting (Spec.algebraMap R A) (Spec.algebraMap A B) (Spec.algebraMap R B)
        (coefficientSpec_comp (R := R) (A := A) (B := B))
        (Spec.algebraMap K L) (Spec.algebraMap L P) (Spec.algebraMap K P)
        (coefficientSpec_comp (R := K) (A := L) (B := P))
        (Spec.algebraMap R K) (Spec.algebraMap A L) (Spec.algebraMap B P)
        (solutionCoefficientSquare (R := R) (K := K) (A := A) (L := L))
        (solutionCoefficientSquare (R := A) (K := L) (A := B) (L := P))
        (solutionCoefficientSquare (R := R) (K := K) (A := B) (L := P)) M.group)
    simpa only [Category.assoc] using h

end Langlands.GroupScheme.IntegralModel
