import Langlands.GroupScheme.Rational.SteinbergRootProduct

/-! # Closed immersion target for products with independent torus weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IndependentWeightProduct

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} {r : ℕ}
    (y : Fin r → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))

/-- Ordered multiplication of the supplied additive factors, evaluated at global functions. -/
def point (T : Over (Spec (CommRingCat.of k))) (c : Fin r → Γ(T.left, ⊤)) : T ⟶ G.X :=
  (List.ofFn fun i => VectorGroup.scalarPoint (CommRingCat.of k) T (c i) ≫
    (y i).hom.hom).prod

/-- The actual ordered morphism from standard affine space. -/
def morphism : (VectorGroup.groupScheme (CommRingCat.of k) r).X ⟶ G.X :=
  point y _ (VectorGroup.coordinateSection (CommRingCat.of k) r)

private theorem comp_list_prod {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T)
    (l : List (T ⟶ G.X)) :
    f ≫ l.prod = (l.map (fun g => f ≫ g)).prod := by
  induction l with
  | nil => simp
  | cons g l ih => simp only [List.prod_cons, List.map_cons, MonObj.comp_mul, ih]

/-- Pulling back the ordered formula pulls back each coordinate. -/
theorem point_comp {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T)
    (c : Fin r → Γ(T.left, ⊤)) :
    f ≫ point y T c = point y W (fun i => f.left.appTop (c i)) := by
  simp only [point, comp_list_prod, List.map_ofFn, Function.comp_def,
    ← Category.assoc, VectorGroup.scalarPoint_comp]

/-- Evaluation of the actual morphism on every scheme test. -/
theorem comp_morphism {T : Over (Spec (CommRingCat.of k))}
    (c : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) r).X) :
    c ≫ morphism y = point y T
      (fun i => (VectorGroup.coordinates (CommRingCat.of k) r T c).toAdd i) := by
  rw [morphism, point_comp]
  simp only [VectorGroup.coordinates_apply]

end IndependentWeightProduct

/-- An ordered product of closed additive embeddings of independent weights for
an actual split-torus action is a closed immersion of schemes. -/
def IndependentWeightProductImmersionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus S.toGrp →
    ∀ (b : AutomorphicAction S.toGrp G) (r : ℕ)
      (y : Fin r → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))
      (w : Fin r → characterLattice S),
      LinearIndependent ℤ w →
      (∀ i, IsClosedSubgroup (y i)) →
      (∀ (i : Fin r) (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
        (c : Γ(T.left, ⊤)),
        b.act s (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ (y i).hom.hom) =
          VectorGroup.scalarPoint (CommRingCat.of k) T
            (VectorGroup.charValue (w i) T s * c) ≫ (y i).hom.hom) →
      IsClosedImmersion (IndependentWeightProduct.morphism y).left

end Langlands.GroupScheme
