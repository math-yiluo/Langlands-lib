import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.SubgroupFunctor.FppfProductGeometry

/-! # Fixed vectors of represented fppf-local products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G H U P : GroupScheme (Spec R)}
variable {n : Type} [Fintype n] [DecidableEq n]

/-- The fixed-vector equation on one specified relative scheme point. -/
def IsFixedAt (ρ : MatrixRepresentation G n) {T : Over (Spec R)}
    (x : T ⟶ G.X) (v : n → R) : Prop :=
  (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ
    (fun i => scalarMap T (v i)) = fun i => scalarMap T (v i)

/-- An epimorphic scheme test detects the all-test fixed-vector equation. -/
theorem isFixedVector_iff_epi_point (ρ : MatrixRepresentation G n)
    {T : Over (Spec R)} (x : T ⟶ G.X) [Epi x.left] (v : n → R) :
    ρ.IsFixedVector v ↔ ρ.IsFixedAt x v := by
  constructor
  · exact fun h => h T x
  · intro h
    apply (ρ.isFixedVector_iff_universal v).2
    funext i
    apply Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi x.left
    have hi := congrFun h i
    have hmat := ρ.pointMatrix_naturality x (𝟙 G.X)
    rw [Category.comp_id] at hmat
    rw [hmat] at hi
    change (((ρ.pointMatrix G.X (𝟙 G.X) : Matrix n n Γ(G.X.left, ⊤)).map
      x.left.appTop.hom) *ᵥ (fun j => scalarMap T (v j))) i = _ at hi
    rw [x.left.appTop.hom.map_mulVec]
    simpa only [Function.comp_def, scalarMap_naturality] using hi

/-- A represented fppf-local product fixes every vector fixed by both factors. -/
theorem isFixedVector_restrict_fppfProduct (ρ : MatrixRepresentation G n)
    {F N : SubgroupFunctor G} {i : P ⟶ G} {j : H ⟶ G} {l : U ⟶ G}
    (hi : SubgroupFunctor.IsFppfProduct F N i)
    (hH : F.IsRepresentedBy j) (hU : N.IsRepresentedBy l)
    (v : n → R) (hfixH : (ρ.restrict j).IsFixedVector v)
    (hfixU : (ρ.restrict l).IsFixedVector v) :
    (ρ.restrict i).IsFixedVector v := by
  let m := hi.productMul hH hU
  let : Epi m.left := hi.epi_productMul hH hU
  apply ((ρ.restrict i).isFixedVector_iff_epi_point m v).2
  rw [IsFixedAt, pointMatrix_restrict, hi.productMul_comp hH hU, map_mul,
    Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
  rw [← pointMatrix_restrict ρ l, hfixU (H.X ⊗ U.X) (snd H.X U.X)]
  exact hfixH (H.X ⊗ U.X) (fst H.X U.X)

end Langlands.GroupScheme.MatrixRepresentation
