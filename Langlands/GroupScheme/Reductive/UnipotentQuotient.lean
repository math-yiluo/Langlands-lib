import Langlands.GroupScheme.Reductive.Basic
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.FunctionDescent

/-! # Fixed vectors and unipotence descend along scheme epimorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

section Coefficients

variable {R : CommRingCat.{u}}

/-- The actual structure-ring maps commute with pullback along every test map. -/
theorem scalarMap_naturality {T W : Over (Spec R)} (a : W ⟶ T) (c : R) :
    a.left.appTop (scalarMap T c) = scalarMap W c := by
  change a.left.appTop (T.hom.appTop ((Scheme.ΓSpecIso R).inv c)) =
    W.hom.appTop ((Scheme.ΓSpecIso R).inv c)
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Over.w a]

namespace MatrixRepresentation

variable {G H : GroupScheme (Spec R)} {n : Type} [Fintype n] [DecidableEq n]

/-- One universal-point equation tests fixedness on every scheme. -/
theorem isFixedVector_iff_universal (ρ : MatrixRepresentation G n) (v : n → R) :
    ρ.IsFixedVector v ↔
      (ρ.pointMatrix G.X (𝟙 G.X) : Matrix n n Γ(G.X.left, ⊤)) *ᵥ
        (fun i => scalarMap G.X (v i)) = fun i => scalarMap G.X (v i) := by
  constructor
  · exact fun h => h G.X (𝟙 G.X)
  · intro h T g
    have hmat := ρ.pointMatrix_naturality g (𝟙 G.X)
    rw [Category.comp_id] at hmat
    rw [hmat]
    funext i
    have hi := congrArg (fun w => g.left.appTop.hom (w i)) h
    rw [g.left.appTop.hom.map_mulVec] at hi
    change (((ρ.pointMatrix G.X (𝟙 G.X) : Matrix n n Γ(G.X.left, ⊤)).map
      g.left.appTop.hom) *ᵥ (fun j => scalarMap T (v j))) i = _
    simpa only [Function.comp_def, scalarMap_naturality] using hi

/-- Restricting to a scheme-epimorphic source changes no fixed-vector equation. -/
theorem isFixedVector_restrict_iff (ρ : MatrixRepresentation G n) (q : H ⟶ G)
    [Epi q.hom.hom.left] (v : n → R) :
    (ρ.restrict q).IsFixedVector v ↔ ρ.IsFixedVector v := by
  constructor
  · intro h
    apply (ρ.isFixedVector_iff_universal v).2
    funext i
    apply Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi q.hom.hom.left
    have hi := congrFun (h H.X (𝟙 H.X)) i
    rw [pointMatrix_restrict, Category.id_comp] at hi
    have hmat := ρ.pointMatrix_naturality q.hom.hom (𝟙 G.X)
    rw [Category.comp_id] at hmat
    rw [hmat] at hi
    change (((ρ.pointMatrix G.X (𝟙 G.X) : Matrix n n Γ(G.X.left, ⊤)).map
      q.hom.hom.left.appTop.hom) *ᵥ (fun j => scalarMap H.X (v j))) i = _ at hi
    rw [q.hom.hom.left.appTop.hom.map_mulVec]
    simpa only [Function.comp_def, scalarMap_naturality] using hi
  · intro h T x
    rw [pointMatrix_restrict]
    exact h T (x ≫ q.hom.hom)

/-- The fixed submodules before and after scheme-epimorphic restriction coincide. -/
theorem fixedSubmodule_restrict_eq (ρ : MatrixRepresentation G n) (q : H ⟶ G)
    [Epi q.hom.hom.left] : (ρ.restrict q).fixedSubmodule = ρ.fixedSubmodule := by
  ext v
  exact ρ.isFixedVector_restrict_iff q v

/-- Identity on coordinate vectors identifies the fixed modules under restriction. -/
def fixedSubmoduleRestrictEquiv (ρ : MatrixRepresentation G n) (q : H ⟶ G)
    [Epi q.hom.hom.left] :
    (ρ.restrict q).fixedSubmodule ≃ₗ[R] ρ.fixedSubmodule where
  toFun v := ⟨v.val, (ρ.isFixedVector_restrict_iff q v.val).1 v.property⟩
  invFun v := ⟨v.val, (ρ.isFixedVector_restrict_iff q v.val).2 v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end MatrixRepresentation

end Coefficients

section Unipotence

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual finite-representation definition of unipotence descends along
any group homomorphism whose underlying scheme map is epimorphic. -/
theorem IsUnipotent.of_epi (hH : IsUnipotent H) (q : H ⟶ G)
    [Epi q.hom.hom.left] : IsUnipotent G := by
  intro n hn hd hne ρ
  obtain ⟨v, hv, hfix⟩ := hH n (ρ.restrict q)
  exact ⟨v, hv, (ρ.isFixedVector_restrict_iff q v).1 hfix⟩

/-- In particular, flat surjective homomorphisms preserve unipotence. -/
theorem IsUnipotent.of_flat_surjective (hH : IsUnipotent H) (q : H ⟶ G)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] : IsUnipotent G := by
  let := Flat.epi_of_flat_of_surjective q.hom.hom.left
  exact hH.of_epi q

end Unipotence

end Langlands.GroupScheme
