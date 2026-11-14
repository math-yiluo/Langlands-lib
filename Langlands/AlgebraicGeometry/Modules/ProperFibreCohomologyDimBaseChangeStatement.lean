import Langlands.AlgebraicGeometry.Modules.ProperFlatFibreCohomologySemicontinuityStatement

/-! # Invariance of fibre cohomology dimensions under base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- Let `g : Y ⟶ T` be proper and `F` an invertible module on `Y`. Let
```
Y' --h'--> Y
|g'        |g
v          v
T' --h---> T
```
be a cartesian square. Then for every point `t'` of `T'` and every `p`, the fibre cohomology
spaces `Hᵖ(Y'_{t'}, (h'^* F)_{t'})` over `κ(t')` and `Hᵖ(Y_{h t'}, F_{h t'})` over `κ(h t')` have
the same dimension. -/
def ProperFibreCohomologyDimBaseChangeStatement : Prop :=
  ∀ (T T' Y Y' : Scheme.{u}) (g : Y ⟶ T) (h : T' ⟶ T) (g' : Y' ⟶ T') (h' : Y' ⟶ Y),
    IsPullback h' g' g h → IsProper g →
    ∀ F : Y.Modules, Scheme.Modules.IsInvertible F → ∀ (t' : T') (p : ℕ),
      fibreCohomologyDim g' t' ((Scheme.Modules.pullback h').obj F) p =
        fibreCohomologyDim g (h t') F p

end Langlands.AlgebraicGeometry.Modules
