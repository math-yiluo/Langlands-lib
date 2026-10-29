import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # Line bundles glued from unit cocycles -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Given an open cover `T` of a scheme `X` and units `g i j` on the overlaps
`T i ⊓ T j` satisfying the cocycle identity `g i j * g j k = g i k` on triple
overlaps, there is an actual line bundle `N` on `X` with the following property:
for every family of functions `a i` on `T i` that is compatible with the cocycle,
`a i = g i j * a j` on `T i ⊓ T j`, there is a global section `t` of `N` whose
generation open meets each `T i` exactly in the basic open of `a i`.
The intended witness is the bundle glued from `g`, with `t` the section whose
local expressions are the `a i`; only the generation-open property is asserted.
This proposition is a statement target, not a proof. -/
def CocycleLineBundleStatement : Prop :=
  ∀ (X : Scheme.{u}) (ι : Type u) (T : ι → X.Opens), (⨆ i, T i) = ⊤ →
    ∀ g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ,
      (∀ i j k : ι,
        X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ⊓ T k ≤ T i ⊓ T j)).op
            (g i j : Γ(X, T i ⊓ T j)) *
          X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            T i ⊓ T j ⊓ T k ≤ T j ⊓ T k)).op (g j k : Γ(X, T j ⊓ T k)) =
        X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            T i ⊓ T j ⊓ T k ≤ T i ⊓ T k)).op (g i k : Γ(X, T i ⊓ T k))) →
      ∃ N : LineBundle X, ∀ a : ∀ i : ι, Γ(X, T i),
        (∀ i j : ι,
          X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (a i) =
            (g i j : Γ(X, T i ⊓ T j)) *
              X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (a j)) →
        ∃ t : Langlands.SchemeModule.GlobalSections N.obj, ∀ i : ι,
          T i ⊓ Langlands.SchemeModule.trivializationOpen N.obj t = X.basicOpen (a i)

end Langlands.AlgebraicGeometry.Picard
