import Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardNoetherianTestsStatement
import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over

/-! # Gluing a Zariski sheaf from quasi-projective open pieces on locally noetherian tests -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard

/-- Let `A` be a noetherian ring, `S = Spec A`, and `F` a Zariski sheaf on schemes over `S`.
Suppose that for every locally noetherian `S`-scheme `T` and every `ξ ∈ F(T)` there are opens
`V T ξ c m` of `T`, indexed by `c : κ` and `m : ℕ`, which are compatible with base change,
increase with `m`, are disjoint for distinct `c`, and cover `T`. Suppose also that each piece
`{ξ | V T ξ c m = T}` is represented on locally noetherian tests by an `S`-scheme `Q c m` that
admits an immersion into a finite projective space over `A`. Then some `S`-scheme `P`, locally
of finite presentation and with finite affine neighbourhoods, represents `F` on noetherian
affine tests. -/
def NoetherianOpenPiecesGluingStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
    (F : (Over (Spec (CommRingCat.of A)))ᵒᵖ ⥤ Type (u + 1)),
    Presheaf.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of A))) F →
    ∀ (κ : Type)
      (V : ∀ T : Over (Spec (CommRingCat.of A)), F.obj (op T) → κ → ℕ → T.left.Opens)
      (Q : κ → ℕ → Over (Spec (CommRingCat.of A)))
      (β : ∀ (c : κ) (m : ℕ), uliftYoneda.{u + 1}.obj (Q c m) ⟶ F),
      -- the opens are compatible with base change
      (∀ (T T' : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian T.left]
          [IsLocallyNoetherian T'.left] (h : T' ⟶ T) (ξ : F.obj (op T)) (c : κ) (m : ℕ),
          V T' (F.map h.op ξ) c m = h.left ⁻¹ᵁ V T ξ c m) →
      -- increasing in `m`, disjoint in `c`, covering
      (∀ (T : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian T.left] (ξ : F.obj (op T)),
          (∀ (c : κ) (m : ℕ), V T ξ c m ≤ V T ξ c (m + 1)) ∧
          (∀ (c c' : κ) (m m' : ℕ), c ≠ c' → Disjoint (V T ξ c m) (V T ξ c' m')) ∧
          (⨆ (c : κ) (m : ℕ), V T ξ c m) = ⊤) →
      -- each `Q c m` is quasi-projective over `A`
      (∀ (c : κ) (m : ℕ), ∃ (n : ℕ) (i : (Q c m).left ⟶ ProjectiveSpace A n),
          IsImmersion i ∧ i ≫ projectiveSpaceToSpec A n = (Q c m).hom) →
      -- `Q c m` represents the piece `{ξ | V T ξ c m = T}` on locally noetherian tests
      (∀ (c : κ) (m : ℕ) (T : Over (Spec (CommRingCat.of A))) [IsLocallyNoetherian T.left],
          Function.Injective ((β c m).app (op T)) ∧
            ∀ ξ : F.obj (op T), V T ξ c m = ⊤ ↔ ξ ∈ Set.range ((β c m).app (op T))) →
      ∃ P : Over (Spec (CommRingCat.of A)),
        LocallyOfFinitePresentation P.hom ∧
          PointTopology.HasFiniteAffineNeighborhoods P.left ∧
            Nonempty ((noetherianAffineOverι (Spec (CommRingCat.of A))).op ⋙
                yoneda.obj P ⋙ uliftFunctor.{u + 1} ≅
              (noetherianAffineOverι (Spec (CommRingCat.of A))).op ⋙ F)

end Langlands.AlgebraicGeometry.Picard
