import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.TorsorCocycle
import Langlands.Galois.Local.SeparableInertiaDefinitions
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-! # Splitting of simply connected cocycles by finite unramified extensions -/

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every actual cocycle of a semisimple simply connected group over a nonarchimedean local
field `F`, on a finite Galois field cover `Spec M`, becomes trivial over some finite unramified
extension `E` of `F`. The base change of the cover to `Spec E` is the fibre product
`Spec M ⊗ Spec E` over `Spec F`, and triviality there is tested on pairs of points with the
same image in `Spec E`. -/
def LocalSimplyConnectedUnramifiedSplittingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom],
    IsSimplyConnected G →
    ∀ (M : Type u) [Field M] [Algebra F M] [FiniteDimensional F M] [IsGalois F M]
      (ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F M))))),
      ∃ E : IntermediateField F (SeparableClosure F),
        FiniteDimensional F E ∧ E ≤ LocalGalois.Separable.inertiaFixedField F ∧
          ∃ g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F M))) ⊗
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E))) ⟶ G.X,
            ∀ {Z : Over (Spec (CommRingCat.of F))}
              (a b : Z ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F M))) ⊗
                Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E)))),
              a ≫ snd _ _ = b ≫ snd _ _ →
                ξ.toFun (a ≫ fst _ _) (b ≫ fst _ _) = (a ≫ g) * (b ≫ g)⁻¹

end Langlands.GroupScheme
