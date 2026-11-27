import Langlands.Cohomology.AbelianScheme.RelativeMultiplicationStatement
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Relative étale Künneth isomorphisms for abelian schemes

The cohomological formula of Milne, *Étale Cohomology*, VI.8, Theorem 8.5,
for abelian schemes and constant prime-power coefficients, with naturality
for the actual relative pullbacks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Langlands.Geometry EtaleDerivedSections EtaleDerivedDirectImage

set_option autoImplicit false
set_option quotPrecheck false

universe wS wX

namespace Langlands.Cohomology.AbelianRelativeEtale

attribute [local instance] Abelian.hasFiniteBiproducts

variable {S : Scheme.{0}} (p r : ℕ)

local notation "R" => ZMod (p ^ r)
local notation "Mod" => ModuleCat.{0} R

/-- The tensor product of two small-étale module sheaves is the
sheafification of their sectionwise tensor product. -/
def etaleSheafTensor (F G : ModuleSheaf S R) : ModuleSheaf S R :=
  (presheafToSheaf S.smallEtaleTopology Mod).obj (F.obj ⊗ G.obj)

/-- The morphism on this tensor product induced by two small-étale
sheaf morphisms. -/
def etaleSheafTensorMap {F F' G G' : ModuleSheaf S R} (a : F ⟶ F') (b : G ⟶ G') :
    etaleSheafTensor p r F G ⟶ etaleSheafTensor p r F' G' :=
  (presheafToSheaf S.smallEtaleTopology Mod).map (a.hom ⊗ₘ b.hom)

/-- The relative étale cohomology with the constant regular module as coefficients. -/
def relativeCohomology (X : Over S) (q : ℕ) : ModuleSheaf S R :=
  (higherDirectImage X.hom R q).obj
    ((constantSheaf X.left.smallEtaleTopology Mod).obj (ModuleCat.of R R))

/-- Pullback on the actual relative cohomology sheaves. -/
def relativePullback {X Y : Over S} (f : X ⟶ Y) (q : ℕ)
    [baseDerived : HasDerivedCategory.{wS} (ModuleSheaf S R)]
    [totalDerived : ∀ Z : Scheme.{0}, HasDerivedCategory.{wX} (ModuleSheaf Z R)] :
    relativeCohomology p r Y q ⟶ relativeCohomology p r X q :=
  @relativeConstantCohomologyPullback.{0, wS, wX, wX} S Y.left X.left R _
    baseDerived (totalDerived Y.left) (totalDerived X.left) _ _ f.left f.w
    (ModuleCat.of R R) q

/-- The sum over all pairs of degrees adding to `q`, with sheaf tensor
products over the constant coefficient ring. -/
def kunnethSum (X Y : Over S) (q : ℕ) : ModuleSheaf S R :=
  ⨁ (fun i : Fin (q + 1) => etaleSheafTensor p r
    (relativeCohomology p r X i.val) (relativeCohomology p r Y (q - i.val)))

/-- The tensor product of the pullbacks in each summand. -/
def kunnethSumPullback {X X' Y Y' : Over S} (a : X ⟶ X') (b : Y ⟶ Y') (q : ℕ)
    [baseDerived : HasDerivedCategory.{wS} (ModuleSheaf S R)]
    [totalDerived : ∀ Z : Scheme.{0}, HasDerivedCategory.{wX} (ModuleSheaf Z R)] :
    kunnethSum p r X' Y' q ⟶ kunnethSum p r X Y q :=
  biproduct.map fun i : Fin (q + 1) =>
    etaleSheafTensorMap p r
      (relativePullback p r a i.val (baseDerived := baseDerived) (totalDerived := totalDerived))
      (relativePullback p r b (q - i.val)
        (baseDerived := baseDerived) (totalDerived := totalDerived))

/-- The relative étale Künneth isomorphisms for the fibre products of
abelian schemes with finite prime-power coefficients. One family of
isomorphisms is natural under morphisms over the base on both factors. -/
def RelativeEtaleKunnethStatement [CompactSpace S] [Fact p.Prime] (q : ℕ)
    [baseDerived : HasDerivedCategory.{wS} (ModuleSheaf S R)]
    [totalDerived : ∀ Z : Scheme.{0}, HasDerivedCategory.{wX} (ModuleSheaf Z R)] : Prop :=
  IsUnit (p : Γ(S, ⊤)) →
    ∃ Φ : ∀ A B : Langlands.AbelianScheme S,
      kunnethSum p r A.X B.X q ≅ relativeCohomology p r (A.X ⨯ B.X) q,
      ∀ (A A' B B' : Langlands.AbelianScheme S) (f : A.X ⟶ A'.X) (g : B.X ⟶ B'.X),
        kunnethSumPullback p r f g q (baseDerived := baseDerived) (totalDerived := totalDerived) ≫
            (Φ A B).hom =
          (Φ A' B').hom ≫ relativePullback p r (Limits.prod.map f g) q
            (baseDerived := baseDerived) (totalDerived := totalDerived)

end Langlands.Cohomology.AbelianRelativeEtale
