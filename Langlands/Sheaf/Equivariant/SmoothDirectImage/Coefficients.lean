import Langlands.Sheaf.Equivariant.SmoothDirectImage
import Langlands.Sheaf.Equivariant.LocallyConstantSmooth

/-! # Full smooth coefficient sheaves under spatial direct image -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.SmoothDirectImage

open CategoryTheory Opposite

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]
  [HasStableNeighbourhoods G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- The full coefficient pullback factors through the actual smooth direct image
by its universal property; no section of the coefficient sheaf is discarded. -/
def coefficientMap (M : Langlands.SmoothRep.{u, u, u} R G) :
    (LocallyConstantSheaf.smoothFunctor R G Y).obj M ⟶
      (functor f hf).obj ((LocallyConstantSheaf.smoothFunctor R G X).obj M) :=
  lift f hf (DirectImage.coefficientMap f hf M.representation)

/-- Its image in the full ordinary direct image is the original coefficient map. -/
@[reassoc (attr := simp)]
theorem coefficientMap_inclusion (M : Langlands.SmoothRep.{u, u, u} R G) :
    (smoothInclusion R G Y).map (coefficientMap f hf M) ≫
        (inclusion f hf).app ((LocallyConstantSheaf.smoothFunctor R G X).obj M) =
      DirectImage.coefficientMap f hf M.representation := rfl

/-- On each original section the map is precomposition by the actual spatial map. -/
@[simp]
theorem coefficientMap_apply (M : Langlands.SmoothRep.{u, u, u} R G)
    (U : ActionOpens G Y) (s : LocallyConstant U.openSet M)
    (x : ((DirectImage.preimage f hf).obj U).openSet) :
    LocallyConstant.toFun
      ((((coefficientMap f hf M).hom.hom.app (op U)).hom s).val) x =
      s (DirectImage.pointMap f hf U x) := rfl

/-- Spatial pullback of full smooth coefficient sheaves retains every original
intertwiner as a natural transformation of coefficient functors. -/
def coefficientNatTrans :
    LocallyConstantSheaf.smoothFunctor R G Y ⟶
      LocallyConstantSheaf.smoothFunctor R G X ⋙ functor f hf where
  app M := coefficientMap f hf M
  naturality M N a := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    rfl

/-- Naturality for every original smooth coefficient intertwiner. -/
@[reassoc]
theorem coefficientMap_naturality {M N : Langlands.SmoothRep.{u, u, u} R G}
    (a : M ⟶ N) :
    (LocallyConstantSheaf.smoothFunctor R G Y).map a ≫ coefficientMap f hf N =
      coefficientMap f hf M ≫
        (functor f hf).map ((LocallyConstantSheaf.smoothFunctor R G X).map a) :=
  (coefficientNatTrans f hf).naturality a

/-- The original coefficient map for the identity is precisely the actual
smooth-direct-image unit. -/
theorem coefficientMap_id (M : Langlands.SmoothRep.{u, u, u} R G) :
    coefficientMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) M =
      (idIso (R := R) (G := G) (X := X)).hom.app
        ((LocallyConstantSheaf.smoothFunctor R G X).obj M) := by
  apply hom_ext
  change DirectImage.coefficientMap (ContinuousMap.id X)
    (fun (_ : G) (_ : X) => rfl) M.representation = 𝟙 _
  exact DirectImage.coefficientMap_id M.representation

/-- The original coefficient maps compose through the constructed lax
smooth-direct-image comparison, with no invertibility assumption. -/
@[reassoc]
theorem coefficientMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    coefficientMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) M =
      coefficientMap g hg M ≫
        (functor g hg).map (coefficientMap f hf M) ≫
        (compMap f hf g hg).app ((LocallyConstantSheaf.smoothFunctor R G X).obj M) := by
  apply hom_ext
  change DirectImage.coefficientMap (g.comp f)
      (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
      M.representation =
    DirectImage.coefficientMap g hg M.representation ≫
      (DirectImage.sheaf g hg (ModuleCat.{u} R)).map
        (DirectImage.coefficientMap f hf M.representation)
  exact DirectImage.coefficientMap_comp f hf g hg M.representation

end Langlands.Sheaf.Equivariant.SmoothDirectImage
