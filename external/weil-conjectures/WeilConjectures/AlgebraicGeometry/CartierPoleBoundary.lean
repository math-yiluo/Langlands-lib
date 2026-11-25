/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundary

/-!
# The normalized Cartier pole-extension class

proof.md, (G1) and the local lifts
paragraph (auxiliary; not a blueprint node).

The relative extension model records the frame torsor of O(D), its canonical section
on the complement, and the lift of supported one. Locally a frame is t⁻¹; its image
in the extension generates the powers u t⁻ᵃ. Thus the quotient sends t⁻¹ to +1.
Only the extension class, invariant under isomorphisms of extensions, is retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The integral relative extension of the dual ideal, trivialized by the canonical
Cartier section on the complement. Its torsor map is equivariant and lies over the
supported section +1. Killing the specified complementary frame fixes the relative
class, including the sign, rather than only its image in Pic(T).
proof.md, (G1) and the local lifts
paragraph (auxiliary; not a blueprint node). -/
def CartierPoleBoundarySpec {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible)
    (β : Ext ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      T.gmSheaf 1) : Prop :=
  letI := hI.isInvertible_dual_toModules
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  ∀ (W : T.Opens) (_hW : (W : Set T) = (Set.range i.base)ᶜ),
    ∃ (τ : (Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj
          (op (Scheme.Etale.mk W.ι)))
      (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (a : T.gmSheaf ⟶ E)
      (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
      (f : (Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)).sheaf ⟶
        (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj E),
      Scheme.Modules.etaleIsoTorsorVal (Scheme.Modules.dual i.ker.toModules) τ =
        supportedDivisorSectionPullback i W ∧
      (∀ (U : T.Etaleᵒᵖ) (g : T.gmSheaf.obj.obj U)
        (p : (Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj U),
        @id (E.obj.obj U) (f.hom.app U ((Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).vadd U g p)) =
          a.hom.app U g + (@id (E.obj.obj U) (f.hom.app U p))) ∧
      (∀ (U : T.Etaleᵒᵖ) (p : (Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj U),
        b.hom.app U (f.hom.app U p) =
          ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)).obj.map
            ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).from U.unop).op
            ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
              (supportedIntegralOne T))) ∧
      @id (E.obj.obj (op (Scheme.Etale.mk W.ι)))
        (f.hom.app (op (Scheme.Etale.mk W.ι)) τ) = 0 ∧
      β = hE.extClass

end AlgebraicGeometry.Etale
