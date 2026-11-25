/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.EtaleSetConstantTransportIdentity
import WeilConjectures.AlgebraicGeometry.EtaleSetConstantTransportGenerators

/-! # Extending a constant trivialization by inverse image

Source: Stacks Project, Tags 03CB, 03CC, and 0A3H, final proof paragraph.
(blueprint: lem-weil-pbc-etale-constant-trivialization-pullback).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- A constant trivialization over P extends coherently to every scheme over P.
Source: Stacks Project, Tags 03CB and 03CC (composition of inverse images),
and Tag 0A3H, final paragraph (pullback of a constant sheaf).
(blueprint: lem-weil-pbc-etale-constant-trivialization-pullback).

Proof:
1. Transport beta along `𝟙 P ≫ s = s`. For h : U → P, compose the inverse
   composition comparison, the pullback of beta, and the canonical comparison
   from the inverse image of a constant sheaf to the constant sheaf on U.
   The latter is obtained from the universal property of constant sheafification:
   it carries the unit-pulled constant generator to the generator of the same
   value. This universal property works for all sets in Type (u + 1), without
   assuming that they are lifts of sets in Type u. The inverse comparison follows
   by uniqueness of left adjoints: composing the inverse-image adjunction with
   the constant-sheaf adjunction makes the pulled constant functor left adjoint
   to evaluation of direct image at the terminal P-neighbourhood. Its pullback
   is terminal on U, so this right adjoint is naturally global sections on U,
   also the right adjoint of the constant sheaf functor on U. Each comparison is
   natural in the coefficient set,
   so whiskering with E gives a natural isomorphism in F.
2. At h = identity, the unit-preserving composition comparison and the
   constant-generator comparison have identity unit equations. Uniqueness of
   these comparisons, or the adjunction triangle identities, therefore identifies
   the composite with beta. This proves the normalization, including its casts.
3. For v : V → U, use associativity of the composition comparisons to compare
   the two iterated composites. Naturality of the inverse-image unit moves the
   pullback of beta across that unit. Both constant-sheaf comparisons carry each
   pulled generator to the generator of the same value on V; equality follows
   from the universal property of sheafification and the inverse-image adjunction.
   Evaluating this equality at the pulled-back W gives the displayed formula,
   with the associativity cast in exactly the indicated direction. -/
theorem etaleConstantTrivializationPullback
    (S P : Scheme.{u}) (s : P ⟶ S)
    (E : Sheaf S.smallEtaleTopology (Type (u + 1)) ⥤ Type (u + 1))
    (β : Scheme.etaleSetPullback (𝟙 P ≫ s) ≅
      E ⋙ constantSheaf P.smallEtaleTopology (Type (u + 1))) :
    ∃ α : ∀ (U : Scheme.{u}) (h : U ⟶ P),
      Scheme.etaleSetPullback (h ≫ s) ≅
        E ⋙ constantSheaf U.smallEtaleTopology (Type (u + 1)),
      α P (𝟙 P) = β ∧
      ∀ (U V : Scheme.{u}) (h : U ⟶ P) (v : V ⟶ U)
        (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
        (W : U.Etale) (e : E.obj F),
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
          S U V (h ≫ s) v).hom.app F).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ v) (Type (u + 1))
            (U.smallGrothendieckTopology @Etale)
            (V.smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback (h ≫ s)).obj F)).hom.app (op W)
            (((α U h).inv.app F).hom.app (op W)
              ((toSheafify U.smallEtaleTopology
                ((Functor.const U.Etaleᵒᵖ).obj
                  (E.obj F))).app (op W) e))) =
        (((α V (v ≫ h)).inv.app F ≫
          eqToHom (congrArg
            (fun k : V ⟶ S => (Scheme.etaleSetPullback k).obj F)
            (Category.assoc v h s))).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)))
          ((toSheafify V.smallEtaleTopology
            ((Functor.const V.Etaleᵒᵖ).obj
              (E.obj F))).app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)) e) := by
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2
  let β' : Scheme.etaleSetPullback s ≅
      E ⋙ constantSheaf P.smallEtaleTopology (Type (u + 1)) :=
    (eqToIso (congrArg Scheme.etaleSetPullback (Category.id_comp s))).symm ≪≫ β
  let α : ∀ (U : Scheme.{u}) (h : U ⟶ P),
      Scheme.etaleSetPullback (h ≫ s) ≅
        E ⋙ constantSheaf U.smallEtaleTopology (Type (u + 1)) := fun U h ↦
    (c S P U s h).symm ≪≫
      Functor.isoWhiskerRight β' (Scheme.etaleSetPullback h) ≪≫
      Functor.associator E _ _ ≪≫
      Functor.isoWhiskerLeft E (etaleSetConstantPullbackComparison h)
  have hα (U : Scheme.{u}) (h : U ⟶ P)
      (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
      (α U h).inv.app F =
        (etaleSetConstantPullbackComparison h).inv.app (E.obj F) ≫
          (Scheme.etaleSetPullback h).map (β'.inv.app F) ≫ (c S P U s h).hom.app F := by
    simp [α]
  refine ⟨α, ?_, ?_⟩
  · apply Iso.ext_inv
    apply NatTrans.ext
    funext F
    have hi := etaleSetConstantTransportIdentity S P s F (E.obj F) (β'.inv.app F)
    rw [hα]
    simpa [β', c] using hi
  · intro U V h v F W e
    rw [hα, hα]
    exact etaleSetConstantTransportGenerators S P U V s h v F (E.obj F) (β'.inv.app F) W e


end AlgebraicGeometry
