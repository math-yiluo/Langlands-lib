/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Mathlib.CategoryTheory.Limits.Types.Colimits

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Étale Cohomology, Tag 09XN, proof of lemma-describe-pullback.
(blueprint: lem-weil-pbc-etale-inverse-image-section-description-representation).

Proof:
Compute the pointwise left Kan extension as the colimit over costructured
arrows. Joint surjectivity of the colimit maps gives an object V, an arrow
a : Z → g*V and a section t of F(V). Its colimit map is the Kan unit at V
followed by restriction along a. Naturality of the sheafification unit moves
restriction past sheafification. The composite-adjunction unit is the Kan
unit followed by the sheafification unit, giving the required equality. -/
theorem etaleInverseImageSectionDescription_representation (S T : Scheme.{u}) (g : T ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (Z : T.Etale)
    (p : ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan.obj
      ((sheafToPresheaf S.smallEtaleTopology (Type (u + 1))).obj F)).obj (op Z)) :
    ∃ (V : S.Etale)
      (a : Z ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj V)
      (t : F.obj.obj (op V)),
      (toSheafify T.smallEtaleTopology
        ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan.obj
          ((sheafToPresheaf S.smallEtaleTopology (Type (u + 1))).obj F))).app (op Z) p =
        ((Scheme.etaleSetPullback g).obj F).obj.map a.op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
            (S.smallGrothendieckTopology @Etale)
            (T.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op V) t) := by
  let b := MorphismProperty.Over.pullback @Etale ⊤ g
  let Q := (sheafToPresheaf S.smallEtaleTopology (Type (u + 1))).obj F
  let h := b.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit Q (op Z)
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective _ h p
  refine ⟨j.left.unop, j.hom.unop, t, ?_⟩
  change (toSheafify T.smallEtaleTopology (b.op.lan.obj Q)).app (op Z) p = _
  rw [← ht]
  change (toSheafify T.smallEtaleTopology (b.op.lan.obj Q)).app (op Z)
      ((b.op.lan.obj Q).map j.hom ((b.op.lanUnit.app Q).app j.left t)) = _
  have hn := NatTrans.naturality_apply
    (toSheafify T.smallEtaleTopology (b.op.lan.obj Q)) j.hom
    ((b.op.lanUnit.app Q).app j.left t)
  rw [hn]
  congr 1

end AlgebraicGeometry
