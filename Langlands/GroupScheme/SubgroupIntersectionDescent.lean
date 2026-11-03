import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.BaseChangeReflection
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Subgroup intersections over a field and over its algebraic closure -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G P P' : GroupScheme (Spec (CommRingCat.of k))}

/-- The comparison isomorphism carries the inclusion of the base-changed intersection to the
base change of the inclusion of the intersection. -/
@[reassoc]
theorem subgroupIntersectionBaseChangeIso_inv_ι {S S' : Scheme.{u}} {P P' G : GroupScheme S}
    (b : S' ⟶ S) (j : P ⟶ G) (j' : P' ⟶ G) :
    (subgroupIntersectionBaseChangeIso b j j').inv ≫
        (GroupScheme.baseChange b).map (subgroupIntersectionHom j j') =
      subgroupIntersectionHom ((GroupScheme.baseChange b).map j)
        ((GroupScheme.baseChange b).map j') := by
  rw [← subgroupIntersectionBaseChangeIso_hom_ι, Iso.inv_hom_id_assoc]

/-- The intersection of two subgroups of a group over a field is smooth when the intersection
of their base changes to an algebraic closure is smooth. -/
theorem smooth_pullback_of_smooth_pullback_baseChange (j : P ⟶ G) (j' : P' ⟶ G)
    (h : Smooth (pullback ((GroupScheme.baseChange (toAlgebraicClosure k)).map j)
      ((GroupScheme.baseChange (toAlgebraicClosure k)).map j')).X.hom) :
    Smooth (pullback j j').X.hom := by
  have hK : Smooth ((GroupScheme.baseChange (toAlgebraicClosure k)).obj (pullback j j')).X.hom :=
    smooth_of_over_iso
      ((Grp.forget _).mapIso (subgroupIntersectionBaseChangeIso (toAlgebraicClosure k) j j')) h
  obtain ⟨h1, h2, h3⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := (pullback j j').X.hom) (g := toAlgebraicClosure k) ⟨⟨h1, h2⟩, h3⟩ hK

/-- The base change to an algebraic closure of the intersection of two subgroups has connected
underlying space when the intersection of the base-changed subgroups does. -/
theorem connectedSpace_baseChange_pullback (j : P ⟶ G) (j' : P' ⟶ G)
    (h : ConnectedSpace (pullback ((GroupScheme.baseChange (toAlgebraicClosure k)).map j)
      ((GroupScheme.baseChange (toAlgebraicClosure k)).map j')).X.left) :
    ConnectedSpace ((GroupScheme.baseChange (toAlgebraicClosure k)).obj (pullback j j')).X.left :=
  (Scheme.homeoOfIso ((Over.forget _).mapIso ((Grp.forget _).mapIso
    (subgroupIntersectionBaseChangeIso (toAlgebraicClosure k) j j')))).connectedSpace_iff.2 h

end Langlands.GroupScheme
