import Langlands.GroupScheme.GroupLikeActionAffine
import Langlands.GroupScheme.Torus.SplittingAssembly

/-! # Rigidity for closed subgroups of split tori -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineCoordinates

variable {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine H.X.left] [IsAffine G.X.left]

/-- The contravariant Hopf coordinate map induced by an actual affine group
homomorphism. -/
def hopfRestriction (f : H ⟶ G) : hopfAlgebra G ⟶ hopfAlgebra H :=
  (hopfSpec.fullyFaithful.preimage
    ((hopfSpecIso H).hom ≫ f ≫ (hopfSpecIso G).inv)).unop

/-- The coordinate map recovers the original homomorphism between the actual
Hopf spectrum presentations. -/
theorem hopfRestriction_map (f : H ⟶ G) :
    (hopfSpec (CommRingCat.of k)).map (hopfRestriction f).op =
      (hopfSpecIso H).hom ≫ f ≫ (hopfSpecIso G).inv :=
  hopfSpec.fullyFaithful.map_preimage _

/-- A closed immersion of affine groups induces a surjection of their Hopf
coordinate algebras. -/
theorem hopfRestriction_surjective (f : H ⟶ G) (hf : IsClosedSubgroup f) :
    Function.Surjective (hopfRestriction f).hom := by
  let r := hopfRestriction f
  let φ : CommRingCat.of (hopfAlgebra G) ⟶ CommRingCat.of (hopfAlgebra H) :=
    CommRingCat.ofHom r.hom.toAlgHom.toRingHom
  have hc : IsClosedImmersion (Spec.map φ) := by
    change IsClosedSubgroup ((hopfSpec (CommRingCat.of k)).map r.op)
    rw [hopfRestriction_map]
    let : IsClosedImmersion (hopfSpecIso H).hom.hom.hom.left :=
      IsClosedSubgroup.of_iso (hopfSpecIso H)
    let : IsClosedImmersion f.hom.hom.left := hf
    let : IsClosedImmersion (hopfSpecIso G).inv.hom.hom.left :=
      IsClosedSubgroup.of_iso (hopfSpecIso G).symm
    change IsClosedImmersion
      ((hopfSpecIso H).hom.hom.hom.left ≫
        f.hom.hom.left ≫ (hopfSpecIso G).inv.hom.hom.left)
    infer_instance
  let : IsClosedImmersion (Spec.map φ) := hc
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map φ)).2
  have he : (Scheme.ΓSpecIso (CommRingCat.of (hopfAlgebra G))).inv ≫
      (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (hopfAlgebra H))).hom = φ := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hh : Function.Surjective
      ((Scheme.ΓSpecIso (CommRingCat.of (hopfAlgebra G))).inv ≫
        (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (hopfAlgebra H))).hom) :=
    (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (hopfAlgebra H))).hom).2.comp
      (hs.comp (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (hopfAlgebra G))).inv).2)
  rw [he] at hh
  exact hh

/-- Group-like spanning descends along every closed affine subgroup immersion. -/
theorem span_groupLike_of_isClosedSubgroup (f : H ⟶ G) (hf : IsClosedSubgroup f)
    (hspan : Submodule.span k {c : hopfAlgebra G | IsGroupLikeElem k c} = ⊤) :
    Submodule.span k {c : hopfAlgebra H | IsGroupLikeElem k c} = ⊤ := by
  apply top_unique
  intro c _
  obtain ⟨b, rfl⟩ := hopfRestriction_surjective f hf c
  have hb : b ∈ Submodule.span k {c : hopfAlgebra G | IsGroupLikeElem k c} := by
    rw [hspan]
    exact Submodule.mem_top
  have hm := Submodule.mem_map_of_mem (f := (hopfRestriction f).hom.toLinearMap) hb
  rw [Submodule.map_span] at hm
  exact Submodule.span_mono
    (Set.image_subset_iff.2 fun _ hx => hx.map (hopfRestriction f).hom.toCoalgHom) hm

end AffineCoordinates

variable {k : Type u} [Field k]

/-- The full coordinate Hopf algebra of a closed subgroup of a split torus is
spanned by its group-like elements, even when the subgroup is not smooth. -/
theorem IsSplitTorus.span_groupLike_of_isClosedSubgroup
    {Z S : GroupScheme (Spec (CommRingCat.of k))} [IsAffine Z.X.left]
    (hS : IsSplitTorus S) (i : Z ⟶ S) (hi : IsClosedSubgroup i) :
    Submodule.span k
      {c : AffineCoordinates.hopfAlgebra Z | IsGroupLikeElem k c} = ⊤ := by
  let : IsAffineHom S.X.hom := hS.isAffineHom
  let : IsAffine S.X.left := isAffine_of_isAffineHom S.X.hom
  apply AffineCoordinates.span_groupLike_of_isClosedSubgroup i hi
  exact SplittingAssembly.span_of_isSplit_hopfSpec (AffineCoordinates.hopfAlgebra S)
    (IsSplitTorus.of_iso (AffineCoordinates.hopfSpecIso S) hS)

/-- Every automorphic action of a smooth connected affine group on a closed
subgroup of a split torus is trivial on every scheme test. -/
theorem IsSplitTorus.act_eq_self_of_isClosedSubgroup
    {H Z S : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffine H.X.left] [ConnectedSpace H.X.left]
    [IsAffine Z.X.left] (hS : IsSplitTorus S)
    (i : Z ⟶ S) (hi : IsClosedSubgroup i) (a : AutomorphicAction H Z)
    {T : Over (Spec (CommRingCat.of k))} (h : T ⟶ H.X) (z : T ⟶ Z.X) :
    a.act h z = z :=
  AutomorphicAction.act_eq_self_of_smooth_connected_affine
    (hS.span_groupLike_of_isClosedSubgroup i hi) a h z

end Langlands.GroupScheme
