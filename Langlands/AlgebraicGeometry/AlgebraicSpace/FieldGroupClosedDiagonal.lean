import Langlands.AlgebraicGeometry.AlgebraicSpace.GroupIdentityDiagonal
import Langlands.AlgebraicGeometry.AlgebraicSpace.FieldImmersionClosed
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleClosedImmersionDescent

/-! # Closed diagonals of group presheaves with etale field atlases -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.GroupIdentity

variable {k : Type u} [Field k]
  (G : (Over (Spec (CommRingCat.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The zero section of an immersed group presheaf is closed when it has an
etale-surjective atlas locally of finite type over the field. -/
theorem zero_isClosedImmersion_of_etale_field_atlas
    (hz : (MorphismProperty.inverseImage @IsImmersion.{u}
      (Over.forget (Spec (CommRingCat.of k)))).relative
        (schemeYoneda _) (zero G))
    {U : Over (Spec (CommRingCat.of k))}
    (a : (schemeYoneda _).obj U ⟶ underlying G)
    (ha : IsEtale a) (hs : IsSurjective a) [LocallyOfFiniteType U.hom] :
    IsClosedImmersion (zero G) := by
  let Y := schemeYoneda (Spec (CommRingCat.of k))
  let Z := hz.rep.pullback a
  let i : Z ⟶ U := hz.rep.snd a
  have hi : IsImmersion i.left := hz.property_snd a
  have hsq := hz.rep.isPullback a
  obtain ⟨p, hp⟩ := Y.map_surjective (hz.rep.fst a)
  rw [← hp] at hsq
  have hpe : Etale p.left := ha.projection (zero G) (Y.map i) p hsq.flip
  have hw : i.left ≫ U.hom = p.left := by
    calc
      i.left ≫ U.hom = Z.hom := Over.w i
      _ = p.left ≫ 𝟙 _ := (Over.w p).symm
      _ = p.left := Category.comp_id _
  have hie : Etale (i.left ≫ U.hom) := by
    rw [hw]
    exact hpe
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  have hc := isClosedImmersion_of_etale_field_source i.left U.hom
  exact isClosedImmersion_of_etale_atlas hz a ha hs hc

/-- An immersed diagonal is closed if there is an etale-surjective atlas
locally of finite type over a field. -/
theorem isClosedImmersion_diag_of_etale_field_atlas
    (hd : (MorphismProperty.inverseImage @IsImmersion.{u}
      (Over.forget (Spec (CommRingCat.of k)))).relative
        (schemeYoneda _) (diag (underlying G)))
    {U : Over (Spec (CommRingCat.of k))}
    (a : (schemeYoneda _).obj U ⟶ underlying G)
    (ha : IsEtale a) (hs : IsSurjective a) [LocallyOfFiniteType U.hom] :
    IsClosedImmersion (diag (underlying G)) := by
  have : MorphismProperty.RespectsIso @IsImmersion.{u} :=
    IsImmersion.isStableUnderBaseChange.respectsIso
  apply (isClosedImmersion_diag_iff_zero G).mpr
  exact zero_isClosedImmersion_of_etale_field_atlas G
    ((relative_diag_iff_zero G @IsImmersion.{u}).mp hd) a ha hs

/-- The actual open complement of the identity in the pullback to the atlas. -/
def fieldIdentityAtlasComplement
    (hz : (MorphismProperty.inverseImage @IsImmersion.{u}
      (Over.forget (Spec (CommRingCat.of k)))).relative
        (schemeYoneda _) (zero G))
    {U : Over (Spec (CommRingCat.of k))}
    (a : (schemeYoneda _).obj U ⟶ underlying G)
    (ha : IsEtale a) (hs : IsSurjective a) [LocallyOfFiniteType U.hom] : U.left.Opens := by
  have hc : _root_.AlgebraicGeometry.IsClosedImmersion (hz.rep.snd a).left :=
    (zero_isClosedImmersion_of_etale_field_atlas G hz a ha hs).projection
      a (hz.rep.fst a) (hz.rep.snd a) (hz.rep.isPullback a)
  exact ⟨(Set.range (hz.rep.snd a).left)ᶜ,
    (hz.rep.snd a).left.isClosedEmbedding.isClosed_range.isOpen_compl⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.GroupIdentity
