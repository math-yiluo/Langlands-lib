import Langlands.GroupScheme.Reductive.CenterExistenceProof
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AlgebraicGeometry.FieldExtensionAffineDescentProof
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent

/-! # Reflection of finiteness of the full scheme-theoretic centre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

section General

variable {S S' : Scheme.{u}} {G Z : GroupScheme S}

/-- Every actual representative of a finite full centre is finite. -/
theorem IsSchemeTheoreticCenter.isFinite_of_hasFiniteCenter {z : Z ⟶ G}
    (hz : IsSchemeTheoreticCenter z) (hG : HasFiniteCenter G) : IsFinite Z.X.hom := by
  obtain ⟨C, c, hc, hfin⟩ := hG
  let e := hz.isRepresentedBy.isoOfIsRepresentedBy hc.isRepresentedBy
  let : IsFinite C.X.hom := hfin
  have : IsIso e.hom.hom.hom.left :=
    ((Grp.forget (Over S)) ⋙ Over.forget S).map_isIso e.hom
  rw [← Over.w e.hom.hom.hom]
  infer_instance

/-- An fpqc base change detects finiteness of an existing full centre representative. -/
theorem IsSchemeTheoreticCenter.isFinite_of_baseChange {z : Z ⟶ G}
    (hz : IsSchemeTheoreticCenter z) (b : S' ⟶ S)
    [Surjective b] [Flat b] [QuasiCompact b]
    (hG : HasFiniteCenter ((GroupScheme.baseChange b).obj G)) : IsFinite Z.X.hom := by
  have hfin := (hz.baseChange b).isFinite_of_hasFiniteCenter hG
  change IsFinite (pullback.snd Z.X.hom b) at hfin
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hfin

/-- Given existence of a full centre, its finiteness is detected fpqc locally. -/
theorem hasFiniteCenter_of_baseChange (b : S' ⟶ S)
    [Surjective b] [Flat b] [QuasiCompact b]
    (hZ : ∃ (Z : GroupScheme S) (z : Z ⟶ G), IsSchemeTheoreticCenter z)
    (hG : HasFiniteCenter ((GroupScheme.baseChange b).obj G)) : HasFiniteCenter G := by
  obtain ⟨Z, z, hz⟩ := hZ
  exact ⟨Z, z, hz, hz.isFinite_of_baseChange b hG⟩

end General

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- An affine group over a field has an actual closed representative of its full centre. -/
theorem schemeTheoreticCenterExistence_of_isAffineHom (hG : IsAffineHom G.X.hom) :
    ∃ (Z : GroupScheme (Spec (CommRingCat.of k))) (z : Z ⟶ G),
      IsSchemeTheoreticCenter z := by
  obtain ⟨Z, z, hz, hclosed⟩ :=
    fieldFixedSubgroupRepresentability k G G hG (AutomorphicAction.conjugation (𝟙 G))
  exact ⟨Z, z, hclosed, hz.2.trans (conjugation_id_fixedSubgroup_eq_center G)⟩

/-- Affineness and finiteness of the full centre after any field extension suffice
to construct an actual finite full centre over the original field. -/
theorem HasFiniteCenter.of_fieldExtension
    (hGAff : IsAffineHom
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.hom)
    (hG : HasFiniteCenter
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    HasFiniteCenter G := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := hGAff
  have hAff : IsAffine ((GroupScheme.baseChange b).obj G).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange b).obj G).X.hom
  change IsAffine (pullback G.X.hom b) at hAff
  let : IsAffine G.X.left :=
    Langlands.AlgebraicGeometry.fieldExtensionAffineDescent k K G.X.left G.X.hom hAff
  have hGAff' : IsAffineHom G.X.hom := inferInstance
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k K
  let : Surjective b := hsurj
  let : Flat b := hflat
  let : QuasiCompact b := hqc
  exact hasFiniteCenter_of_baseChange b
    (schemeTheoreticCenterExistence_of_isAffineHom hGAff') hG

/-- Construct actual finite-centre data over the original field from such data after extension. -/
def FiniteCenter.of_fieldExtension
    (hGAff : IsAffineHom
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.hom)
    (C : FiniteCenter
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    FiniteCenter G := by
  let h := C.hasFiniteCenter.of_fieldExtension hGAff
  exact ⟨h.choose, h.choose_spec.choose,
    h.choose_spec.choose_spec.1, h.choose_spec.choose_spec.2⟩

/-- The constructed finite centre recovers the supplied representative after extension. -/
def FiniteCenter.fieldExtensionIso
    (hGAff : IsAffineHom
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.hom)
    (C : FiniteCenter
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
      (C.of_fieldExtension hGAff).group ≅ C.group :=
  ((C.of_fieldExtension hGAff).isCenter.baseChange _).isRepresentedBy.isoOfIsRepresentedBy
    C.isCenter.isRepresentedBy

/-- Recovery of a finite centre preserves its actual inclusion into the ambient group. -/
@[reassoc]
theorem FiniteCenter.fieldExtensionIso_hom_comp
    (hGAff : IsAffineHom
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.hom)
    (C : FiniteCenter
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    (C.fieldExtensionIso hGAff).hom ≫ C.inclusion =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
        (C.of_fieldExtension hGAff).inclusion :=
  ((C.of_fieldExtension hGAff).isCenter.baseChange _).isRepresentedBy.isoOfIsRepresentedBy_hom_comp
    C.isCenter.isRepresentedBy

/-- The finite-centre component of semisimplicity reflects under every field extension. -/
theorem IsSemisimple.hasFiniteCenter_of_fieldExtension
    (hG : IsSemisimple
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    HasFiniteCenter G :=
  hG.hasFiniteCenter.of_fieldExtension hG.isConnectedReductive.isAffineHom

end Field

end Langlands.GroupScheme
