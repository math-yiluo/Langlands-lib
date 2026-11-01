import Langlands.Geometry.Analytic.ChosenAtlasDomainPresentation
import Langlands.Geometry.Analytic.OriginalDomainLocallyConstantLocalization

/-! # Concrete locally constant sheaf transport by chosen atlas isomorphisms -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} {D E : Type z}

/-- Pull sections on the actual image domain back by the actual restricted map. -/
def isoOriginalDomainLocallyConstantEquiv (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain) :
    LocallyConstant (isoOriginalDomain e S) D ≃ LocallyConstant S D :=
  LocallyConstant.congrLeft (isoOriginalDomainHomeomorph e S).symm

@[simp]
theorem isoOriginalDomainLocallyConstantEquiv_apply (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain) (f : LocallyConstant (isoOriginalDomain e S) D)
    (x : S) :
    isoOriginalDomainLocallyConstantEquiv e S f x =
      f (isoOriginalDomainHomeomorph e S x) := rfl

@[simp]
theorem isoOriginalDomainLocallyConstantEquiv_symm_apply (e : A ≅ B)
    (S : A.atlas.OriginalChartDomain) (f : LocallyConstant S D)
    (y : isoOriginalDomain e S) :
    (isoOriginalDomainLocallyConstantEquiv e S).symm f y =
      f ((isoOriginalDomainHomeomorph e S).symm y) := rfl

/-- Actual inclusion pullback commutes with the forward section comparison. -/
theorem isoOriginalDomainLocallyConstantEquiv_restrict (e : A ≅ B)
    {S T : A.atlas.OriginalChartDomain} (hST : S ≤ T)
    (f : LocallyConstant (isoOriginalDomain e T) D) :
    isoOriginalDomainLocallyConstantEquiv e S
        (locallyConstantRestrict (isoOriginalDomain_mono e hST) f) =
      locallyConstantRestrict hST (isoOriginalDomainLocallyConstantEquiv e T f) := by
  ext x
  rfl

/-- The inverse comparison also commutes with all actual domain inclusions. -/
theorem isoOriginalDomainLocallyConstantEquiv_symm_restrict (e : A ≅ B)
    {S T : A.atlas.OriginalChartDomain} (hST : S ≤ T)
    (f : LocallyConstant T D) :
    (isoOriginalDomainLocallyConstantEquiv e S).symm (locallyConstantRestrict hST f) =
      locallyConstantRestrict (isoOriginalDomain_mono e hST)
        ((isoOriginalDomainLocallyConstantEquiv e T).symm f) := by
  ext x
  rfl

/-- Full image-domain function sets with the actual image-domain inclusions. -/
abbrev isoOriginalDomainLocallyConstantPresheaf (e : A ≅ B) (D : Type z) :
    A.atlas.OriginalChartDomainᵒᵖ ⥤ Type (max v z) where
  obj S := LocallyConstant (isoOriginalDomain e S.unop) D
  map f := TypeCat.ofHom
    (locallyConstantRestrict (isoOriginalDomain_mono e (leOfHom f.unop)))
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro f
    ext x
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro h
    ext x
    rfl

/-- This concrete presheaf is the literal pullback along the image functor. -/
theorem isoOriginalDomainLocallyConstantPresheaf_eq (e : A ≅ B) (D : Type z) :
    isoOriginalDomainLocallyConstantPresheaf e D =
      (isoOriginalDomainEquivalence e).functor.op ⋙ locallyConstantPresheaf B.atlas D := rfl

/-- The actual restricted homeomorphisms give a natural presheaf isomorphism. -/
def isoOriginalDomainLocallyConstant (e : A ≅ B) (D : Type z) :
    isoOriginalDomainLocallyConstantPresheaf e D ≅ locallyConstantPresheaf A.atlas D :=
  NatIso.ofComponents
    (fun S => (isoOriginalDomainLocallyConstantEquiv e S.unop).toIso)
    (fun f => by
      apply ConcreteCategory.hom_ext
      intro h
      exact isoOriginalDomainLocallyConstantEquiv_restrict e (leOfHom f.unop) h)

/-- The full image-domain sections form a sheaf on the unchanged source site. -/
theorem isoOriginalDomainLocallyConstant_isSheaf (e : A ≅ B) (D : Type z) :
    Presheaf.IsSheaf (quasinetTopology A.atlas)
      (isoOriginalDomainLocallyConstantPresheaf e D) :=
  (Presheaf.isSheaf_of_iso_iff (isoOriginalDomainLocallyConstant e D)).mpr
    (locallyConstantPresheaf_isSheaf A.atlas D)

/-- The actual target section sheaf pulled back to the source domain site. -/
def isoOriginalDomainLocallyConstantSheaf (e : A ≅ B) (D : Type z) :
    Sheaf (quasinetTopology A.atlas) (Type (max v z)) :=
  ⟨isoOriginalDomainLocallyConstantPresheaf e D,
    isoOriginalDomainLocallyConstant_isSheaf e D⟩

/-- The concrete section comparison as an isomorphism of the actual sheaves. -/
def isoOriginalDomainLocallyConstantSheafIso (e : A ≅ B) (D : Type z) :
    isoOriginalDomainLocallyConstantSheaf e D ≅ locallyConstantSheaf A.atlas D :=
  ObjectProperty.isoMk _ (isoOriginalDomainLocallyConstant e D)

/-- Literal coefficient postcomposition commutes with chosen-isomorphism transport. -/
theorem isoOriginalDomainLocallyConstant_coefficient_naturality
    (e : A ≅ B) (φ : D → E) :
    Functor.whiskerLeft (isoOriginalDomainEquivalence e).functor.op
        (locallyConstantCoefficientMap (a := B.atlas) φ) ≫
        (isoOriginalDomainLocallyConstant e E).hom =
      (isoOriginalDomainLocallyConstant e D).hom ≫
        locallyConstantCoefficientMap (a := A.atlas) φ := by
  ext S f
  rfl

section Gluing

variable (e : A ≅ B) {S : A.atlas.OriginalChartDomain} {R : Sieve S}
  (p : Presieve.FamilyOfElements (isoOriginalDomainLocallyConstantPresheaf e D) R.arrows)
  (hp : p.Compatible) (hR : IsCovering R)

/-- Pull back the whole matching family, construct its source glue, and transport
it to the actual target image domain. -/
def isoOriginalDomainLocallyConstantSieveGlue : LocallyConstant (isoOriginalDomain e S) D :=
  (isoOriginalDomainLocallyConstantEquiv e S).symm
    (locallyConstantSieveGlue (p.map (isoOriginalDomainLocallyConstant e D).hom)
      (hp.map (isoOriginalDomainLocallyConstant e D).hom) hR)

/-- The constructed image-domain glue recovers every original local section
along the literal image-domain inclusion. -/
theorem isoOriginalDomainLocallyConstantSieveGlue_apply
    {T : A.atlas.OriginalChartDomain} (f : T ⟶ S) (hf : R f)
    (x : isoOriginalDomain e T) :
    isoOriginalDomainLocallyConstantSieveGlue e p hp hR
        (Set.inclusion (isoOriginalDomain_mono e (leOfHom f)) x) =
      (p f hf : LocallyConstant (isoOriginalDomain e T) D) x := by
  have h := locallyConstantSieveGlue_apply
    (p.map (isoOriginalDomainLocallyConstant e D).hom)
    (hp.map (isoOriginalDomainLocallyConstant e D).hom) hR f hf
    ((isoOriginalDomainHomeomorph e T).symm x)
  change locallyConstantSieveGlue (p.map (isoOriginalDomainLocallyConstant e D).hom)
      (hp.map (isoOriginalDomainLocallyConstant e D).hom) hR
      (Set.inclusion (leOfHom f) ((isoOriginalDomainHomeomorph e T).symm x)) = _ at h
  change locallyConstantSieveGlue (p.map (isoOriginalDomainLocallyConstant e D).hom)
      (hp.map (isoOriginalDomainLocallyConstant e D).hom) hR
      (Set.inclusion (leOfHom f) ((isoOriginalDomainHomeomorph e T).symm x)) = _
  simpa only [Presieve.FamilyOfElements.map,
    isoOriginalDomainLocallyConstant, NatIso.ofComponents_hom_app,
    Equiv.toIso_hom_hom_apply, TypeCat.hom_ofHom, isoOriginalDomainLocallyConstantEquiv_apply,
    Homeomorph.apply_symm_apply] using h

/-- Pulling the constructed image glue back gives exactly the constructed
source glue of the transported family, for every covering sieve. -/
theorem isoOriginalDomainLocallyConstantSieveGlue_pullback :
    isoOriginalDomainLocallyConstantEquiv e S
        (isoOriginalDomainLocallyConstantSieveGlue e p hp hR) =
      locallyConstantSieveGlue (p.map (isoOriginalDomainLocallyConstant e D).hom)
        (hp.map (isoOriginalDomainLocallyConstant e D).hom) hR :=
  (isoOriginalDomainLocallyConstantEquiv e S).apply_symm_apply _

/-- Point coverage and the original local value equations give uniqueness
for the full actual image-domain function sets. -/
theorem isoOriginalDomainLocallyConstantSieveGlue_unique
    (f : LocallyConstant (isoOriginalDomain e S) D) (hf : p.IsAmalgamation f) :
    f = isoOriginalDomainLocallyConstantSieveGlue e p hp hR := by
  ext x
  let y := (isoOriginalDomainHomeomorph e S).symm x
  obtain ⟨T, hTS, hRT, hyT⟩ := hR.exists_mem y.property
  let z : isoOriginalDomain e T := isoOriginalDomainHomeomorph e T ⟨y.val, hyT⟩
  have hx : Set.inclusion (isoOriginalDomain_mono e hTS) z = x := by
    exact (isoOriginalDomainHomeomorph e S).apply_symm_apply x
  have he := congrArg (fun q : LocallyConstant (isoOriginalDomain e T) D => q z)
    (hf (homOfLE hTS) hRT)
  have hg := isoOriginalDomainLocallyConstantSieveGlue_apply e p hp hR
    (homOfLE hTS) hRT z
  change f (Set.inclusion (isoOriginalDomain_mono e hTS) z) = _ at he
  rw [hx] at he hg
  exact he.trans hg.symm

end Gluing

end Langlands.Analytic.AffinoidAtlasPresentation
