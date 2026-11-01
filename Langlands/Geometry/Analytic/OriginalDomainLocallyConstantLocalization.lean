import Langlands.Geometry.Analytic.OriginalDomainNested
import Langlands.Geometry.Analytic.OriginalDomainLocallyConstantSheaf
import Mathlib.CategoryTheory.Whiskering

/-! # Localization and coefficient maps of actual locally constant sections -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.IndexedAffinoidAtlas.OriginalChartDomain

open Set CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {A B : Type z}

/-- Coefficient change is literal postcomposition on every section. -/
def locallyConstantCoefficientMap (φ : A → B) :
    locallyConstantPresheaf a A ⟶ locallyConstantPresheaf a B where
  app _ := TypeCat.ofHom (LocallyConstant.map φ)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro f
    ext x
    rfl

@[simp]
theorem locallyConstantCoefficientMap_apply (φ : A → B)
    (U : OriginalChartDomain a) (f : LocallyConstant U A) (x : U) :
    (locallyConstantCoefficientMap φ).app (Opposite.op U) f x = φ (f x) := rfl

/-- The same actual section maps give morphisms of the constructed sheaves. -/
def locallyConstantSheafMap (φ : A → B) :
    locallyConstantSheaf a A ⟶ locallyConstantSheaf a B :=
  ObjectProperty.homMk (locallyConstantCoefficientMap φ)

/-- Locally constant section sheaves vary functorially in all coefficients. -/
def locallyConstantSheafFunctor (a : IndexedAffinoidAtlas.{u, v, w} K X) :
    Type z ⥤ Sheaf (quasinetTopology a) (Type (max v z)) where
  obj A := locallyConstantSheaf a A
  map φ := locallyConstantSheafMap (fun x => φ x)
  map_id _ := by
    apply ObjectProperty.hom_ext
    ext U f
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    ext U f
    rfl

/-- Coefficient postcomposition commutes with the constructed gluing on
every arbitrary covering sieve, including empty permitted cases. -/
theorem locallyConstantSieveGlue_map (φ : A → B)
    {U : OriginalChartDomain a} {R : Sieve U}
    (p : Presieve.FamilyOfElements (locallyConstantPresheaf a A) R.arrows)
    (hp : p.Compatible) (hR : IsCovering R) :
    LocallyConstant.map φ (locallyConstantSieveGlue p hp hR) =
      locallyConstantSieveGlue (p.map (locallyConstantCoefficientMap φ))
        (hp.map (locallyConstantCoefficientMap φ)) hR := by
  ext x
  obtain ⟨V, hVU, hRV, hxV⟩ := hR.exists_mem x.property
  change φ (locallyConstantSieveGlueFun p hp hR x) =
    locallyConstantSieveGlueFun (p.map (locallyConstantCoefficientMap φ))
      (hp.map (locallyConstantCoefficientMap φ)) hR x
  rw [locallyConstantSieveGlueFun_apply p hp hR (homOfLE hVU) hRV x hxV,
    locallyConstantSieveGlueFun_apply (p.map (locallyConstantCoefficientMap φ))
      (hp.map (locallyConstantCoefficientMap φ)) hR (homOfLE hVU) hRV x hxV]
  rfl

/-- Actual functions on the ambient image and on the nested subspace are
identified by the already constructed homeomorphism. -/
def locallyConstantLocalizationEquiv (S : OriginalChartDomain a)
    (U : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)) :
    LocallyConstant (S.subspaceExtend U) A ≃ LocallyConstant U A :=
  LocallyConstant.congrLeft (S.subspaceExtendHomeomorph U)

@[simp]
theorem locallyConstantLocalizationEquiv_apply (S : OriginalChartDomain a)
    (U : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain))
    (f : LocallyConstant (S.subspaceExtend U) A) (x : U) :
    locallyConstantLocalizationEquiv S U f x =
      f ⟨x.val.val, ⟨x.val, x.property, rfl⟩⟩ := rfl

@[simp]
theorem locallyConstantLocalizationEquiv_symm_apply (S : OriginalChartDomain a)
    (U : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain))
    (f : LocallyConstant U A) (x : S.subspaceExtend U) :
    (locallyConstantLocalizationEquiv S U).symm f x =
      f (S.subspaceExtendHomeomorph U x) := rfl

/-- Forgetting the intermediate membership commutes with every restriction. -/
theorem locallyConstantLocalizationEquiv_restrict (S : OriginalChartDomain a)
    {U V : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)}
    (hUV : U ≤ V) (f : LocallyConstant (S.subspaceExtend V) A) :
    locallyConstantLocalizationEquiv S U
        (locallyConstantRestrict (S.subspaceExtend_mono hUV) f) =
      locallyConstantRestrict hUV (locallyConstantLocalizationEquiv S V f) := by
  ext x
  rfl

/-- Inserting the intermediate membership also commutes with restriction. -/
theorem locallyConstantLocalizationEquiv_symm_restrict (S : OriginalChartDomain a)
    {U V : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)}
    (hUV : U ≤ V) (f : LocallyConstant V A) :
    (locallyConstantLocalizationEquiv S U).symm (locallyConstantRestrict hUV f) =
      locallyConstantRestrict (S.subspaceExtend_mono hUV)
        ((locallyConstantLocalizationEquiv S V).symm f) := by
  ext x
  rfl

/-- The full ambient-image section sets, with literal ambient inclusions.
The transparent object assignment exposes the actual section functions. -/
abbrev locallyConstantLocalizedPresheaf (S : OriginalChartDomain a) (A : Type z) :
    (OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain))ᵒᵖ ⥤
      Type (max v z) where
  obj U := LocallyConstant (S.subspaceExtend U.unop) A
  map f := TypeCat.ofHom
    (locallyConstantRestrict (S.subspaceExtend_mono (leOfHom f.unop)))
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro f
    ext x
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro h
    ext x
    rfl

/-- This concrete presentation is the literal ambient presheaf pullback. -/
theorem locallyConstantLocalizedPresheaf_eq (S : OriginalChartDomain a) (A : Type z) :
    locallyConstantLocalizedPresheaf S A =
      S.subspaceExtensionFunctor.op ⋙ locallyConstantPresheaf a A := rfl

/-- The section comparison is natural on the actual subspace domain category. -/
def locallyConstantLocalization (S : OriginalChartDomain a) (A : Type z) :
    locallyConstantLocalizedPresheaf S A ≅
      locallyConstantPresheaf (a.subspaceAtlas S.carrier S.is_domain) A :=
  NatIso.ofComponents
    (fun U => (locallyConstantLocalizationEquiv S U.unop).toIso)
    (fun f => by
      apply ConcreteCategory.hom_ext
      intro h
      exact locallyConstantLocalizationEquiv_restrict S (leOfHom f.unop) h)

/-- The literal ambient-image presheaf is a sheaf on the subspace site,
by the explicit section isomorphism and the constructed subspace sheaf. -/
theorem locallyConstantLocalization_isSheaf (S : OriginalChartDomain a) (A : Type z) :
    Presheaf.IsSheaf (quasinetTopology (a.subspaceAtlas S.carrier S.is_domain))
      (locallyConstantLocalizedPresheaf S A) :=
  (Presheaf.isSheaf_of_iso_iff (locallyConstantLocalization S A)).mpr
    (locallyConstantPresheaf_isSheaf (a.subspaceAtlas S.carrier S.is_domain) A)

/-- The ambient-image section sets, with their unchanged ambient restrictions,
form an actual sheaf on the subspace domain site. -/
def locallyConstantLocalizedSheaf (S : OriginalChartDomain a) (A : Type z) :
    Sheaf (quasinetTopology (a.subspaceAtlas S.carrier S.is_domain)) (Type (max v z)) :=
  ⟨locallyConstantLocalizedPresheaf S A, locallyConstantLocalization_isSheaf S A⟩

/-- An isomorphism of the actual sheaves, with the explicit nested-subspace
section maps as its underlying natural isomorphism. -/
def locallyConstantSheafLocalization (S : OriginalChartDomain a) (A : Type z) :
    locallyConstantLocalizedSheaf S A ≅
      locallyConstantSheaf (a.subspaceAtlas S.carrier S.is_domain) A :=
  ObjectProperty.isoMk _ (locallyConstantLocalization S A)

/-- Localization commutes with every coefficient function. -/
theorem locallyConstantLocalization_coefficient_naturality
    (S : OriginalChartDomain a) (φ : A → B) :
    Functor.whiskerLeft S.subspaceExtensionFunctor.op (locallyConstantCoefficientMap φ) ≫
        (locallyConstantLocalization S B).hom =
      (locallyConstantLocalization S A).hom ≫
        locallyConstantCoefficientMap (a := a.subspaceAtlas S.carrier S.is_domain) φ := by
  ext U f
  rfl

section Gluing

variable (S : OriginalChartDomain a)
  {U : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)}
  {R : Sieve U}
  (p : Presieve.FamilyOfElements
    (locallyConstantLocalizedPresheaf S A) R.arrows)
  (hp : p.Compatible) (hR : IsCovering R)

/-- Glue an actual compatible ambient-image section family by transporting
to nested sections, constructing their glue, and inserting membership back. -/
def locallyConstantLocalizationSieveGlue : LocallyConstant (S.subspaceExtend U) A :=
  (locallyConstantLocalizationEquiv S U).symm
    (locallyConstantSieveGlue (p.map (locallyConstantLocalization S A).hom)
      (hp.map (locallyConstantLocalization S A).hom) hR)

/-- The constructed ambient-image glue recovers each original section value
along the original ambient subset inclusion. -/
theorem locallyConstantLocalizationSieveGlue_apply
    {V : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)}
    (f : V ⟶ U) (hf : R f) (x : S.subspaceExtend V) :
    locallyConstantLocalizationSieveGlue S p hp hR
        (Set.inclusion (S.subspaceExtend_mono (leOfHom f)) x) =
      (p f hf : LocallyConstant (S.subspaceExtend V) A) x := by
  exact locallyConstantSieveGlue_apply
    (p.map (locallyConstantLocalization S A).hom)
    (hp.map (locallyConstantLocalization S A).hom) hR f hf
    (S.subspaceExtendHomeomorph V x)

/-- Localization of the constructed glue equals the constructed nested glue
on every arbitrary covering sieve. -/
theorem locallyConstantLocalizationSieveGlue_localize :
    locallyConstantLocalizationEquiv S U (locallyConstantLocalizationSieveGlue S p hp hR) =
      locallyConstantSieveGlue (p.map (locallyConstantLocalization S A).hom)
        (hp.map (locallyConstantLocalization S A).hom) hR :=
  (locallyConstantLocalizationEquiv S U).apply_symm_apply _

/-- Point coverage proves uniqueness directly for the literal ambient-image
section functions, rather than assuming an ambient gluing output. -/
theorem locallyConstantLocalizationSieveGlue_unique
    (f : LocallyConstant (S.subspaceExtend U) A)
    (hf : p.IsAmalgamation f) :
    f = locallyConstantLocalizationSieveGlue S p hp hR := by
  ext x
  let y := S.subspaceExtendHomeomorph U x
  obtain ⟨V, hVU, hRV, hyV⟩ := hR.exists_mem y.property
  let z : S.subspaceExtend V := ⟨x.val, ⟨y.val, hyV, rfl⟩⟩
  have he := congrArg (fun q : LocallyConstant (S.subspaceExtend V) A => q z)
    (hf (homOfLE hVU) hRV)
  exact he.trans (locallyConstantLocalizationSieveGlue_apply S p hp hR
    (homOfLE hVU) hRV z).symm

end Gluing

end Langlands.Analytic.IndexedAffinoidAtlas.OriginalChartDomain
