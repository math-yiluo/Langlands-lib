import Langlands.Geometry.Analytic.InvariantAnalyticDomains
import Langlands.Geometry.Analytic.SaturatedDomainPreimage

/-! # Actual domain base change in the localized analytic category -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y Z : LocalizedCategory.{u, v, w} (K := K)}

/-- The inverse image of an actual analytic domain under an arbitrary
localized morphism is an analytic domain. -/
theorem isOriginalChartDomain_preimage (f : X ⟶ Y)
    (D : (presentationOf Y).AnalyticDomain) :
    (presentationOf X).presentation.atlas.IsOriginalChartDomain
      (localizedSpaceFunctor.map f ⁻¹' D.carrier) := by
  have h := SourceCategory.isOriginalChartDomain_preimage
    (sourceHomEquiv.symm f) D
  change (presentationOf X).presentation.atlas.IsOriginalChartDomain
    (localizedSpaceFunctor.map (sourceHomEquiv (sourceHomEquiv.symm f)) ⁻¹' D.carrier) at h
  have he : sourceHomEquiv (sourceHomEquiv.symm f) = f :=
    (sourceHomEquiv (A := presentationOf X) (B := presentationOf Y)).apply_symm_apply f
  rw [he] at h
  exact h

/-- Base change uses the literal inverse-image subset and its proved domain
structure, rather than a supplied representative of that subset. -/
def domainPreimage (f : X ⟶ Y) (D : (presentationOf Y).AnalyticDomain) :
    (presentationOf X).AnalyticDomain :=
  ⟨localizedSpaceFunctor.map f ⁻¹' D.carrier, isOriginalChartDomain_preimage f D⟩

@[simp]
theorem mem_domainPreimage (f : X ⟶ Y) (D : (presentationOf Y).AnalyticDomain)
    (x : localizedSpaceFunctor.obj X) :
    x ∈ domainPreimage f D ↔ localizedSpaceFunctor.map f x ∈ D := Iff.rfl

@[simp]
theorem domainPreimage_id (D : (presentationOf X).AnalyticDomain) :
    domainPreimage (𝟙 X) D = D := by
  ext x
  change localizedSpaceFunctor.map (𝟙 X) x ∈ D.carrier ↔ x ∈ D.carrier
  have hx := congrArg
    (fun k : localizedSpaceFunctor.obj X ⟶ localizedSpaceFunctor.obj X => k x)
    (localizedSpaceFunctor.map_id X)
  exact (congrArg (fun y => y ∈ D.carrier) hx).to_iff

@[simp]
theorem domainPreimage_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (D : (presentationOf Z).AnalyticDomain) :
    domainPreimage (f ≫ g) D = domainPreimage f (domainPreimage g D) := by
  ext x
  change localizedSpaceFunctor.map (f ≫ g) x ∈ D.carrier ↔
    localizedSpaceFunctor.map g (localizedSpaceFunctor.map f x) ∈ D.carrier
  rw [Functor.map_comp]
  rfl

@[simp]
theorem domainPreimage_inf (f : X ⟶ Y)
    (D E : (presentationOf Y).AnalyticDomain) :
    domainPreimage f (D ⊓ E) = domainPreimage f D ⊓ domainPreimage f E := by
  ext x
  rfl

@[simp]
theorem domainPreimage_top (f : X ⟶ Y) :
    domainPreimage f ⊤ = ⊤ := by
  ext x
  rfl

@[simp]
theorem domainPreimage_bot (f : X ⟶ Y) :
    domainPreimage f ⊥ = ⊥ := by
  ext x
  rfl

/-- Inverse image is monotone in actual domain inclusion. -/
def domainPreimageOrderHom (f : X ⟶ Y) :
    (presentationOf Y).AnalyticDomain →o (presentationOf X).AnalyticDomain where
  toFun := domainPreimage f
  monotone' _ _ h _ hx := h hx

/-- The analytic map from the literal inverse image to the target domain. -/
def domainPreimageMap (f : X ⟶ Y) (D : (presentationOf Y).AnalyticDomain) :
    domainObj X (domainPreimage f D) ⟶ domainObj Y D :=
  domainRestrict (domainPreimage f D) D f (fun _ hx => hx)

@[reassoc (attr := simp)]
theorem domainPreimageMap_comp_inclusion (f : X ⟶ Y)
    (D : (presentationOf Y).AnalyticDomain) :
    domainPreimageMap f D ≫ domainι Y D = domainι X (domainPreimage f D) ≫ f :=
  domainRestrict_comp _ _ _ _

@[simp]
theorem val_domainPreimageMap_apply (f : X ⟶ Y)
    (D : (presentationOf Y).AnalyticDomain)
    (x : localizedSpaceFunctor.obj (domainObj X (domainPreimage f D))) :
    (localizedSpaceFunctor.map (domainPreimageMap f D) x).val =
      localizedSpaceFunctor.map f x.val := by
  have h := congrArg
    (fun k : domainObj X (domainPreimage f D) ⟶ Y => localizedSpaceFunctor.map k x)
    (domainPreimageMap_comp_inclusion f D)
  simp only [Functor.map_comp, TopCat.comp_app, domainι_apply] at h
  exact h

/-- A commuting cone has its first leg in the literal inverse-image subset. -/
theorem image_mem_domainPreimage (f : X ⟶ Y)
    (D : (presentationOf Y).AnalyticDomain) (a : Z ⟶ X) (b : Z ⟶ domainObj Y D)
    (h : a ≫ f = b ≫ domainι Y D) :
    ∀ z, localizedSpaceFunctor.map a z ∈ domainPreimage f D := by
  intro z
  have hz := congrArg (fun k : Z ⟶ Y => localizedSpaceFunctor.map k z) h
  rw [Functor.map_comp, Functor.map_comp, TopCat.comp_app, TopCat.comp_app,
    domainι_apply] at hz
  change localizedSpaceFunctor.map f (localizedSpaceFunctor.map a z) ∈ D
  rw [hz]
  exact (localizedSpaceFunctor.map b z).property

/-- The universal analytic arrow into the inverse-image domain. -/
def domainPreimageLift (f : X ⟶ Y) (D : (presentationOf Y).AnalyticDomain)
    (a : Z ⟶ X) (b : Z ⟶ domainObj Y D) (h : a ≫ f = b ≫ domainι Y D) :
    Z ⟶ domainObj X (domainPreimage f D) :=
  domainLift (domainPreimage f D) a (image_mem_domainPreimage f D a b h)

@[reassoc (attr := simp)]
theorem domainPreimageLift_fst (f : X ⟶ Y) (D : (presentationOf Y).AnalyticDomain)
    (a : Z ⟶ X) (b : Z ⟶ domainObj Y D) (h : a ≫ f = b ≫ domainι Y D) :
    domainPreimageLift f D a b h ≫ domainι X (domainPreimage f D) = a :=
  domainLift_comp _ _ _

@[reassoc (attr := simp)]
theorem domainPreimageLift_snd (f : X ⟶ Y) (D : (presentationOf Y).AnalyticDomain)
    (a : Z ⟶ X) (b : Z ⟶ domainObj Y D) (h : a ≫ f = b ≫ domainι Y D) :
    domainPreimageLift f D a b h ≫ domainPreimageMap f D = b := by
  apply (cancel_mono (domainι Y D)).1
  rw [Category.assoc, domainPreimageMap_comp_inclusion, ← Category.assoc,
    domainPreimageLift_fst]
  exact h

/-- The actual inverse-image object and its two analytic projection maps. -/
def domainPreimageCone (f : X ⟶ Y) (D : (presentationOf Y).AnalyticDomain) :
    PullbackCone f (domainι Y D) :=
  PullbackCone.mk (domainι X (domainPreimage f D)) (domainPreimageMap f D)
    (domainPreimageMap_comp_inclusion f D).symm

/-- The constructed cone is a limit against all localized test objects. -/
def domainPreimageIsLimit (f : X ⟶ Y) (D : (presentationOf Y).AnalyticDomain) :
    IsLimit (domainPreimageCone f D) :=
  PullbackCone.IsLimit.mk (domainPreimageMap_comp_inclusion f D).symm
    (fun c => domainPreimageLift f D c.fst c.snd c.condition)
    (fun c => domainPreimageLift_fst f D c.fst c.snd c.condition)
    (fun c => domainPreimageLift_snd f D c.fst c.snd c.condition)
    (fun c _m hm _ => (cancel_mono (domainι X (domainPreimage f D))).1
      (hm.trans (domainPreimageLift_fst f D c.fst c.snd c.condition).symm))

/-- Analytic domain inclusions admit actual base change along arbitrary
localized analytic morphisms, realized by the literal inverse-image domain. -/
theorem domainPreimage_isPullback (f : X ⟶ Y) (D : (presentationOf Y).AnalyticDomain) :
    IsPullback (domainι X (domainPreimage f D)) (domainPreimageMap f D) f (domainι Y D) where
  w := (domainPreimageMap_comp_inclusion f D).symm
  isLimit' := ⟨domainPreimageIsLimit f D⟩

/-- An isomorphism induces an order isomorphism on actual analytic domains,
contravariantly by inverse image. -/
def domainPreimageOrderIso (e : X ≅ Y) :
    (presentationOf Y).AnalyticDomain ≃o (presentationOf X).AnalyticDomain where
  toFun := domainPreimage e.hom
  invFun := domainPreimage e.inv
  left_inv D := by
    rw [← domainPreimage_comp, e.inv_hom_id, domainPreimage_id]
  right_inv D := by
    rw [← domainPreimage_comp, e.hom_inv_id, domainPreimage_id]
  map_rel_iff' := by
    intro D E
    constructor
    · intro h
      have hi : domainPreimage e.inv (domainPreimage e.hom D) ≤
          domainPreimage e.inv (domainPreimage e.hom E) :=
        (domainPreimageOrderHom e.inv).monotone h
      simpa only [← domainPreimage_comp, e.inv_hom_id, domainPreimage_id] using hi
    · exact fun h _ hx => h hx

end Langlands.Analytic.SaturatedAtlasPresentation
