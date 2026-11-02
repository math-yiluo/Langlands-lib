import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCovering
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartTerminal
import Mathlib.CategoryTheory.Sites.Point.Basic

/-! # Actual spectrum points and stalks on the finite rational chart site -/

noncomputable section

universe u vE uE uC

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits Opposite

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}

/-- The fiber of a chart over an actual base-spectrum point is its
proposition of membership, regarded as a type. -/
def pointFiber (x : BanachSpectrum A) : RationalChart K A ⥤ Type u where
  obj d := ULift.{u} (PLift (x ∈ d.locus))
  map f := TypeCat.ofHom fun hx => ⟨⟨f.subset hx.down.down⟩⟩
  map_id _ := by
    ext hx
    rfl
  map_comp _ _ := by
    ext hx
    rfl

instance (x : BanachSpectrum A) (d : RationalChart K A) :
    Subsingleton ((pointFiber x).obj d) := by
  change Subsingleton (ULift.{u} (PLift (x ∈ d.locus)))
  infer_instance

/-- Membership is the actual fiber of the constructed structural spectrum map. -/
def spectrumFiberEquiv (x : BanachSpectrum A) (d : RationalChart K A) :
    (pointFiber x).obj d ≃ {y : BanachSpectrum d.algebra // d.spectrumMap y = x} where
  toFun hx := ⟨d.locusHomeomorph.symm ⟨x, hx.down.down⟩,
    congrArg Subtype.val (d.locusHomeomorph.apply_symm_apply _)⟩
  invFun y := ⟨⟨by
    rw [← y.property]
    exact (d.locusHomeomorph y.val).property⟩⟩
  left_inv _ := Subsingleton.elim _ _
  right_inv y := by
    apply Subtype.ext
    apply d.locusHomeomorph.injective
    apply Subtype.ext
    exact (congrArg Subtype.val (d.locusHomeomorph.apply_symm_apply _)).trans y.property.symm

/-- The comparison retains the original bounded spectrum restriction. -/
theorem spectrumFiberEquiv_naturality (x : BanachSpectrum A)
    {d e : RationalChart K A} (f : d ⟶ e) (hx : (pointFiber x).obj d) :
    (spectrumFiberEquiv x e ((pointFiber x).map f hx)).val =
      f.spectrumMap (spectrumFiberEquiv x d hx).val := by
  apply e.locusHomeomorph.injective
  apply Subtype.ext
  change e.spectrumMap _ = e.spectrumMap _
  rw [f.spectrumMap_over_base]
  exact (spectrumFiberEquiv x e ((pointFiber x).map f hx)).property.trans
    (spectrumFiberEquiv x d hx).property.symm

/-- Charts containing the point, with their original bounded restrictions. -/
abbrev PointNeighborhood (x : BanachSpectrum A) :=
  (pointFiber x).Elements

instance (x : BanachSpectrum A) (d e : PointNeighborhood x) :
    Subsingleton (d ⟶ e) :=
  ⟨fun _ _ => Functor.Elements.hom_ext
    (@Subsingleton.elim (Restriction d.obj e.obj) inferInstance _ _)⟩

variable [CompleteSpace K]

/-- Actual rational intersections refine any two charts through the point. -/
instance pointNeighborhood_isCofiltered (x : BanachSpectrum A) :
    IsCofiltered (PointNeighborhood x) where
  nonempty := ⟨Functor.elementsMk _ (whole K A) ⟨⟨by simp⟩⟩⟩
  cone_objs d e :=
    ⟨Functor.elementsMk _ (d.obj.inter e.obj)
      ⟨⟨by rw [locus_inter]; exact ⟨d.val.down.down, e.val.down.down⟩⟩⟩,
      Functor.Elements.homMk (interLeft d.obj e.obj) (Subsingleton.elim _ _),
      Functor.Elements.homMk (interRight d.obj e.obj) (Subsingleton.elim _ _), trivial⟩
  cone_maps {X Y} f g := ⟨X, 𝟙 X, Subsingleton.elim _ _⟩

/-- Membership in actual rational loci defines a point of the finite-covering
site. Cover lifting is proved from the covering sieve's finite family. -/
def spectrumPoint (x : BanachSpectrum A) :
    GrothendieckTopology.Point.{u} (finiteRationalTopology K A) where
  fiber := pointFiber x
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR hx := by
    obtain ⟨I, _, D, f, hf, hcover⟩ := hR
    obtain ⟨i, hi⟩ := hcover x hx.down.down
    exact ⟨D i, f i, hf i, ⟨⟨hi⟩⟩, Subsingleton.elim _ _⟩

variable (E : Type uE) [Category.{vE} E] [HasColimitsOfSize.{u, u} E]

/-- The actual filtered neighborhood colimit of a coefficient presheaf. -/
abbrev presheafStalk (x : BanachSpectrum A) :
    ((RationalChart K A)ᵒᵖ ⥤ E) ⥤ E :=
  (spectrumPoint x).presheafFiber

/-- The same stalk functor restricted to sheaves on the finite rational site. -/
abbrev stalk (x : BanachSpectrum A) :
    CategoryTheory.Sheaf (finiteRationalTopology K A) E ⥤ E :=
  (spectrumPoint x).sheafFiber

variable {E}

/-- The germ map from a chart containing the chosen spectrum point. -/
def germ (x : BanachSpectrum A) (d : RationalChart K A) (hx : x ∈ d.locus)
    (F : (RationalChart K A)ᵒᵖ ⥤ E) :
    F.obj (op d) ⟶ (presheafStalk E x).obj F :=
  (spectrumPoint x).toPresheafFiber d ⟨⟨hx⟩⟩ F

@[reassoc (attr := simp)]
theorem germ_restriction (x : BanachSpectrum A) {d e : RationalChart K A}
    (f : d ⟶ e) (hx : x ∈ d.locus) (F : (RationalChart K A)ᵒᵖ ⥤ E) :
    F.map f.op ≫ germ x d hx F = germ x e (f.subset hx) F :=
  (spectrumPoint x).toPresheafFiber_w f ⟨⟨hx⟩⟩ F

@[reassoc (attr := simp)]
theorem germ_naturality (x : BanachSpectrum A) (d : RationalChart K A)
    (hx : x ∈ d.locus) {F G : (RationalChart K A)ᵒᵖ ⥤ E} (f : F ⟶ G) :
    germ x d hx F ≫ (presheafStalk E x).map f =
      f.app (op d) ≫ germ x d hx G :=
  (spectrumPoint x).toPresheafFiber_naturality f d ⟨⟨hx⟩⟩

/-- All chart germ maps jointly determine a map out of the stalk. -/
@[ext]
theorem presheafStalk_hom_ext (x : BanachSpectrum A)
    {F : (RationalChart K A)ᵒᵖ ⥤ E} {T : E}
    {f g : (presheafStalk E x).obj F ⟶ T}
    (h : ∀ (d : RationalChart K A) (hx : x ∈ d.locus),
      germ x d hx F ≫ f = germ x d hx F ≫ g) : f = g :=
  (spectrumPoint x).presheafFiber_hom_ext (fun d hx => h d hx.down.down)

/-- Compatible maps from all point-containing charts descend to the stalk. -/
def presheafStalkDesc (x : BanachSpectrum A)
    {F : (RationalChart K A)ᵒᵖ ⥤ E} {T : E}
    (φ : ∀ (d : RationalChart K A) (_ : x ∈ d.locus), F.obj (op d) ⟶ T)
    (hφ : ∀ {d e : RationalChart K A} (f : d ⟶ e) (hx : x ∈ d.locus),
      F.map f.op ≫ φ d hx = φ e (f.subset hx)) :
    (presheafStalk E x).obj F ⟶ T :=
  (spectrumPoint x).presheafFiberDesc (fun d hx => φ d hx.down.down)
    (fun {_ _} f hx => hφ f hx.down.down)

@[reassoc (attr := simp)]
theorem germ_presheafStalkDesc (x : BanachSpectrum A)
    {F : (RationalChart K A)ᵒᵖ ⥤ E} {T : E}
    (φ : ∀ (d : RationalChart K A) (_ : x ∈ d.locus), F.obj (op d) ⟶ T)
    (hφ : ∀ {d e : RationalChart K A} (f : d ⟶ e) (hx : x ∈ d.locus),
      F.map f.op ≫ φ d hx = φ e (f.subset hx))
    (d : RationalChart K A) (hx : x ∈ d.locus) :
    germ x d hx F ≫ presheafStalkDesc x φ hφ = φ d hx :=
  (spectrumPoint x).toPresheafFiber_presheafFiberDesc _ _ d ⟨⟨hx⟩⟩

/-- The stalk is the colimit over the original charts containing the point. -/
def stalkCocone (x : BanachSpectrum A) (F : (RationalChart K A)ᵒᵖ ⥤ E) :
    Cocone ((Functor.Elements.π (pointFiber x)).op ⋙ F) :=
  (spectrumPoint x).presheafFiberCocone F

/-- The displayed germ cocone has the actual colimit universal property. -/
def stalkCoconeIsColimit (x : BanachSpectrum A)
    (F : (RationalChart K A)ᵒᵖ ⥤ E) :
    IsColimit (stalkCocone x F) :=
  (spectrumPoint x).isColimitPresheafFiberCocone F

variable (E)

instance (x : BanachSpectrum A) [HasFiniteLimits E] [AB5OfSize.{u, u} E] :
    PreservesFiniteLimits (presheafStalk E x) := by
  infer_instance

instance (x : BanachSpectrum A) [HasFiniteLimits E] [AB5OfSize.{u, u} E] :
    PreservesFiniteLimits (stalk E x) := by
  infer_instance

section Concrete

variable {E} {FC : E → E → Type*} {CC : E → Type uC}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{uC} E FC]
  [PreservesFilteredColimitsOfSize.{u, u} (forget E)]

/-- Every stalk element has a section representative on an actual chart
containing the spectrum point. -/
theorem germ_jointly_surjective (x : BanachSpectrum A)
    (F : (RationalChart K A)ᵒᵖ ⥤ E) (s : ToType ((presheafStalk E x).obj F)) :
    ∃ (d : RationalChart K A) (hx : x ∈ d.locus) (t : ToType (F.obj (op d))),
      germ x d hx F t = s := by
  obtain ⟨d, hx, t, ht⟩ := (spectrumPoint x).toPresheafFiber_jointly_surjective s
  exact ⟨d, hx.down.down, t, ht⟩

/-- Equality of germs from one chart is witnessed by an actual bounded
restriction from a chart through the same spectrum point. -/
theorem germ_eq_iff (x : BanachSpectrum A) (d : RationalChart K A)
    (hx : x ∈ d.locus) (F : (RationalChart K A)ᵒᵖ ⥤ E)
    (s t : ToType (F.obj (op d))) :
    germ x d hx F s = germ x d hx F t ↔
      ∃ (e : RationalChart K A) (f : e ⟶ d) (_ : x ∈ e.locus),
        F.map f.op s = F.map f.op t := by
  constructor
  · intro h
    obtain ⟨e, f, he, _, heq⟩ :=
      ((spectrumPoint x).toPresheafFiber_eq_iff' d ⟨⟨hx⟩⟩ s t).mp h
    exact ⟨e, f, he.down.down, heq⟩
  · rintro ⟨e, f, he, heq⟩
    exact ((spectrumPoint x).toPresheafFiber_eq_iff' d ⟨⟨hx⟩⟩ s t).mpr
      ⟨e, f, ⟨⟨he⟩⟩, rfl, heq⟩

end Concrete

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
