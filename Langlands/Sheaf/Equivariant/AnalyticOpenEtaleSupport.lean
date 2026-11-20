import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleRestriction
import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleRestriction.GlobalSections
import Langlands.Sheaf.Equivariant.AnalyticEtaleCompactGeometry

/-! # Ordinary-open germs and actual analytic étale support -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v uL

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointSupport

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))

/-- The canonical arrow of an actual open domain to the identity étale object. -/
def openEtaleToSelf (U : Opens (localizedSpaceFunctor.obj X)) :
    openEtaleObject X U ⟶ etaleSelf X :=
  OpenEtaleRestriction.openEtaleToSelf X (etaleOpenDomainStatement X) U

/-- The full open analytic domain is canonically the original identity object. -/
def openEtaleTopIso : openEtaleObject X ⊤ ≅ etaleSelf X :=
  OpenEtaleRestriction.openEtaleTopIso X (etaleOpenDomainStatement X)

/-- Ordinary restriction retains the original global section module. -/
def etaleUnderlyingGlobalIso {A : Type*} [Category A] (F : Sheaf (etaleTopology X) A) :
    F.obj.obj (op (etaleSelf X)) ≅
      ((etaleUnderlyingSheaf X A).obj F).obj.obj (op ⊤) :=
  OpenEtaleRestriction.etaleUnderlyingGlobalIso X (etaleOpenDomainStatement X) F

/-- Restriction of the global comparison is the original étale restriction. -/
theorem etaleUnderlyingGlobalIso_restrict
    {R : Type (max u (v + 1) uL)} [CommRing R]
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (U : Opens (localizedSpaceFunctor.obj X))
    (s : F.obj.obj (op (etaleSelf X))) :
    ((etaleUnderlyingSheaf X (ModuleCat R)).obj F).obj.map
        (homOfLE le_top : U ⟶ ⊤).op ((etaleUnderlyingGlobalIso X F).hom s) =
      F.obj.map (openEtaleToSelf X U).op s := by
  simpa only [ModuleCat.comp_apply] using!
    congrArg (fun f => f s)
      (OpenEtaleRestriction.etaleUnderlyingGlobalIso_restrict X (etaleOpenDomainStatement X) F U)

/-- The usual ordinary-topology point, with its fiber universe lifted to the
coefficient universe rather than identified with the space universe. -/
def underlyingTopologyPoint (y : localizedSpaceFunctor.obj X) :
    (Opens.grothendieckTopology (localizedSpaceFunctor.obj X)).Point.{max u (v + 1) uL} where
  fiber.obj U := ULift.{max u (v + 1) uL} (PLift (y ∈ U))
  fiber.map f := ↾fun h => ⟨⟨leOfHom f h.down.down⟩⟩
  isCofiltered :=
    { nonempty := ⟨.mk (obj := ⊤) ⟨⟨by simp⟩⟩⟩
      cone_objs U V := by
        induction U with | @mk U hU
        induction V with | @mk V hV
        obtain ⟨⟨hU⟩⟩ := hU
        obtain ⟨⟨hV⟩⟩ := hV
        exact ⟨.mk (obj := U ⊓ V) ⟨⟨hU, hV⟩⟩,
          Functor.Elements.homMk (homOfLE inf_le_left) rfl,
          Functor.Elements.homMk (homOfLE inf_le_right) rfl, trivial⟩
      cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    rintro U S hS ⟨⟨hy⟩⟩
    obtain ⟨V, f, hf, hV⟩ := hS y hy
    exact ⟨V, f, hf, ⟨⟨hV⟩⟩, rfl⟩

variable {X}
variable {R : Type (max u (v + 1) uL)} [CommRing R]

/-- A global ordinary-open germ vanishes exactly on some open neighborhood. -/
theorem not_mem_support_underlyingTopologyPoint_iff
    (P : (Opens (localizedSpaceFunctor.obj X))ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (s : P.obj (op ⊤)) (y : localizedSpaceFunctor.obj X) :
    y ∉ support (underlyingTopologyPoint.{u, v, uL} X) P s ↔
      ∃ U : Opens (localizedSpaceFunctor.obj X), y ∈ U ∧
        P.map (homOfLE le_top : U ⟶ ⊤).op s = 0 := by
  let p : (underlyingTopologyPoint.{u, v, uL} X y).fiber.obj ⊤ := ⟨⟨trivial⟩⟩
  constructor
  · intro hy
    have hz : (underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber ⊤ p P s =
        (underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber ⊤ p P 0 := by
      rw [map_zero]
      by_contra hn
      exact hy ⟨p, hn⟩
    obtain ⟨U, f, q, _, hq⟩ :=
      ((underlyingTopologyPoint.{u, v, uL} X y).toPresheafFiber_eq_iff' _ _ s 0).mp hz
    exact ⟨U, q.down.down, by
      simpa only [show f = (homOfLE le_top : U ⟶ ⊤) from Subsingleton.elim _ _, map_zero]
        using hq⟩
  · rintro ⟨U, hyU, hz⟩ ⟨q, hq⟩
    let r : (underlyingTopologyPoint.{u, v, uL} X y).fiber.obj U := ⟨⟨hyU⟩⟩
    have hr : (underlyingTopologyPoint.{u, v, uL} X y).fiber.map (homOfLE le_top : U ⟶ ⊤) r = q := by
      apply ULift.ext
      exact Subsingleton.elim _ _
    apply hq
    rw [← hr, ← GrothendieckTopology.Point.toPresheafFiber_w_apply, hz, map_zero]

/-- Vanishing after an étale map descends to its entire open image. -/
theorem restriction_open_image_eq_zero
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (s : F.obj.obj (op (etaleSelf X))) (U : EtaleSite X) (f : U ⟶ etaleSelf X)
    (hz : F.obj.map f.op s = 0) :
    let V : Opens (localizedSpaceFunctor.obj X) :=
      ⟨Set.range (localizedSpaceFunctor.map U.hom), (etaleOpenMap K U.hom U.prop).isOpen_range⟩
    F.obj.map (openEtaleToSelf X V).op s = 0 := by
  let V : Opens (localizedSpaceFunctor.obj X) :=
    ⟨Set.range (localizedSpaceFunctor.map U.hom), (etaleOpenMap K U.hom U.prop).isOpen_range⟩
  let k : U ⟶ openEtaleObject X V := openEtaleLift X V U (fun y => ⟨y, rfl⟩)
  have hksurj : Function.Surjective (localizedSpaceFunctor.map k.left) := by
    intro y
    obtain ⟨z, hz⟩ := y.property
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact (val_domainLift_apply
      ((presentationOf X).openDomain (V : Set (localizedSpaceFunctor.obj X)) V.isOpen)
      U.hom (fun y => ⟨y, rfl⟩) z).trans hz
  have hfac : k ≫ openEtaleToSelf X V = f := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (𝟙 X)).1
    exact (MorphismProperty.Over.w (k ≫ openEtaleToSelf X V)).trans
      (MorphismProperty.Over.w f).symm
  have hkzero : F.obj.map k.op (F.obj.map (openEtaleToSelf X V).op s) = 0 := by
    rw [← ModuleCat.comp_apply, ← F.obj.map_comp, ← op_comp, hfac]
    exact hz
  let S : Sieve (openEtaleObject X V) :=
    { arrows := fun _ a => ∃ b, b ≫ k = a
      downward_closed := by
        rintro W W' a ⟨b, rfl⟩ c
        exact ⟨c ≫ b, Category.assoc _ _ _⟩ }
  have hS : S ∈ etaleTopology X (openEtaleObject X V) := by
    apply mem_etaleTopology_of_jointlySurjective
    intro y
    obtain ⟨z, hz⟩ := hksurj y
    exact ⟨U, k, ⟨𝟙 U, Category.id_comp _⟩, z, hz⟩
  apply isSeparated_of_isSheaf F.property hS
  rintro W _ ⟨b, rfl⟩
  rw [op_comp, F.obj.map_comp, ModuleCat.comp_apply, hkzero, map_zero, map_zero]

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable [T2Space (localizedSpaceFunctor.obj X)]

/-- The germ support on ordinary opens is exactly the existing underlying
analytic étale support, retaining the actual global-section identification. -/
theorem support_etaleUnderlyingGlobalIso
    (hX : Function.Surjective (pointProjection L X))
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (s : F.obj.obj (op (etaleSelf X))) :
    support (underlyingTopologyPoint.{u, v, uL} X)
        ((etaleUnderlyingSheaf X (ModuleCat R)).obj F).obj
        ((etaleUnderlyingGlobalIso X F).hom s) =
      etaleUnderlyingSupport L h F.obj s := by
  ext y
  apply not_iff_not.mp
  rw [not_mem_support_underlyingTopologyPoint_iff.{u, v, uL},
    not_mem_etaleUnderlyingSupport_iff L h
      (etalePointLifting_of_hausdorff L h) hX]
  constructor
  · rintro ⟨U, hyU, hz⟩
    refine ⟨openEtaleObject X U, openEtaleToSelf X U, ?_, ?_⟩
    · exact ⟨⟨y, hyU⟩, domainι_apply _ _⟩
    · rwa [etaleUnderlyingGlobalIso_restrict.{u, v, uL}] at hz
  · rintro ⟨U, f, hy, hz⟩
    let V : Opens (localizedSpaceFunctor.obj X) :=
      ⟨Set.range (localizedSpaceFunctor.map U.hom), (etaleOpenMap K U.hom U.prop).isOpen_range⟩
    refine ⟨V, hy, ?_⟩
    rw [etaleUnderlyingGlobalIso_restrict.{u, v, uL}]
    exact restriction_open_image_eq_zero.{u, v, uL} F s U f hz

/-- Ordinary-topology compact sections, using the existing point-support
construction with the standard ordinary points in the coefficient universe. -/
def underlyingTopologyCompactSections :
    TopCat.Sheaf (ModuleCat.{max u (v + 1) uL} R) (localizedSpaceFunctor.obj X) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  sheafCompactSections (Opens.grothendieckTopology (localizedSpaceFunctor.obj X))
    (underlyingTopologyPoint.{u, v, uL} X) R ⊤

/-- The actual global comparison preserves and reflects compact support. -/
theorem isCompactlySupported_etaleUnderlyingGlobalIso_iff
    (hX : Function.Surjective (pointProjection L X))
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
    (s : F.obj.obj (op (etaleSelf X))) :
    letI := pointTopology L X
    IsCompactlySupported (underlyingTopologyPoint.{u, v, uL} X)
        ((etaleUnderlyingSheaf X (ModuleCat R)).obj F).obj
        ((etaleUnderlyingGlobalIso X F).hom s) ↔
      IsCompactlySupported (etalePoints L h) F.obj s := by
  let := pointTopology L X
  change (∃ C, IsCompact C ∧
    support (underlyingTopologyPoint.{u, v, uL} X)
      ((etaleUnderlyingSheaf X (ModuleCat R)).obj F).obj
      ((etaleUnderlyingGlobalIso X F).hom s) ⊆ C) ↔ _
  rw [support_etaleUnderlyingGlobalIso L h hX]
  exact (exists_isCompact_superset_iff_of_surjective L hX
    (support (etalePoints L h) F.obj s)).symm

/-- The original global-section comparison restricted to the actual compact
submodules. -/
def etaleUnderlyingCompactMap
    (hX : Function.Surjective (pointProjection L X)) :
    etaleCompactSections L h R ⟶
      etaleUnderlyingSheaf X (ModuleCat R) ⋙ underlyingTopologyCompactSections.{u, v, uL} (X := X) (R := R) := by
  let := pointTopology L X
  refine
    { app := fun F => ModuleCat.ofHom (((etaleUnderlyingGlobalIso X F).hom).hom.restrict
        (fun s hs => (isCompactlySupported_etaleUnderlyingGlobalIso_iff L h hX F s).2 hs))
      naturality := ?_ }
  intro F F' f
  ext s
  apply Subtype.ext
  exact (ConcreteCategory.congr_hom
    (f.hom.naturality (openEtaleToSelf X ⊤).op) s.val).symm

/-- The compact global comparison is invertible under the geometric support
hypotheses, independently of any cohomological comparison. -/
theorem isIso_etaleUnderlyingCompactMap
    (hX : Function.Surjective (pointProjection L X)) :
    IsIso (etaleUnderlyingCompactMap L h hX (R := R)) := by
  let := pointTopology L X
  have : ∀ F, IsIso ((etaleUnderlyingCompactMap L h hX (R := R)).app F) := by
    intro F
    let e := (etaleUnderlyingGlobalIso X F).toLinearEquiv
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro s t hst
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val hst)
    · intro t
      have hs : IsCompactlySupported (etalePoints L h) F.obj (e.symm t.val) :=
        (isCompactlySupported_etaleUnderlyingGlobalIso_iff L h hX F (e.symm t.val)).1 (by
          change IsCompactlySupported (underlyingTopologyPoint.{u, v, uL} X)
            ((etaleUnderlyingSheaf X (ModuleCat R)).obj F).obj (e (e.symm t.val))
          rw [e.apply_symm_apply]
          exact t.property)
      exact ⟨⟨e.symm t.val, hs⟩, Subtype.ext (e.apply_symm_apply t.val)⟩
  exact NatIso.isIso_of_isIso_app _

/-- The natural identification of actual étale compact sections with compact
sections of the ordinary restriction, using its actual ordinary point germs. -/
def etaleUnderlyingCompactIso
    (hX : Function.Surjective (pointProjection L X)) :
    etaleCompactSections L h R ≅
      etaleUnderlyingSheaf X (ModuleCat R) ⋙ underlyingTopologyCompactSections.{u, v, uL} (X := X) (R := R) :=
  haveI := isIso_etaleUnderlyingCompactMap L h hX (R := R)
  asIso (etaleUnderlyingCompactMap L h hX (R := R))

end Langlands.Sheaf.Equivariant.Analytic
