import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleGerms
import Langlands.Sheaf.Equivariant.TwistedGlobalSections

/-! # Germ cohomology through neighbourhood cohomology -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.PointGerms

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v

section Homology

variable {R : Type w} [Ring R] {ι : Type*} {c : ComplexShape ι}

/-- A cycle has zero homology class exactly when it is a boundary. -/
theorem homologyπ_apply_eq_zero_iff (L : HomologicalComplex (ModuleCat.{w} R) c) (n : ι)
    (y : L.cycles n) :
    L.homologyπ n y = 0 ↔ ∃ x : L.X (c.prev n), L.d (c.prev n) n x = L.iCycles n y := by
  constructor
  · intro h
    have h₁ := ShortComplex.π_moduleCatCyclesIso_hom_apply (L.sc n) y
    have h₂ : (L.sc n).homologyπ y = 0 := h
    rw [h₂, map_zero] at h₁
    obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).1 h₁.symm
    refine ⟨x, ?_⟩
    have h₄ := congrArg Subtype.val hx
    have h₅ := ShortComplex.moduleCatCyclesIso_hom_i_apply (L.sc n) y
    exact h₄.trans h₅
  · rintro ⟨x, hx⟩
    have hy : y = L.toCycles (c.prev n) n x := by
      apply (ModuleCat.mono_iff_injective (L.iCycles n)).1 inferInstance
      rw [← hx, ← ConcreteCategory.comp_apply, L.toCycles_i]
    rw [hy, ← ConcreteCategory.comp_apply, L.toCycles_comp_homologyπ]
    rfl

/-- The homology class of a cycle dies under a morphism of complexes exactly when the
image of the cycle is a boundary. -/
theorem homologyMap_homologyπ_apply_eq_zero_iff
    {L L' : HomologicalComplex (ModuleCat.{w} R) c} (φ : L ⟶ L') (n : ι) (y : L.cycles n) :
    HomologicalComplex.homologyMap φ n (L.homologyπ n y) = 0 ↔
      ∃ x : L'.X (c.prev n), L'.d (c.prev n) n x = φ.f n (L.iCycles n y) := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, homologyπ_apply_eq_zero_iff,
    ← ConcreteCategory.comp_apply (HomologicalComplex.cyclesMap φ n),
    HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]

/-- Every element killed by the outgoing differential is a cycle. -/
theorem exists_iCycles_eq (L : HomologicalComplex (ModuleCat.{w} R) c) (n : ι) (z : L.X n)
    (hz : L.d n (c.next n) z = 0) : ∃ y : L.cycles n, L.iCycles n y = z := by
  refine ⟨(L.sc n).moduleCatCyclesIso.inv ⟨z, hz⟩, ?_⟩
  exact ShortComplex.moduleCatCyclesIso_inv_iCycles_apply (L.sc n) ⟨z, hz⟩

/-- A cycle is killed by the outgoing differential. -/
theorem d_iCycles_apply (L : HomologicalComplex (ModuleCat.{w} R) c) (n : ι) (y : L.cycles n) :
    L.d n (c.next n) (L.iCycles n y) = 0 := by
  rw [← ConcreteCategory.comp_apply, L.iCycles_d]
  rfl

end Homology

section Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : J.Point.{w})
  {R : Type w} [Ring R] {ι : Type*} {c : ComplexShape ι}

/-- The complex of sections over `X` of a complex of presheaves. -/
abbrev sectionsComplex (K : HomologicalComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) c) (X : C) :
    HomologicalComplex (ModuleCat.{w} R) c :=
  (((evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (op X)).mapHomologicalComplex c).obj K

/-- Restriction of section complexes along `f : Y ⟶ X`. -/
abbrev sectionsComplexMap (K : HomologicalComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) c) {X Y : C}
    (f : Y ⟶ X) : sectionsComplex K X ⟶ sectionsComplex K Y :=
  (NatTrans.mapHomologicalComplex ((evaluation Cᵒᵖ (ModuleCat.{w} R)).map f.op) c).app K

/-- The complex of germs at a point of a complex of presheaves. -/
abbrev germComplex (K : HomologicalComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) c) :
    HomologicalComplex (ModuleCat.{w} R) c :=
  (Φ.presheafFiber.mapHomologicalComplex c).obj K

/-- Germs may be computed after restriction to a smaller element of the fibre. -/
theorem toPresheafFiber_eq_of_hom {X Y : C} {x : Φ.fiber.obj X} {y : Φ.fiber.obj Y}
    (f : Y ⟶ X) (h : Φ.fiber.map f y = x) (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (p : P.obj (op X)) :
    Φ.toPresheafFiber X x P p = Φ.toPresheafFiber Y y P (P.map f.op p) := by
  subst h
  exact (Φ.toPresheafFiber_w_apply f y P p).symm

/-- Naturality of a morphism of presheaves of modules, elementwise. -/
theorem app_map_apply {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (g : P ⟶ Q) {X Y : C} (f : Y ⟶ X)
    (p : P.obj (op X)) : g.app (op Y) (P.map f.op p) = Q.map f.op (g.app (op X) p) := by
  rw [← ConcreteCategory.comp_apply, g.naturality, ConcreteCategory.comp_apply]

variable [LocallySmall.{w} C]

/-- The germ complex at a point is exact in degree `n` exactly when every cycle of degree
`n` over a neighbourhood of the point becomes a boundary over a smaller neighbourhood. -/
theorem germComplex_exactAt_iff (K : HomologicalComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) c) (n : ι) :
    (germComplex Φ K).ExactAt n ↔
      ∀ (X : C) (x : Φ.fiber.obj X) (z : (K.X n).obj (op X)),
        (K.d n (c.next n)).app (op X) z = 0 →
        ∃ (Y : C) (f : Y ⟶ X) (y : Φ.fiber.obj Y) (w : (K.X (c.prev n)).obj (op Y)),
          Φ.fiber.map f y = x ∧ (K.d (c.prev n) n).app (op Y) w = (K.X n).map f.op z := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff]
  constructor
  · intro hex X x z hz
    obtain ⟨w', hw'⟩ := hex (Φ.toPresheafFiber X x (K.X n) z) (by
      change Φ.presheafFiber.map (K.d n (c.next n)) (Φ.toPresheafFiber X x (K.X n) z) = 0
      rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply, hz, map_zero])
    change Φ.presheafFiber.map (K.d (c.prev n) n) w' = _ at hw'
    obtain ⟨X', x', w₀, rfl⟩ := Φ.toPresheafFiber_jointly_surjective w'
    rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply] at hw'
    let e₁ : Φ.fiber.Elements := Φ.fiber.elementsMk X x
    let e₂ : Φ.fiber.Elements := Φ.fiber.elementsMk X' x'
    let g₁ := IsCofiltered.minToLeft e₁ e₂
    let g₂ := IsCofiltered.minToRight e₁ e₂
    rw [toPresheafFiber_eq_of_hom Φ g₂.1 g₂.2, toPresheafFiber_eq_of_hom Φ g₁.1 g₁.2,
      GrothendieckTopology.Point.toPresheafFiber_eq_iff'] at hw'
    obtain ⟨Y, f, y, hy, hf⟩ := hw'
    refine ⟨Y, f ≫ g₁.1, y, (K.X (c.prev n)).map (f ≫ g₂.1).op w₀, ?_, ?_⟩
    · rw [Φ.fiber.map_comp, types_comp_apply, hy]
      exact g₁.2
    · rw [app_map_apply, op_comp, (K.X n).map_comp, ConcreteCategory.comp_apply, hf,
        op_comp, (K.X n).map_comp, ConcreteCategory.comp_apply]
  · intro h g hg
    obtain ⟨X, x, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective g
    change Φ.presheafFiber.map (K.d n (c.next n)) (Φ.toPresheafFiber X x (K.X n) z) = 0 at hg
    rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
      ← map_zero (ConcreteCategory.hom (Φ.toPresheafFiber X x (K.X (c.next n)))),
      GrothendieckTopology.Point.toPresheafFiber_eq_iff'] at hg
    obtain ⟨Y, f, y, hy, hf⟩ := hg
    rw [map_zero, ← app_map_apply] at hf
    obtain ⟨Y', f', y', w, hy', hw⟩ := h Y y ((K.X n).map f.op z) hf
    refine ⟨Φ.toPresheafFiber Y' y' (K.X (c.prev n)) w, ?_⟩
    change Φ.presheafFiber.map (K.d (c.prev n) n)
      (Φ.toPresheafFiber Y' y' (K.X (c.prev n)) w) = _
    rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply, hw,
      ← toPresheafFiber_eq_of_hom Φ f' hy', ← toPresheafFiber_eq_of_hom Φ f hy]

/-- The germ complex at a point is exact in degree `n` exactly when every degree-`n`
cohomology class over a neighbourhood of the point dies over a smaller neighbourhood. -/
theorem germComplex_exactAt_iff_homology
    (K : HomologicalComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) c) (n : ι) :
    (germComplex Φ K).ExactAt n ↔
      ∀ (X : C) (x : Φ.fiber.obj X) (a : (sectionsComplex K X).homology n),
        ∃ (Y : C) (f : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map f y = x ∧
          HomologicalComplex.homologyMap (sectionsComplexMap K f) n a = 0 := by
  rw [germComplex_exactAt_iff]
  constructor
  · intro h X x a
    obtain ⟨y₀, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((sectionsComplex K X).homologyπ n)).1 inferInstance a
    obtain ⟨Y, f, y, w, hy, hw⟩ :=
      h X x ((sectionsComplex K X).iCycles n y₀) (d_iCycles_apply _ n y₀)
    exact ⟨Y, f, y, hy, (homologyMap_homologyπ_apply_eq_zero_iff _ n y₀).2 ⟨w, hw⟩⟩
  · intro h X x z hz
    obtain ⟨y₀, hy₀⟩ := exists_iCycles_eq (sectionsComplex K X) n z hz
    obtain ⟨Y, f, y, hy, ha⟩ := h X x ((sectionsComplex K X).homologyπ n y₀)
    obtain ⟨w, hw⟩ := (homologyMap_homologyπ_apply_eq_zero_iff _ n y₀).1 ha
    refine ⟨Y, f, y, w, hy, ?_⟩
    rw [← hy₀]
    exact hw

end Point

end Langlands.Cohomology.PointGerms

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (R : Type w) [CommRing R]

/-- Restriction of sections along `f : V ⟶ U`, as a natural transformation of section
functors on module sheaves. -/
def sheafSectionsRestriction {U V : C} (f : V ⟶ U) :
    sheafSectionsModule J R U ⟶ sheafSectionsModule J R V :=
  Functor.whiskerLeft (sheafToPresheaf J (ModuleCat.{w} R))
    ((CategoryTheory.evaluation Cᵒᵖ (ModuleCat.{w} R)).map f.op)

variable [HasSheafify J (ModuleCat.{w} R)] [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]

/-- Restriction of cohomology along `f : V ⟶ U`: the right derived natural transformation
of restriction of sections. -/
def sectionsDerivedMap {U V : C} (f : V ⟶ U) (q : ℕ) :
    sectionsDerived J R U q ⟶ sectionsDerived J R V q :=
  NatTrans.rightDerived (sheafSectionsRestriction J R f) q

end Langlands.Sheaf.Equivariant.TwistedOver

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Cohomology.PointGerms

universe u v uL

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Germ cohomology at an ordinary point vanishes exactly when every cohomology class over
an open neighbourhood of the point dies on a smaller open neighbourhood. -/
theorem isZero_etaleUnderlyingGermCohomology_iff (y : localizedSpaceFunctor.obj X) (q : ℕ)
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) :
    haveI := etale_hasSheafify.{u, v, uL} X R
    haveI := etale_enoughInjectives.{u, v, uL} X R
    IsZero ((etaleUnderlyingGermCohomology.{u, v, uL} X R y q).obj F) ↔
      ∀ (U : Opens (localizedSpaceFunctor.obj X)), y ∈ U →
        ∀ a : (sectionsDerived (etaleTopology X) R (openEtaleObject X U) q).obj F,
          ∃ (V : Opens (localizedSpaceFunctor.obj X)) (h : V ≤ U), y ∈ V ∧
            (sectionsDerivedMap (etaleTopology X) R (openEtaleMap X (homOfLE h)) q).app F a =
              0 := by
  have := etale_hasSheafify.{u, v, uL} X R
  have := underlyingTopology_hasSheafify.{u, v, uL} X R
  have := etale_enoughInjectives.{u, v, uL} X R
  have : (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).Additive :=
    etaleUnderlyingSheaf_additive.{u, v, uL} X R
  let Φ := underlyingTopologyPoint.{u, v, uL} X y
  let P := Φ.sheafFiber (A := ModuleCat.{max u (v + 1) uL} R)
  have : P.Additive := Functor.additive_of_preserves_binary_products P
  let I := injectiveResolution F
  let L := ((sheafToPresheaf _ (ModuleCat.{max u (v + 1) uL} R)).mapHomologicalComplex _).obj
    (((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).mapHomologicalComplex _).obj
      I.cocomplex)
  have hgerm : IsZero ((etaleUnderlyingGermCohomology.{u, v, uL} X R y q).obj F) ↔
      (germComplex Φ L).ExactAt q := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact Iso.isZero_iff (I.isoRightDerivedObj
      (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R) ⋙ P) q)
  rw [hgerm, germComplex_exactAt_iff_homology]
  let hsec : ∀ (U : Opens (localizedSpaceFunctor.obj X)),
      (sectionsDerived (etaleTopology X) R (openEtaleObject X U) q).obj F ≅
        (sectionsComplex L U).homology q := fun U =>
    I.isoRightDerivedObj (sheafSectionsModule (etaleTopology X) R (openEtaleObject X U)) q
  have hmap : ∀ {U V : Opens (localizedSpaceFunctor.obj X)} (f : V ⟶ U),
      (sectionsDerivedMap (etaleTopology X) R (openEtaleMap X f) q).app F =
        (hsec U).hom ≫ HomologicalComplex.homologyMap (sectionsComplexMap L f) q ≫
          (hsec V).inv := fun f =>
    InjectiveResolution.rightDerived_app_eq
      (sheafSectionsRestriction (etaleTopology X) R (openEtaleMap X f)) I q
  constructor
  · intro h U hy a
    obtain ⟨V, f, ⟨⟨hV⟩⟩, -, ha⟩ := h U ⟨⟨hy⟩⟩ ((hsec U).hom a)
    refine ⟨V, leOfHom f, hV, ?_⟩
    rw [show homOfLE (leOfHom f) = f from rfl, hmap, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, ha, map_zero]
  · intro h U x a
    obtain ⟨⟨hy⟩⟩ := x
    obtain ⟨V, hVU, hV, ha⟩ := h U hy ((hsec U).inv a)
    refine ⟨V, homOfLE hVU, ⟨⟨hV⟩⟩, rfl, ?_⟩
    rw [hmap] at ha
    have ha' := congrArg (hsec V).hom ha
    rw [map_zero, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply (hsec V).inv (hsec V).hom, Iso.inv_hom_id,
      ← ConcreteCategory.comp_apply (hsec U).inv (hsec U).hom, Iso.inv_hom_id] at ha'
    exact ha'

end Langlands.Sheaf.Equivariant.Analytic
