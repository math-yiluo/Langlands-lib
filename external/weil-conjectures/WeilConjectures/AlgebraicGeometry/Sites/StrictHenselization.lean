/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Pointed étale neighbourhoods and the strict henselization

Let `s : Spec Ω ⟶ S` be a geometric point of a scheme `S`, that is, `Ω` is a separably closed
field. A *pointed étale neighbourhood* of `s` is an étale `S`-scheme `V` together with a lift
`Spec Ω ⟶ V` of `s`; these form the category of elements of the fibre functor of Mathlib's
point `AlgebraicGeometry.Scheme.pointSmallEtale s` of the small étale site of `S`.

In this file we show that the affine pointed étale neighbourhoods are initial among all pointed
étale neighbourhoods, define the strict henselization `𝒪^{sh}_{S,s}` as the colimit of the rings
of global sections of the affine pointed étale neighbourhoods, and show that its spectrum, the
strict localization `S_(s)`, is the limit of the affine pointed étale neighbourhoods, both as a
scheme and as a scheme over `S`. Base change along any morphism `X ⟶ S` commutes with this limit.

Finally we record that the stalk functor of abelian sheaves on the small étale site at a
geometric point is exact.

## Main definitions

- `AlgebraicGeometry.Scheme.PointedEtaleNeighborhood s`: the category of pointed étale
  neighbourhoods of `s`.
- `AlgebraicGeometry.Scheme.AffinePointedEtaleNeighborhood s`: its full subcategory of affine
  pointed étale neighbourhoods.
- `AlgebraicGeometry.Scheme.strictHenselization s`: the ring `colim Γ(V, 𝒪_V)` over the affine
  pointed étale neighbourhoods `V` of `s`.
- `AlgebraicGeometry.Scheme.strictLocalization s`: its spectrum `S_(s)`.
- `AlgebraicGeometry.Scheme.strictLocalizationCone s`: the cone over the affine pointed étale
  neighbourhoods with point `S_(s)`, and `strictLocalizationConeOver s`, the same over `S`.
- `AlgebraicGeometry.Scheme.geometricStalkFunctor s A`: the stalk functor at `s`.

## Main results

- `AlgebraicGeometry.Scheme.AffinePointedEtaleNeighborhood.initial_ι`: affine pointed étale
  neighbourhoods are initial.
- `AlgebraicGeometry.Scheme.isLimitStrictLocalizationCone`: `S_(s)` is the limit of the affine
  pointed étale neighbourhoods.
- `AlgebraicGeometry.Scheme.isLimitStrictLocalizationConePullback`: `X ×_S S_(s)` is the limit
  of the `X ×_S V`.
- `AlgebraicGeometry.Scheme.preservesFiniteLimits_geometricStalkFunctor`,
  `AlgebraicGeometry.Scheme.preservesFiniteColimits_geometricStalkFunctor`: geometric stalks of
  abelian étale sheaves are exact.

## Implementation details

No quasi-compactness or quasi-separatedness of `f` is needed in
`AlgebraicGeometry.Scheme.isLimitStrictLocalizationConePullback`: base change
`Over S ⥤ Over X` is a right adjoint and `Over X ⥤ Scheme` creates connected limits.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The category of pointed étale neighbourhoods of a geometric point `s: Spec Ω ⟶ S`: its
objects are pairs `(V, v)` of an étale `S`-scheme `V` and a morphism `v: Spec Ω ⟶ V` over `S`,
and its morphisms `(V, v) ⟶ (W, w)` are the `S`-morphisms `V ⟶ W` carrying `v` to `w`. This is
the category of elements of the fibre functor of the point `pointSmallEtale s` of the small
étale site, the same category as `AlgebraicGeometry.Scheme.Hom.Nbhd s`. -/
abbrev PointedEtaleNeighborhood : Type (u + 1) :=
  (pointSmallEtale s).fiber.Elements

namespace PointedEtaleNeighborhood

/-- The property of a pointed étale neighbourhood `(V, v)` that `V` is affine. -/
def isAffine : ObjectProperty (PointedEtaleNeighborhood s) :=
  fun x ↦ IsAffine x.1.left

/-- The pointed étale neighbourhood `(S, s)`; it is a terminal object. -/
noncomputable def base : PointedEtaleNeighborhood s :=
  Functor.elementsMk _ (Etale.mk (𝟙 S)) (CategoryTheory.Over.homMk s (by simp))

/-- The structure morphism of a pointed étale neighbourhood, as a morphism to `base s`. -/
noncomputable def toBase (x : PointedEtaleNeighborhood s) : x ⟶ base s :=
  Functor.Elements.homMk (MorphismProperty.Over.homMk x.1.hom (Category.comp_id _)) (by
    obtain @⟨X, x⟩ := x
    exact CategoryTheory.Over.OverMorphism.ext (CategoryTheory.Over.w x))

/-- The pointed étale neighbourhood `(S, s)` is terminal. -/
noncomputable def isTerminalBase : IsTerminal (base s) :=
  IsTerminal.ofUniqueHom (toBase s) fun x f ↦ by
    apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact f.hom.w.trans (Category.comp_id _)

/-- Every pointed étale neighbourhood `(V, v)` is refined by the spectrum of a ring with an
étale morphism to `S`: take an affine open of `V` containing the image of `v`. -/
lemma exists_precomp_hom (d : PointedEtaleNeighborhood s) :
    ∃ c, Nonempty ((Functor.Elements.precomp (AffineEtale.Spec S)
      (pointSmallEtale s).fiber).obj c ⟶ d) := by
  obtain @⟨X, x⟩ := d
  cases X with | _ Y f
  obtain ⟨y, hy, rfl⟩ := CategoryTheory.Over.homMk_surjective x
  dsimp at y hy
  obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec (.of R) ⟶ Y)
      (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
    obtain ⟨R, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
      (x := y.base default) (U := ⊤) (by simp)
    refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  exact ⟨Functor.elementsMk _ (AffineEtale.mk (j ≫ f)) (CategoryTheory.Over.homMk y'),
    ⟨⟨MorphismProperty.Over.homMk j rfl (by simp), by cat_disch⟩⟩⟩

lemma isAffine_precomp_obj
    (c : (AffineEtale.Spec S ⋙ (pointSmallEtale s).fiber).Elements) :
    isAffine s ((Functor.Elements.precomp (AffineEtale.Spec S)
      (pointSmallEtale s).fiber).obj c) := by
  exact inferInstanceAs (IsAffine (Spec _))

end PointedEtaleNeighborhood

/-- The full subcategory of affine pointed étale neighbourhoods of `s`. -/
abbrev AffinePointedEtaleNeighborhood : Type (u + 1) :=
  (PointedEtaleNeighborhood.isAffine s).FullSubcategory

namespace AffinePointedEtaleNeighborhood

/-- The inclusion of the affine pointed étale neighbourhoods into all pointed étale
neighbourhoods. -/
noncomputable abbrev ι : AffinePointedEtaleNeighborhood s ⥤ PointedEtaleNeighborhood s :=
  (PointedEtaleNeighborhood.isAffine s).ι

instance (x : AffinePointedEtaleNeighborhood s) : IsAffine x.obj.1.left := x.2

/-- The refinement of a pointed étale neighbourhood by an affine one. -/
lemma exists_hom (d : PointedEtaleNeighborhood s) :
    ∃ c : AffinePointedEtaleNeighborhood s, Nonempty ((ι s).obj c ⟶ d) := by
  obtain ⟨c, ⟨f⟩⟩ := PointedEtaleNeighborhood.exists_precomp_hom s d
  exact ⟨⟨_, PointedEtaleNeighborhood.isAffine_precomp_obj s c⟩, ⟨f⟩⟩

/-- **Affine pointed étale neighbourhoods are cofinal**: the inclusion of the full subcategory
of affine pointed étale neighbourhoods is initial, hence cofinal for the opposite-indexed stalk
colimits. -/
instance initial_ι : (ι s).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ (exists_hom s)

instance : IsCofiltered (AffinePointedEtaleNeighborhood s) :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful (ι s) (exists_hom s)

instance : InitiallySmall.{u} (AffinePointedEtaleNeighborhood s) :=
  initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
    (ObjectProperty.lift _ (Functor.Elements.precomp (AffineEtale.Spec S)
      (pointSmallEtale s).fiber) (PointedEtaleNeighborhood.isAffine_precomp_obj s)).essImage
    (fun d ↦ by
      obtain ⟨c, ⟨f⟩⟩ := PointedEtaleNeighborhood.exists_precomp_hom s d.obj
      exact ⟨_, ⟨c, ⟨Iso.refl _⟩⟩, ⟨ObjectProperty.homMk f⟩⟩)

end AffinePointedEtaleNeighborhood

/-- The underlying scheme of a pointed étale neighbourhood. -/
noncomputable def neighborhoodDiagram : PointedEtaleNeighborhood s ⥤ Scheme.{u} :=
  Functor.Elements.π _ ⋙ Etale.forget S ⋙ CategoryTheory.Over.forget S

/-- The underlying scheme of an affine pointed étale neighbourhood. -/
noncomputable def affineNeighborhoodDiagram : AffinePointedEtaleNeighborhood s ⥤ Scheme.{u} :=
  AffinePointedEtaleNeighborhood.ι s ⋙ neighborhoodDiagram s

instance (x : AffinePointedEtaleNeighborhood s) :
    IsAffine ((affineNeighborhoodDiagram s).obj x) :=
  x.2

/-- The diagram `(V, v) ↦ Γ(V, 𝒪_V)` of rings of the affine pointed étale neighbourhoods of
`s`, indexed by the opposite category so that the restriction maps point forward. -/
noncomputable def strictHenselizationDiagram :
    (AffinePointedEtaleNeighborhood s)ᵒᵖ ⥤ CommRingCat.{u} :=
  (affineNeighborhoodDiagram s).op ⋙ Scheme.Γ

instance : HasColimitsOfShape (AffinePointedEtaleNeighborhood s)ᵒᵖ CommRingCat.{u} :=
  hasColimitsOfShape_of_finallySmall _ _

/-- The **strict henselization** `𝒪^{sh}_{S,s} = colim Γ(V, 𝒪_V)` of `S` at the geometric
point `s`, the colimit over the affine pointed étale neighbourhoods `(V, v)` of `s`. -/
noncomputable def strictHenselization : CommRingCat.{u} :=
  colimit (strictHenselizationDiagram s)

/-- The **strict localization** `S_(s) = Spec 𝒪^{sh}_{S,s}` of `S` at the geometric point `s`. -/
noncomputable abbrev strictLocalization : Scheme.{u} :=
  Spec (strictHenselization s)

/-- An affine scheme is the spectrum of its global sections, naturally: the affine pointed étale
neighbourhoods are the spectra of the rings in `strictHenselizationDiagram s`. -/
noncomputable def affineNeighborhoodDiagramIso :
    affineNeighborhoodDiagram s ≅ (strictHenselizationDiagram s).rightOp ⋙ Scheme.Spec :=
  NatIso.ofComponents (fun x ↦ asIso ((affineNeighborhoodDiagram s).obj x).toSpecΓ)
    (fun _ ↦ Scheme.toSpecΓ_naturality _)

/-- The cone over the affine pointed étale neighbourhoods of `s` with point the strict
localization `S_(s)`, with legs `S_(s) ⟶ Spec Γ(V, 𝒪_V) ≅ V`. -/
noncomputable def strictLocalizationCone : Cone (affineNeighborhoodDiagram s) :=
  (Cone.postcompose (affineNeighborhoodDiagramIso s).inv).obj
    (Scheme.Spec.mapCone (coneRightOpOfCocone (colimit.cocone (strictHenselizationDiagram s))))

lemma strictLocalizationCone_pt : (strictLocalizationCone s).pt = strictLocalization s := rfl


lemma strictLocalizationCone_π_app (x : AffinePointedEtaleNeighborhood s) :
    (strictLocalizationCone s).π.app x =
      Spec.map (colimit.ι (strictHenselizationDiagram s) (op x)) ≫
        inv ((affineNeighborhoodDiagram s).obj x).toSpecΓ :=
  rfl

/-- **The strict localization is the limit of the affine pointed étale neighbourhoods**: the
anti-equivalence between affine schemes and rings carries the colimit cocone defining the strict
henselization to a limit cone `S_(s) ≅ lim V`. -/
noncomputable def isLimitStrictLocalizationCone : IsLimit (strictLocalizationCone s) :=
  (IsLimit.postcomposeInvEquiv (affineNeighborhoodDiagramIso s) _).symm
    (isLimitOfPreserves Scheme.Spec
      (isLimitConeRightOpOfCocone _ (colimit.isColimit (strictHenselizationDiagram s))))

/-- The cone of `strictLocalizationCone s` extended to all pointed étale neighbourhoods. -/
noncomputable def strictLocalizationConeAll : Cone (neighborhoodDiagram s) :=
  (Functor.Initial.extendCone (F := AffinePointedEtaleNeighborhood.ι s)).obj
    (strictLocalizationCone s)

/-- The strict localization is also the limit of all pointed étale neighbourhoods. -/
noncomputable def isLimitStrictLocalizationConeAll : IsLimit (strictLocalizationConeAll s) :=
  (Functor.Initial.isLimitExtendConeEquiv _ _).symm (isLimitStrictLocalizationCone s)

/-- The structure morphism `S_(s) ⟶ S` of the strict localization: the leg of the limit cone at
the terminal pointed étale neighbourhood `(S, s)`. -/
noncomputable def strictLocalizationToBase : strictLocalization s ⟶ S :=
  (strictLocalizationConeAll s).π.app (PointedEtaleNeighborhood.base s)

@[reassoc (attr := simp)]
lemma strictLocalizationCone_π_app_hom (x : AffinePointedEtaleNeighborhood s) :
    (strictLocalizationCone s).π.app x ≫ x.obj.1.hom = strictLocalizationToBase s :=
  (Functor.Initial.extendCone_obj_π_app' (F := AffinePointedEtaleNeighborhood.ι s) _
    (PointedEtaleNeighborhood.toBase s ((AffinePointedEtaleNeighborhood.ι s).obj x))).symm

/-- The diagram of affine pointed étale neighbourhoods of `s`, as schemes over `S`. -/
noncomputable def affineNeighborhoodDiagramOver :
    AffinePointedEtaleNeighborhood s ⥤ CategoryTheory.Over S :=
  AffinePointedEtaleNeighborhood.ι s ⋙ Functor.Elements.π _ ⋙ Etale.forget S

/-- The strict localization `S_(s)` as a cone over the affine pointed étale neighbourhoods of
`s` in the category of schemes over `S`. -/
noncomputable def strictLocalizationConeOver : Cone (affineNeighborhoodDiagramOver s) where
  pt := CategoryTheory.Over.mk (strictLocalizationToBase s)
  π :=
    { app x := CategoryTheory.Over.homMk ((strictLocalizationCone s).π.app x)
        (strictLocalizationCone_π_app_hom s x)
      naturality x y f := by
        ext
        dsimp
        rw [Category.id_comp]
        exact ((strictLocalizationCone s).w f).symm }

/-- **The strict localization is the limit of the affine pointed étale neighbourhoods over
`S`.** -/
noncomputable def isLimitStrictLocalizationConeOver : IsLimit (strictLocalizationConeOver s) :=
  have := IsCofiltered.isConnected (AffinePointedEtaleNeighborhood s)
  isLimitOfReflects (CategoryTheory.Over.forget S)
    ((isLimitStrictLocalizationCone s).ofIsoLimit (Cone.ext (Iso.refl _)))

/-- **Base change commutes with the neighbourhood limit**: for any morphism `f: X ⟶ S`, the
fibre product `S_(s) ×_S X` is the limit of the fibre products `V ×_S X` over the affine pointed
étale neighbourhoods `(V, v)` of `s`. The cone is the image of `strictLocalizationConeOver s`
under base change along `f`, whose point is `pullback (strictLocalizationToBase s) f`. -/
noncomputable def isLimitStrictLocalizationConePullback {X : Scheme.{u}} (f : X ⟶ S) :
    IsLimit ((CategoryTheory.Over.forget X).mapCone
      ((CategoryTheory.Over.pullback f).mapCone (strictLocalizationConeOver s))) :=
  have := IsCofiltered.isConnected (AffinePointedEtaleNeighborhood s)
  isLimitOfPreserves (CategoryTheory.Over.forget X)
    (isLimitOfPreserves (CategoryTheory.Over.pullback f) (isLimitStrictLocalizationConeOver s))

/-- The point of the cone of `isLimitStrictLocalizationConePullback` is the fibre product
`S_(s) ×_S X`. -/
lemma isLimitStrictLocalizationConePullback_pt {X : Scheme.{u}} (f : X ⟶ S) :
    ((CategoryTheory.Over.forget X).mapCone
      ((CategoryTheory.Over.pullback f).mapCone (strictLocalizationConeOver s))).pt =
      pullback (strictLocalizationToBase s) f :=
  rfl


section Stalk

variable (A : Type*) [Category A] [HasColimitsOfSize.{u, u} A]

/-- Geometric stalks

The **geometric stalk** functor `F ↦ F_s = colim F(U)` at a geometric point `s` of `S`, the
colimit running over the opposite of the category of pointed étale neighbourhoods `(U, u)`
of `s`. This is the fibre functor on sheaves of Mathlib's point `pointSmallEtale s` of the
small étale site. -/
noncomputable abbrev geometricStalkFunctor : Sheaf S.smallEtaleTopology A ⥤ A :=
  (pointSmallEtale s).sheafFiber

/-- The geometric stalk `F_s` is the colimit of the sections `F(U)` over the pointed étale
neighbourhoods `(U, u)` of `s`. -/
noncomputable def isColimitGeometricStalk (F : Sheaf S.smallEtaleTopology A) :
    IsColimit ((pointSmallEtale s).presheafFiberCocone F.obj) :=
  (pointSmallEtale s).isColimitPresheafFiberCocone F.obj

/-- **Geometric stalks are left exact.** -/
instance preservesFiniteLimits_geometricStalkFunctor :
    PreservesFiniteLimits (geometricStalkFunctor s AddCommGrpCat.{u}) :=
  inferInstance

/-- **Geometric stalks are right exact.** -/
instance preservesFiniteColimits_geometricStalkFunctor :
    PreservesFiniteColimits (geometricStalkFunctor s AddCommGrpCat.{u}) :=
  inferInstance

/-- **Exactness of geometric stalks**: the stalk functor `Ab(S_ét) ⥤ Ab` at a geometric point
carries short exact sequences of abelian étale sheaves to short exact sequences. -/
theorem shortExact_map_geometricStalkFunctor
    {T : ShortComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})} (hT : T.ShortExact) :
    (T.map (geometricStalkFunctor s AddCommGrpCat.{u})).ShortExact :=
  hT.map_of_exact _


end Stalk

end AlgebraicGeometry.Scheme
