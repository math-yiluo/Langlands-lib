/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Cospecialization
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.StalkZeroLocus
public import WeilConjectures.Algebra.Category.ModuleCat.FinitePresentationColimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Finite.Stalk
public import WeilConjectures.Topology.SpectralSpace.Constructible

/-!
# A specialization criterion for local constancy

Let `Y` be a locally noetherian scheme, `Λ` a noetherian ring and `G` a constructible sheaf of
`Λ`-modules on the small étale site of `Y`. Suppose that for every geometric point `s` of `Y`
and every geometric point `t` of the strict localization `Y_(s)` the cospecialization map
`G_s ⟶ G_t` (`AlgebraicGeometry.Scheme.cospecializationMap`) is bijective. Then `G` is finite
locally constant
(`AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_of_bijective_cospecializationMap`,
[SGA 4, Exp. IX, 2.11], [Stacks, Tag 0GJ2]).

The proof follows the classical argument. Fix a point `y` of `Y` and the geometric point `s`
over it with values in an algebraic closure of `κ(y)`. The stalk `M = G_s` is finitely
presented, so the identity of `M` spreads out to a linear map `α : M ⟶ G(V)` for a pointed
étale neighbourhood `(V, v)` of `s`, which we may take affine
(`ModuleCat.exists_lift_of_isColimit_of_finitePresentation`). Through the pullback `g^* G`
along `g : V ⟶ Y`, `α` is adjoint to a morphism `φ : M_V ⟶ g^* G` from the constant sheaf at
`M` (`AlgebraicGeometry.Scheme.constantSheafSpread`). Its stalk at a geometric point `r` of `V`
is, through `(g^* G)_r ≅ G_{r ≫ g}`, the germ of `α` at `(V, r)`
(`AlgebraicGeometry.Scheme.isIso_sheafFiber_map_constantSheafSpread`). A point `w` of
`V` generizing the image of `v` is the image of a point of `Y_(s)`
(`AlgebraicGeometry.Scheme.exists_strictLocalizationConeAll_π_app_base_eq`); at the
corresponding geometric point the stalk of `φ` is the cospecialization map, which is bijective.
So the kernel and cokernel of `φ`, constructible sheaves on the noetherian scheme `V`, have
vanishing stalks at all generizations of the image of `v`; since their vanishing loci are open
in the constructible topology, they contain an open neighbourhood `W` of that point
(`exists_specializes_of_isClosed_constructibleTopology_of_mem_closure`). On `W` the morphism
`φ` is an isomorphism, so `G` is constant on `W`, an étale neighbourhood of `y`.

## Main results

- `AlgebraicGeometry.Scheme.exists_etale_isConstant_upperStar_of_bijective_cospecializationMap`:
  every point of `Y` has an étale neighbourhood on which `G` is constant.
- `AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_of_bijective_cospecializationMap`:
  the criterion.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite Topology

noncomputable section

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Germ

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {R T : Scheme.{u}} (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology A)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- On stalks, the unit `G ⟶ t_* t^* G` followed by restriction to a geometric point `s` of `T`
and the identification `(t^* G)_s ≅ G_{s ≫ t}` is the identity. -/
lemma sheafFiber_map_unit_stalkRestrict_upperStarCompSheafFiberIso_hom
    (s : Spec (.of Ω) ⟶ T) :
    (pointSmallEtale (s ≫ t)).sheafFiber.map
        ((upperStarLowerStarAdjunction A t).unit.app G) ≫
      Etale.stalkRestrict A t (s ≫ t) ⟨s, rfl⟩ ((t)^*[A].obj G) ≫
      (upperStarCompSheafFiberIso A t s).hom.app G = 𝟙 _ := by
  rw [Etale.stalkRestrict_eq_counit]
  have h := (upperStarCompSheafFiberIso A t s).inv.naturality
    ((upperStarLowerStarAdjunction A t).unit.app G)
  simp only [Category.assoc]
  rw [reassoc_of% h]
  rw [← Functor.map_comp_assoc, Adjunction.left_triangle_components,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

/-- The section of `t^* G` over an étale `T`-scheme `V` pulled back from `G` along a morphism
`φ : V ⟶ U` over `t` to an étale `R`-scheme `U`, as a morphism `G(U) ⟶ (t^* G)(V)`: the unit
`G ⟶ t_* t^* G` at `U`, followed by restriction along `V ⟶ U ×_R T`. -/
def upperStarSectionHom {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) :
    G.obj.obj (op U) ⟶ ((t)^*[A].obj G).obj.obj (op V) :=
  ((upperStarLowerStarAdjunction A t).unit.app G).hom.app (op U) ≫
    ((t)^*[A].obj G).obj.map (homToPullback t φ hφ).op

/-- A point `v` over `s` of an étale `T`-scheme `V`, followed by a morphism `φ : V ⟶ U` over `t`
to an étale `R`-scheme `U`, lies over `s ≫ t`. -/
lemma left_comp_comp_hom_eq {s : Spec (.of Ω) ⟶ T} {V : T.Etale} {U : R.Etale}
    {φ : V.left ⟶ U.left} (hφ : φ ≫ U.hom = V.hom ≫ t) (v : (pointSmallEtale s).fiber.obj V) :
    (v.left ≫ φ) ≫ U.hom = s ≫ t := by
  have hv : v.left ≫ V.hom = s := CategoryTheory.Over.w v
  rw [Category.assoc, hφ, reassoc_of% hv]

/-- The germ of a pulled back section `φ^* g` at a geometric point `v` of `V` is the germ of `g`
at `v ≫ φ`, through the identification `(t^* G)_s ≅ G_{s ≫ t}`. -/
lemma upperStarSectionHom_toPresheafFiber_upperStarCompSheafFiberIso_hom
    (s : Spec (.of Ω) ⟶ T) {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) (v : (pointSmallEtale s).fiber.obj V) :
    upperStarSectionHom A t G φ hφ ≫
        (pointSmallEtale s).toPresheafFiber V v ((t)^*[A].obj G).obj ≫
        (upperStarCompSheafFiberIso A t s).hom.app G =
      (pointSmallEtale (s ≫ t)).toPresheafFiber U
        (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (s ≫ t))
          (V := (Etale.forget R).obj U) (v.left ≫ φ) (left_comp_comp_hom_eq t hφ v)) G.obj := by
  set u : (pointSmallEtale (s ≫ t)).fiber.obj U := CategoryTheory.Over.homMk
    (U := CategoryTheory.Over.mk (s ≫ t)) (V := (Etale.forget R).obj U) (v.left ≫ φ)
    (left_comp_comp_hom_eq t hφ v)
  have hv : v.left ≫ V.hom = s := CategoryTheory.Over.w v
  have e : (pointSmallEtale s).fiber.map (homToPullback t φ hφ) v =
      ((Etale.baseChangeNbhd t (s ≫ t) ⟨s, rfl⟩).obj (Functor.elementsMk _ U u)).2 := by
    refine CategoryTheory.Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · change (v.left ≫ (homToPullback t φ hφ).left) ≫ _ = _
      simp [u, Scheme.Hom.basePt]
    · change (v.left ≫ (homToPullback t φ hφ).left) ≫ _ = _
      simp [u, Scheme.Hom.basePt, hv]
  rw [upperStarSectionHom, Category.assoc,
    GrothendieckTopology.Point.toPresheafFiber_w_assoc, e]
  erw [← Etale.toPresheafFiber_stalkRestrict_assoc A t (s ≫ t) ⟨s, rfl⟩ ((t)^*[A].obj G)
    (Functor.elementsMk _ U u)]
  erw [← GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
  erw [sheafFiber_map_unit_stalkRestrict_upperStarCompSheafFiberIso_hom A t G s]
  exact Category.comp_id _

end Germ

section ConstantStalk

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- The stalk at a geometric point `r` of the morphism `M_X ⟶ H` from a constant sheaf adjoint
to `α : M ⟶ Γ(X, H)` is, through an identification of the stalk of `M_X` with `M`, the germ
of `α` at `r`. -/
lemma exists_sheafFiber_map_constantSheafAdj_homEquiv_symm {T : X.Etale} (hT : IsTerminal T)
    (M : ModuleCat.{u + 1} Λ) (H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (α : M ⟶ H.obj.obj (op T)) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (r : Spec (.of Ω) ⟶ X) (x : (pointSmallEtale r).fiber.obj T) :
    ∃ e : (pointSmallEtale r).sheafFiber.obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≅ M,
      e.inv ≫ (pointSmallEtale r).sheafFiber.map
          (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).homEquiv M H).symm
            α) = α ≫ (pointSmallEtale r).toPresheafFiber T x H.obj := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  set ψ := ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).homEquiv M H).symm α
  have hψ : (CategoryTheory.toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj M)).app (op T) ≫ ψ.hom.app (op T) = α := by
    rw [← constantSheafAdj_homEquiv_apply, Equiv.apply_symm_apply]
  refine ⟨(pointSmallEtale r).sheafFiberConstantSheafIso M, ?_⟩
  have hinv : ((pointSmallEtale r).presheafFiberConstIso M).inv =
      (pointSmallEtale r).toPresheafFiber T x ((Functor.const X.Etaleᵒᵖ).obj M) :=
    ((Iso.comp_hom_eq_id _).1
      ((pointSmallEtale r).toPresheafFiber_presheafFiberConstIso_hom M T x)).symm
  dsimp only [GrothendieckTopology.Point.sheafFiberConstantSheafIso, Iso.trans_inv, Iso.symm_inv,
    asIso_hom]
  rw [hinv, Category.assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  rw [← Category.assoc]
  exact congrArg (· ≫ (pointSmallEtale r).toPresheafFiber T x H.obj) hψ

end ConstantStalk

end Etale

namespace Scheme

section Spread

variable {Λ : Type (u + 1)} [CommRing Λ] {S : Scheme.{u}}

/-- **Spreading out a finitely presented stalk.** If the stalk `G_s` of a sheaf of modules at a
geometric point `s` is finitely presented, the identity of `G_s` factors through the sections
of `G` over some affine pointed étale neighbourhood of `s`. -/
lemma exists_comp_toPresheafFiber_eq_id (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
    [Module.FinitePresentation Λ
      (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G)] :
    ∃ (c : AffinePointedEtaleNeighborhood s)
      (α : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G ⟶
        G.obj.obj (op c.obj.1)),
      α ≫ (pointSmallEtale s).toPresheafFiber c.obj.1 c.obj.2 G.obj = 𝟙 _ := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨j, α, hα⟩ := ModuleCat.exists_lift_of_isColimit_of_finitePresentation
    (isColimitGeometricStalk s (ModuleCat.{u + 1} Λ) G)
    (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) LinearMap.id
  obtain ⟨c, ⟨f⟩⟩ := AffinePointedEtaleNeighborhood.exists_hom s j.unop
  refine ⟨c, ModuleCat.ofHom α ≫ G.obj.map f.1.op, ?_⟩
  have hw : G.obj.map f.1.op ≫ (pointSmallEtale s).toPresheafFiber c.obj.1 c.obj.2 G.obj =
      (pointSmallEtale s).toPresheafFiber j.unop.1 j.unop.2 G.obj := by
    refine ((pointSmallEtale s).toPresheafFiber_w f.1 c.obj.2 G.obj).trans ?_
    exact congrArg (fun x ↦ (pointSmallEtale s).toPresheafFiber j.unop.1 x G.obj) f.2
  rw [Category.assoc, hw]
  exact ModuleCat.hom_ext hα

end Spread

/-- In a spectral space, a set which is open in the constructible topology and contains all
generizations of a point `x` contains an open neighbourhood of `x`. -/
lemma _root_.exists_isOpen_subset_of_isOpen_constructibleTopology {X : Type*}
    [TopologicalSpace X] [SpectralSpace X] {Z : Set X} (hZ : IsOpen[constructibleTopology X] Z)
    {x : X} (hx : ∀ y, y ⤳ x → y ∈ Z) : ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ Z := by
  have hc : IsClosed[constructibleTopology X] Zᶜ :=
    @IsOpen.isClosed_compl X (constructibleTopology X) _ hZ
  refine ⟨(closure Zᶜ)ᶜ, isClosed_closure.isOpen_compl, fun h ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨y, hy, hyx⟩ := exists_specializes_of_isClosed_constructibleTopology_of_mem_closure hc h
    exact hy (hx y hyx)
  · by_contra h
    exact hy (subset_closure h)

section Spread

open _root_.AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {Y : Scheme.{u}}
  (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : Y.Etale) (M : ModuleCat.{u + 1} Λ)
  (α : M ⟶ G.obj.obj (op V))

/-- The morphism `M_V ⟶ g^* G` on the small étale site of `V`, for `g : V ⟶ Y` étale, adjoint
to the map `M ⟶ G(V) ⟶ Γ(V, g^* G)` obtained from `α : M ⟶ G(V)` by pulling back sections. -/
def constantSheafSpread :
    (constantSheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ⟶
      (V.hom)^*[ModuleCat.{u + 1} Λ].obj G :=
  ((constantSheafAdj V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (MorphismProperty.Over.mkIdTerminal _ V.left)).homEquiv M _).symm
    (α ≫ Etale.upperStarSectionHom (ModuleCat.{u + 1} Λ) V.hom G
      (V := Scheme.Etale.mk (𝟙 V.left)) (U := V) (𝟙 V.left) (by simp))

/-- The stalk of `constantSheafSpread G V M α` at a geometric point `r` of `V` is invertible as
soon as the germ of `α` at `r` is. -/
lemma isIso_sheafFiber_map_constantSheafSpread {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (r : Spec (.of Ω) ⟶ V.left) {q : Spec (.of Ω) ⟶ Y} (hq : r ≫ V.hom = q)
    (x : (pointSmallEtale q).fiber.obj V) (hx : x.left = r)
    (h : IsIso (α ≫ (pointSmallEtale q).toPresheafFiber V x G.obj)) :
    IsIso ((pointSmallEtale r).sheafFiber.map (constantSheafSpread G V M α)) := by
  subst hq
  let v : (pointSmallEtale r).fiber.obj (Scheme.Etale.mk (𝟙 V.left)) :=
    CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk r)
      (V := (Etale.forget V.left).obj (Scheme.Etale.mk (𝟙 V.left))) r (Category.comp_id r)
  obtain ⟨e, he⟩ := Etale.exists_sheafFiber_map_constantSheafAdj_homEquiv_symm
    (MorphismProperty.Over.mkIdTerminal _ V.left) M ((V.hom)^*[ModuleCat.{u + 1} Λ].obj G)
    (α ≫ Etale.upperStarSectionHom (ModuleCat.{u + 1} Λ) V.hom G
      (V := Scheme.Etale.mk (𝟙 V.left)) (U := V) (𝟙 V.left) (by simp)) r v
  have hg := Etale.upperStarSectionHom_toPresheafFiber_upperStarCompSheafFiberIso_hom
    (ModuleCat.{u + 1} Λ) V.hom G r (V := Scheme.Etale.mk (𝟙 V.left)) (U := V) (𝟙 V.left)
    (by simp) v
  have hxv : x = CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (r ≫ V.hom))
      (V := (Etale.forget Y).obj V) (v.left ≫ 𝟙 V.left) (by simp [v]) :=
    CategoryTheory.Over.OverMorphism.ext (hx.trans (Category.comp_id r).symm)
  have hg' := hg.trans (congrArg (fun y ↦ (pointSmallEtale (r ≫ V.hom)).toPresheafFiber V y G.obj)
    hxv.symm)
  have hcomp : (pointSmallEtale r).sheafFiber.map (constantSheafSpread G V M α) ≫
      (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) V.hom r).hom.app G =
      e.hom ≫ α ≫ (pointSmallEtale (r ≫ V.hom)).toPresheafFiber V x G.obj := by
    erw [(Iso.inv_comp_eq _).1 he]
    simp only [Category.assoc]
    erw [hg']
  have : IsIso ((pointSmallEtale r).sheafFiber.map (constantSheafSpread G V M α) ≫
      (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) V.hom r).hom.app G) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ)
    V.hom r).hom.app G)

end Spread

section Criterion

open _root_.AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- A morphism of sheaves of modules is invertible on the stalk at a geometric point exactly when
the stalks of its kernel and cokernel vanish there. -/
lemma isIso_sheafFiber_map_iff {X : Scheme.{u}}
    {F H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ψ : F ⟶ H) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (r : Spec (.of Ω) ⟶ X) :
    IsIso ((pointSmallEtale r).sheafFiber.map ψ) ↔
      IsZero ((pointSmallEtale r).sheafFiber.obj (kernel ψ)) ∧
        IsZero ((pointSmallEtale r).sheafFiber.obj (cokernel ψ)) := by
  refine ⟨fun h ↦ ⟨(isZero_kernel_of_mono _).of_iso
    (PreservesKernel.iso (pointSmallEtale r).sheafFiber ψ),
    (isZero_cokernel_of_epi _).of_iso
    (PreservesCokernel.iso (pointSmallEtale r).sheafFiber ψ)⟩, fun ⟨hK, hC⟩ ↦ ?_⟩
  have := Preadditive.mono_of_isZero_kernel _
    (hK.of_iso (PreservesKernel.iso (pointSmallEtale r).sheafFiber ψ).symm)
  have := Preadditive.epi_of_isZero_cokernel _
    (hC.of_iso (PreservesCokernel.iso (pointSmallEtale r).sheafFiber ψ).symm)
  exact isIso_of_mono_of_epi _

/-- Blueprint `lem-kun-constant-constructible`: a constant sheaf of finitely generated modules is
constructible. -/
lemma isConstructibleSheaf_constantSheaf {X : Scheme.{u}} (M : ModuleCat.{u + 1} Λ)
    [Module.Finite Λ M] :
    IsConstructibleSheaf ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hlc : IsLocallyConstantSheaf
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    Sheaf.IsConstant.isLocallyConstantSheaf (Sheaf.isConstant_of_iso _ (Iso.refl _))
  have hfin : IsFiniteSheaf
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    ⟨fun _ _ _ r ↦ ((ModuleCat.isFinitelyGenerated_iff M).2 inferInstance).of_iso
      ((pointSmallEtale r).sheafFiberConstantSheafIso M).symm⟩
  have : IsFiniteLocallyConstantSheaf
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := ⟨⟩
  exact ⟨Stratification.trivial X, fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar (𝟙 X) _⟩

/-- The stalks of a constructible sheaf of modules are finitely generated: a geometric point lies
in a stratum, through whose immersion it factors, and the stalk there is the stalk of the finite
locally constant pullback of the sheaf to the stratum. -/
lemma moduleFinite_sheafFiber_of_isConstructibleSheaf {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Module.Finite Λ (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := F)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
    (S.iUnion_stratum_eq_univ ▸ Set.mem_univ (s.base (IsLocalRing.closedPoint Ω)))
  rw [← S.range_immersion] at hi
  obtain ⟨t, rfl⟩ := IsImmersion.exists_comp_eq_of_field (S.immersion i) s hi
  have := (hS i).toIsFiniteSheaf
  exact (ModuleCat.isFinitelyGenerated_iff _).1
    ((IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      (F := (S.immersion i)^*[ModuleCat.{u + 1} Λ].obj F) Ω t).of_iso
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (S.immersion i) t).app F))

/-- **Local form of the specialization criterion.** Let `Y` be locally noetherian, `Λ`
noetherian and `G` a constructible sheaf of `Λ`-modules on `Y` all of whose cospecialization
maps are bijective. Then every point of `Y` lies in the image of an étale morphism `W ⟶ Y`
along which `G` pulls back to a constant sheaf. -/
theorem exists_etale_isConstant_upperStar_of_bijective_cospecializationMap
    [IsNoetherianRing Λ] {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf G]
    (hG : ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) {Ω' : Type u}
      [Field Ω'] [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ strictLocalization s),
      Function.Bijective (cospecializationMap s t (ModuleCat.{u + 1} Λ) G).hom)
    (y : Y) :
    ∃ (W : Scheme.{u}) (i : W ⟶ Y), Etale i ∧ y ∈ Set.range i.base ∧
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj G).IsConstant W.smallEtaleTopology := by
  classical
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  -- the stalk at a geometric point over `y` is finitely presented
  let s := Y.algClosurePoint y
  let M := ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G
  have : Module.Finite Λ M := moduleFinite_sheafFiber_of_isConstructibleSheaf G s
  have : Module.FinitePresentation Λ M := Module.finitePresentation_of_finite _ _
  -- spread the identity of `M` out to an affine pointed étale neighbourhood `(V, v)`
  obtain ⟨c, α, hα⟩ := exists_comp_toPresheafFiber_eq_id G s
  let V := c.obj.1
  have : IsAffine V.left := c.2
  have : Etale V.hom := V.prop
  have : IsNoetherian V.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (Y := Y) V.hom }
  let ψ := constantSheafSpread G V M α
  have : IsConstructibleSheaf ((V.hom)^*[ModuleCat.{u + 1} Λ].obj G) :=
    IsConstructibleSheaf.upperStar V.hom G
  have : IsConstructibleSheaf
      ((constantSheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
    isConstructibleSheaf_constantSheaf M
  have : IsConstructibleSheaf (kernel ψ) := IsConstructibleSheaf.kernel ψ
  have : IsConstructibleSheaf (cokernel ψ) := IsConstructibleSheaf.cokernel ψ
  let Z := stalkZeroLocus (kernel ψ) ∩ stalkZeroLocus (cokernel ψ)
  let leg := (strictLocalizationConeAll s).π.app ((AffinePointedEtaleNeighborhood.ι s).obj c)
  -- at the geometric points coming from the strict localization, `ψ` is the cospecialization
  -- map on stalks, hence invertible
  have key (p : strictLocalization s) : leg.base p ∈ Z := by
    let t := (strictLocalization s).algClosurePoint p
    have hr : IsIso ((pointSmallEtale (t ≫ leg)).sheafFiber.map ψ) := by
      refine isIso_sheafFiber_map_constantSheafSpread G V M α (t ≫ leg)
        (q := t ≫ strictLocalizationToBase s) ((Category.assoc _ _ _).trans
          (congrArg (t ≫ ·) (strictLocalizationConeAll_π_app_hom s _)))
        ((cospecializationNeighborhoodFunctor s t).obj
          ((AffinePointedEtaleNeighborhood.ι s).obj c)).2 rfl ?_
      have e : α ≫ (pointSmallEtale (t ≫ strictLocalizationToBase s)).toPresheafFiber V
          ((cospecializationNeighborhoodFunctor s t).obj
            ((AffinePointedEtaleNeighborhood.ι s).obj c)).2 G.obj =
          cospecializationMap s t (ModuleCat.{u + 1} Λ) G := by
        erw [← toPresheafFiber_cospecializationMap s t _ G
          ((AffinePointedEtaleNeighborhood.ι s).obj c)]
        exact (Category.assoc _ _ _).symm.trans ((congrArg
          (· ≫ cospecializationMap s t (ModuleCat.{u + 1} Λ) G) hα).trans (Category.id_comp _))
      rw [e, ConcreteCategory.isIso_iff_bijective]
      exact hG s t
    obtain ⟨hK, hC⟩ := (isIso_sheafFiber_map_iff ψ (t ≫ leg)).1 hr
    have hpt : (t ≫ leg).base (IsLocalRing.closedPoint _) = leg.base p :=
      congrArg leg.base (algClosurePoint_base (strictLocalization s) p _)
    exact ⟨hpt ▸ mem_stalkZeroLocus_of_isZero_sheafFiber _ _ hK,
      hpt ▸ mem_stalkZeroLocus_of_isZero_sheafFiber _ _ hC⟩
  -- so the stalks of the kernel and cokernel vanish near the base point `v₀` of `V`
  let v₀ := c.obj.2.left.base (IsLocalRing.closedPoint _)
  have hZ (w : V.left) (hw : w ⤳ v₀) : w ∈ Z := by
    obtain ⟨p, hp⟩ := exists_strictLocalizationConeAll_π_app_base_eq s
      ((AffinePointedEtaleNeighborhood.ι s).obj c) hw
    exact hp ▸ key p
  have : SpectralSpace V.left := {}
  have hZo : IsOpen[constructibleTopology V.left] Z :=
    @IsOpen.inter V.left (constructibleTopology V.left) _ _
      (isOpen_constructibleTopology_stalkZeroLocus (kernel ψ))
      (isOpen_constructibleTopology_stalkZeroLocus (cokernel ψ))
  obtain ⟨O, hO, hv₀, hOZ⟩ := exists_isOpen_subset_of_isOpen_constructibleTopology hZo hZ
  let U : V.left.Opens := ⟨O, hO⟩
  refine ⟨U, U.ι ≫ V.hom, inferInstance, ⟨⟨v₀, hv₀⟩, ?_⟩, ?_⟩
  · have h : c.obj.2.left ≫ V.hom = s := CategoryTheory.Over.w c.obj.2
    exact (congrArg (fun f ↦ f.base (IsLocalRing.closedPoint _)) h).trans
      (algClosurePoint_base _ _ _)
  -- on `U` the morphism `ψ` is an isomorphism
  have hiso : IsIso ((U.ι)^*[ModuleCat.{u + 1} Λ].map ψ) := by
    refine isIso_of_isIso_sheafFiber_map _ fun z ↦ ?_
    let a := U.toScheme.algClosurePoint z
    have hz : (a ≫ U.ι).base (IsLocalRing.closedPoint _) ∈ Z := by
      rw [Scheme.Hom.comp_apply, algClosurePoint_base]
      exact hOZ z.2
    have h₁ : IsIso ((pointSmallEtale (a ≫ U.ι)).sheafFiber.map ψ) :=
      (isIso_sheafFiber_map_iff ψ (a ≫ U.ι)).2 ⟨hz.1 _ _ rfl, hz.2 _ _ rfl⟩
    have h₂ : IsIso ((pointSmallEtale a).sheafFiber.map ((U.ι)^*[ModuleCat.{u + 1} Λ].map ψ)) :=
      (NatIso.isIso_map_iff (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.ι a) ψ).2 h₁
    exact (NatIso.isIso_map_iff ((pointSmallEtale a).uliftSheafFiberIso _) _).2 h₂
  exact Sheaf.isConstant_of_iso _
    ((upperStarComp (ModuleCat.{u + 1} Λ) U.ι V.hom).app G ≪≫
      (asIso ((U.ι)^*[ModuleCat.{u + 1} Λ].map ψ)).symm ≪≫
      (upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) U.ι).app M)

/-- **A specialization criterion for local constancy** ([SGA 4, Exp. IX, 2.11],
[Stacks, Tag 0GJ2]). Let `Y` be a locally noetherian scheme, `Λ` a noetherian ring and `G` a
constructible sheaf of `Λ`-modules on the small étale site of `Y`. If for every geometric point
`s` of `Y` and every geometric point `t` of the strict localization `Y_(s)` the cospecialization
map `G_s ⟶ G_t` (`AlgebraicGeometry.Scheme.cospecializationMap`) is bijective, then `G` is
finite locally constant. -/
theorem isFiniteLocallyConstantSheaf_of_bijective_cospecializationMap
    [IsNoetherianRing Λ] {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf G]
    (hG : ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) {Ω' : Type u}
      [Field Ω'] [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ strictLocalization s),
      Function.Bijective (cospecializationMap s t (ModuleCat.{u + 1} Λ) G).hom) :
    IsFiniteLocallyConstantSheaf G := by
  choose W i hi hy hc using exists_etale_isConstant_upperStar_of_bijective_cospecializationMap G hG
  let 𝒰 : Cover.{u} etalePrecoverage Y := Cover.mkOfCovers Y W i (fun y ↦ ⟨y, hy y⟩) hi
  have hlc : IsLocallyConstantSheaf G :=
    ⟨⟨⟨𝒰, fun y ↦ (isConstant_over_iff_upperStar _ _ G).2 (hc y)⟩⟩⟩
  exact
    { toIsLocallyConstantSheaf := hlc
      toIsFiniteSheaf := ⟨fun _ _ _ s ↦ (ModuleCat.isFinitelyGenerated_iff _).2
        (moduleFinite_sheafFiber_of_isConstructibleSheaf G s)⟩ }

end Criterion

end Scheme

end AlgebraicGeometry
