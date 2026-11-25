/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.CategoryTheory.Galois.Topology
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverConstruction

/-!
# Universal profinite étale covers

Let `Y` be a connected scheme and `y : Spec Ω̄ ⟶ Y` a geometric point. The *universal profinite
étale cover* of `Y` at `y` is the limit `Ỹ_y = lim A` over the pointed Galois finite étale
`Y`-schemes `(A, a)`, `a ∈ F_y(A)`, with its point `ỹ : Spec Ω̄ ⟶ Ỹ_y` given by the points `a`.
It is weakly étale (pro-étale) over `Y`, connected, and every finite étale `Y`-scheme `P` splits
over it: precomposition with `ỹ` is a bijection `Hom_Y(Ỹ_y, P) ≃ F_y(P)`. A path
`τ : F_y ≅ F_z` induces an isomorphism `Ỹ_y ≅ Ỹ_z` over `Y` (the pro-objects `(A, a)` and
`(A, τ a)` agree), functorially in `τ`; and a morphism `f : Y' ⟶ Y` induces
`Ỹ'_y ⟶ Ỹ_{y ≫ f}` over `f`, sending `ỹ` to the point over `y ≫ f`.

This file records these data and their compatibilities as a structure
(`AlgebraicGeometry.Scheme.UniversalCovers`), the form in which they are used to transport stalks
of lisse `ℓ`-adic sheaves along paths (`WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy`):
the stalk of a lisse sheaf at `y` is identified with its sections over `Ỹ_y`, on which it is
constant (Bhatt–Scholze, *The pro-étale topology for schemes*, §7.4).

## Main definitions

- `AlgebraicGeometry.Scheme.UniversalCovers`: universal profinite étale covers at all geometric
  points with values in `Ω̄`, with their transport along paths and functoriality.
- `AlgebraicGeometry.Scheme.universalCovers`: the universal covers of a connected qcqs scheme,
  as limits over the pointed Galois finite étale covers.
- `AlgebraicGeometry.Scheme.UniversalCovers.Hom`: morphisms of universal covers over a morphism
  of schemes; `AlgebraicGeometry.Scheme.universalCoversHom` is the one between the limits.

## Main statements

- `AlgebraicGeometry.Scheme.nonempty_universalCovers`: universal covers exist over a connected
  scheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

open FiniteEtale

variable (Y : Scheme.{u}) (Ω : Type u) [Field Ω]

/-- **Universal profinite étale covers** of `Y` at the geometric points with values in `Ω̄`:
for every geometric point `y : Spec Ω̄ ⟶ Y` a weakly étale `Y`-scheme `Ỹ_y`, connected, with a
point `ỹ` over `y`, over which every finite étale `Y`-scheme `P` splits
(`Hom_Y(Ỹ_y, P) ≃ F_y(P)` by precomposition with `ỹ`); for every path `τ : F_y ≅ F_z` an
isomorphism `Ỹ_y ≅ Ỹ_z` over `Y`, functorial in `τ` and sending the point of a reparametrised
geometric point to the reparametrised point; and for every endomorphism `f` of `Y` a morphism
`Ỹ_y ⟶ Ỹ_{y ≫ f}` over `f`, sending `ỹ` to the point over `y ≫ f` and compatible with the
transports along `τ` and along the induced path `F_{y ≫ f} ≅ F_{z ≫ f}`. -/
structure UniversalCovers where
  /-- The universal cover `Ỹ_y` at `y`. -/
  cover (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : Scheme.{u}
  /-- The projection `Ỹ_y ⟶ Y`. -/
  proj (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : cover y ⟶ Y
  weaklyEtale_proj (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : WeaklyEtale (proj y)
  /-- The base point `ỹ` of `Ỹ_y`. -/
  pt (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : Spec (.of (AlgebraicClosure Ω)) ⟶ cover y
  pt_proj (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : pt y ≫ proj y = y
  connectedSpace (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : ConnectedSpace (cover y)
  surjective_proj (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : Function.Surjective (proj y).base
  /-- The projection `Ỹ_y ⟶ Y` is quasi-compact (`Ỹ_y` is affine over `Y`). -/
  quasiCompact_proj (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : QuasiCompact (proj y)
  /-- Every finite étale `Y`-scheme splits over `Ỹ_y`: its `Y`-morphisms from `Ỹ_y` are the
  points of the fibre at `y`, through `ỹ`. -/
  bijective_fiber (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (P : Y.FiniteEtale) :
    Function.Bijective fun f : {f : cover y ⟶ P.obj.left // f ≫ P.obj.hom = proj y} ↦
      fiberMk y P (pt y ≫ f.1) (by rw [Category.assoc, f.2, pt_proj])
  /-- The transport `Ỹ_y ≅ Ỹ_z` along a path `τ : F_y ≅ F_z`. -/
  transport {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z) :
    cover y ≅ cover z
  transport_proj {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z) :
    (transport τ).hom ≫ proj z = proj y
  /-- The transport along `τ` acts on fibres by `τ⁻¹`: under `bijective_fiber`, precomposition
  with `transport τ` sends `x ∈ F_z(P)` to `τ⁻¹ x ∈ F_y(P)`. -/
  transport_fiber {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z)
    (P : Y.FiniteEtale) (f : cover z ⟶ P.obj.left) (hf : f ≫ P.obj.hom = proj z) :
    fiberMk y P (pt y ≫ (transport τ).hom ≫ f)
        (by rw [Category.assoc, Category.assoc, hf, transport_proj, pt_proj]) =
      τ.inv.app P (fiberMk z P (pt z ≫ f) (by rw [Category.assoc, hf, pt_proj]))
  transport_refl (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    transport (Iso.refl (fiber y)) = Iso.refl _
  transport_trans {y z w : Spec (.of (AlgebraicClosure Ω)) ⟶ Y} (τ : fiber y ≅ fiber z)
    (τ' : fiber z ≅ fiber w) : transport (τ ≪≫ τ') = transport τ ≪≫ transport τ'
  /-- The transport along the reparametrisation path `F_{a ≫ y} ≅ F_y` sends the point over
  `a ≫ y` to the reparametrised point `a ≫ ỹ`. -/
  pt_transport_reparam (a : Spec (.of (AlgebraicClosure Ω)) ≅ Spec (.of (AlgebraicClosure Ω)))
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    pt (a.hom ≫ y) ≫ (transport (fiberReparamIso a y)).hom = a.hom ≫ pt y
  /-- The morphism `Ỹ_y ⟶ Ỹ_{y ≫ f}` over an endomorphism `f` of `Y`. -/
  map (f : Y ⟶ Y) (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : cover y ⟶ cover (y ≫ f)
  map_proj (f : Y ⟶ Y) (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    map f y ≫ proj (y ≫ f) = proj y ≫ f
  pt_map (f : Y ⟶ Y) (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : pt y ≫ map f y = pt (y ≫ f)
  map_transport (f : Y ⟶ Y) {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y}
    (τ : fiber y ≅ fiber z) :
    map f y ≫ (transport (pullbackPathIso f τ)).hom = (transport τ).hom ≫ map f z
  /-- Every point of `Ỹ_y ×_Y Ỹ_y` lies on the graph `x ↦ (x, g x)` of the transport along some
  loop `g ∈ π₁(Y, y) = Aut F_y`. -/
  exists_graph (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (p : (pullback (proj y) (proj y) : Scheme.{u})) :
    ∃ (g : Aut (fiber y)) (x : cover y),
      (pullback.lift (f := proj y) (g := proj y) (𝟙 _) (transport g.asIso).hom
        (by rw [Category.id_comp, transport_proj])).base x = p
  /-- The point `(ỹ, g ỹ)` of `Ỹ_y ×_Y Ỹ_y` depends continuously on `g ∈ π₁(Y, y)`. -/
  continuous_graph (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (x : Spec (.of (AlgebraicClosure Ω))) :
    Continuous fun g : Aut (fiber y) ↦ (pullback.lift (f := proj y) (g := proj y) (pt y)
      (pt y ≫ (transport g.asIso).hom)
      (by rw [Category.assoc, transport_proj])).base x
  /-- The loop `g ∈ π₁(Y, y)` of a point `(x, g x)` of `Ỹ_y ×_Y Ỹ_y`. -/
  loop (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    (pullback (proj y) (proj y) : Scheme.{u}) → Aut (fiber y)
  /-- The loop of a point of `Ỹ_y ×_Y Ỹ_y` depends continuously on the point. -/
  continuous_loop (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) : Continuous (loop y)
  /-- The loop of `(x, g x)` is `g`: the graphs of the transports along distinct loops are
  disjoint. -/
  loop_graph (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (g : Aut (fiber y)) (x : cover y) :
    loop y ((pullback.lift (f := proj y) (g := proj y) (𝟙 _) (transport g.asIso).hom
      (by rw [Category.id_comp, transport_proj])).base x) = g

/-- **The universal profinite étale covers** of a connected quasi-compact quasi-separated
scheme: the limits `Ỹ_y = lim A` over the pointed Galois finite étale `Y`-schemes
(`AlgebraicGeometry.Scheme.UniversalCover.cover`). -/
noncomputable def universalCovers [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    UniversalCovers Y Ω where
  cover := UniversalCover.cover
  proj := UniversalCover.proj
  weaklyEtale_proj := UniversalCover.weaklyEtale_proj
  pt := UniversalCover.pt
  pt_proj := UniversalCover.pt_proj
  connectedSpace y := UniversalCover.connectedSpace_cover y
  surjective_proj := UniversalCover.surjective_proj
  quasiCompact_proj := UniversalCover.quasiCompact_proj
  bijective_fiber y P := UniversalCover.bijective_fiber y P
  transport := UniversalCover.transport
  transport_proj τ := UniversalCover.transportHom_proj τ
  transport_fiber {y z} τ P f hf := by
    have hx : UniversalCover.toObj (Y := Y) z P (fiberMk z P (UniversalCover.pt z ≫ f)
        (by rw [Category.assoc, hf]; exact UniversalCover.pt_proj (Y := Y) z)) = f :=
      UniversalCover.eq_of_pt_comp_eq (Y := Y) z P (UniversalCover.toObj_hom (Y := Y) z P _) hf
        (UniversalCover.pt_toObj (Y := Y) z P _)
    apply fiber_ext
    conv_lhs => rw [fiberMk_left, ← hx]
    rw [UniversalCover.transport_hom, UniversalCover.transportHom_toObj,
      UniversalCover.pt_toObj]
  transport_refl := UniversalCover.transport_refl
  transport_trans := UniversalCover.transport_trans
  pt_transport_reparam := UniversalCover.pt_transport_reparam
  map := UniversalCover.map
  map_proj := UniversalCover.map_proj
  pt_map := UniversalCover.pt_map
  map_transport := UniversalCover.map_transport
  exists_graph y q := UniversalCover.exists_graph y q
  continuous_graph y x := UniversalCover.continuous_graph y x
  loop y := UniversalCover.loop y
  continuous_loop y := UniversalCover.continuous_loop y
  loop_graph y g x := by exact UniversalCover.loop_loopGraph y g x

/-- **Existence of universal profinite étale covers** over a connected quasi-compact
quasi-separated scheme: the limits `Ỹ_y = lim A` over the pointed Galois finite étale `Y`-schemes
(`AlgebraicGeometry.Scheme.UniversalCover.cover`). -/
theorem nonempty_universalCovers [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    Nonempty (UniversalCovers Y Ω) :=
  ⟨universalCovers Y Ω⟩

variable {Y Ω} {Y' : Scheme.{u}}

/-- A *morphism of universal covers* over a morphism `f : Y' ⟶ Y`: morphisms
`Ỹ'_y ⟶ Ỹ_{y ≫ f}` over `f`, sending the base point to the base point and compatible with the
transports along a path `τ` of `Y'` and along the induced path `F_{y ≫ f} ≅ F_{z ≫ f}` of `Y`. -/
structure UniversalCovers.Hom (f : Y' ⟶ Y) (U' : UniversalCovers Y' Ω) (U : UniversalCovers Y Ω)
    where
  /-- The morphism `Ỹ'_y ⟶ Ỹ_{y ≫ f}`. -/
  map (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y') : U'.cover y ⟶ U.cover (y ≫ f)
  map_proj (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y') : map y ≫ U.proj (y ≫ f) = U'.proj y ≫ f
  pt_map (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y') : U'.pt y ≫ map y = U.pt (y ≫ f)
  map_transport {y z : Spec (.of (AlgebraicClosure Ω)) ⟶ Y'} (τ : fiber y ≅ fiber z) :
    map y ≫ (U.transport (pullbackPathIso f τ)).hom = (U'.transport τ).hom ≫ map z

/-- The universal profinite étale covers are functorial along morphisms of connected
quasi-compact quasi-separated schemes (`AlgebraicGeometry.Scheme.UniversalCover.map`). -/
noncomputable def universalCoversHom [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [ConnectedSpace Y'] [CompactSpace Y'] [QuasiSeparatedSpace Y'] (f : Y' ⟶ Y) :
    UniversalCovers.Hom f (universalCovers Y' Ω) (universalCovers Y Ω) where
  map := UniversalCover.map f
  map_proj := UniversalCover.map_proj f
  pt_map := UniversalCover.pt_map f
  map_transport := UniversalCover.map_transport f

end AlgebraicGeometry.Scheme
