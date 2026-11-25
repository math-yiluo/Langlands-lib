/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Skeletal
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-!
# The Picard group of a scheme and the Picard presheaf

For a scheme `Y` we define `AlgebraicGeometry.Scheme.Pic Y`, the set of isomorphism classes of
invertible sheaves of `𝒪_Y`-modules, as the invertible classes inside the skeleton of
`Y.Modules`, and the contravariant functoriality `AlgebraicGeometry.Scheme.Pic.map` given by
pulling back invertible modules.  For a morphism of schemes `f : X ⟶ S` this assembles into the
`Set`-valued Picard presheaf `T ↦ Pic (X ×[S] T)` on the category of schemes over `S`.

The auxiliary isomorphisms in the `AlgebraicGeometry.Scheme.Modules` namespace identify, via
`AlgebraicGeometry.Scheme.Modules.overEquiv`, the restriction `M.over U` of a sheaf of modules
to an open subset `U` with the pullback of `M` along the open immersion `U.ι`; this is what
makes invertibility stable under pullback.

## Implementation notes

`Y.Modules` lives in `Type (u + 1)`, so `Y.Pic` as defined here does too, even though `Pic Y`
is really a small group; that it is `u`-small is `AlgebraicGeometry.Scheme.Pic.small`. The group
law, which comes from the tensor product of invertible modules, is defined in
`WeilConjectures/AlgebraicGeometry/Picard/Group.lean`.

## Main definitions

- `AlgebraicGeometry.Scheme.Pic`: the Picard group of a scheme, as a set
  (blueprint `def:sc-picard-group`).
- `AlgebraicGeometry.Scheme.Pic.map`: the pullback map on Picard groups
  (blueprint `lem:pc-pic-presheaf-functorial`).
- `AlgebraicGeometry.picardPresheaf`: the Picard presheaf of `f : X ⟶ S`
  (blueprint `def:pc-picard-presheaf`).

## Main results

- `SheafOfModules.IsInvertible.pullback`: the pullback of an invertible sheaf of modules along
  a morphism of schemes is invertible (blueprint `lem:pc-pic-presheaf-functorial`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

namespace Modules

/-- The restriction of the structure sheaf to an open subset, as a sheaf of modules over
the localized sheaf of rings, is the unit object. -/
noncomputable def overFunctorObjUnitIso (U : Y.Opens) :
    (SheafOfModules.overFunctor Y.ringCatSheaf U).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit (Y.ringCatSheaf.over U) :=
  Iso.refl _

/-- Under the equivalence `Scheme.Modules.overEquiv`, the unit object corresponds to the
unit object. -/
noncomputable def overEquivObjUnitIso (U : Y.Opens) :
    (overEquiv U).functor.obj (SheafOfModules.unit (Y.ringCatSheaf.over U)) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (overEquiv U).functor.mapIso (overFunctorObjUnitIso U).symm ≪≫
    (overFunctorEquiv U).app _ ≪≫ restrictUnitIso U.ι

/-- Under the equivalence `Scheme.Modules.overEquiv`, the restriction `M.over U` of a sheaf
of modules to an open subset corresponds to its pullback along the open immersion `U.ι`. -/
noncomputable def overEquivObjOverIso (M : Y.Modules) (U : Y.Opens) :
    (overEquiv U).functor.obj (M.over U) ≅ (Modules.pullback U.ι).obj M :=
  (overFunctorEquiv U).app M ≪≫ (restrictFunctorIsoPullback U.ι).app M

/-- If the restriction of `M` to an open subset `U` is trivial, then so is its pullback
along the open immersion `U.ι`. -/
noncomputable def pullbackIotaUnitIsoOfOverIso {M : Y.Modules} {U : Y.Opens}
    (e : M.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U)) :
    (Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (overEquivObjOverIso M U).symm ≪≫ (overEquiv U).functor.mapIso e ≪≫ overEquivObjUnitIso U

/-- Conversely, if the pullback of `M` along an open immersion `U.ι` is trivial, then so is
the restriction of `M` to `U`. -/
noncomputable def overIsoUnitOfPullbackIotaIso {M : Y.Modules} {U : Y.Opens}
    (e : (Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U) :=
  (overEquiv U).functor.preimageIso
    (overEquivObjOverIso M U ≪≫ e ≪≫ (overEquivObjUnitIso U).symm)

/-- The key local computation behind functoriality of the Picard presheaf: if `M` is trivial
on an open subset `U` of `Y`, then its pullback along `g : X ⟶ Y` is trivial on `g ⁻¹ᵁ U`.

The isomorphism is read off the restriction square of `g` over `U`, in which both composites
are `g ⁻¹ᵁ U ⟶ Y`, so that pulling `M` back along either path gives the same module:

```
  (g ⁻¹ᵁ U).toScheme ── g ∣_ U ──▶ U.toScheme
        │                              │
  (g ⁻¹ᵁ U).ι                        U.ι
        │                              │
        ▼                              ▼
        X ──────────── g ────────────▶ Y
```
-/
noncomputable def pullbackOverUnitIso (g : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (e : M.over U ≅ SheafOfModules.unit (Y.ringCatSheaf.over U)) :
    ((Modules.pullback g).obj M).over (g ⁻¹ᵁ U) ≅
      SheafOfModules.unit (X.ringCatSheaf.over (g ⁻¹ᵁ U)) :=
  overIsoUnitOfPullbackIotaIso
    ((Modules.pullbackComp (g ⁻¹ᵁ U).ι g).app M ≪≫
      (Modules.pullbackCongr (morphismRestrict_ι g U).symm).app M ≪≫
      ((Modules.pullbackComp (g ∣_ U) U.ι).symm).app M ≪≫
      (Modules.pullback (g ∣_ U)).mapIso (pullbackIotaUnitIsoOfOverIso e) ≪≫
      pullbackObjUnitIso (g ∣_ U))

end Modules

/-- The pullback of an invertible sheaf of modules along a morphism of schemes is invertible.
This is the functoriality part of blueprint `lem:pc-pic-presheaf-functorial`. -/
theorem _root_.SheafOfModules.IsInvertible.pullback {g : X ⟶ Y} {M : Y.Modules}
    (hM : M.IsInvertible) : ((Modules.pullback g).obj M).IsInvertible := by
  obtain ⟨q, hq⟩ := hM.exists_isInvertibleData
  have := hq
  refine SheafOfModules.isInvertible_of_forall_over_unit (M := (Modules.pullback g).obj M)
    (fun i : q.I ↦ g ⁻¹ᵁ q.X i) ?_ ?_
  · have h : IsOpenCover q.X := (Opens.coversTop_iff _ _).mp q.coversTop
    rw [Opens.coversTop_iff]
    refine IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ ?_)
    obtain ⟨i, hi⟩ := h.exists_mem (g.base x)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    obtain ⟨hu⟩ := SheafOfModules.LocalGeneratorsData.IsInvertibleData.nonempty_unique (q := q) i
    have := hu
    exact ⟨Modules.pullbackOverUnitIso g M (q.X i)
      ((asIso (q.generators i).π).symm ≪≫ SheafOfModules.freeUniqueIso _)⟩

-- The universes of `IsInvertible.of_iso` have to be given explicitly: without them the
-- instance arguments of `of_iso` are elaborated before its category is known, and the
-- universe metavariables are defaulted to `0`.
/-- Invertibility of a sheaf of modules only depends on its isomorphism class, so it transfers
to the chosen representative of that class in the skeleton. -/
lemma _root_.SheafOfModules.IsInvertible.fromSkeleton_toSkeleton (M : Y.Modules)
    [M.IsInvertible] : ((fromSkeleton Y.Modules).obj (toSkeleton M)).IsInvertible :=
  SheafOfModules.IsInvertible.of_iso.{u, u, u} (fromSkeletonToSkeletonIso M).symm

variable (Y) in
/-- The Picard group of a scheme `Y`: the set of isomorphism classes of invertible sheaves
of `𝒪_Y`-modules, realized as the invertible classes inside the skeleton of `Y.Modules`.
Its group law, induced by the tensor product with the dual as inverse, is
`AlgebraicGeometry.Scheme.Pic.instCommGroup`.

(blueprint: `def-sc-picard-group`)

This lives in `Type (u + 1)` rather than `Type u`; see the implementation notes of this
module. -/
def Pic : Type (u + 1) :=
  { L : Skeleton Y.Modules // ((fromSkeleton Y.Modules).obj L).IsInvertible }

namespace Pic

/-- The isomorphism class in `Skeleton Y.Modules` underlying an element of `Y.Pic`. -/
def val (L : Y.Pic) : Skeleton Y.Modules :=
  Subtype.val L

lemma isInvertible (L : Y.Pic) : ((fromSkeleton Y.Modules).obj L.val).IsInvertible :=
  Subtype.property L

@[ext]
lemma ext {L L' : Y.Pic} (h : L.val = L'.val) : L = L' :=
  Subtype.ext h

/-- The class of an invertible sheaf of modules in the Picard group. -/
def mk (M : Y.Modules) [M.IsInvertible] : Y.Pic :=
  Subtype.mk (p := fun L ↦ ((fromSkeleton Y.Modules).obj L).IsInvertible) (toSkeleton M)
    (SheafOfModules.IsInvertible.fromSkeleton_toSkeleton M)

@[simp]
lemma val_mk (M : Y.Modules) [M.IsInvertible] : (mk M).val = toSkeleton M :=
  rfl

lemma mk_eq_mk_iff (M N : Y.Modules) [M.IsInvertible] [N.IsInvertible] :
    mk M = mk N ↔ Nonempty (M ≅ N) := by
  rw [← toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun h ↦ congrArg val h, fun h ↦ ext h⟩

/-- Two classes in the Picard group agree if and only if their chosen representatives are
isomorphic. -/
lemma eq_iff_nonempty_iso {L L' : Y.Pic} :
    L = L' ↔
      Nonempty ((fromSkeleton Y.Modules).obj L.val ≅ (fromSkeleton Y.Modules).obj L'.val) := by
  rw [Pic.ext_iff, ← toSkeleton_eq_toSkeleton_iff, toSkeleton_fromSkeleton_obj,
    toSkeleton_fromSkeleton_obj]

/-- **The Picard group is small.** Although `Y.Pic` lives in `Type (u + 1)`, it is `u`-small.

Let `P` be the product, over all opens `U` of `Y`, of the pushforwards `U.ι_* 𝒪_U`. An invertible
module `M` embeds into `P`: on each open `U` over which `M` is trivial, `M` maps to
`U.ι_* (M|_U) ≅ U.ι_* 𝒪_U`, and since these opens cover `Y` the resulting map is a monomorphism
(`Scheme.Modules.hom_ext_of_restrictAdjunction_unit`). So the isomorphism class of `M` is
determined by a subobject of `P`, and `Y.Modules` is well-powered, being Grothendieck abelian. -/
theorem small (Y : Scheme.{u}) : Small.{u} Y.Pic := by
  classical
  have : IsGrothendieckAbelian.{u} Y.Modules := SheafOfModules.isGrothendieckAbelian Y.ringCatSheaf
  let P : Y.Modules := ∏ᶜ fun U : Y.Opens ↦
    (Modules.pushforward U.ι).obj (SheafOfModules.unit U.toScheme.ringCatSheaf)
  let φ (M : Y.Modules) : M ⟶ P := Pi.lift fun U ↦
    if h : Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) then
      (Modules.restrictAdjunction U.ι).unit.app M ≫ ((Modules.pushforward U.ι).mapIso h.some).hom
    else 0
  have hφ (M : Y.Modules) [M.IsInvertible] : Mono (φ M) := by
    refine ⟨fun g₁ g₂ hg ↦ Modules.hom_ext_of_restrictAdjunction_unit
      (fun U : {U : Y.Opens //
        Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)} ↦ U.1)
      (fun x ↦ ?_) fun U ↦ ?_⟩
    · obtain ⟨V, hx, ⟨e⟩⟩ := Modules.exists_mem_over_iso_unit M x
      exact ⟨⟨V, ⟨(Modules.restrictFunctorIsoPullback V.ι).app M ≪≫
        Modules.pullbackIotaUnitIsoOfOverIso e⟩⟩, hx⟩
    · have h := hg =≫ Pi.π _ U.1
      simp only [Category.assoc, Pi.lift_comp_π, φ, dite_eq_left U.2] at h
      rw [← Category.assoc, ← Category.assoc] at h
      exact (cancel_mono _).mp h
  let f (L : Y.Pic) : Subobject P :=
    @Subobject.mk _ _ _ _ (φ ((fromSkeleton Y.Modules).obj L.val)) (@hφ _ L.isInvertible)
  refine small_of_injective (f := f) fun L L' h ↦ ?_
  rw [eq_iff_nonempty_iso]
  have := L.isInvertible
  have := L'.isInvertible
  have := hφ ((fromSkeleton Y.Modules).obj L.val)
  have := hφ ((fromSkeleton Y.Modules).obj L'.val)
  exact ⟨Subobject.isoOfMkEqMk _ _ h⟩

/-- Pulling back invertible sheaves of modules along `g : X ⟶ Y` gives the map
`Pic Y → Pic X` underlying the functoriality of the Picard presheaf. -/
noncomputable def map (g : X ⟶ Y) (L : Y.Pic) : X.Pic :=
  Subtype.mk (p := fun L' ↦ ((fromSkeleton X.Modules).obj L').IsInvertible)
    ((Modules.pullback g).mapSkeleton.obj L.val) (by
      rw [Functor.mapSkeleton_obj]
      have := SheafOfModules.IsInvertible.pullback (g := g)
        (M := (fromSkeleton Y.Modules).obj L.val) L.isInvertible
      exact SheafOfModules.IsInvertible.fromSkeleton_toSkeleton _)

@[simp]
lemma val_map (g : X ⟶ Y) (L : Y.Pic) :
    (map g L).val = toSkeleton ((Modules.pullback g).obj ((fromSkeleton Y.Modules).obj L.val)) :=
  rfl

@[simp]
lemma map_id (L : X.Pic) : map (𝟙 X) L = L := by
  refine ext ?_
  rw [val_map]
  conv_rhs => rw [← toSkeleton_fromSkeleton_obj L.val]
  exact congr_toSkeleton_of_iso ((Modules.pullbackId X).app _)

lemma map_comp {Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) (L : Z.Pic) :
    map (g ≫ h) L = map g (map h L) := by
  refine ext ?_
  simp only [val_map]
  exact congr_toSkeleton_of_iso (((Modules.pullbackComp g h).app _).symm ≪≫
    (Modules.pullback g).mapIso (fromSkeletonToSkeletonIso _).symm)

/-- Pulling back the trivial invertible sheaf gives the trivial invertible sheaf.

The two invertibility instances are taken as hypotheses rather than synthesised: the instance
`SheafOfModules.instIsInvertibleUnit` needs sheafification on the over-sites of the small
Zariski site, which is not available with the imports of this file. -/
@[simp]
lemma map_mk_unit (g : X ⟶ Y) [(SheafOfModules.unit Y.ringCatSheaf).IsInvertible]
    [(SheafOfModules.unit X.ringCatSheaf).IsInvertible] :
    map g (mk (SheafOfModules.unit Y.ringCatSheaf)) =
      mk (SheafOfModules.unit X.ringCatSheaf) :=
  ext (congr_toSkeleton_of_iso ((Modules.pullback g).mapIso (fromSkeletonToSkeletonIso _) ≪≫
    Modules.pullbackObjUnitIso g))

end Pic

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}}

/-- The base change along `φ : T' ⟶ T` in `Over S` of the fibre product `X ×[S] T`. -/
noncomputable abbrev baseChangeMap (f : X ⟶ S) {T T' : Over S} (φ : T' ⟶ T) :
    Limits.pullback f T'.hom ⟶ Limits.pullback f T.hom :=
  Limits.pullback.map f T'.hom f T.hom (𝟙 X) φ.left (𝟙 S) (by simp) (by simp)

@[simp]
lemma baseChangeMap_id (f : X ⟶ S) (T : Over S) : baseChangeMap f (𝟙 T) = 𝟙 _ := by
  apply Limits.pullback.hom_ext <;> simp

@[simp]
lemma baseChangeMap_comp (f : X ⟶ S) {T T' T'' : Over S} (φ : T'' ⟶ T') (ψ : T' ⟶ T) :
    baseChangeMap f (φ ≫ ψ) = baseChangeMap f φ ≫ baseChangeMap f ψ := by
  apply Limits.pullback.hom_ext <;> simp

/-- The base change square of `X_T ⟶ T` along a morphism `g : T' ⟶ T` of schemes over `S`. -/
lemma isPullback_baseChangeMap (f : X ⟶ S) {T T' : Over S} (g : T' ⟶ T) :
    IsPullback (baseChangeMap f g) (Limits.pullback.snd f T'.hom) (Limits.pullback.snd f T.hom)
      g.left := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback f T.hom)
  rw [Over.w g]
  simpa using IsPullback.of_hasPullback f T'.hom

/-- Base change along `f` preserves pullback squares: if the square of schemes underlying a
commutative square in `Over S` is a pullback square, so is the square of fibre products with
`X`. -/
lemma isPullback_baseChangeMap_of_isPullback (f : X ⟶ S) {T₁ T₂ T₃ T₄ : Over S} {i : T₁ ⟶ T₂}
    {j : T₁ ⟶ T₃} {k : T₂ ⟶ T₄} {l : T₃ ⟶ T₄} (h : IsPullback i.left j.left k.left l.left) :
    IsPullback (baseChangeMap f i) (baseChangeMap f j) (baseChangeMap f k)
      (baseChangeMap f l) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_baseChangeMap f k).flip
  · rw [Limits.pullback.lift_snd, Limits.pullback.lift_snd]
    exact (isPullback_baseChangeMap f j).flip.paste_horiz h
  · rw [← baseChangeMap_comp, ← baseChangeMap_comp]
    congr 1
    exact Over.OverMorphism.ext h.w

/-- The Picard presheaf of a morphism of schemes `f : X ⟶ S`: it sends a scheme `T` over `S`
to the Picard group of the fibre product `X_T = X ×[S] T`, and a morphism over `S` to the
corresponding pullback map on Picard groups. Functoriality: pulling back along `X_{T'} ⟶ X_T`
sends invertible modules to invertible modules and respects isomorphisms
(`AlgebraicGeometry.Scheme.Pic.map`), and `(g₁ ∘ g₂)^* = g₂^* g₁^*`, `id^* = id`
(`AlgebraicGeometry.Scheme.Pic.map_comp`, `AlgebraicGeometry.Scheme.Pic.map_id`).

(blueprint: `definition-relative-picard-functor`,
`definition-relative-picard-functor`) -/
noncomputable def picardPresheaf (f : X ⟶ S) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := (Limits.pullback f T.unop.hom).Pic
  map φ := TypeCat.ofHom (Pic.map (baseChangeMap f φ.unop))
  map_id T := by
    simp only [unop_id, baseChangeMap_id]
    exact congrArg TypeCat.ofHom (funext Pic.map_id)
  map_comp φ ψ := by
    simp only [unop_comp, baseChangeMap_comp]
    exact congrArg TypeCat.ofHom (funext fun L ↦ Pic.map_comp _ _ L)

end AlgebraicGeometry
