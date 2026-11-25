/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.Rigidification
public import WeilConjectures.AlgebraicGeometry.Seesaw
public import WeilConjectures.AlgebraicGeometry.TheoremOfCube.SpreadOut
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# The theorem of the cube

Let `X`, `Y` be proper and geometrically integral over a field `K`, let `Z` be connected, and
let `x`, `y`, `z` be `K`-points of `X`, `Y`, `Z`. An invertible module on `X ×_K Y ×_K Z` is
determined, up to isomorphism, by its restrictions to the three slices `{x} × Y × Z`,
`X × {y} × Z` and `X × Y × {z}` (Stacks, Tag 0BF4).

Products are taken in the cartesian monoidal category `Over (Spec K)`, so that
`((X ⊗ Y) ⊗ Z).left` is the fibre product `(X ×_K Y) ×_K Z`, and the slice inclusions are
written with `CartesianMonoidalCategory.lift`.

## Main statements

- `AlgebraicGeometry.nonempty_iso_of_nonempty_iso_overPullback_slices`: the theorem of the cube.

The proof follows Stacks: the locus of points of `Z` over which `M` and `N` are locally
isomorphic is open, closed (`AlgebraicGeometry.isClosed_setOf_exists_nonempty_iso_preimageSnd`)
and contains `z` (`AlgebraicGeometry.exists_mem_nonempty_iso_preimageSnd`), hence is all of the
connected scheme `Z`, and an isomorphism locally over `Z` globalises
(`AlgebraicGeometry.nonempty_iso_of_forall_exists_nonempty_iso_preimageSnd`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules

variable {K : Type u} [Field K]


/-- The open subscheme `X ×_K Y ×_K U` of `X ×_K Y ×_K Z` lying over an open `U ⊆ Z`. -/
noncomputable abbrev preimageSnd (X Y Z : Over (Spec (.of K))) (U : Z.left.Opens) :
    ((X ⊗ Y) ⊗ Z).left.Opens :=
  (snd (X ⊗ Y) Z).left ⁻¹ᵁ U

instance (X Y : Over (Spec (.of K))) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom :=
  inferInstanceAs (IsProper (Limits.pullback.fst X.hom Y.hom ≫ X.hom))

instance (X Y : Over (Spec (.of K))) [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] : GeometricallyIntegral (X ⊗ Y).hom :=
  GeometricallyIntegral.comp_of_flat (Limits.pullback.fst X.hom Y.hom) X.hom

instance (W Z : Over (Spec (.of K))) [IsProper W.hom] : IsProper (snd W Z).left :=
  inferInstanceAs (IsProper (Limits.pullback.snd W.hom Z.hom))

instance (W Z : Over (Spec (.of K))) : Flat (snd W Z).left :=
  inferInstanceAs (Flat (Limits.pullback.snd W.hom Z.hom))

instance (W Z : Over (Spec (.of K))) [IsProper W.hom] :
    LocallyOfFinitePresentation (snd W Z).left :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd W.hom Z.hom))

instance (W Z : Over (Spec (.of K))) [GeometricallyIntegral W.hom] :
    GeometricallyIntegral (snd W Z).left :=
  inferInstanceAs (GeometricallyIntegral (Limits.pullback.snd W.hom Z.hom))

/-- Isomorphic modules stay isomorphic after pulling back along a further morphism. -/
lemma nonempty_iso_pullback_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) {M N : C.Modules}
    (e : (Scheme.Modules.pullback g).obj M ≅ (Scheme.Modules.pullback g).obj N) :
    Nonempty ((Scheme.Modules.pullback (f ≫ g)).obj M ≅ (Scheme.Modules.pullback (f ≫ g)).obj N) :=
  ⟨(pullbackComp f g).symm.app M ≪≫ (Scheme.Modules.pullback f).mapIso e ≪≫
    (pullbackComp f g).app N⟩

/-- **Triviality on a fibre spreads out** (Stacks, Tag 0BF3).

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`, and
let `M`, `N` be invertible modules on `X ×_K Y ×_K Z` which become isomorphic on the slices
`{x} × Y × Z` and `X × {y} × Z`. If `M` and `N` become isomorphic on the fibre
`X ×_K Y ×_K Spec F` over a point `φ : Spec F ⟶ Z` with values in a field `F`, then they are
isomorphic on `X ×_K Y ×_K U` for an open neighbourhood `U` of the image of `φ`.

This is Tag 0BF3 applied over the base `Z` to `X ×_K Z` and `Y ×_K Z` with the sections given
by `x` and `y`. Its proof is an infinitesimal lifting argument based on the injectivity of
`H¹(X × Y, 𝒪) → H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` (Künneth, Tag 0BF2). Tag 0BF3 asks for triviality on the
fibre over the residue field `κ(t)` of the image `t` of `φ`; this is equivalent to triviality
over `F`, since a morphism `Spec F ⟶ Z` factors through the locally closed subscheme of
Tag 0BDP if and only if `t` lies in it. -/
theorem exists_mem_nonempty_iso_preimageSnd_of_nonempty_iso_fiber (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N))
    (hy : Nonempty (overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) M ≅
      overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) N))
    {F : Type u} [Field F] (φ : Spec (.of F) ⟶ Z.left)
    (hφ : Nonempty
      ((Scheme.Modules.pullback (Limits.pullback.fst (snd (X ⊗ Y) Z).left φ)).obj M ≅
        (Scheme.Modules.pullback (Limits.pullback.fst (snd (X ⊗ Y) Z).left φ)).obj N)) :
    ∃ U : Z.left.Opens, φ.base (IsLocalRing.closedPoint F) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N) := by
  obtain ⟨ex⟩ := hx
  obtain ⟨ey⟩ := hy
  obtain ⟨e⟩ := Scheme.Modules.nonempty_iso_fiber_of_nonempty_iso_pullback
    (snd (X ⊗ Y) Z).left M N φ hφ
  obtain ⟨U, htU, m, hm⟩ := TheoremOfCube.exists_mem_isFreeGenerator X Y Z x y (M ⊗ Nᵛ)
    (nonempty_pullback_tensorObj_dual_iso_unit _ M N ex)
    (nonempty_pullback_tensorObj_dual_iso_unit _ M N ey) _
    (nonempty_pullback_tensorObj_dual_iso_unit _ M N e)
  obtain ⟨d⟩ := nonempty_pullback_ι_iso_unit_of_isFreeGenerator _ hm
  exact ⟨U, htU, nonempty_pullback_iso_of_pullback_tensorObj_dual_iso_unit _ M N d⟩

/-- **The locus of triviality on the fibres is closed** (Stacks, Tags 0BDP and 0BF0).

Let `X`, `Y` be proper and geometrically integral over a field `K`, and let `M`, `N` be
invertible modules on `X ×_K Y ×_K Z`. The set of points `t ∈ Z` such that `M` and `N` become
isomorphic on the fibre `X ×_K Y ×_K Spec κ(t)` is closed.

The projection `X ×_K Y ×_K Z ⟶ Z` is proper, flat, of finite presentation and has
geometrically integral fibres, so this is the seesaw principle
`AlgebraicGeometry.Scheme.Modules.isClosed_setOf_nonempty_iso_fiber`. -/
theorem isClosed_setOf_nonempty_iso_fiber (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible]
    [N.IsInvertible] :
    IsClosed {t : Z.left | Nonempty
      ((Scheme.Modules.pullback
          (Limits.pullback.fst (snd (X ⊗ Y) Z).left (Z.left.fromSpecResidueField t))).obj M ≅
        (Scheme.Modules.pullback
          (Limits.pullback.fst (snd (X ⊗ Y) Z).left (Z.left.fromSpecResidueField t))).obj N)} :=
  Scheme.Modules.isClosed_setOf_nonempty_iso_fiber (snd (X ⊗ Y) Z).left M N

/-- If `M ≅ N` over an open `U ⊆ Z`, then `M ≅ N` on the fibre over every field-valued point
of `U`. -/
lemma nonempty_iso_fiber_of_nonempty_iso_preimageSnd (X Y Z : Over (Spec (.of K)))
    (M N : ((X ⊗ Y) ⊗ Z).left.Modules) {U : Z.left.Opens}
    (e : (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
      (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N)
    {F : Type u} [Field F] (φ : Spec (.of F) ⟶ Z.left)
    (hφ : φ.base (IsLocalRing.closedPoint F) ∈ U) :
    Nonempty
      ((Scheme.Modules.pullback (Limits.pullback.fst (snd (X ⊗ Y) Z).left φ)).obj M ≅
        (Scheme.Modules.pullback (Limits.pullback.fst (snd (X ⊗ Y) Z).left φ)).obj N) := by
  have H : Set.range (Limits.pullback.fst (snd (X ⊗ Y) Z).left φ) ⊆
      Set.range (preimageSnd X Y Z U).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (snd (X ⊗ Y) Z).left ((Limits.pullback.fst (snd (X ⊗ Y) Z).left φ) w) ∈ U
    rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply,
      Subsingleton.elim ((Limits.pullback.snd (snd (X ⊗ Y) Z).left φ) w)
        (IsLocalRing.closedPoint F)]
    exact hφ
  rw [← IsOpenImmersion.lift_fac _ _ H]
  exact nonempty_iso_pullback_comp _ _ e

/-- **Closedness of the locus of triviality** (Stacks, Tags 0BDP, 0BF0 and 0BF3).

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`, and
let `M`, `N` be invertible modules on `X ×_K Y ×_K Z` which become isomorphic on the slices
`{x} × Y × Z` and `X × {y} × Z`. Then the set of points `t ∈ Z` having an open neighbourhood
`U` with `M ≅ N` on `X ×_K Y ×_K U` is closed.

By Tag 0BF3 (`AlgebraicGeometry.exists_mem_nonempty_iso_preimageSnd_of_nonempty_iso_fiber`)
this set is the set of `t` such that `M` and `N` are isomorphic on the fibre over `t`, which is
closed by Tags 0BDP and 0BF0 (`AlgebraicGeometry.isClosed_setOf_nonempty_iso_fiber`). -/
theorem isClosed_setOf_exists_nonempty_iso_preimageSnd (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N))
    (hy : Nonempty (overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) M ≅
      overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) N)) :
    IsClosed {t : Z.left | ∃ U : Z.left.Opens, t ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N)} := by
  convert isClosed_setOf_nonempty_iso_fiber X Y Z M N using 1
  ext t
  constructor
  · rintro ⟨U, htU, ⟨e⟩⟩
    refine nonempty_iso_fiber_of_nonempty_iso_preimageSnd X Y Z M N e _ ?_
    convert htU
    exact Scheme.fromSpecResidueField_apply _ _
  · intro ht
    obtain ⟨U, htU, e⟩ :=
      exists_mem_nonempty_iso_preimageSnd_of_nonempty_iso_fiber X Y Z x y M N hx hy _ ht
    refine ⟨U, ?_, e⟩
    convert htU
    exact (Scheme.fromSpecResidueField_apply _ _).symm

/-- **Openness of the locus of triviality at a rational point** (Stacks, Tag 0BF3).

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`, and
let `z` be a `K`-point of `Z`. If two invertible modules `M`, `N` on `X ×_K Y ×_K Z` become
isomorphic on the slices `{x} × Y × Z`, `X × {y} × Z` and `X × Y × {z}`, then they are
isomorphic on `X ×_K Y ×_K U` for some open neighbourhood `U` of `z`.

The slice `X × Y × {z}` is the fibre over `z`, so this is
`AlgebraicGeometry.exists_mem_nonempty_iso_preimageSnd_of_nonempty_iso_fiber`. -/
theorem exists_mem_nonempty_iso_preimageSnd (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (z : 𝟙_ _ ⟶ Z) (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N))
    (hy : Nonempty (overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) M ≅
      overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) N))
    (hz : Nonempty (overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) M ≅
      overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) N)) :
    ∃ U : Z.left.Opens, z.left.base (IsLocalRing.closedPoint K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N) := by
  refine exists_mem_nonempty_iso_preimageSnd_of_nonempty_iso_fiber X Y Z x y M N hx hy
    (F := K) z.left ?_
  -- The fibre over `z` is the slice `X × Y × {z}`.
  have H : Limits.pullback.fst (snd (X ⊗ Y) Z).left z.left =
      (Limits.pullback.fst (snd (X ⊗ Y) Z).left z.left ≫ (fst (X ⊗ Y) Z).left) ≫
        (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)).left := by
    set pf := Limits.pullback.fst (snd (X ⊗ Y) Z).left z.left
    apply Over.tensorObj_ext
    · change pf ≫ (fst (X ⊗ Y) Z).left =
        (pf ≫ (fst (X ⊗ Y) Z).left) ≫ (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)).left ≫ (fst (X ⊗ Y) Z).left
      rw [← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
    · change pf ≫ (snd (X ⊗ Y) Z).left =
        (pf ≫ (fst (X ⊗ Y) Z).left) ≫ (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)).left ≫ (snd (X ⊗ Y) Z).left
      rw [← Over.comp_left, lift_snd, Over.comp_left, Limits.pullback.condition, ← Category.assoc,
        Over.toUnit_left]
      congr 1
      calc Limits.pullback.snd (snd (X ⊗ Y) Z).left z.left
          = Limits.pullback.snd (snd (X ⊗ Y) Z).left z.left ≫ z.left ≫ Z.hom := by
            rw [Over.w z]; exact (Category.comp_id _).symm
        _ = pf ≫ (snd (X ⊗ Y) Z).left ≫ Z.hom := by rw [← Limits.pullback.condition_assoc]
        _ = (pf ≫ (fst (X ⊗ Y) Z).left) ≫ (X ⊗ Y).hom := by
            rw [Over.w, Category.assoc, Over.w]
  rw [H]
  exact nonempty_iso_pullback_comp _ _ hz.some

/-- **Invertible modules isomorphic locally over the base are isomorphic** (Stacks, Tag 0BDP and
the last step of the proof of Tag 0BF4).

Let `X`, `Y` be proper and geometrically integral over a field `K` and let `x` be a `K`-point of
`X`. If two invertible modules `M`, `N` on `X ×_K Y ×_K Z` are isomorphic on `X ×_K Y ×_K U` for
the members `U` of an open cover of `Z`, and are isomorphic on the slice `{x} × Y × Z`, then
`M ≅ N`.

We show that `L = M ⊗ Nᵛ` is trivial. Let `π : X ×_K (Y ×_K Z) ⟶ Y ×_K Z` be the projection and
`σ` the slice `{x} × Y × Z`, a section of `π`. As `X` is proper and geometrically integral, `π`
induces bijections `Γ(V, 𝒪) ≅ Γ(π⁻¹ V, 𝒪)` on all opens `V`. Local generators of `L` over the
opens `π⁻¹ V`, `V` lying over an open of the cover of `Z`, can be rescaled so that their
pullbacks along `σ` agree with a fixed generator of `σ^* L ≅ 𝒪`; they then agree on overlaps and
glue (`AlgebraicGeometry.Scheme.Modules.exists_isFreeGenerator_top_of_comp_eq_id`). -/
theorem nonempty_iso_of_forall_exists_nonempty_iso_preimageSnd (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X)
    (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hloc : ∀ t : Z.left, ∃ U : Z.left.Opens, t ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
        (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N))
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N)) :
    Nonempty (M ≅ N) := by
  let : X.left.Over (Spec (.of K)) := ⟨X.hom⟩
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : Scheme.GlobalSectionsBijective K X.left :=
    have : IsProper (X.left ↘ Spec (.of K)) := inferInstanceAs (IsProper X.hom)
    have : GeometricallyIntegral (X.left ↘ Spec (.of K)) :=
      inferInstanceAs (GeometricallyIntegral X.hom)
    .of_geometricallyIntegral (k := K) (X := X.left)
  -- The slice `σ : Y × Z ⟶ X × Y × Z` at `x` is a section of the projection `π`.
  set σ := lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)
  let π : ((X ⊗ Y) ⊗ Z).left ⟶ (Y ⊗ Z).left := ((α_ X Y Z).hom ≫ snd X (Y ⊗ Z)).left
  have hσ : σ.left ≫ π = 𝟙 _ := by
    rw [← Over.comp_left]
    have : σ ≫ (α_ X Y Z).hom ≫ snd X (Y ⊗ Z) = 𝟙 _ := by simp [σ]
    rw [this]
    rfl
  have hπq : π ≫ (snd Y Z).left = (snd (X ⊗ Y) Z).left := by
    rw [← Over.comp_left]
    congr 1
    simp
  -- `π` is the base change of `X ⟶ Spec K`, so it induces bijections on sections.
  have H : IsPullback ((α_ X Y Z).hom ≫ fst X (Y ⊗ Z)).left π (X.left ↘ Spec (.of K))
      (Y ⊗ Z).hom := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget _).mapIso (α_ X Y Z)) rfl rfl
    change _ ≫ X.hom = _ ≫ (Y ⊗ Z).hom
    rw [Over.w, Over.w]
  have hπ (V : (Y ⊗ Z).left.Opens) : Function.Surjective (π.app V) :=
    (Scheme.Hom.bijective_app_of_comp_eq_id π σ.left hσ (fun _ hA ↦
      Scheme.GlobalSectionsBijective.isIso_app_of_isPullback H hA) V).2
  -- `L = M ⊗ Nᵛ` is trivial over the opens `π⁻¹ q⁻¹ U` and on the slice.
  choose U hU e using hloc
  have hV : ⨆ t, (snd Y Z).left ⁻¹ᵁ U t = ⊤ :=
    eq_top_iff.2 fun b _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨_, hU ((snd Y Z).left b)⟩
  have hgen (t : Z.left) :
      ∃ m : Γ(M ⊗ Nᵛ, π ⁻¹ᵁ ((snd Y Z).left ⁻¹ᵁ U t)), IsFreeGenerator m := by
    obtain ⟨d⟩ := nonempty_pullback_tensorObj_dual_iso_unit _ M N (e t).some
    obtain ⟨m, hm⟩ := exists_isFreeGenerator_of_pullback_ι_iso _ _ d
    have hO : π ⁻¹ᵁ ((snd Y Z).left ⁻¹ᵁ U t) = preimageSnd X Y Z (U t) := by
      rw [← Scheme.Hom.comp_preimage, hπq]
    exact ⟨_, hm.map hO.le⟩
  choose m hm using hgen
  obtain ⟨d⟩ := nonempty_pullback_tensorObj_dual_iso_unit σ.left M N hx.some
  obtain ⟨g, hg⟩ := exists_isFreeGenerator_top_of_comp_eq_id π σ.left hσ hπ (M ⊗ Nᵛ) _ hV m hm
    ((isFreeGenerator_one ⊤).app_hom d.symm)
  have := isIso_homOfGlobalSection hg
  exact nonempty_iso_of_tensorObj_dual_iso_unit M N (asIso (homOfGlobalSection _ g)).symm

/-- **The theorem of the cube** (Stacks, Tag 0BF4, over `S = Spec K` with `K`-rational points).

Let `X`, `Y` be proper and geometrically integral over a field `K`, let `Z` be a connected
`K`-scheme and let `x`, `y`, `z` be `K`-points of `X`, `Y`, `Z`. If two invertible modules `M`,
`N` on `X ×_K Y ×_K Z` become isomorphic on each of the three slices `{x} × Y × Z`,
`X × {y} × Z` and `X × Y × {z}`, then `M ≅ N`.

Stacks states this for one invertible module `L` (if `L` is trivial on the three slices then
`L` is trivial); the form here follows by applying it to `L = M ⊗ N⁻¹`. Over a field the
flatness and finite presentation hypotheses of Tag 0BF4 are automatic. -/
theorem nonempty_iso_of_nonempty_iso_overPullback_slices (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] [ConnectedSpace Z.left] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (z : 𝟙_ _ ⟶ Z) (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N))
    (hy : Nonempty (overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) M ≅
      overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) N))
    (hz : Nonempty (overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) M ≅
      overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) N)) :
    Nonempty (M ≅ N) := by
  -- The set of points of `Z` over which `M` and `N` are locally isomorphic is open by
  -- definition, closed and contains `z`, hence is all of `Z`.
  set T : Set Z.left := {t | ∃ U : Z.left.Opens, t ∈ U ∧
    Nonempty ((Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj M ≅
      (Scheme.Modules.pullback (preimageSnd X Y Z U).ι).obj N)} with hT
  have hopen : IsOpen T := isOpen_iff_forall_mem_open.2 fun _ ⟨U, htU, e⟩ =>
    ⟨U, fun _ ht' => ⟨U, ht', e⟩, U.isOpen, htU⟩
  have hclosed : IsClosed T :=
    isClosed_setOf_exists_nonempty_iso_preimageSnd X Y Z x y M N hx hy
  have hmem : z.left.base (IsLocalRing.closedPoint K) ∈ T :=
    exists_mem_nonempty_iso_preimageSnd X Y Z x y z M N hx hy hz
  have huniv : T = Set.univ :=
    (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨_, hmem⟩)
  exact nonempty_iso_of_forall_exists_nonempty_iso_preimageSnd X Y Z x M N
    (fun t => show t ∈ T from huniv ▸ Set.mem_univ t) hx

end AlgebraicGeometry
