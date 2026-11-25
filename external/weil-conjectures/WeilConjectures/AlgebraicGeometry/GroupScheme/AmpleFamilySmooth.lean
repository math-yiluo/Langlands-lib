/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated
public import WeilConjectures.AlgebraicGeometry.Divisor.Image
public import WeilConjectures.AlgebraicGeometry.NoetherNormalizationChart
public import WeilConjectures.AlgebraicGeometry.Picard.LocalizationAwayRigidity
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.AmpleFamily

/-!
# Smooth irreducible group schemes have an ample family

Let `G` be a smooth irreducible group scheme of finite type over an algebraically closed field
`k`. We show that `G` has an ample family (`AlgebraicGeometry.Scheme.HasAmpleFamily`), following
the last part of the proof of Stacks 0BF7:

* the complement of a nonempty affine open `U ⊆ G` is an effective Cartier divisor `D` (Stacks
  0BCW), as `G` is separated, noetherian and its local rings are UFDs;
* an affine open `W ⊆ G` is finite and flat over an open `V = D(r) ⊆ 𝔸^d_k`
  (`AlgebraicGeometry.exists_finite_flat_chart`);
* the image `E ⊆ G × V` of `𝒟 = {(g, w) | g j(w) ∈ D} ⊆ G × W` is an effective Cartier divisor,
  whose fibre over a rational point `v` of `V` is `⋃_{w ↦ v} D j(w)⁻¹`, with affine complement
  (`AlgebraicGeometry.GrpObj.compl_support_comap_eq`);
* every closed point of `G` avoids some fibre `E_v`
  (`AlgebraicGeometry.GrpObj.exists_notMem_support_comap`);
* by rigidity (Stacks 0BEH) the line bundles `𝒪_G(E_v)` are all isomorphic, and their canonical
  sections give the ample family (`AlgebraicGeometry.hasAmpleFamily_of_forall_isAffineOpen`).

## Main statements

- `AlgebraicGeometry.GrpObj.hasAmpleFamily_of_smooth_of_irreducibleSpace`: a smooth irreducible
  group scheme of finite type over an algebraically closed field has an ample family.
- `AlgebraicGeometry.Scheme.HasAmpleFamily.of_forall_isClosed`: on a quasi-compact Jacobson
  scheme, sections of an invertible module with affine non-vanishing loci covering the closed
  points form an ample family.
- `AlgebraicGeometry.left_apply_mem_image_iff`: rational points of the image of a closed subset.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj AlgebraicGeometry.Scheme.Modules

/-- Two opens of a Jacobson space containing the same closed points are equal. -/
lemma TopologicalSpace.Opens.eq_of_forall_isClosed_singleton {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {U V : TopologicalSpace.Opens X}
    (h : ∀ x : X, IsClosed {x} → (x ∈ U ↔ x ∈ V)) : U = V := by
  have key {U V : TopologicalSpace.Opens X} (h : ∀ x : X, IsClosed {x} → x ∈ U → x ∈ V) :
      U ≤ V := by
    by_contra hUV
    obtain ⟨x, hxU, hxV⟩ := IsConcreteLE.not_le_iff_exists.mp hUV
    obtain ⟨y, ⟨hyU, hyV⟩, hy⟩ := nonempty_inter_closedPoints (Z := (U : Set X) ∩ (V : Set X)ᶜ)
      ⟨x, hxU, hxV⟩ ⟨U, (V : Set X)ᶜ, U.isOpen, V.isOpen.isClosed_compl, rfl⟩
    exact hyV (h y hy hyU)
  exact le_antisymm (key fun x hx ↦ (h x hx).mp) (key fun x hx ↦ (h x hx).mpr)

namespace AlgebraicGeometry

namespace Scheme

/-- **A criterion for an ample family.** On a quasi-compact Jacobson scheme `X`, an invertible
module `L` with a family of sections whose non-vanishing loci are affine and contain all closed
points of `X` between them gives an ample family: the non-vanishing loci cover `X`, hence finitely
many of them do. -/
theorem HasAmpleFamily.of_forall_isClosed {X : Scheme.{u}} [CompactSpace X] [JacobsonSpace X]
    (L : X.Modules) [L.IsInvertible] {T : Type u} (s : T → (𝟙_ X.Modules ⟶ L))
    (hs : ∀ t, IsAffineOpen (Modules.Hom.zeroLocus (s t)).support.compl)
    (hcov : ∀ x : X, IsClosed {x} → ∃ t, x ∈ (Modules.Hom.zeroLocus (s t)).support.compl) :
    X.HasAmpleFamily := by
  have htop : ⨆ t, (Modules.Hom.zeroLocus (s t)).support.compl = ⊤ :=
    TopologicalSpace.Opens.eq_of_forall_isClosed_singleton fun x hx ↦
      ⟨fun _ ↦ trivial, fun _ ↦ TopologicalSpace.Opens.mem_iSup.mpr (hcov x hx)⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun t ↦ ((Modules.Hom.zeroLocus (s t)).support.compl : Set X))
    (fun t ↦ (Modules.Hom.zeroLocus (s t)).support.compl.isOpen) fun x _ ↦ by
      simpa using (SetLike.ext_iff.mp htop x).mpr trivial
  refine ⟨L, Modules.IsInvertible.sheafOfModules_isInvertible L, F, inferInstance,
    fun t ↦ s t, fun t ↦ hs t, eq_top_iff.mpr fun x _ ↦ ?_⟩
  obtain ⟨t, ht, hx⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨t, ht⟩, hx⟩

/-- An invertible ideal sheaf on a nonempty scheme does not have full support: locally it is
generated by a non-zerodivisor, which is not nilpotent. -/
theorem IdealSheafData.IsInvertible.exists_notMem_support {X : Scheme.{u}} [Nonempty X]
    {J : X.IdealSheafData} (hJ : J.IsInvertible) : ∃ x : X, x ∉ J.support := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨U, hxU, f, hf, hU⟩ := hJ x
  by_contra! h
  have hb : X.basicOpen f = ⊥ := eq_bot_iff.mpr fun y hy ↦ by
    have := (IdealSheafData.mem_support_iff_of_mem (X.basicOpen_le f hy)).mp (h y)
    rw [Scheme.mem_zeroLocus_iff] at this
    exact (this f (hU ▸ Ideal.subset_span rfl) hy).elim
  have := U.2.isLocalization_basicOpen f
  have : Subsingleton Γ(X, X.basicOpen f) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hb)
  obtain ⟨n, hn⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers f)
    (S := Γ(X, X.basicOpen f))).mp this
  have : Nontrivial Γ(X, U.1) := (X.presheaf.germ U.1 x hxU).hom.domain_nontrivial
  have hn' : f ^ n = 0 := hn
  exact zero_notMem_nonZeroDivisors (hn' ▸ pow_mem hf n)

/-- An invertible ideal sheaf `J` is the zero scheme of a section of any invertible module
isomorphic to `𝒪_X(J) = J^∨`. -/
theorem IdealSheafData.IsInvertible.exists_zeroLocus_eq_of_iso {X : Scheme.{u}}
    {J : X.IdealSheafData} (hJ : J.IsInvertible) {L : X.Modules} (e : J.toModulesᵛ ≅ L) :
    ∃ s : 𝟙_ X.Modules ⟶ L, Modules.Hom.zeroLocus s = J := by
  obtain ⟨s, hs⟩ := hJ.exists_zeroLocus_eq
  exact ⟨s ≫ e.hom, by
    rw [Modules.Hom.zeroLocus_eq_of_arrowIso (s ≫ e.hom) s
      (Arrow.isoMk (Iso.refl _) e.symm (by simp)), hs]⟩

end Scheme

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]

variable (k) in
/-- The unique point of the base `Spec k`, as a point of the monoidal unit of `k`-schemes. -/
noncomputable def unitPoint : (𝟙_ (Over (Spec (.of k)))).left :=
  IsLocalRing.closedPoint k

local notation "pt" => unitPoint k

/-- A rational point of a scheme locally of finite type over an algebraically closed field is a
closed point. -/
lemma isClosed_singleton_left_apply {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) : IsClosed {y.left pt} :=
  ((pointEquivClosedPoint Y.hom) ⟨y.left, Over.w y⟩).2

/-- **Rational points of an image.** Let `f : X ⟶ Y` be a morphism of `k`-schemes locally of finite
type over an algebraically closed field `k`, with `X` quasi-compact, and let `Z ⊆ X` be closed. A
rational point `y` of `Y` lies in `f(Z)` if and only if it is the image of a rational point of
`X` lying in `Z`. -/
theorem left_apply_mem_image_iff {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [CompactSpace X.left] (f : X ⟶ Y) {Z : Set X.left}
    (hZ : IsClosed Z) (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y) :
    y.left pt ∈ f.left '' Z ↔ ∃ x : 𝟙_ (Over (Spec (.of k))) ⟶ X, x ≫ f = y ∧ x.left pt ∈ Z := by
  refine ⟨fun ⟨z, hz, hfz⟩ ↦ ?_, fun ⟨x, hx, hxZ⟩ ↦
    ⟨x.left pt, hxZ, by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hx]⟩⟩
  obtain ⟨z', hz', hcl⟩ := isClosed_closure.exists_closed_singleton
    (⟨z, subset_closure rfl⟩ : (closure {z}).Nonempty)
  have hfz' : f.left z' = y.left pt := by
    have := image_closure_subset_closure_image f.left.continuous ⟨z', hz', rfl⟩
    rwa [Set.image_singleton, hfz, (isClosed_singleton_left_apply y).closure_eq] at this
  refine ⟨Over.homMk (pointOfClosedPoint X.hom z' hcl) (pointOfClosedPoint_comp _ _ _), ?_,
    by simpa using hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz) hz'⟩
  refine Over.OverMorphism.ext (ext_of_apply_closedPoint_eq Y.hom (by simp) (Over.w y) ?_)
  simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.homMk_left, pointOfClosedPoint_apply]
  exact hfz'

/-- There are only finitely many rational points of `W` over a given rational point of `V` along a
finite morphism `W ⟶ V`. -/
lemma finite_hom_comp_eq {W V : Over (Spec (.of k))} [LocallyOfFiniteType W.hom] (π : W ⟶ V)
    [IsFinite π.left] (v : 𝟙_ (Over (Spec (.of k))) ⟶ V) :
    Finite {w : 𝟙_ (Over (Spec (.of k))) ⟶ W // w ≫ π = v} := by
  have := (π.left.finite_preimage_singleton (v.left pt)).to_subtype
  refine Finite.of_injective (β := π.left ⁻¹' {v.left pt})
    (fun w ↦ ⟨w.1.left pt, by simp [← Scheme.Hom.comp_apply, ← Over.comp_left, w.2]⟩)
    fun w w' h ↦ Subtype.ext (Over.OverMorphism.ext ?_)
  exact ext_of_apply_closedPoint_eq W.hom (Over.w w.1) (Over.w w'.1) congr($(h).1)

section Group

variable (G : Over (Spec (.of k))) [GrpObj G]

omit [IsAlgClosed k] in
/-- Right translation of a rational point: `g ≫ R_h = g * h`. -/
lemma GrpObj.comp_mulRight (g h : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    g ≫ GrpObj.mulRight G h = lift g h ≫ μ[G] := by
  rw [GrpObj.mulRight, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc,
    toUnit_unique (g ≫ toUnit G) (𝟙 _), Category.id_comp]

omit [IsAlgClosed k] in
/-- Left translation of a rational point: `h ≫ L_g = g * h`. -/
lemma GrpObj.comp_mulLeft (g h : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    h ≫ GrpObj.mulLeft G g = lift g h ≫ μ[G] := by
  rw [GrpObj.mulLeft, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc,
    toUnit_unique (h ≫ toUnit G) (𝟙 _), Category.id_comp]

omit [IsAlgClosed k] in
/-- Right translation by a rational point is an automorphism of the underlying scheme. -/
instance (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) : IsIso (GrpObj.mulRight G g).left :=
  inferInstanceAs (IsIso ((Over.forget _).mapIso (GrpObj.mulRightIso G g)).hom)

variable {W V : Over (Spec (.of k))} (j : W ⟶ G) (π : W ⟶ V)
  (J : G.left.IdealSheafData) (E : (G ⊗ V).left.IdealSheafData)

/-- **The fibres of the image divisor.** Let `j : W ⟶ G` and `π : W ⟶ V`, let `D` be a divisor on
`G` with ideal `J`, `𝒟 = {(g, w) | g j(w) ∈ D}` its pullback along `G × W ⟶ G`, and `E` a divisor
on `G × V` with support `(1 × π)(𝒟)`. A rational point `g` of `G` lies on the fibre `E_v` of `E`
at a rational point `v` of `V` if and only if `g j(w) ∈ D` for some rational point `w` of `W`
over `v`. -/
theorem GrpObj.left_apply_mem_support_comap_iff [LocallyOfFiniteType (G ⊗ W).hom]
    [LocallyOfFiniteType (G ⊗ V).hom] [CompactSpace (G ⊗ W).left]
    (hE : (E.support : Set (G ⊗ V).left) =
      (G ◁ π).left '' (J.comap ((G ◁ j) ≫ μ[G]).left).support)
    (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) (v : 𝟙_ (Over (Spec (.of k))) ⟶ V) :
    g.left pt ∈ (E.comap (lift (𝟙 G) (toUnit G ≫ v)).left).support ↔
      ∃ w : 𝟙_ (Over (Spec (.of k))) ⟶ W, w ≫ π = v ∧
        (GrpObj.mulRight G (w ≫ j)).left (g.left pt) ∈ J.support := by
  have hgv : g ≫ lift (𝟙 G) (toUnit G ≫ v) = lift g v := by simp
  rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_comap, Set.mem_preimage,
    ← Scheme.Hom.comp_apply, ← Over.comp_left, hgv, hE,
    left_apply_mem_image_iff _ (Scheme.IdealSheafData.support _).isClosed]
  have key (x : 𝟙_ (Over (Spec (.of k))) ⟶ G ⊗ W) :
      x.left pt ∈ (J.comap ((G ◁ j) ≫ μ[G]).left).support ↔
        (x ≫ (G ◁ j) ≫ μ[G]).left pt ∈ J.support := by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_comap, Set.mem_preimage,
      ← Scheme.Hom.comp_apply, ← Over.comp_left, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, hxs⟩
    have hg : x ≫ fst _ _ = g := by
      rw [← whiskerLeft_fst G π, ← Category.assoc, hx, lift_fst]
    refine ⟨x ≫ snd _ _, ?_, ?_⟩
    · rw [Category.assoc, ← whiskerLeft_snd, ← Category.assoc, hx, lift_snd]
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.comp_mulRight]
      have h : lift g ((x ≫ snd _ _) ≫ j) ≫ μ[G] = x ≫ (G ◁ j) ≫ μ[G] := by
        rw [← hg, ← Category.assoc]
        congr 1
        ext <;> simp
      rw [h]
      exact (key x).mp hxs
  · rintro ⟨w, hw, hmem⟩
    refine ⟨lift g w, by rw [lift_whiskerLeft, hw], (key _).mpr ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.comp_mulRight] at hmem
    rwa [← Category.assoc, lift_whiskerLeft]

/-- The rational point of `G` through a closed point `x`. -/
noncomputable abbrev overPointOfClosedPoint [LocallyOfFiniteType G.hom] (x : G.left)
    (hx : IsClosed {x}) :
    𝟙_ (Over (Spec (.of k))) ⟶ G :=
  Over.homMk (pointOfClosedPoint G.hom x hx) (pointOfClosedPoint_comp _ _ _)

omit [GrpObj G] in
/-- The rational point through a closed point `x` passes through `x`. -/
lemma overPointOfClosedPoint_left_apply [LocallyOfFiniteType G.hom] (x : G.left)
    (hx : IsClosed {x}) :
    (overPointOfClosedPoint G x hx).left pt = x :=
  pointOfClosedPoint_apply _ _ _ _

/-- **The fibres of the image divisor are affine.** In the situation of
`GrpObj.left_apply_mem_support_comap_iff`, if `D` is the complement of an open `U`, then the
complement of the fibre `E_v` is the intersection of the right translates `U j(w)⁻¹` over the
rational points `w` of `W` over `v`. -/
theorem GrpObj.compl_support_comap_eq [LocallyOfFiniteType G.hom] [LocallyOfFiniteType W.hom]
    [LocallyOfFiniteType (G ⊗ W).hom] [LocallyOfFiniteType (G ⊗ V).hom]
    [CompactSpace (G ⊗ W).left] [IsFinite π.left]
    (hE : (E.support : Set (G ⊗ V).left) =
      (G ◁ π).left '' (J.comap ((G ◁ j) ≫ μ[G]).left).support)
    {U : G.left.Opens} (hJU : (J.support : Set G.left) = (U : Set G.left)ᶜ)
    (v : 𝟙_ (Over (Spec (.of k))) ⟶ V) :
    (E.comap (lift (𝟙 G) (toUnit G ≫ v)).left).support.compl =
      ⨅ w : {w : 𝟙_ (Over (Spec (.of k))) ⟶ W // w ≫ π = v},
        (GrpObj.mulRight G (w.1 ≫ j)).left ⁻¹ᵁ U := by
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  refine TopologicalSpace.Opens.eq_of_forall_isClosed_singleton fun x hx ↦ ?_
  rw [← overPointOfClosedPoint_left_apply G x hx]
  have := finite_hom_comp_eq π v
  have hc (y : G.left) (C : G.left.IdealSheafData) : y ∈ C.support.compl ↔ y ∉ C.support :=
    Iff.rfl
  rw [← SetLike.mem_coe (p := ⨅ _, _), TopologicalSpace.Opens.coe_iInf, hc,
    GrpObj.left_apply_mem_support_comap_iff G j π J E hE]
  simp [← SetLike.mem_coe, hJU]

/-- **Every closed point lies outside some fibre of the image divisor.** In the situation of
`GrpObj.left_apply_mem_support_comap_iff`, assume that `j` is flat, `J` is invertible and that the
image of every effective Cartier divisor on `W` under `π` is the support of an effective Cartier
divisor on `V`. Then for every closed point `x` of `G` there is a rational point `v` of `V` with
`x ∉ E_v`: choose `v` outside the image of `{w | x j(w) ∈ D}`. -/
theorem GrpObj.exists_notMem_support_comap [LocallyOfFiniteType G.hom]
    [LocallyOfFiniteType (G ⊗ W).hom] [LocallyOfFiniteType (G ⊗ V).hom]
    [CompactSpace (G ⊗ W).left] [LocallyOfFiniteType V.hom] [Nonempty V.left] [Flat j.left]
    (hπ : ∀ C : W.left.IdealSheafData, C.IsInvertible →
      ∃ E' : V.left.IdealSheafData, E'.IsInvertible ∧
        (E'.support : Set V.left) = π.left '' C.support)
    (hJ : J.IsInvertible)
    (hE : (E.support : Set (G ⊗ V).left) =
      (G ◁ π).left '' (J.comap ((G ◁ j) ≫ μ[G]).left).support)
    (x : G.left) (hx : IsClosed {x}) :
    ∃ v : 𝟙_ (Over (Spec (.of k))) ⟶ V, x ∉ (E.comap (lift (𝟙 G) (toUnit G ≫ v)).left).support := by
  have := GrpObj.isIso_mulLeft_left G (overPointOfClosedPoint G x hx)
  have : Flat (j ≫ GrpObj.mulLeft G (overPointOfClosedPoint G x hx)).left := by
    rw [Over.comp_left]
    infer_instance
  obtain ⟨E', hE', hE's⟩ :=
    hπ _ (hJ.comap_of_flat (j ≫ GrpObj.mulLeft G (overPointOfClosedPoint G x hx)).left)
  obtain ⟨v₀, hv₀⟩ := hE'.exists_notMem_support
  have : JacobsonSpace V.left := LocallyOfFiniteType.jacobsonSpace V.hom
  obtain ⟨v₁, hv₁, hv₁c⟩ := nonempty_inter_closedPoints (Z := (E'.support : Set V.left)ᶜ) ⟨v₀, hv₀⟩
    E'.support.isClosed.isOpen_compl.isLocallyClosed
  rw [mem_closedPoints_iff] at hv₁c
  refine ⟨Over.homMk (pointOfClosedPoint V.hom v₁ hv₁c) (pointOfClosedPoint_comp _ _ _), ?_⟩
  rw [← overPointOfClosedPoint_left_apply G x hx,
    GrpObj.left_apply_mem_support_comap_iff G j π J E hE]
  rintro ⟨w, hw, hmem⟩
  refine hv₁ (hE's ▸ ⟨w.left pt, ?_, ?_⟩)
  · rw [Scheme.IdealSheafData.coe_support_comap, Set.mem_preimage,
      ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Category.assoc, GrpObj.comp_mulLeft,
      ← GrpObj.comp_mulRight, Over.comp_left, Scheme.Hom.comp_apply]
    exact hmem
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hw]
    exact pointOfClosedPoint_apply _ _ _ _

omit [GrpObj G] in
/-- **Assembly of the ample family.** Let `G` be an integral group scheme of finite type over an
algebraically closed field `k` with factorial local rings, let `V = D(r) ⊆ 𝔸^d_k` and let `E` be
an effective Cartier divisor on `G × V` whose fibres `E_v` over the rational points `v` of `V`
have affine complements, every closed point of `G` lying outside some `E_v`. Then `G` has an
ample family: by rigidity (Stacks 0BEH) the line bundles `𝒪_G(E_v)` are all isomorphic to a single
`L`, and the canonical sections of the `𝒪_G(E_v)` give sections of `L` with non-vanishing loci
`G \ E_v`. -/
theorem hasAmpleFamily_of_forall_isAffineOpen [LocallyOfFiniteType G.hom]
    [QuasiCompact G.hom] [IsIntegral G.left]
    (hG : ∀ x : G.left, UniqueFactorizationMonoid (G.left.presheaf.stalk x)) {d : ℕ}
    (r : MvPolynomial (Fin d) k)
    (E : (G ⊗ Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap k (Localization.Away r))))).left.IdealSheafData) (hE : E.IsInvertible)
    (haff : ∀ v, IsAffineOpen (E.comap (lift (𝟙 G) (toUnit G ≫ v)).left).support.compl)
    (hcov : ∀ x : G.left, IsClosed {x} →
      ∃ v, x ∉ (E.comap (lift (𝟙 G) (toUnit G ≫ v)).left).support) :
    G.left.HasAmpleFamily := by
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  have : Scheme.Modules.IsInvertible (X := pullback G.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))))) E.toModulesᵛ :=
    hE.isInvertible_dual_toModules
  let T := {v // ∃ x, x ∉ (E.comap (lift (𝟙 G) (toUnit G ≫ v)).left).support}
  have hT (t : T) : (E.comap (lift (𝟙 G) (toUnit G ≫ t.1)).left).IsInvertible := by
    refine (hE.isLocallyPrincipal.comap _).isInvertible fun h ↦ ?_
    obtain ⟨x, hx⟩ := t.2
    exact hx (by rw [h, Scheme.IdealSheafData.support_bot]; trivial)
  obtain ⟨x₀, -, hx₀⟩ := (isClosed_univ (X := G.left)).exists_closed_singleton
    ⟨Classical.arbitrary _, trivial⟩
  obtain ⟨v₀, hv₀⟩ := hcov x₀ hx₀
  let t₀ : T := ⟨v₀, x₀, hv₀⟩
  have he (t : T) : Nonempty ((E.comap (lift (𝟙 G) (toUnit G ≫ t.1)).left).toModulesᵛ ≅
      (E.comap (lift (𝟙 G) (toUnit G ≫ t₀.1)).left).toModulesᵛ) := by
    obtain ⟨e₁⟩ := hE.nonempty_pullback_dual_toModules_iso _ (hT t)
    obtain ⟨e₂⟩ := hE.nonempty_pullback_dual_toModules_iso _ (hT t₀)
    obtain ⟨e⟩ := nonempty_iso_pullback_lift_of_isAlgClosed_mvPolynomial G.left hG G.hom r
      t.1.left t₀.1.left (Over.w t.1) (Over.w t₀.1) E.toModulesᵛ
    exact ⟨e₁.symm ≪≫ e ≪≫ e₂⟩
  have hs (t : T) := (hT t).exists_zeroLocus_eq_of_iso (he t).some
  have := (hT t₀).isInvertible_dual_toModules
  refine Scheme.HasAmpleFamily.of_forall_isClosed _ (fun t ↦ (hs t).choose) (fun t ↦ ?_)
    fun x hx ↦ ?_
  · rw [(hs t).choose_spec]
    exact haff t.1
  · obtain ⟨v, hv⟩ := hcov x hx
    exact ⟨⟨v, x, hv⟩, by rw [(hs _).choose_spec]; exact hv⟩

omit [IsAlgClosed k] in
/-- Multiplication `G ⊗ G ⟶ G` of a group scheme over a field is flat: it is the composite of
the shear automorphism and the second projection. -/
instance GrpObj.flat_mul_left [Flat G.hom] : Flat μ[G].left := by
  have h : μ[G] = (CategoryTheory.GrpObj.shearIso G).hom ≫ snd G G := by
    simp [CategoryTheory.GrpObj.shearIso, Hom.mul_def]
  have : IsIso (CategoryTheory.GrpObj.shearIso G).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso (CategoryTheory.GrpObj.shearIso G)).hom)
  rw [h, Over.comp_left, Over.snd_left]
  infer_instance

/-- **Smooth irreducible group schemes have an ample family** (Stacks 0BF7, smooth irreducible
case). Let `G` be a smooth irreducible group scheme of finite type over an algebraically closed
field `k`. Then `G` carries an invertible module with finitely many sections whose non-vanishing
loci are affine and cover `G`. -/
@[stacks 0BF7]
theorem GrpObj.hasAmpleFamily_of_smooth_of_irreducibleSpace [LocallyOfFiniteType G.hom]
    [QuasiCompact G.hom] [Smooth G.hom] [IrreducibleSpace G.left] : G.left.HasAmpleFamily := by
  have := IsRegular.of_smooth G.hom
  have := isNoetherian_left G
  have : IsIntegral G.left := IsRegular.isIntegral G.left
  have hG := IsRegular.uniqueFactorizationMonoid_stalk (X := G.left)
  have : G.left.IsSeparated := ⟨by rw [← terminal.comp_from G.hom]; infer_instance⟩
  obtain ⟨x₀⟩ : Nonempty G.left := inferInstance
  obtain ⟨U, hU, hx₀U, -⟩ := exists_isAffineOpen_mem_and_subset (x := x₀) (U := ⊤) trivial
  obtain ⟨J, hJ, hJU⟩ := G.left.exists_isInvertible_support_eq_compl hG hU ⟨x₀, hx₀U⟩
  obtain ⟨W, j, d, r, π, hj, hWa, hWne, hr, hπf, hπfl, hπlfp, hcomm⟩ :=
    exists_finite_flat_chart G.left G.hom
  have := smooth_specMap_algebraMap_localizationAway r
  have := geometricallyIrreducible_specMap_algebraMap_localizationAway hr
  let V : Over (Spec (.of k)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))))
  let jo : Over.mk (j ≫ G.hom) ⟶ G := Over.homMk j
  let πo : Over.mk (j ≫ G.hom) ⟶ V := Over.homMk π hcomm.symm
  have : LocallyOfFiniteType (Over.mk (j ≫ G.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ G.hom))
  have : LocallyOfFiniteType V.hom := inferInstanceAs (LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r)))))
  have : LocallyOfFiniteType (G ⊗ Over.mk (j ≫ G.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom (j ≫ G.hom) ≫ G.hom))
  have : Smooth (G ⊗ V).hom := inferInstanceAs (Smooth (pullback.fst G.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) ≫ G.hom))
  have := IsRegular.of_smooth (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))))
  have : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  have : CompactSpace (G ⊗ Over.mk (j ≫ G.hom)).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd G.hom (j ≫ G.hom))
  have := IsRegular.of_smooth (G ⊗ V).hom
  have := LocallyOfFiniteType.isLocallyNoetherian (G ⊗ V).hom
  have : IrreducibleSpace (G ⊗ V).left :=
    inferInstanceAs (IrreducibleSpace ↥(Limits.pullback G.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))))))
  have : IsIntegral (G ⊗ V).left := IsRegular.isIntegral _
  have : IsFinite (G ◁ πo).left := by
    rw [Over.whiskerLeft_left]
    exact MorphismProperty.pullbackMap (MorphismProperty.id_mem _ _) hπf (by simp) hcomm
  have : Flat (G ◁ πo).left := by
    rw [Over.whiskerLeft_left]
    exact MorphismProperty.pullbackMap (MorphismProperty.id_mem _ _) hπfl (by simp) hcomm
  have : Flat ((G ◁ jo) ≫ μ[G]).left := by
    rw [Over.comp_left, Over.whiskerLeft_left]
    exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.pullbackMap
      (MorphismProperty.id_mem _ _) (inferInstanceAs (Flat j)) (by simp) (by simp)) inferInstance
  obtain ⟨E, hE, hEs⟩ := Scheme.Hom.exists_isInvertible_support_eq_image (G ◁ πo).left
    IsRegular.uniqueFactorizationMonoid_stalk (hJ.comap_of_flat ((G ◁ jo) ≫ μ[G]).left)
  have : IsFinite πo.left := hπf
  have : Flat jo.left := inferInstanceAs (Flat j)
  have : CompactSpace (Over.mk (j ≫ G.hom)).left := inferInstanceAs (CompactSpace W)
  have hsurj : Function.Surjective π := by
    have hcl : IsClopen (Set.range π) := ⟨π.isClosedMap.isClosed_range, π.isOpenMap.isOpen_range⟩
    exact Set.range_eq_univ.mp (hcl.eq_univ ⟨_, hWne.some, rfl⟩)
  refine hasAmpleFamily_of_forall_isAffineOpen G hG r E hE (fun v ↦ ?_) fun x hx ↦ ?_
  · rw [GrpObj.compl_support_comap_eq G jo πo J E hEs hJU v]
    have := finite_hom_comp_eq πo v
    obtain ⟨w, hw, -⟩ := (left_apply_mem_image_iff πo isClosed_univ v).mp (by
      obtain ⟨y, hy⟩ := hsurj (v.left (unitPoint k))
      exact ⟨y, trivial, hy⟩)
    have : Nonempty {w // w ≫ πo = v} := ⟨⟨w, hw⟩⟩
    exact IsAffineOpen.iInf fun w ↦ hU.preimage _
  · have : Nonempty V.left := ⟨π hWne.some⟩
    exact GrpObj.exists_notMem_support_comap G jo πo J E
      (fun C hC ↦ Scheme.Hom.exists_isInvertible_support_eq_image π
        IsRegular.uniqueFactorizationMonoid_stalk hC) hJ hEs x hx

end Group

end AlgClosed

end AlgebraicGeometry
