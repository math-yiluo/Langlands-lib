/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.AlgebraicGeometry.Sites.FilteredColimitSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.CategoryTheory.Sites.CohomologyFilteredColimit

/-!
# Étale cohomology of a qcqs scheme commutes with filtered colimits

Let `X` be a quasi-compact quasi-separated scheme and `c` a colimit cocone of a filtered diagram
`D : K ⥤ Sh(X_ét, Ab)` of abelian étale sheaves. Then `colim_k Hᵠ(X, D_k) ⟶ Hᵠ(X, c.pt)` is
bijective for every `q` ([Stacks 03Q6]).

## Main statements

- `AlgebraicGeometry.Scheme.exists_app_eq_of_isColimit_ab`,
  `AlgebraicGeometry.Scheme.exists_map_eq_of_isColimit_ab`: sections over a quasi-compact
  quasi-separated étale `X`-scheme commute with filtered colimits of abelian étale sheaves.
- `AlgebraicGeometry.Scheme.subsingleton_H_succ_of_isColimit_of_injective`: a filtered colimit
  of injective abelian étale sheaves on a qcqs scheme has no higher cohomology.
- `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered_small`: étale cohomology of a qcqs
  scheme commutes with filtered colimits indexed by a `u + 1`-small category.
- `AlgebraicGeometry.Scheme.H_map_of_directed_of_locally`: étale cohomology of a qcqs scheme
  commutes with directed unions of subsheaves, indexed by a type of arbitrary size.
- `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered_of_large`: étale cohomology of a qcqs
  scheme commutes with filtered colimits indexed by a category of arbitrary size.

## Implementation notes

The small case is the site-generic `CategoryTheory.Sheaf.H_map_isColimit_of_isFiltered_small`
applied to the quasi-compact quasi-separated étale `X`-schemes. Its proof is the one sketched in
[Stacks 03Q6]. Sections over quasi-compact quasi-separated
étale `X`-schemes commute with filtered colimits, hence so do the Čech complexes on finite
families of such schemes. A filtered colimit of injective sheaves (which need not be injective)
therefore has exact Čech complexes in positive degrees, so it has no higher cohomology by the
Čech criterion `CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex`. Embedding the
diagram functorially into a diagram of injective sheaves (by the functorial factorization of
`CategoryTheory.IsGrothendieckAbelian`), filtered colimits being exact, we conclude by dimension
shifting along the long exact cohomology sequences.

For filtered categories which are not `u + 1`-small, colimits of other diagrams of that shape
need not exist, so dimension shifting is not available directly. Instead we use that the stalk
functors at geometric points, being left adjoints, preserve colimits of any size: this shows
that the images of the legs of the colimit cocone form a directed family of subsheaves locally
exhausting the colimit, and that the kernels of the transition maps locally exhaust the kernels
of the legs. Reindexing directed families of subsheaves by their `u + 1`-small families of
sections reduces to the small case.
-/

@[expose] public section

universe w w₁ w₂ v₁ u₁ u

open CategoryTheory Limits Opposite

/-! ### Filtered colimits of arbitrary size -/

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  {P : ObjectProperty (GrothendieckTopology.Point.{w} J)} [ObjectProperty.Small.{w} P]
  {𝒥 : Type w₁} [Category.{w₂} 𝒥] [IsFiltered 𝒥] {D : 𝒥 ⥤ Sheaf J AddCommGrpCat.{w}}
  {c : Cocone D}

/-- **Sections of a filtered colimit of arbitrary size are locally lifted.** On a site with a
conservative family of points, every section of the colimit `c.pt` of a filtered diagram of
abelian sheaves is, on the members of a covering sieve, the image of a section of some `D j`.
-/
lemma exists_mem_forall_exists_app_eq_of_isColimit (hP : P.IsConservativeFamilyOfPoints)
    (hc : IsColimit c) {X : C} (s : c.pt.obj.obj (op X)) :
    ∃ R ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f →
      ∃ (j : 𝒥) (t : (D.obj j).obj.obj (op Y)),
        (c.ι.app j).hom.app (op Y) t = c.pt.obj.map f.op s := by
  let R : Sieve X :=
    { arrows Y f := ∃ (j : 𝒥) (t : (D.obj j).obj.obj (op Y)),
        (c.ι.app j).hom.app (op Y) t = c.pt.obj.map f.op s
      downward_closed {Y Z f} := by
        rintro ⟨j, t, ht⟩ g
        refine ⟨j, (D.obj j).obj.map g.op t, ?_⟩
        rw [NatTrans.naturality_apply, ht, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        rfl }
  refine ⟨R, ?_, fun _ _ hf ↦ hf⟩
  obtain ⟨I, Y, f, hf⟩ := R.exists_eq_ofArrows
  rw [hf, hP.jointly_reflect_ofArrows_mem_of_small]
  intro Φ x
  have hd := isColimitOfPreserves (Φ.obj.sheafFiber (A := AddCommGrpCat.{w})) hc
  obtain ⟨j, p, hp⟩ := AddCommGrpCat.exists_ι_apply_eq_of_isColimit hd
    (Φ.obj.toPresheafFiber X x c.pt.obj s)
  obtain ⟨Y₁, y₁, t, rfl⟩ := Φ.obj.toPresheafFiber_jointly_surjective (P := (D.obj j).obj) p
  -- the two germs live over a common neighbourhood `Z` of `x` and `y₁`
  let Z := IsCofiltered.min (Φ.obj.fiber.elementsMk X x) (Φ.obj.fiber.elementsMk Y₁ y₁)
  let f₁ := IsCofiltered.minToLeft (Φ.obj.fiber.elementsMk X x) (Φ.obj.fiber.elementsMk Y₁ y₁)
  let f₂ := IsCofiltered.minToRight (Φ.obj.fiber.elementsMk X x) (Φ.obj.fiber.elementsMk Y₁ y₁)
  have e₁ : Φ.obj.toPresheafFiber X x c.pt.obj s =
      Φ.obj.toPresheafFiber Z.1 Z.2 c.pt.obj (c.pt.obj.map f₁.1.op s) := by
    rw [← ConcreteCategory.comp_apply, Φ.obj.toPresheafFiber_w, f₁.2]
  have e₂ : (Φ.obj.sheafFiber.map (c.ι.app j)) (Φ.obj.toPresheafFiber Y₁ y₁ (D.obj j).obj t) =
      Φ.obj.toPresheafFiber Z.1 Z.2 c.pt.obj
        (c.pt.obj.map f₂.1.op ((c.ι.app j).hom.app (op Y₁) t)) := by
    rw [← ConcreteCategory.comp_apply, Φ.obj.toPresheafFiber_w, f₂.2]
    exact ConcreteCategory.congr_hom
      (Φ.obj.toPresheafFiber_naturality (c.ι.app j).hom Y₁ y₁) t
  change (Φ.obj.sheafFiber.map (c.ι.app j)) _ = _ at hp
  rw [e₂, e₁, GrothendieckTopology.Point.toPresheafFiber_eq_iff'] at hp
  obtain ⟨W, g, w, hw, hg⟩ := hp
  have hgR : R (g ≫ f₁.1) := by
    refine ⟨j, (D.obj j).obj.map (g ≫ f₂.1).op t, ?_⟩
    rw [NatTrans.naturality_apply]
    change c.pt.obj.map (g ≫ f₂.1).op ((c.ι.app j).hom.app _ t) = _
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hg, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp]
  rw [hf] at hgR
  obtain ⟨V, a, b, ⟨i⟩, hab⟩ := hgR
  refine ⟨i, Φ.obj.fiber.map a w, ?_⟩
  rw [← Functor.map_comp_apply, hab, Functor.map_comp_apply, hw, f₁.2]

/-- **Sections of a filtered colimit of arbitrary size are locally separated.** On a site with
a conservative family of points, a section of `D j` which vanishes in the colimit `c.pt`
vanishes, on the members of a covering sieve, in some later `D j'`. -/
lemma exists_mem_forall_exists_map_eq_zero_of_isColimit (hP : P.IsConservativeFamilyOfPoints)
    (hc : IsColimit c) {X : C} {j : 𝒥} (s : (D.obj j).obj.obj (op X))
    (hs : (c.ι.app j).hom.app (op X) s = 0) :
    ∃ R ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f →
      ∃ (j' : 𝒥) (a : j ⟶ j'), (D.map a).hom.app (op Y) ((D.obj j).obj.map f.op s) = 0 := by
  let R : Sieve X :=
    { arrows Y f := ∃ (j' : 𝒥) (a : j ⟶ j'),
        (D.map a).hom.app (op Y) ((D.obj j).obj.map f.op s) = 0
      downward_closed {Y Z f} := by
        rintro ⟨j', a, ha⟩ g
        refine ⟨j', a, ?_⟩
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, NatTrans.naturality_apply,
          ha, map_zero] }
  refine ⟨R, ?_, fun _ _ hf ↦ hf⟩
  obtain ⟨I, Y, f, hf⟩ := R.exists_eq_ofArrows
  rw [hf, hP.jointly_reflect_ofArrows_mem_of_small]
  intro Φ x
  have hd := isColimitOfPreserves (Φ.obj.sheafFiber (A := AddCommGrpCat.{w})) hc
  have h0 : (Φ.obj.sheafFiber.map (c.ι.app j)) (Φ.obj.toPresheafFiber X x (D.obj j).obj s) =
      0 := by
    have := ConcreteCategory.congr_hom
      (Φ.obj.toPresheafFiber_naturality (c.ι.app j).hom X x) s
    refine this.trans ?_
    rw [ConcreteCategory.comp_apply, hs, map_zero]
  obtain ⟨j', a, ha⟩ := AddCommGrpCat.exists_map_eq_zero_of_isColimit hd _ h0
  have ha' : Φ.obj.toPresheafFiber X x (D.obj j').obj ((D.map a).hom.app (op X) s) =
      Φ.obj.toPresheafFiber X x (D.obj j').obj 0 := by
    rw [map_zero, ← ha]
    exact (ConcreteCategory.congr_hom
      (Φ.obj.toPresheafFiber_naturality (D.map a).hom X x) s).symm
  rw [GrothendieckTopology.Point.toPresheafFiber_eq_iff'] at ha'
  obtain ⟨W, g, w, hw, hg⟩ := ha'
  have hgR : R g := ⟨j', a, by rw [NatTrans.naturality_apply, hg, map_zero]⟩
  rw [hf] at hgR
  obtain ⟨V, p, b, ⟨i⟩, hab⟩ := hgR
  exact ⟨i, Φ.obj.fiber.map p w, by rw [← Functor.map_comp_apply, hab, hw]⟩

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.Scheme

section Sections

open Presheaf

variable {X : Scheme.{u}}

/-- Every covering sieve of a quasi-compact étale `X`-scheme `W` contains a finite family
generating a covering sieve. -/
lemma exists_finite_ofArrows_mem_smallEtaleTopology {W : X.Etale} [CompactSpace W.left]
    (R : Sieve W) (hR : R ∈ X.smallEtaleTopology W) :
    ∃ (n : ℕ) (U : Fin n → Over W), (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ X.smallEtaleTopology W := by
  obtain ⟨n, U, g, hRg, -, hg⟩ := (AlgebraicGeometry.Etale.exists_affine_refinement _) hR
  exact ⟨n, fun a ↦ Over.mk (g a), hRg, (ofArrows_mem_smallEtaleTopology_iff g).2 hg⟩

/-- The quasi-compact quasi-separated étale `X`-schemes satisfy the hypothesis of the Čech
criterion `CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex`: every covering
sieve of such a `V` contains a finite family generating a covering sieve, whose Čech nerve has
quasi-compact quasi-separated members. -/
lemma exists_finite_cechNerve_qcqs (V : X.Etale)
    (hV : CompactSpace V.left ∧ QuasiSeparatedSpace V.left) (R : Sieve V)
    (hR : R ∈ X.smallEtaleTopology V) :
    ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), CompactSpace (cechNerveObj U y).left.left ∧
        QuasiSeparatedSpace (cechNerveObj U y).left.left) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ X.smallEtaleTopology V := by
  obtain ⟨_, _⟩ := hV
  obtain ⟨n, U, g, hRg, hU, hg⟩ := (AlgebraicGeometry.Etale.exists_affine_refinement _) hR
  refine ⟨n, fun a ↦ Over.mk (g a), fun k y ↦ ?_, hRg,
    (ofArrows_mem_smallEtaleTopology_iff g).2 hg⟩
  refine compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦ ?_
  have := hU (y l)
  exact ⟨inferInstanceAs (CompactSpace (U (y l)).left),
    inferInstanceAs (QuasiSeparatedSpace (U (y l)).left)⟩

variable {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]
  {F : K ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone F}

/-- **Sections over a quasi-compact `W` of a filtered colimit of abelian sheaves are separated
at a finite stage.** Two sections of `F k` over `W` with the same image in `c.pt` agree in some
later `F k'`. -/
theorem exists_map_eq_of_isColimit_ab (hc : IsColimit c) {W : X.Etale} [CompactSpace W.left]
    {k : K} (t t' : (F.obj k).obj.obj (op W))
    (h : (c.ι.app k).hom.app (op W) t = (c.ι.app k).hom.app (op W) t') :
    ∃ (k' : K) (a : k ⟶ k'), (F.map a).hom.app (op W) t = (F.map a).hom.app (op W) t' :=
  Sheaf.exists_map_eq_of_isColimit_of_finite hc exists_finite_ofArrows_mem_smallEtaleTopology
    t t' h

/-- **Sections over a quasi-compact `W` of a filtered colimit of abelian sheaves vanish at a
finite stage.** A section of `F k` over `W` which vanishes in `c.pt` vanishes in some later
`F k'`. -/
theorem exists_map_eq_zero_of_isColimit_ab (hc : IsColimit c) {W : X.Etale}
    [CompactSpace W.left] {k : K} (t : (F.obj k).obj.obj (op W))
    (h : (c.ι.app k).hom.app (op W) t = 0) :
    ∃ (k' : K) (a : k ⟶ k'), (F.map a).hom.app (op W) t = 0 :=
  Sheaf.exists_map_eq_zero_of_isColimit_of_finite hc
    exists_finite_ofArrows_mem_smallEtaleTopology t h

/-- **Sections over a quasi-compact quasi-separated `W` of a filtered colimit of abelian
sheaves come from a finite stage.** Every section of `c.pt` over `W` is the image of a section
of some `F k` (Stacks 0738). -/
theorem exists_app_eq_of_isColimit_ab (hc : IsColimit c) {W : X.Etale} [CompactSpace W.left]
    [QuasiSeparatedSpace W.left] (s : c.pt.obj.obj (op W)) :
    ∃ (k : K) (t : (F.obj k).obj.obj (op W)), (c.ι.app k).hom.app (op W) t = s :=
  Sheaf.exists_app_eq_of_isColimit_of_finite hc _ exists_finite_cechNerve_qcqs
    ⟨‹_›, ‹_›⟩ s

variable (X) in
/-- On a quasi-compact quasi-separated scheme `X`, a filtered colimit of injective abelian étale
sheaves has no higher cohomology. This is
`CategoryTheory.Sheaf.subsingleton_H_succ_of_isColimit_of_injective` for the étale `X`-schemes
with quasi-compact quasi-separated underlying scheme. -/
theorem subsingleton_H_succ_of_isColimit_of_injective [CompactSpace X]
    [QuasiSeparatedSpace X] [∀ k, Injective (F.obj k)] (hc : IsColimit c) (q : ℕ) :
    Subsingleton (Sheaf.H c.pt (q + 1)) :=
  Sheaf.subsingleton_H_succ_of_isColimit_of_injective
    (MorphismProperty.Over.mkIdTerminal _ X : IsTerminal (Etale.mk (𝟙 X))) _
    ⟨‹CompactSpace X›, ‹QuasiSeparatedSpace X›⟩ exists_finite_cechNerve_qcqs hc q

end Sections

/-- **Étale cohomology commutes with `u + 1`-small filtered colimits on a qcqs scheme.** Let
`X` be quasi-compact and quasi-separated and let `c` be a colimit cocone of a filtered diagram
`D : K ⥤ Sh(X_ét, Ab)` indexed by a `u + 1`-small category. Then for every `q` the canonical
map `colim_k Hᵠ(X, D_k) ⟶ Hᵠ(X, c.pt)` is bijective, spelled out elementwise. This is
`CategoryTheory.Sheaf.H_map_isColimit_of_isFiltered_small` for the étale `X`-schemes with
quasi-compact quasi-separated underlying scheme. -/
@[stacks 03Q6]
theorem H_map_isColimit_of_isFiltered_small (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]
    {D : K ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) :
    (∀ x : Sheaf.H c.pt q, ∃ (k : K) (y : Sheaf.H (D.obj k) q),
      Sheaf.H.map (c.ι.app k) q y = x) ∧
    ∀ (k : K) (y : Sheaf.H (D.obj k) q), Sheaf.H.map (c.ι.app k) q y = 0 →
      ∃ (k' : K) (a : k ⟶ k'), Sheaf.H.map (D.map a) q y = 0 :=
  Sheaf.H_map_isColimit_of_isFiltered_small
    (MorphismProperty.Over.mkIdTerminal _ X : IsTerminal (Etale.mk (𝟙 X))) _
    ⟨‹CompactSpace X›, ‹QuasiSeparatedSpace X›⟩ exists_finite_cechNerve_qcqs hc q

section DirectedUnion

variable {X : Scheme.{u}}

/-- **Filtered unions of subsheaves.** A cocone of a `u + 1`-small filtered diagram of abelian
étale sheaves whose legs are monomorphisms is a colimit cocone as soon as every section of the
cocone point is locally in the image of some leg: the comparison map from the colimit is a
monomorphism since filtered colimits are exact, and an epimorphism since it is locally
surjective. -/
noncomputable def isColimitOfMonoOfLocallySurjectiveAb {K : Type (u + 1)} [SmallCategory K]
    [IsFiltered K] {D : K ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (c : Cocone D)
    [∀ k, Mono (c.ι.app k)]
    (h : ∀ (V : X.Etale) (s : c.pt.obj.obj (op V)), ∃ R ∈ X.smallEtaleTopology V,
      ∀ ⦃W : X.Etale⦄ (g : W ⟶ V), R g →
        ∃ (k : K) (t : (D.obj k).obj.obj (op W)),
          (c.ι.app k).hom.app (op W) t = c.pt.obj.map g.op s) :
    IsColimit c := by
  have : IsConnected K := IsFiltered.isConnected _
  let φ := colimit.desc D c
  have hmono : Mono φ := by
    let α : D ⟶ (Functor.const _).obj c.pt := { app k := c.ι.app k }
    have : Mono α := NatTrans.mono_of_mono_app _
    have : Mono (colim.map α) := inferInstance
    let e := (colimit.isColimit ((Functor.const K).obj c.pt)).coconePointUniqueUpToIso
      (isColimitConstCocone K c.pt)
    have : φ = colim.map α ≫ e.hom := by
      refine colimit.hom_ext fun k ↦ ?_
      simp [φ, e, α]
    rw [this]
    infer_instance
  have hepi : Epi φ := by
    have : Sheaf.IsLocallySurjective φ := by
      refine ⟨fun {V} s ↦ ?_⟩
      obtain ⟨R, hR, hRs⟩ := h V s
      refine X.smallEtaleTopology.superset_covering ?_ hR
      intro W g hg
      obtain ⟨k, t, ht⟩ := hRs g hg
      refine ⟨(colimit.ι D k).hom.app (op W) t, ?_⟩
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        ← ObjectProperty.FullSubcategory.comp_hom, colimit.ι_desc]
      exact ht
    exact Sheaf.epi_of_isLocallySurjective _
  have : IsIso ((colimit.isColimit D).desc c) := isIso_of_mono_of_epi φ
  exact IsColimit.ofPointIso (colimit.isColimit D)

/-- A morphism of abelian étale sheaves `g` whose image is sectionwise contained in the image of
a monomorphism `f` composes to zero with the cokernel of `f`. -/
lemma comp_cokernel_π_eq_zero {A B F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : A ⟶ F) (g : B ⟶ F)
    (h : ∀ (V : X.Etale) (t : B.obj.obj (op V)), ∃ t', f.hom.app (op V) t' = g.hom.app (op V) t) :
    g ≫ cokernel.π f = 0 := by
  refine (sheafToPresheaf _ _).map_injective (NatTrans.ext (funext fun V ↦ ?_))
  ext t
  obtain ⟨t', ht'⟩ := h V.unop t
  change (cokernel.π f).hom.app V (g.hom.app V t) = 0
  rw [← ht', ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, cokernel.condition]
  rfl

/-- **Cohomology of a directed union of subsheaves.** Let `X` be quasi-compact and
quasi-separated, and let `m i : A i ⟶ F` be a directed family of subsheaves of an abelian étale
sheaf `F`, indexed by a type of arbitrary size, such that every section of `F` is locally a
section of some `A i`. Then every class in `Hᵠ(X, F)` comes from some `A i`, and a class on
`A i` which vanishes on `F` vanishes on some larger `A i'`. -/
theorem H_map_of_directed_of_locally (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {ι : Type*} [Nonempty ι]
    {A : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (m : ∀ i, A i ⟶ F)
    [∀ i, Mono (m i)]
    (hdir : ∀ i i', ∃ (i'' : ι) (φ : A i ⟶ A i'') (φ' : A i' ⟶ A i''),
      φ ≫ m i'' = m i ∧ φ' ≫ m i'' = m i')
    (hloc : ∀ (V : X.Etale) (s : F.obj.obj (op V)), ∃ R ∈ X.smallEtaleTopology V,
      ∀ ⦃W : X.Etale⦄ (g : W ⟶ V), R g →
        ∃ (i : ι) (t : (A i).obj.obj (op W)), (m i).hom.app (op W) t = F.obj.map g.op s)
    (q : ℕ) :
    (∀ x : Sheaf.H F q, ∃ (i : ι) (y : Sheaf.H (A i) q), Sheaf.H.map (m i) q y = x) ∧
    ∀ (i : ι) (y : Sheaf.H (A i) q), Sheaf.H.map (m i) q y = 0 →
      ∃ (i' : ι) (φ : A i ⟶ A i') (_ : φ ≫ m i' = m i), Sheaf.H.map φ q y = 0 := by
  -- the families of sections of the subsheaves
  let rng (i : ι) : (V : X.Etale) → Set (F.obj.obj (op V)) :=
    fun V ↦ Set.range ((m i).hom.app (op V))
  let K := {T : (V : X.Etale) → Set (F.obj.obj (op V)) // ∃ i, rng i = T}
  let idx (T : K) : ι := T.2.choose
  have hidx (T : K) : rng (idx T) = T.1 := T.2.choose_spec
  have hle {i i' : ι} (h : rng i ≤ rng i') : m i ≫ cokernel.π (m i') = 0 :=
    comp_cokernel_π_eq_zero _ _ fun V t ↦ h V ⟨t, rfl⟩
  have hrng {i i' : ι} (φ : A i ⟶ A i') (hφ : φ ≫ m i' = m i) : rng i ≤ rng i' := by
    rintro V _ ⟨t, rfl⟩
    exact ⟨φ.hom.app _ t, by rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, hφ]⟩
  have : IsDirectedOrder K := ⟨fun T₁ T₂ ↦ by
    obtain ⟨i'', φ, φ', hφ, hφ'⟩ := hdir (idx T₁) (idx T₂)
    exact ⟨⟨rng i'', i'', rfl⟩, (hidx T₁).symm.le.trans (hrng φ hφ),
      (hidx T₂).symm.le.trans (hrng φ' hφ')⟩⟩
  have : Nonempty K := ⟨⟨rng (Classical.arbitrary ι), _, rfl⟩⟩
  -- the diagram of subsheaves indexed by their families of sections
  let G : K ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    { obj T := A (idx T)
      map {T T'} h := Abelian.monoLift (m (idx T')) (m (idx T))
        (hle (by rw [hidx, hidx]; exact leOfHom h))
      map_id T := by
        rw [← cancel_mono (m (idx T)), Abelian.monoLift_comp, Category.id_comp]
      map_comp {T T' T''} h h' := by
        rw [← cancel_mono (m (idx T'')), Abelian.monoLift_comp, Category.assoc,
          Abelian.monoLift_comp, Abelian.monoLift_comp] }
  let cG : Cocone G :=
    { pt := F
      ι :=
        { app T := m (idx T)
          naturality T T' h := by
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
            exact Abelian.monoLift_comp _ _ _ } }
  have : ∀ T, Mono (cG.ι.app T) := fun T ↦ inferInstanceAs (Mono (m (idx T)))
  have hcG : IsColimit cG := isColimitOfMonoOfLocallySurjectiveAb cG fun V s ↦ by
    obtain ⟨R, hR, hRs⟩ := hloc V s
    refine ⟨R, hR, fun W g hg ↦ ?_⟩
    obtain ⟨i, t, ht⟩ := hRs g hg
    let T : K := ⟨rng i, i, rfl⟩
    obtain ⟨t', ht'⟩ : (m i).hom.app (op W) t ∈ rng (idx T) W := by
      rw [hidx]
      exact ⟨t, rfl⟩
    exact ⟨T, t', ht'.trans ht⟩
  obtain ⟨hsurj, hinj⟩ := H_map_isColimit_of_isFiltered_small X hcG q
  refine ⟨fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · obtain ⟨T, y, hy⟩ := hsurj x
    exact ⟨idx T, y, hy⟩
  · let T : K := ⟨rng i, i, rfl⟩
    let φ₀ : A i ⟶ A (idx T) := Abelian.monoLift (m (idx T)) (m i) (hle (by rw [hidx]))
    have hφ₀ : φ₀ ≫ m (idx T) = m i := Abelian.monoLift_comp _ _ _
    obtain ⟨T', h, hh⟩ := hinj T (Sheaf.H.map φ₀ q y) (by
      change Sheaf.H.map (m (idx T)) q _ = 0
      rw [← Sheaf.H.map_comp_apply, hφ₀, hy])
    refine ⟨idx T', φ₀ ≫ G.map h, ?_, ?_⟩
    · rw [Category.assoc]
      change φ₀ ≫ G.map h ≫ cG.ι.app T' = _
      rw [cG.w h]
      exact hφ₀
    · rw [Sheaf.H.map_comp_apply]
      exact hh

end DirectedUnion

section General

variable {X : Scheme.{u}}

/-- A section of an abelian étale sheaf which is killed by a morphism lifts to the kernel. -/
lemma exists_kernel_ι_app_eq_ab {G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (ψ : G ⟶ H) {W : X.Etale} (x : G.obj.obj (op W)) (hx : ψ.hom.app (op W) x = 0) :
    ∃ t : (kernel ψ).obj.obj (op W), (kernel.ι ψ).hom.app (op W) t = x := by
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj (op W)
  let e := PreservesKernel.iso E ψ ≪≫ AddCommGrpCat.kernelIsoKer (E.map ψ)
  refine ⟨e.inv ⟨x, hx⟩, ?_⟩
  have h₁ := PreservesKernel.iso_inv_ι E ψ
  have h₂ := AddCommGrpCat.kernelIsoKer_inv_comp_ι (E.map ψ)
  change (e.inv ≫ E.map (kernel.ι ψ)) ⟨x, hx⟩ = x
  rw [Iso.trans_inv, Category.assoc, h₁, h₂]
  rfl

/-- A monomorphism of abelian étale sheaves is injective on sections. -/
lemma injective_app_of_mono_ab {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : A ⟶ B) [Mono f] (V : X.Etaleᵒᵖ) : Function.Injective (f.hom.app V) :=
  Sheaf.injective_app_f (S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
    (.mk' (ShortComplex.exact_cokernel f) inferInstance inferInstance) V

/-- The zero morphism induces the zero map on cohomology. -/
lemma H_map_zero_apply {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (n : ℕ)
    (x : Sheaf.H A n) : Sheaf.H.map (0 : A ⟶ B) n x = 0 := by
  rw [Sheaf.H.map_apply, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

/-- **Étale cohomology commutes with filtered colimits on a qcqs scheme**, for filtered
categories of arbitrary size: every class on `c.pt` comes from some `D j`, and a class on `D j`
which dies on `c.pt` already dies on some `D j'`, `j ⟶ j'`. -/
theorem H_map_isColimit_of_isFiltered_of_large (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {J : Type w₁} [Category.{w₂} J] [IsFiltered J]
    {D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) :
    (∀ x : Sheaf.H c.pt q, ∃ (j : J) (y : Sheaf.H (D.obj j) q),
      Sheaf.H.map (c.ι.app j) q y = x) ∧
    ∀ (j : J) (y : Sheaf.H (D.obj j) q), Sheaf.H.map (c.ι.app j) q y = 0 →
      ∃ (j' : J) (φ : j ⟶ j'), Sheaf.H.map (D.map φ) q y = 0 := by
  have hP := isConservativeFamilyOfPoints_ulift_pointSmallEtale X
  have : Nonempty J := IsFiltered.nonempty
  -- the images of the legs
  let I (j : J) := image (c.ι.app j)
  let m (j : J) : I j ⟶ c.pt := image.ι (c.ι.app j)
  let e (j : J) : D.obj j ⟶ I j := factorThruImage (c.ι.app j)
  have hem (j : J) : e j ≫ m j = c.ι.app j := image.fac _
  let ρ {j j' : J} (a : j ⟶ j') : I j ⟶ I j' := image.lift
    { I := I j', m := m j', e := D.map a ≫ e j', fac := by rw [Category.assoc, hem, c.w a] }
  have hρ {j j' : J} (a : j ⟶ j') : ρ a ≫ m j' = m j := image.lift_fac _
  have heρ {j j' : J} (a : j ⟶ j') : e j ≫ ρ a = D.map a ≫ e j' := by
    rw [← cancel_mono (m j'), Category.assoc, hρ, hem, Category.assoc, hem, c.w a]
  have himage (n : ℕ) := H_map_of_directed_of_locally X m
    (fun j j' ↦ ⟨IsFiltered.max j j', ρ (IsFiltered.leftToMax j j'),
      ρ (IsFiltered.rightToMax j j'), hρ _, hρ _⟩) (fun V s ↦ by
      obtain ⟨R, hR, hRs⟩ :=
        GrothendieckTopology.exists_mem_forall_exists_app_eq_of_isColimit hP hc s
      refine ⟨R, hR, fun W g hg ↦ ?_⟩
      obtain ⟨j, t, ht⟩ := hRs g hg
      exact ⟨j, (e j).hom.app _ t, by rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        ← ObjectProperty.FullSubcategory.comp_hom, hem]; exact ht⟩) n
  -- the short exact sequences `0 → K j → D j → I j → 0`
  let κ (j : J) := kernel.ι (c.ι.app j)
  have hκe (j : J) : κ j ≫ e j = 0 := by
    rw [← cancel_mono (m j), Category.assoc, hem, kernel.condition, zero_comp]
  let S (j : J) := ShortComplex.mk (κ j) (e j) (hκe j)
  have hS (j : J) : (S j).ShortExact := by
    refine .mk' (ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
      (fun g hg ↦ kernel.lift _ g (by rw [← hem, ← Category.assoc, hg, zero_comp]))
      (fun g hg ↦ kernel.lift_ι _ _ _)
      (fun g hg l hl ↦ by rw [← cancel_mono (κ j), hl, kernel.lift_ι])))
      inferInstance inferInstance
  let τ {j j' : J} (a : j ⟶ j') : S j ⟶ S j' :=
    { τ₁ := kernel.lift _ (κ j ≫ D.map a) (by rw [Category.assoc, c.w a, kernel.condition])
      τ₂ := D.map a
      τ₃ := ρ a
      comm₁₂ := kernel.lift_ι _ _ _
      comm₂₃ := (heρ a).symm }
  -- the kernels of the transition maps out of `D j`
  let mk (j : J) (a : (j' : J) × (j ⟶ j')) : kernel (D.map a.2) ⟶ kernel (c.ι.app j) :=
    kernel.lift _ (kernel.ι (D.map a.2)) (by
      rw [← c.w a.2, ← Category.assoc, kernel.condition, zero_comp])
  have hmk (j : J) (a : (j' : J) × (j ⟶ j')) : mk j a ≫ κ j = kernel.ι (D.map a.2) :=
    kernel.lift_ι _ _ _
  have : ∀ j a, Mono (mk j a) := fun j a ↦ mono_of_mono_fac (hmk j a)
  have : ∀ j : J, Nonempty ((j' : J) × (j ⟶ j')) := fun j ↦ ⟨⟨j, 𝟙 j⟩⟩
  have hsub (j : J) {j₁ j₃ : J} (a₁ : j ⟶ j₁) (b : j₁ ⟶ j₃) (a : j ⟶ j₃) (h : a₁ ≫ b = a) :
      ∃ φ : kernel (D.map a₁) ⟶ kernel (D.map a), φ ≫ mk j ⟨j₃, a⟩ = mk j ⟨j₁, a₁⟩ := by
    subst h
    refine ⟨kernel.lift _ (kernel.ι (D.map a₁)) (by
      rw [D.map_comp, ← Category.assoc, kernel.condition, zero_comp]), ?_⟩
    rw [← cancel_mono (κ j), Category.assoc, hmk, hmk, kernel.lift_ι]
  have hker (j : J) (n : ℕ) := H_map_of_directed_of_locally X (ι := (j' : J) × (j ⟶ j'))
    (A := fun a ↦ kernel (D.map a.2))
    (mk j) (fun a₁ a₂ ↦ by
      let j₃ := IsFiltered.coeq (a₁.2 ≫ IsFiltered.leftToMax a₁.1 a₂.1)
        (a₂.2 ≫ IsFiltered.rightToMax a₁.1 a₂.1)
      let b₁ := IsFiltered.leftToMax a₁.1 a₂.1 ≫ IsFiltered.coeqHom
        (a₁.2 ≫ IsFiltered.leftToMax a₁.1 a₂.1) (a₂.2 ≫ IsFiltered.rightToMax a₁.1 a₂.1)
      let b₂ := IsFiltered.rightToMax a₁.1 a₂.1 ≫ IsFiltered.coeqHom
        (a₁.2 ≫ IsFiltered.leftToMax a₁.1 a₂.1) (a₂.2 ≫ IsFiltered.rightToMax a₁.1 a₂.1)
      have h₂ : a₂.2 ≫ b₂ = a₁.2 ≫ b₁ := by
        simp only [b₁, b₂, ← Category.assoc]
        exact (IsFiltered.coeq_condition _ _).symm
      obtain ⟨φ₁, hφ₁⟩ := hsub j a₁.2 b₁ (a₁.2 ≫ b₁) rfl
      obtain ⟨φ₂, hφ₂⟩ := hsub j a₂.2 b₂ (a₁.2 ≫ b₁) h₂
      exact ⟨⟨j₃, a₁.2 ≫ b₁⟩, φ₁, φ₂, hφ₁, hφ₂⟩) (fun V s ↦ by
      have hs : (c.ι.app j).hom.app (op V) ((κ j).hom.app (op V) s) = 0 := by
        rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
          ← ObjectProperty.FullSubcategory.comp_hom, kernel.condition]
        rfl
      obtain ⟨R, hR, hRs⟩ :=
        GrothendieckTopology.exists_mem_forall_exists_map_eq_zero_of_isColimit hP hc _ hs
      refine ⟨R, hR, fun W g hg ↦ ?_⟩
      obtain ⟨j', a, ha⟩ := hRs g hg
      obtain ⟨t, ht⟩ := exists_kernel_ι_app_eq_ab (D.map a) _ ha
      refine ⟨⟨j', a⟩, t, injective_app_of_mono_ab (κ j) _ ?_⟩
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        ← ObjectProperty.FullSubcategory.comp_hom, hmk, ht, NatTrans.naturality_apply]) n
  refine ⟨fun x ↦ ?_, fun j y hy ↦ ?_⟩
  · obtain ⟨j, z, rfl⟩ := (himage q).1 x
    obtain ⟨⟨j', a⟩, w, hw⟩ := (hker j (q + 1)).1 (Sheaf.H.δSucc (hS j) q z)
    have hz : Sheaf.H.δSucc (hS j') q (Sheaf.H.map (ρ a) q z) = 0 := by
      rw [← Sheaf.H.map_δSucc (hS j) (hS j') (τ a), ← hw, ← Sheaf.H.map_comp_apply]
      have h0 : mk j ⟨j', a⟩ ≫ (τ a).τ₁ = 0 := by
        rw [← cancel_mono (κ j'), Category.assoc]
        change mk j ⟨j', a⟩ ≫ kernel.lift _ (κ j ≫ D.map a) _ ≫ κ j' = _
        rw [kernel.lift_ι, ← Category.assoc, hmk, kernel.condition, zero_comp]
      rw [h0, H_map_zero_apply]
    obtain ⟨y', hy'⟩ := ((Sheaf.H.exact_map_δSucc (hS j') q) _).1 hz
    refine ⟨j', y', ?_⟩
    change Sheaf.H.map (e j') q y' = _ at hy'
    rw [← hem, Sheaf.H.map_comp_apply, hy', ← Sheaf.H.map_comp_apply, hρ]
    rfl
  · have h₁ : Sheaf.H.map (m j) q (Sheaf.H.map (e j) q y) = 0 := by
      rw [← Sheaf.H.map_comp_apply, hem]
      exact hy
    obtain ⟨j₂, φ, hφ, hφy⟩ := (himage q).2 j _ h₁
    let j₃ := IsFiltered.max j j₂
    let b := IsFiltered.leftToMax j j₂
    let b' := IsFiltered.rightToMax j j₂
    have hρb : ρ b = φ ≫ ρ b' := by
      rw [← cancel_mono (m j₃), Category.assoc, hρ, hρ, hφ]
    have h₂ : Sheaf.H.map (e j₃) q (Sheaf.H.map (D.map b) q y) = 0 := by
      rw [← Sheaf.H.map_comp_apply, ← heρ, Sheaf.H.map_comp_apply, hρb,
        Sheaf.H.map_comp_apply, hφy, map_zero]
    obtain ⟨w, hw⟩ := ((Sheaf.H.exact_map_map (hS j₃) q) _).1 h₂
    obtain ⟨⟨j₄, a⟩, w', rfl⟩ := (hker j₃ q).1 w
    refine ⟨j₄, b ≫ a, ?_⟩
    change Sheaf.H.map (κ j₃) q _ = _ at hw
    rw [D.map_comp, Sheaf.H.map_comp_apply, ← hw, ← Sheaf.H.map_comp_apply,
      ← Sheaf.H.map_comp_apply, ← Category.assoc, hmk, kernel.condition, H_map_zero_apply]

end General

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

universe w'

/-- **Étale cohomology commutes with filtered colimits on a qcqs scheme.** Let `X` be
quasi-compact and quasi-separated and let `c` be a colimit cocone of a filtered diagram `D` of
abelian étale sheaves on `X`. Then for every `q` the canonical map
`colim_λ Hᵠ(X, D_λ) ⟶ Hᵠ(X, colim_λ D_λ)` is bijective; this is spelled out elementwise:
every class on the colimit comes from some `D_λ`, and a class on `D_λ` which dies on the colimit
already dies on some `D_μ`, `λ ⟶ μ`. -/
@[stacks 03Q6]
theorem Scheme.H_map_isColimit_of_isFiltered (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {J : Type w} [Category.{w'} J] [IsFiltered J]
    {D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) :
    (∀ x : Sheaf.H c.pt q, ∃ (j : J) (y : Sheaf.H (D.obj j) q),
      Sheaf.H.map (c.ι.app j) q y = x) ∧
    ∀ (j : J) (y : Sheaf.H (D.obj j) q), Sheaf.H.map (c.ι.app j) q y = 0 →
      ∃ (j' : J) (φ : j ⟶ j'), Sheaf.H.map (D.map φ) q y = 0 :=
  Scheme.H_map_isColimit_of_isFiltered_of_large X hc q

end AlgebraicGeometry
