/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyTrivial
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.RepresentableGluing
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Effective étale descent for finite étale morphisms

Let `p : Y' ⟶ Y` be a surjective étale morphism of schemes. A finite étale `Y'`-scheme `V`
with a descent datum relative to `p` (in the transport form `CategoryTheory.Over.DescentDatum`)
descends to a finite étale `Y`-scheme, and morphisms between base changes which are compatible
with the descent data descend uniquely. Together these say that base change along `p` is an
equivalence between finite étale `Y`-schemes and finite étale `Y'`-schemes with descent datum.

## Main statements

- `CategoryTheory.Over.DescentDatum.exists_isPullback_of_etale`: effectivity of descent data on
  finite étale schemes along a surjective étale morphism.
- `CategoryTheory.Over.DescentDatum.existsUnique_hom_of_isPullback_of_etale`: compatible
  morphisms descend uniquely along a surjective étale morphism.
- `AlgebraicGeometry.Scheme.FiniteEtale.galois_descent`: the two statements together
  (blueprint `lem-galois-descent`).

## Proof

Full faithfulness holds because the base change of a surjective étale morphism is an effective
epimorphism. For effectivity, the descent datum `D` on `V` defines a sheaf `F` on the small
étale site of `Y`: its sections over an étale `U ⟶ Y` are the `Y'`-morphisms
`U ×_Y Y' ⟶ V` compatible with `D`. It is a subsheaf of the pushforward along `p` of the sheaf
represented by `V`, the compatibility being a local condition. Over an étale `Y`-scheme `Z`
equipped with a factorisation `z : Z ⟶ Y'` of its structure morphism, the sections of `F` are the
morphisms `Z ⟶ V` over `z`, using the transport of `D`. Hence `F` is represented by a finite étale
scheme over every affine open of `Y` which admits a surjective étale map from an affine scheme
factoring through `p` (`AlgebraicGeometry.Scheme.Etale.exists_representableBy_of_isAffine`).
These opens form a basis, so `F` is represented by a finite étale `Y`-scheme `X`
(`AlgebraicGeometry.Scheme.Etale.exists_representableBy_of_isBasis`), and the section of `F`
over `V` given by the identity of `V` exhibits `V` as `X ×_Y Y'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Over.DescentDatum

variable {C : Type*} [Category* C] {X Y : C} {p : X ⟶ Y} {V : Over X} (D : DescentDatum p V)

/-- The transport of a descent datum, on underlying morphisms: a morphism `b : T ⟶ V` over
`f₁` is sent to a morphism `T ⟶ V` over `f₂`. -/
def trLeft {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (b : T ⟶ V.left)
    (hb : b ≫ V.hom = f₁) : T ⟶ V.left :=
  (D.transport f₁ f₂ h (Over.homMk b hb)).left

@[reassoc (attr := simp)]
lemma trLeft_hom {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (b : T ⟶ V.left)
    (hb : b ≫ V.hom = f₁) : D.trLeft f₁ f₂ h b hb ≫ V.hom = f₂ :=
  Over.w (D.transport f₁ f₂ h (Over.homMk b hb))

lemma trLeft_congr {T : C} {f₁ f₂ f₁' f₂' : T ⟶ X} {h : f₁ ≫ p = f₂ ≫ p}
    {b b' : T ⟶ V.left} {hb : b ≫ V.hom = f₁} (e₁ : f₁ = f₁') (e₂ : f₂ = f₂') (e : b = b') :
    D.trLeft f₁ f₂ h b hb = D.trLeft f₁' f₂' (by rw [← e₁, ← e₂]; exact h) b'
      (by rw [← e, ← e₁]; exact hb) := by
  subst e₁ e₂ e
  rfl

lemma trLeft_of_eq {T : C} {f₁ f₂ : T ⟶ X} {h : f₁ ≫ p = f₂ ≫ p} {b : T ⟶ V.left}
    {hb : b ≫ V.hom = f₁} (e : f₁ = f₂) : D.trLeft f₁ f₂ h b hb = b := by
  subst e
  simp [trLeft, D.transport_self]

lemma trLeft_comp {T T' : C} (g : T' ⟶ T) {f₁ f₂ : T ⟶ X} (h : f₁ ≫ p = f₂ ≫ p)
    {b : T ⟶ V.left} (hb : b ≫ V.hom = f₁) {f₁' f₂' : T' ⟶ X} {b' : T' ⟶ V.left}
    (e₁ : f₁' = g ≫ f₁) (e₂ : f₂' = g ≫ f₂) (e : b' = g ≫ b) :
    D.trLeft f₁' f₂' (by rw [e₁, e₂, Category.assoc, Category.assoc, h]) b'
      (by rw [e, e₁, Category.assoc, hb]) = g ≫ D.trLeft f₁ f₂ h b hb := by
  subst e₁ e₂ e
  have := D.transport_homMk_comp g f₁ f₂ h (Over.homMk b hb)
  have e : (Over.homMk g : Over.mk (g ≫ f₁) ⟶ Over.mk f₁) ≫ Over.homMk b hb =
      Over.homMk (g ≫ b) (by simp [hb]) := by
    ext
    simp
  rw [e] at this
  exact congrArg CommaMorphism.left this

lemma trLeft_trLeft {T : C} {f₁ f₂ f₃ : T ⟶ X} (h₁₂ : f₁ ≫ p = f₂ ≫ p)
    (h₂₃ : f₂ ≫ p = f₃ ≫ p) {b : T ⟶ V.left} (hb : b ≫ V.hom = f₁) :
    D.trLeft f₂ f₃ h₂₃ (D.trLeft f₁ f₂ h₁₂ b hb) (D.trLeft_hom _ _ _ _ _) =
      D.trLeft f₁ f₃ (h₁₂.trans h₂₃) b hb := by
  have e : (Over.homMk (D.trLeft f₁ f₂ h₁₂ b hb) (D.trLeft_hom _ _ _ _ _) :
      Over.mk f₂ ⟶ V) = D.transport f₁ f₂ h₁₂ (Over.homMk b hb) := by
    ext
    rfl
  change (D.transport f₂ f₃ h₂₃ (Over.homMk (D.trLeft f₁ f₂ h₁₂ b hb) _)).left = _
  rw [e, D.transport_transport]
  rfl

end CategoryTheory.Over.DescentDatum

namespace AlgebraicGeometry.Scheme

/-- Morphisms out of a scheme agreeing on a jointly surjective family of étale morphisms are
equal: the étale topology is subcanonical. -/
lemma Hom.ext_of_etale {T S : Scheme.{u}} {ι : Type*} {Z : ι → Scheme.{u}} (π : ∀ i, Z i ⟶ T)
    [∀ i, AlgebraicGeometry.Etale (π i)] (hπ : ∀ x, ∃ i, x ∈ Set.range (π i)) {a b : T ⟶ S}
    (h : ∀ i, π i ≫ a = π i ≫ b) : a = b := by
  have hS : Sieve.ofArrows Z π ∈ etaleTopology T :=
    Precoverage.generate_mem_toGrothendieck
      ((ofArrows_mem_precoverage_iff (P := @AlgebraicGeometry.Etale)).2 ⟨hπ, fun i ↦ inferInstance⟩)
  have hF := (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := etaleTopology) (yoneda.obj S))
  refine (hF _ hS).isSeparatedFor.ext ?_
  rintro W g ⟨_, f, _, ⟨i⟩, rfl⟩
  change (f ≫ π i) ≫ a = (f ≫ π i) ≫ b
  rw [Category.assoc, Category.assoc, h i]

/-- **Affine étale neighbourhoods.** Let `f : T ⟶ Y` be étale and `y ∈ V` a point in the image
of `f`. There are an affine open `y ∈ U ⊆ V` and a surjective morphism `p : W ⟶ U` from an
affine scheme `W` which factors through `f` by an étale morphism `q : W ⟶ T`. -/
lemma exists_isAffineOpen_surjective_etale {Y T : Scheme.{u}} (f : T ⟶ Y) [Etale f]
    {V : Y.Opens} {y : Y} (hy : y ∈ V) (hyf : y ∈ Set.range f) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U ∧ U ≤ V ∧ ∃ (W : Scheme.{u}) (_ : IsAffine W)
      (q : W ⟶ T) (_ : Etale q) (p : W ⟶ U.toScheme), p ≫ U.ι = q ≫ f ∧ Surjective p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ (V : Set Y) ∩ Set.range f from ⟨hy, hyf⟩) (V.2.inter f.isOpenMap.isOpen_range)
  let 𝒱 := {A : T.affineOpens // (A : T.Opens) ≤ f ⁻¹ᵁ U}
  obtain ⟨s, hs⟩ := hU.isCompact.elim_finite_subcover
    (fun A : 𝒱 ↦ f.base '' (A.1 : Set T)) (fun A ↦ f.isOpenMap _ A.1.1.2) (fun z hz ↦ by
      obtain ⟨x, rfl⟩ := (hUV hz).2
      obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAsub⟩ :=
        T.isBasis_affineOpens.exists_subset_of_mem_open (a := x) hz (f ⁻¹ᵁ U).2
      exact Set.mem_iUnion.2 ⟨⟨⟨A, hA⟩, hAsub⟩, x, hxA, rfl⟩)
  let g : s → Scheme.{u} := fun i ↦ ((i.1.1 : T.affineOpens) : T.Opens).toScheme
  have : ∀ i, IsAffine (g i) := fun i ↦ i.1.1.2
  let q : ∐ g ⟶ T := Sigma.desc fun i ↦ ((i.1.1 : T.affineOpens) : T.Opens).ι
  have : Etale q := IsZariskiLocalAtSource.sigmaDesc fun i ↦ inferInstance
  have hq (i : s) (a : g i) : q (Sigma.ι g i a) = a.1 := by
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
    rfl
  have hr : Set.range (q ≫ f) ⊆ Set.range (Scheme.Opens.ι (X := Y) U) := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨⟨i, a⟩, rfl⟩ := (sigmaMk g).surjective w
    rw [Scheme.Opens.range_ι, sigmaMk_mk, Scheme.Hom.comp_apply, hq]
    exact i.1.2 a.2
  let p := IsOpenImmersion.lift (Scheme.Opens.ι (X := Y) U) (q ≫ f) hr
  have hp : p ≫ Scheme.Opens.ι (X := Y) U = q ≫ f := IsOpenImmersion.lift_fac _ _ _
  refine ⟨U, hU, hyU, fun z hz ↦ (hUV hz).1, ∐ g, inferInstance, q, inferInstance, p, hp,
    ⟨fun z ↦ ?_⟩⟩
  obtain ⟨i, hz⟩ := Set.mem_iUnion.1 (hs z.2)
  obtain ⟨hi, x, hx, hxz⟩ := Set.mem_iUnion.1 hz
  refine ⟨Sigma.ι g ⟨i, hi⟩ ⟨x, hx⟩, Subtype.ext ?_⟩
  rw [← Scheme.Opens.ι_apply, ← Scheme.Hom.comp_apply, hp, Scheme.Hom.comp_apply, hq]
  exact hxz

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.EtaleDescent

variable {Y Y' : Scheme.{u}} {p : Y' ⟶ Y} {V : Over Y'} (D : Over.DescentDatum p V)

/-- A `Y'`-morphism `a : U ×_Y Y' ⟶ V` is *compatible* with the descent datum `D` if for any two
points `t₁, t₂` of `U ×_Y Y'` with the same image in `U`, the transport by `D` of `a ∘ t₁` is
`a ∘ t₂`. -/
def Compat {U : Scheme.{u}} {g : U ⟶ Y} (a : pullback g p ⟶ V.left)
    (ha : a ≫ V.hom = pullback.snd g p) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (t₁ t₂ : T ⟶ pullback g p)
    (h : t₁ ≫ pullback.fst g p = t₂ ≫ pullback.fst g p),
    D.trLeft (t₁ ≫ pullback.snd g p) (t₂ ≫ pullback.snd g p)
      (by simp only [Category.assoc, ← pullback.condition, reassoc_of% h])
      (t₁ ≫ a) (by simp [ha]) = t₂ ≫ a

variable [AlgebraicGeometry.Etale V.hom]

/-- The presheaf `U ↦ Hom_{Y'}(U ×_Y Y', V)` on the small étale site of `Y`. -/
noncomputable abbrev ambient : Y.Etaleᵒᵖ ⥤ Type u :=
  p.Etale.op ⋙ yoneda.obj (Etale.mk V.hom)

omit [AlgebraicGeometry.Etale V.hom] in
lemma etale_map_left_fst {U₁ U₂ : Y.Etale} (g : U₂ ⟶ U₁) :
    (p.Etale.map g).left ≫ pullback.fst U₁.hom p = pullback.fst U₂.hom p ≫ g.left :=
  pullback.lift_fst _ _ _

omit [AlgebraicGeometry.Etale V.hom] in
lemma etale_map_left_snd {U₁ U₂ : Y.Etale} (g : U₂ ⟶ U₁) :
    (p.Etale.map g).left ≫ pullback.snd U₁.hom p = pullback.snd U₂.hom p :=
  pullback.lift_snd _ _ _

/-- The subpresheaf of `ambient` of morphisms compatible with the descent datum. -/
noncomputable def subfunctor : Subfunctor (ambient (p := p) (V := V)) where
  obj U := {a | Compat D a.left (MorphismProperty.Over.w a)}
  map {U₁ U₂} g a ha := by
    intro T t₁ t₂ h
    change D.trLeft _ _ _ (t₁ ≫ (p.Etale.map g.unop).left ≫ a.left) _ =
      t₂ ≫ (p.Etale.map g.unop).left ≫ a.left
    have h' : (t₁ ≫ (p.Etale.map g.unop).left) ≫ pullback.fst _ p =
        (t₂ ≫ (p.Etale.map g.unop).left) ≫ pullback.fst _ p := by
      simp only [Category.assoc, etale_map_left_fst, reassoc_of% h]
    refine (D.trLeft_congr ?_ ?_ (Category.assoc _ _ _).symm).trans
      ((ha _ _ h').trans (Category.assoc _ _ _))
    · simp [etale_map_left_snd]
    · simp [etale_map_left_snd]

lemma isSheaf_ambient : Presieve.IsSheaf Y.smallEtaleTopology (ambient (p := p) (V := V)) :=
  p.Etale.op_comp_isSheaf_of_isSheaf_type _
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Y'.smallEtaleTopology) _)

lemma isSheaf_subfunctor : Presieve.IsSheaf Y.smallEtaleTopology (subfunctor D).toFunctor := by
  refine ((subfunctor D).isSheaf_iff isSheaf_ambient).2 fun U a ha ↦ ?_
  rw [mem_smallEtaleTopology_iff] at ha
  intro T t₁ t₂ h
  choose W g hg hx using fun x : T ↦ ha ((t₁ ≫ pullback.fst _ p) x)
  have : ∀ x, AlgebraicGeometry.Etale (g x).left := fun x ↦ by
    have : AlgebraicGeometry.Etale ((g x).left ≫ U.unop.hom) := by
      rw [MorphismProperty.Over.w]; exact (W x).prop
    exact AlgebraicGeometry.Etale.of_comp _ U.unop.hom
  let π (x : T) : pullback (t₁ ≫ pullback.fst _ p) (g x).left ⟶ T := pullback.fst _ _
  refine Hom.ext_of_etale π (fun x ↦ ?_) fun x ↦ ?_
  · obtain ⟨w, hw⟩ := hx x
    obtain ⟨z, hz, -⟩ := Pullback.exists_preimage_pullback x w hw.symm
    exact ⟨x, z, hz⟩
  · have hc : Compat D ((p.Etale.map (g x)).left ≫ a.left)
        (MorphismProperty.Over.w (p.Etale.map (g x) ≫ a)) := hg x
    have hw (t : T ⟶ pullback U.unop.hom p) (ht : t ≫ pullback.fst _ p = t₁ ≫ pullback.fst _ p) :
        pullback.snd (t₁ ≫ pullback.fst _ p) (g x).left ≫ (W x).hom =
          (π x ≫ t ≫ pullback.snd _ p) ≫ p := by
      rw [← MorphismProperty.Over.w (g x), ← pullback.condition_assoc, Category.assoc,
        Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% ht]
    let s (t : T ⟶ pullback U.unop.hom p) (ht : t ≫ pullback.fst _ p = t₁ ≫ pullback.fst _ p) :
        pullback (t₁ ≫ pullback.fst _ p) (g x).left ⟶ pullback (W x).hom p :=
      pullback.lift (pullback.snd _ _) (π x ≫ t ≫ pullback.snd _ p) (hw t ht)
    have hs (t : T ⟶ pullback U.unop.hom p) (ht : t ≫ pullback.fst _ p = t₁ ≫ pullback.fst _ p) :
        s t ht ≫ (p.Etale.map (g x)).left = π x ≫ t := by
      apply pullback.hom_ext
      · simp only [Category.assoc, etale_map_left_fst, s, pullback.lift_fst_assoc, ht]
        rw [← pullback.condition]
      · simp [etale_map_left_snd, s]
    have := hc (s t₁ rfl) (s t₂ h.symm) (by simp [s])
    refine (D.trLeft_comp (π x) _ _ rfl rfl rfl).symm.trans
      ((D.trLeft_congr ?_ ?_ ?_).trans (this.trans (by rw [reassoc_of% (hs t₂ h.symm)])))
    · simp [s]
    · simp [s]
    · rw [reassoc_of% (hs t₁ rfl)]

/-- The sheaf on the small étale site of `Y` of morphisms `U ×_Y Y' ⟶ V` over `Y'` compatible
with the descent datum `D`. -/
noncomputable def sheaf : Sheaf Y.smallEtaleTopology (Type u) :=
  ⟨(subfunctor D).toFunctor, (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_subfunctor D)⟩

/-! ### Sections over a scheme with a point of `Y'` -/

variable {D}

lemma compat {Z : Y.Etale} (a : (sheaf D).obj.obj (op Z)) :
    Compat D a.1.left (MorphismProperty.Over.w a.1) :=
  a.2

/-- The morphism `Z ⟶ V` over `z : Z ⟶ Y'` corresponding to a section of `sheaf D` over `Z`. -/
noncomputable def toPt {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (a : (sheaf D).obj.obj (op Z)) : Z.left ⟶ V.left :=
  pullback.lift (𝟙 _) z (by simp [hz]) ≫ a.1.left

@[reassoc (attr := simp)]
lemma toPt_hom {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (a : (sheaf D).obj.obj (op Z)) : toPt z hz a ≫ V.hom = z := by
  have h : a.1.left ≫ V.hom = pullback.snd Z.hom p := MorphismProperty.Over.w a.1
  rw [toPt, Category.assoc, h]
  exact pullback.lift_snd _ _ _

variable (D) in
/-- The section of `sheaf D` over `Z` corresponding to a morphism `b : Z ⟶ V` over
`z : Z ⟶ Y'`: it sends a point `(x, y')` of `Z ×_Y Y'` to the transport of `b x` to `y'`. -/
noncomputable def ofPtLeft {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (b : Z.left ⟶ V.left) (hb : b ≫ V.hom = z) : pullback Z.hom p ⟶ V.left :=
  D.trLeft (pullback.fst Z.hom p ≫ z) (pullback.snd Z.hom p)
    (by rw [Category.assoc, hz, pullback.condition]) (pullback.fst _ _ ≫ b)
    (by rw [Category.assoc, hb])

omit [AlgebraicGeometry.Etale V.hom] in
lemma compat_ofPtLeft {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (b : Z.left ⟶ V.left) (hb : b ≫ V.hom = z) :
    Compat D (ofPtLeft D z hz b hb) (D.trLeft_hom _ _ _ _ _) := by
  intro T t₁ t₂ h
  have e₁ : t₁ ≫ ofPtLeft D z hz b hb = D.trLeft (t₁ ≫ pullback.fst _ p ≫ z)
      (t₁ ≫ pullback.snd _ p) (by simp [hz, pullback.condition]) (t₁ ≫ pullback.fst _ p ≫ b)
      (by simp [hb]) :=
    (D.trLeft_comp t₁ _ _ rfl rfl rfl).symm
  refine (D.trLeft_congr rfl rfl e₁).trans ((D.trLeft_trLeft _ _ _).trans ?_)
  exact (D.trLeft_congr (by rw [reassoc_of% h]) rfl (by rw [reassoc_of% h])).trans
    (D.trLeft_comp t₂ _ _ rfl rfl rfl)

/-- The section of `sheaf D` over `Z` corresponding to a morphism `b : Z ⟶ V` over
`z : Z ⟶ Y'`. -/
noncomputable def ofPt {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (b : Z.left ⟶ V.left) (hb : b ≫ V.hom = z) : (sheaf D).obj.obj (op Z) :=
  ⟨Etale.homMk (ofPtLeft D z hz b hb) (D.trLeft_hom _ _ _ _ _), compat_ofPtLeft z hz b hb⟩

lemma ofPt_congr {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    {b b' : Z.left ⟶ V.left} (hb : b ≫ V.hom = z) (hb' : b' ≫ V.hom = z) (e : b = b') :
    ofPt (D := D) z hz b hb = ofPt z hz b' hb' := by
  subst e
  rfl

@[simp]
lemma toPt_ofPt {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (b : Z.left ⟶ V.left) (hb : b ≫ V.hom = z) : toPt z hz (ofPt (D := D) z hz b hb) = b := by
  change pullback.lift (𝟙 _) z _ ≫ ofPtLeft D z hz b hb = b
  refine (D.trLeft_comp _ _ _ rfl rfl rfl).symm.trans
    ((D.trLeft_congr (f₁' := z) (f₂' := z) (b' := b) ?_ ?_ ?_).trans (D.trLeft_of_eq rfl))
  · rw [pullback.lift_fst_assoc]; exact Category.id_comp _
  · exact pullback.lift_snd _ _ _
  · rw [pullback.lift_fst_assoc]; exact Category.id_comp _

@[simp]
lemma ofPt_toPt {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (a : (sheaf D).obj.obj (op Z)) : ofPt z hz (toPt z hz a) (toPt_hom z hz a) = a := by
  apply Subtype.ext
  apply EtaleTorsor.etaleHom_ext
  change ofPtLeft D z hz (toPt z hz a) (toPt_hom z hz a) = a.1.left
  have := compat a (pullback.fst Z.hom p ≫ pullback.lift (𝟙 _) z (by simp [hz])) (𝟙 _)
    (by simp)
  refine (D.trLeft_congr ?_ ?_ ?_).trans (this.trans (Category.id_comp _))
  · simp
  · simp
  · simp [toPt]

lemma toPt_injective {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    {a a' : (sheaf D).obj.obj (op Z)} (h : toPt z hz a = toPt z hz a') : a = a' :=
  calc a = ofPt z hz (toPt z hz a) (toPt_hom z hz a) := (ofPt_toPt z hz a).symm
    _ = ofPt z hz (toPt z hz a') (toPt_hom z hz a') := ofPt_congr z hz _ _ h
    _ = a' := ofPt_toPt z hz a'

/-- `toPt` is natural in the étale `Y`-scheme. -/
lemma toPt_map {Z₁ Z₂ : Y.Etale} (g : Z₁ ⟶ Z₂) (z₂ : Z₂.left ⟶ Y') (hz₂ : z₂ ≫ p = Z₂.hom)
    (z₁ : Z₁.left ⟶ Y') (hz₁ : z₁ ≫ p = Z₁.hom) (e : z₁ = g.left ≫ z₂)
    (a : (sheaf D).obj.obj (op Z₂)) :
    toPt z₁ hz₁ ((sheaf D).obj.map g.op a) = g.left ≫ toPt z₂ hz₂ a := by
  change pullback.lift (𝟙 _) z₁ _ ≫ (p.Etale.map g).left ≫ a.1.left =
    g.left ≫ pullback.lift (𝟙 _) z₂ _ ≫ a.1.left
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, etale_map_left_fst, pullback.lift_fst_assoc, pullback.lift_fst,
      Category.comp_id]
    exact Category.id_comp _
  · simp [etale_map_left_snd, e]

/-- Changing the point of `Y'` transports the morphism `toPt` by the descent datum. -/
lemma toPt_eq_trLeft {Z : Y.Etale} (z z' : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (hz' : z' ≫ p = Z.hom) (a : (sheaf D).obj.obj (op Z)) :
    toPt z' hz' a = D.trLeft z z' (hz.trans hz'.symm) (toPt z hz a) (toPt_hom z hz a) := by
  have := compat a (pullback.lift (𝟙 _) z (by simp [hz])) (pullback.lift (𝟙 _) z' (by simp [hz']))
    (by simp)
  exact this.symm.trans (D.trLeft_congr (by simp) (by simp) rfl)

/-! ### Representability over a scheme with a point of `Y'` -/

section Representation

variable {W : Y.Etale} (w : W.left ⟶ Y') (hw : w ≫ p = W.hom)

omit [AlgebraicGeometry.Etale V.hom] in
lemma etale_snd_comp [AlgebraicGeometry.Etale V.hom] :
    AlgebraicGeometry.Etale (pullback.snd V.hom w ≫ W.hom) := by
  have : AlgebraicGeometry.Etale W.hom := W.prop
  infer_instance

/-- `V ×_{Y'} W` as an étale `Y`-scheme over `W`. -/
noncomputable def overW : Over W :=
  haveI := etale_snd_comp (V := V) w
  Over.mk (Etale.homMk (pullback.snd V.hom w) rfl :
    Etale.mk (pullback.snd V.hom w ≫ W.hom) ⟶ W)

lemma overW_hom_left : (overW (V := V) w).hom.left = pullback.snd V.hom w :=
  rfl

instance [IsFinite V.hom] : IsFinite (overW (V := V) w).hom.left :=
  inferInstanceAs (IsFinite (pullback.snd V.hom w))

lemma left_left_snd {Z : Over W} (φ : Z ⟶ overW (V := V) w) :
    φ.left.left ≫ pullback.snd V.hom w = Z.hom.left :=
  congrArg (fun f ↦ f.left) (Over.w φ)

include hw in
lemma hzW (Z : Over W) : (Z.hom.left ≫ w) ≫ p = Z.left.hom := by
  rw [Category.assoc, hw]
  exact MorphismProperty.Over.w Z.hom

variable (D) in
/-- Morphisms `Z ⟶ V ×_{Y'} W` over `W` are the sections of `sheaf D` over `Z`. -/
noncomputable def homEquivW (Z : Over W) :
    (Z ⟶ overW (V := V) w) ≃ (sheaf D).obj.obj (op Z.left) where
  toFun φ := ofPt (Z.hom.left ≫ w) (hzW w hw Z) (φ.left.left ≫ pullback.fst V.hom w)
    (by rw [Category.assoc, pullback.condition, reassoc_of% (left_left_snd w φ)])
  invFun s := Over.homMk (Etale.homMk (pullback.lift (toPt _ (hzW w hw Z) s) Z.hom.left
      (toPt_hom _ _ s)) (by
        change pullback.lift _ _ _ ≫ pullback.snd V.hom w ≫ W.hom = Z.left.hom
        rw [pullback.lift_snd_assoc]
        exact MorphismProperty.Over.w Z.hom)) (by
      apply EtaleTorsor.etaleHom_ext
      exact pullback.lift_snd _ _ _)
  left_inv φ := by
    apply Over.OverMorphism.ext
    apply EtaleTorsor.etaleHom_ext
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (toPt_ofPt _ _ _ _)
    · exact (pullback.lift_snd _ _ _).trans (left_left_snd w φ).symm
  right_inv s := by
    refine (ofPt_congr _ _ _ (toPt_hom _ _ s) ?_).trans (ofPt_toPt _ _ s)
    exact pullback.lift_fst _ _ _

variable (D) in
/-- The restriction of `sheaf D` to étale `Y`-schemes over `W` is represented by `V ×_{Y'} W`. -/
noncomputable def representableByW :
    ((Over.forget W).op ⋙ (sheaf D).obj).RepresentableBy (overW (V := V) w) where
  homEquiv {Z} := homEquivW D w hw Z
  homEquiv_comp {Z' Z} f φ := by
    apply toPt_injective (Z'.hom.left ≫ w) (hzW w hw Z')
    change toPt _ _ (ofPt _ _ _ _) = toPt _ _ ((sheaf D).obj.map f.left.op (ofPt _ _ _ _))
    rw [toPt_ofPt, toPt_map f.left (Z.hom.left ≫ w) (hzW w hw Z), toPt_ofPt]
    · simp
    · rw [← Category.assoc]
      exact congrArg (· ≫ w) (congrArg (fun g ↦ g.left) (Over.w f)).symm

end Representation

/-! ### Effectivity -/

omit [AlgebraicGeometry.Etale V.hom] in
lemma trLeft_left {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ V) : D.trLeft f₁ f₂ h a.left (Over.w a) = (D.transport f₁ f₂ h a).left := by
  have : (Over.homMk a.left (Over.w a) : Over.mk f₁ ⟶ V) = a := by
    ext
    rfl
  unfold Over.DescentDatum.trLeft
  rw [this]

section Descended

variable [AlgebraicGeometry.Etale p] {X : Y.Etale} (r : (sheaf D).obj.RepresentableBy X)

variable (V) in
/-- `V` as an étale `Y`-scheme. -/
noncomputable abbrev VE : Y.Etale :=
  Etale.mk (V.hom ≫ p)

variable (D) in
/-- The section of `sheaf D` over `V` given by the identity of `V`. -/
noncomputable def idSection : (sheaf D).obj.obj (op (VE (p := p) V)) :=
  ofPt V.hom rfl (𝟙 _) (Category.id_comp _)

/-- The morphism `V ⟶ X` of étale `Y`-schemes corresponding to `idSection D`. -/
noncomputable def descQE : VE (p := p) V ⟶ X :=
  r.homEquiv.symm (idSection D)

lemma homEquiv_descQE : r.homEquiv (descQE r) = idSection D :=
  r.homEquiv.apply_symm_apply _

/-- The morphism `V ⟶ X` corresponding to `idSection D`. -/
noncomputable def descQ : V.left ⟶ X.left :=
  (descQE r).left

lemma descQ_comm : descQ r ≫ X.hom = V.hom ≫ p :=
  MorphismProperty.Over.w (r.homEquiv.symm (idSection D))

lemma isPullback_descQ : IsPullback (descQ r) V.hom X.hom p := by
  have : AlgebraicGeometry.Etale X.hom := X.prop
  let ZE : Y.Etale := Etale.mk (pullback.fst X.hom p ≫ X.hom)
  let fstE : ZE ⟶ X := Etale.homMk (pullback.fst X.hom p) rfl
  have hzZ : pullback.snd X.hom p ≫ p = ZE.hom := pullback.condition.symm
  let ψ := toPt (Z := ZE) (pullback.snd X.hom p) hzZ (r.homEquiv fstE)
  let φ := pullback.lift (descQ r) V.hom (descQ_comm r)
  let φE : VE (p := p) V ⟶ ZE := Etale.homMk φ (by
    change φ ≫ pullback.fst X.hom p ≫ X.hom = V.hom ≫ p
    rw [pullback.lift_fst_assoc]
    exact descQ_comm r)
  let ψE : ZE ⟶ VE (p := p) V := Etale.homMk ψ (by
    change ψ ≫ V.hom ≫ p = pullback.fst X.hom p ≫ X.hom
    rw [toPt_hom_assoc]
    exact hzZ)
  have h1 : φ ≫ ψ = 𝟙 _ := by
    have hφ : φE ≫ fstE = descQE r := EtaleTorsor.etaleHom_ext (pullback.lift_fst _ _ _)
    calc φ ≫ ψ = toPt V.hom rfl ((sheaf D).obj.map φE.op (r.homEquiv fstE)) :=
          (toPt_map φE _ hzZ V.hom rfl (pullback.lift_snd _ _ _).symm _).symm
      _ = toPt V.hom rfl (idSection D) := by rw [← r.homEquiv_comp, hφ, homEquiv_descQE]
      _ = 𝟙 _ := toPt_ofPt _ _ _ _
  have h2 : ψ ≫ descQ r = pullback.fst X.hom p := by
    have : ψE ≫ descQE r = fstE := by
      apply r.homEquiv.injective
      rw [r.homEquiv_comp, homEquiv_descQE]
      apply toPt_injective (pullback.snd X.hom p) hzZ
      rw [toPt_map ψE V.hom rfl _ hzZ (toPt_hom (Z := ZE) _ hzZ (r.homEquiv fstE)).symm,
        idSection, toPt_ofPt]
      exact Category.comp_id _
    exact congrArg (fun f ↦ f.left) this
  have h3 : ψ ≫ φ = 𝟙 _ := pullback.hom_ext (by simp [φ, h2]) (by simp [φ, ψ])
  exact IsPullback.of_iso_pullback ⟨descQ_comm r⟩ ⟨φ, ψ, h1, h3⟩ (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

variable (D) in
/-- The underlying morphism of `idSection D`. -/
noncomputable def idLeft : pullback (VE (p := p) V).hom p ⟶ V.left :=
  ofPtLeft D (Z := VE (p := p) V) V.hom rfl (𝟙 _) (Category.id_comp _)

lemma fst_descQ :
    pullback.fst (VE (p := p) V).hom p ≫ descQ (V := V) r = idLeft D ≫ descQ r := by
  have : AlgebraicGeometry.Etale (VE (p := p) V).hom := (VE (p := p) V).prop
  let PE : Y.Etale := Etale.mk (pullback.fst (VE (p := p) V).hom p ≫ (VE (p := p) V).hom)
  have hzP : pullback.snd (VE (p := p) V).hom p ≫ p = PE.hom := pullback.condition.symm
  have he : idLeft D ≫ V.hom = pullback.snd (VE (p := p) V).hom p := D.trLeft_hom _ _ _ _ _
  let fE : PE ⟶ VE (p := p) V := Etale.homMk (pullback.fst _ _) rfl
  let aE : PE ⟶ VE (p := p) V := Etale.homMk (idLeft D) (by
    change idLeft D ≫ V.hom ≫ p = pullback.fst (VE (p := p) V).hom p ≫ (VE (p := p) V).hom
    rw [reassoc_of% he]
    exact hzP)
  have hfa : (sheaf D).obj.map fE.op (idSection D) = (sheaf D).obj.map aE.op (idSection D) := by
    apply toPt_injective (pullback.snd (VE (p := p) V).hom p) hzP
    rw [toPt_map aE V.hom rfl _ hzP he.symm, idSection, toPt_ofPt,
      toPt_eq_trLeft (pullback.fst (VE (p := p) V).hom p ≫ V.hom) _
        (by rw [Category.assoc]; rfl) hzP]
    refine (D.trLeft_congr rfl rfl ?_).trans (Category.comp_id _).symm
    exact (toPt_map fE V.hom rfl _ _ rfl _).trans (congrArg (fE.left ≫ ·) (toPt_ofPt _ _ _ _))
  have : fE ≫ descQE r = aE ≫ descQE r := by
    apply r.homEquiv.injective
    rw [r.homEquiv_comp, r.homEquiv_comp, homEquiv_descQE, hfa]
  exact congrArg (fun f ↦ f.left) this

lemma descQ_invariant {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ V) : (D.transport f₁ f₂ h a).left ≫ descQ r = a.left ≫ descQ r := by
  let t : T ⟶ pullback (VE (p := p) V).hom p := pullback.lift a.left f₂ (by
    change a.left ≫ V.hom ≫ p = f₂ ≫ p
    rw [← Category.assoc, Over.w a]
    exact h)
  have ht : t ≫ idLeft D = (D.transport f₁ f₂ h a).left := by
    refine (D.trLeft_comp t _ _ rfl rfl rfl).symm.trans ?_
    refine (D.trLeft_congr ?_ ?_ ?_).trans (trLeft_left f₁ f₂ h a)
    · rw [pullback.lift_fst_assoc]; exact Over.w a
    · exact pullback.lift_snd _ _ _
    · exact (congrArg (t ≫ ·) (Category.comp_id _)).trans (pullback.lift_fst _ _ _)
  rw [← ht, Category.assoc, ← fst_descQ, pullback.lift_fst_assoc]

end Descended

variable (p) in
/-- The affine opens `U` of `Y` admitting a surjective morphism from an affine scheme which
factors through `p` by an étale morphism. -/
def goodOpens : Set Y.Opens :=
  {U | IsAffineOpen U ∧ ∃ (W : Scheme.{u}) (_ : IsAffine W) (q : W ⟶ Y')
    (_ : AlgebraicGeometry.Etale q) (pU : W ⟶ U.toScheme), pU ≫ U.ι = q ≫ p ∧ Surjective pU}

omit [AlgebraicGeometry.Etale V.hom] in
variable (p) in
lemma isBasis_goodOpens [AlgebraicGeometry.Etale p] [Surjective p] :
    TopologicalSpace.Opens.IsBasis (goodOpens p) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro O y hy
  obtain ⟨U, hU, hyU, hUO, W, hW, q, hq, pU, hpq, hp⟩ :=
    exists_isAffineOpen_surjective_etale p hy (p.surjective y)
  exact ⟨U, ⟨hU, W, hW, q, hq, pU, hpq, hp⟩, hyU, hUO⟩

variable (D) in
lemma exists_representableBy_goodOpens [AlgebraicGeometry.Etale p] [IsFinite V.hom]
    (U : goodOpens p) :
    ∃ X : Over (Etale.openObj U.1), IsFinite X.hom.left ∧
      Nonempty (((Over.forget (Etale.openObj U.1)).op ⋙ (sheaf D).obj).RepresentableBy X) := by
  obtain ⟨hU, W, hW, q, hq, pU, hpq, hp⟩ := U.2
  have : IsAffine (Etale.openObj U.1).left := hU
  let WE : Y.Etale := Etale.mk (q ≫ p)
  have : IsAffine WE.left := hW
  let pE : WE ⟶ Etale.openObj U.1 := Etale.homMk pU hpq
  have : Surjective pE.left := hp
  exact Etale.exists_representableBy_of_isAffine (sheaf D) pE (overW (V := V) (W := WE) q)
    (representableByW D (W := WE) q rfl)

variable (D) in
lemma exists_representableBy [AlgebraicGeometry.Etale p] [Surjective p] [IsFinite V.hom] :
    ∃ X : Y.Etale, IsFinite X.hom ∧ Nonempty ((sheaf D).obj.RepresentableBy X) :=
  Etale.exists_representableBy_of_isBasis (sheaf D) (goodOpens p) (isBasis_goodOpens p)
    (exists_representableBy_goodOpens D)

variable (D) in
/-- **Effective étale descent for finite étale schemes**: a finite étale `Y'`-scheme `V` with a
descent datum relative to a surjective étale morphism `p : Y' ⟶ Y` is the base change of a finite
étale `Y`-scheme `X`, through a morphism `q : V ⟶ X` which is invariant under the transport. -/
theorem exists_isPullback [AlgebraicGeometry.Etale p] [Surjective p] [IsFinite V.hom] :
    ∃ (X : Y.Etale) (q : V.left ⟶ X.left), IsFinite X.hom ∧ IsPullback q V.hom X.hom p ∧
      ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
        (D.transport f₁ f₂ h a).left ≫ q = a.left ≫ q := by
  obtain ⟨X, hX, ⟨r⟩⟩ := exists_representableBy D
  exact ⟨X, descQ r, hX, isPullback_descQ r, descQ_invariant r⟩

end AlgebraicGeometry.Scheme.EtaleDescent

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {Y Y' : Scheme.{u}} {p : Y' ⟶ Y}

/-- **Effective étale descent for finite étale schemes.** Let `p : Y' ⟶ Y` be a surjective
étale morphism and `V` a finite étale `Y'`-scheme. Every descent datum on `V` relative to `p` is
effective, and the descended `Y`-scheme is finite étale. -/
theorem exists_isPullback_of_etale [AlgebraicGeometry.Etale p] [Surjective p] {V : Over Y'}
    [IsFinite V.hom] [AlgebraicGeometry.Etale V.hom] (D : DescentDatum p V) :
    ∃ (V₀ : Over Y) (q : V.left ⟶ V₀.left), IsFinite V₀.hom ∧ AlgebraicGeometry.Etale V₀.hom ∧
      IsPullback q V.hom V₀.hom p ∧
      ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
        (D.transport f₁ f₂ h a).left ≫ q = a.left ≫ q := by
  obtain ⟨X, q, hX, hq, hinv⟩ := Scheme.EtaleDescent.exists_isPullback D
  exact ⟨Over.mk X.hom, q, hX, X.prop, hq, hinv⟩

/-- **Morphisms descend along surjective étale morphisms.** Let `p : Y' ⟶ Y` be surjective and
étale, and let `V`, `W` be `Y'`-schemes with descent data `D`, `E` which are effective, with
descended `Y`-schemes `V₀`, `W₀` and projections `qV`, `qW` invariant under the transport. Then
every morphism `ψ : V ⟶ W` over `Y'` compatible with the descent data is the base change of a
unique morphism `ψ₀ : V₀ ⟶ W₀` over `Y`: the projection `qV`, a base change of `p`, is an
effective epimorphism. -/
theorem existsUnique_hom_of_isPullback_of_etale [AlgebraicGeometry.Etale p] [Surjective p]
    {V W : Over Y'} (D : DescentDatum p V) (E : DescentDatum p W) {V₀ W₀ : Over Y}
    (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (qW : W.left ⟶ W₀.left) (hqW : IsPullback qW W.hom W₀.hom p)
    (hEW : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ W),
      (E.transport f₁ f₂ h a).left ≫ qW = a.left ≫ qW)
    (ψ : V ⟶ W)
    (hψ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      E.transport f₁ f₂ h (a ≫ ψ) = D.transport f₁ f₂ h a ≫ ψ) :
    ∃! ψ₀ : V₀ ⟶ W₀, ψ.left ≫ qW = qV ≫ ψ₀.left := by
  have : AlgebraicGeometry.Etale qV := MorphismProperty.of_isPullback hqV.flip ‹_›
  have : Surjective qV := MorphismProperty.of_isPullback hqV.flip ‹_›
  have hdesc : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ V.left), g₁ ≫ qV = g₂ ≫ qV →
      g₁ ≫ ψ.left ≫ qW = g₂ ≫ ψ.left ≫ qW := by
    intro Z g₁ g₂ hg
    have h : (g₁ ≫ V.hom) ≫ p = (g₂ ≫ V.hom) ≫ p := by
      rw [Category.assoc, Category.assoc, ← hqV.w, reassoc_of% hg]
    let a : Over.mk (g₁ ≫ V.hom) ⟶ V := Over.homMk g₁
    have ha : (D.transport _ _ h a).left = g₂ :=
      hqV.hom_ext ((hDV _ _ h a).trans hg) (Over.w (D.transport _ _ h a))
    have := congrArg (fun f ↦ f.left ≫ qW) (hψ _ _ h a)
    simp only [Over.comp_left, Category.assoc, ha] at this
    rw [← this, ← Category.assoc, hEW]
    rfl
  let ψ₀ : V₀ ⟶ W₀ := Over.homMk (EffectiveEpi.desc qV (ψ.left ≫ qW) hdesc) (by
    rw [← cancel_epi qV, EffectiveEpi.fac_assoc, Category.assoc, hqW.w, Over.w_assoc ψ, hqV.w])
  refine ⟨ψ₀, (EffectiveEpi.fac qV _ hdesc).symm, fun ψ₁ hψ₁ ↦ ?_⟩
  ext
  rw [← cancel_epi qV, ← hψ₁]
  exact (EffectiveEpi.fac qV _ hdesc).symm

end CategoryTheory.Over.DescentDatum

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- **Effective étale descent for finite étale morphisms.** Let `p : Y' ⟶ Y` be a surjective
étale morphism. Then base change along `p` identifies finite étale `Y`-schemes with finite étale
`Y'`-schemes endowed with a descent datum relative to `p`:

* every descent datum `D` on a finite étale `Y'`-scheme `V` is effective: `V` is the base change
  `V₀ ×_Y Y'` of a finite étale `Y`-scheme `V₀`, through a projection `q : V ⟶ V₀` invariant
  under the transport of `D` (essential surjectivity);
* for effective descent data on `V` and `W` with descended schemes `V₀` and `W₀`, every
  morphism `V ⟶ W` over `Y'` compatible with the descent data is the base change of a unique
  morphism `V₀ ⟶ W₀` over `Y` (full faithfulness).

The descent data are in the transport form `CategoryTheory.Over.DescentDatum`, which by the
Yoneda lemma is the same as an isomorphism `φ : p₁^* V ≅ p₂^* V` over `Y' ×_Y Y'` satisfying
the cocycle condition over `Y' ×_Y Y' ×_Y Y'`.
(blueprint: `lem-galois-descent`) -/
theorem galois_descent {Y Y' : Scheme.{u}} (p : Y' ⟶ Y) [AlgebraicGeometry.Etale p]
    [Surjective p] :
    (∀ (V : Over Y') [IsFinite V.hom] [AlgebraicGeometry.Etale V.hom]
      (D : Over.DescentDatum p V),
      ∃ (V₀ : Over Y) (q : V.left ⟶ V₀.left), IsFinite V₀.hom ∧
        AlgebraicGeometry.Etale V₀.hom ∧ IsPullback q V.hom V₀.hom p ∧
        ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
          (D.transport f₁ f₂ h a).left ≫ q = a.left ≫ q) ∧
    (∀ {V W : Over Y'} (D : Over.DescentDatum p V) (E : Over.DescentDatum p W) {V₀ W₀ : Over Y}
      (qV : V.left ⟶ V₀.left) (_ : IsPullback qV V.hom V₀.hom p)
      (_ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
        (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
      (qW : W.left ⟶ W₀.left) (_ : IsPullback qW W.hom W₀.hom p)
      (_ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ W),
        (E.transport f₁ f₂ h a).left ≫ qW = a.left ≫ qW)
      (ψ : V ⟶ W)
      (_ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
        E.transport f₁ f₂ h (a ≫ ψ) = D.transport f₁ f₂ h a ≫ ψ),
      ∃! ψ₀ : V₀ ⟶ W₀, ψ.left ≫ qW = qV ≫ ψ₀.left) :=
  ⟨fun _ _ _ D ↦ D.exists_isPullback_of_etale,
    fun D E _ _ qV hqV hDV qW hqW hEW ψ hψ ↦
      D.existsUnique_hom_of_isPullback_of_etale E qV hqV hDV qW hqW hEW ψ hψ⟩

end AlgebraicGeometry.Scheme.FiniteEtale
