import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalSteps
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Factorization through a monomorphic chart

Fix a presheaf `F` on `Over S` and an element `ξ ∈ F(U)` that is a monomorphism `U → F`.
For `η ∈ F(T)` and `a : T' ⟶ T`, `Fac ξ η a` says that `η|_{T'}` factors through `ξ`.
This module proves the formal properties of this predicate used in SGA 3, XI 3.1 and 3.5:
stability under composition, Zariski gluing, descent along faithfully flat quasi-compact
morphisms, and invariance under field extensions. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} {U : Over S} (ξ : F.obj (op U))

/-- The restriction of `η ∈ F(T)` along `a : T' ⟶ T` factors through `ξ ∈ F(U)`. -/
def Fac {T T' : Over S} (η : F.obj (op T)) (a : T' ⟶ T) : Prop :=
  ∃ h : T' ⟶ U, F.map h.op ξ = F.map a.op η

variable {ξ}

lemma fac_comp {T T' T'' : Over S} {η : F.obj (op T)} {a : T' ⟶ T} (b : T'' ⟶ T')
    (h : Fac ξ η a) : Fac ξ η (b ≫ a) := by
  obtain ⟨h, hh⟩ := h
  refine ⟨b ≫ h, ?_⟩
  rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hh]

lemma fac_map_iff {T₀ T T' : Over S} (η₀ : F.obj (op T₀)) (c : T ⟶ T₀) (b : T' ⟶ T) :
    Fac ξ (F.map c.op η₀) b ↔ Fac ξ η₀ (b ≫ c) := by
  unfold Fac
  rw [op_comp, Functor.map_comp_apply]

/-- Two `S`-morphisms into `U` with the same composite with `ξ` agree. -/
lemma eq_of_fac {T T' : Over S} (hmono : IsMonoElement F ξ) {η : F.obj (op T)}
    {a : T' ⟶ T} {h₁ h₂ : T' ⟶ U} (e₁ : F.map h₁.op ξ = F.map a.op η)
    (e₂ : F.map h₂.op ξ = F.map a.op η) : h₁ = h₂ :=
  hmono h₁ h₂ (e₁.trans e₂.symm)

/-- Descent of a factorization along a flat, surjective, quasi-compact morphism. -/
lemma fac_of_flat (hmono : IsMonoElement F ξ) (hF : FaithfullyFlatSheaf F)
    {T₀ T₁ T : Over S} (φ : T₁ ⟶ T₀) [Flat φ.left] [Surjective φ.left] [QuasiCompact φ.left]
    {η : F.obj (op T)} {a : T₀ ⟶ T} (h : Fac ξ η (φ ≫ a)) : Fac ξ η a := by
  obtain ⟨h, hh⟩ := h
  have key : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ T₁.left), g₁ ≫ φ.left = g₂ ≫ φ.left →
      g₁ ≫ h.left = g₂ ≫ h.left := by
    intro Z g₁ g₂ hg
    let Z' : Over S := Over.mk (g₁ ≫ T₁.hom)
    let g₁' : Z' ⟶ T₁ := Over.homMk g₁
    have hw : g₂ ≫ T₁.hom = Z'.hom := by
      change g₂ ≫ T₁.hom = g₁ ≫ T₁.hom
      rw [← Over.w φ, ← Category.assoc, ← hg, Category.assoc]
    let g₂' : Z' ⟶ T₁ := Over.homMk g₂ hw
    have hg' : g₁' ≫ φ = g₂' ≫ φ := Over.OverMorphism.ext hg
    have : g₁' ≫ h = g₂' ≫ h := by
      apply hmono
      rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hh,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
        ← Category.assoc, ← Category.assoc, hg']
    exact congrArg CommaMorphism.left this
  let h₀ : T₀.left ⟶ U.left := EffectiveEpi.desc φ.left h.left (fun g₁ g₂ hg ↦ key g₁ g₂ hg)
  have hfac : φ.left ≫ h₀ = h.left := EffectiveEpi.fac φ.left _ _
  have hw : h₀ ≫ U.hom = T₀.hom := by
    rw [← cancel_epi φ.left, ← Category.assoc, hfac, Over.w h, Over.w φ]
  let h₀' : T₀ ⟶ U := Over.homMk h₀ hw
  have hφ : φ ≫ h₀' = h := Over.OverMorphism.ext hfac
  refine ⟨h₀', ?_⟩
  apply (hF φ inferInstance inferInstance inferInstance).isSeparatedFor.ext
  rintro Y f ⟨⟩
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    hφ, hh]

/-! ### Points with values in fields -/

/-- The point `Spec κ(t) ⟶ T` of an object of `Over S`. -/
def resPt (T : Over S) (t : T.left) : Over.mk (T.left.fromSpecResidueField t ≫ T.hom) ⟶ T :=
  Over.homMk (T.left.fromSpecResidueField t)

/-- Every point `Spec K ⟶ T` with values in a field factors through the residue field of
its image point. -/
lemma exists_eq_comp_resPt {K : Type u} [Field K] {k : Spec (CommRingCat.of K) ⟶ S}
    {T : Over S} (g : Over.mk k ⟶ T) :
    ∃ (φ : T.left.residueField (g.left (IsLocalRing.closedPoint K)) ⟶ CommRingCat.of K)
      (w : Spec.map φ ≫ T.left.fromSpecResidueField (g.left (IsLocalRing.closedPoint K)) ≫
        T.hom = k),
      g = (Over.homMk (Spec.map φ) w :
        Over.mk k ⟶ Over.mk (T.left.fromSpecResidueField
          (g.left (IsLocalRing.closedPoint K)) ≫ T.hom)) ≫ resPt T _ := by
  have e := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K T.left g.left
  have w : Spec.map (T.left.descResidueField (Scheme.stalkClosedPointTo g.left)) ≫
      T.left.fromSpecResidueField (g.left (IsLocalRing.closedPoint K)) ≫ T.hom = k := by
    rw [← Category.assoc, e]
    exact Over.w g
  refine ⟨_, w, ?_⟩
  apply Over.OverMorphism.ext
  exact e.symm

instance {K L : Type u} [Field K] [Field L] (φ : CommRingCat.of K ⟶ CommRingCat.of L) :
    Flat (Spec.map φ) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  let := φ.hom.toAlgebra
  show Module.Flat K L
  infer_instance

instance {K : Type u} [Field K] {X : CommRingCat.{u}} (φ : X ⟶ CommRingCat.of K) :
    QuasiCompact (Spec.map φ) :=
  inferInstance

lemma surjective_specMap_of_field {K L : Type u} [Field K] [Field L]
    (φ : CommRingCat.of K ⟶ CommRingCat.of L) : Surjective (Spec.map φ) :=
  ⟨fun _ ↦ ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

/-- A factorization at a point with values in a field is equivalent to one at the residue
field of its image. -/
lemma fac_fieldPt_iff (hmono : IsMonoElement F ξ) (hF : FaithfullyFlatSheaf F)
    {K : Type u} [Field K] {k : Spec (CommRingCat.of K) ⟶ S} {T : Over S}
    {η : F.obj (op T)} (g : Over.mk k ⟶ T) :
    Fac ξ η g ↔ Fac ξ η (resPt T (g.left (IsLocalRing.closedPoint K))) := by
  obtain ⟨φ, w, hg⟩ := exists_eq_comp_resPt g
  constructor
  · intro h
    rw [hg] at h
    let φ' : Over.mk k ⟶ Over.mk (T.left.fromSpecResidueField
        (g.left (IsLocalRing.closedPoint K)) ≫ T.hom) := Over.homMk (Spec.map φ) w
    have : Surjective φ'.left := surjective_specMap_of_field φ
    have : Flat φ'.left := (inferInstance : Flat (Spec.map φ))
    have : QuasiCompact φ'.left := (inferInstance : QuasiCompact (Spec.map φ))
    exact fac_of_flat hmono hF φ' h
  · intro h
    rw [hg]
    exact fac_comp _ h

variable (ξ) in
/-- The set of points of `T` at which `η` factors through `ξ`. -/
def W {T : Over S} (η : F.obj (op T)) : Set T.left :=
  {t | Fac ξ η (resPt T t)}

variable (ξ) in
lemma mem_W_iff {T : Over S} (η : F.obj (op T)) (t : T.left) :
    t ∈ W ξ η ↔ Fac ξ η (resPt T t) := Iff.rfl

lemma range_subset_W_of_fac (hmono : IsMonoElement F ξ) (hF : FaithfullyFlatSheaf F)
    {T T' : Over S} {η : F.obj (op T)} {a : T' ⟶ T} (h : Fac ξ η a) :
    Set.range a.left ⊆ W ξ η := by
  rintro _ ⟨t', rfl⟩
  have h' := fac_comp (resPt T' t') h
  rw [fac_fieldPt_iff hmono hF] at h'
  have e : (resPt T' t' ≫ a).left (IsLocalRing.closedPoint _) = a.left t' := by
    exact congrArg a.left (Scheme.fromSpecResidueField_apply (X := T'.left) t' _)
  rw [e] at h'
  exact h'

/-- Membership in the factorization locus is compatible with restriction. -/
lemma mem_W_map_iff (hmono : IsMonoElement F ξ) (hF : FaithfullyFlatSheaf F) {T T' : Over S}
    (η : F.obj (op T)) (c : T' ⟶ T) (t' : T'.left) :
    t' ∈ W ξ (F.map c.op η) ↔ c.left t' ∈ W ξ η := by
  rw [mem_W_iff, fac_map_iff, fac_fieldPt_iff hmono hF]
  have e : (resPt T' t' ≫ c).left (IsLocalRing.closedPoint _) = c.left t' :=
    congrArg c.left (Scheme.fromSpecResidueField_apply (X := T'.left) t' _)
  rw [e]
  rfl

/-! ### Zariski gluing -/

/-- The open subscheme `V ⊆ T` as an object over `T`. -/
def ιOver (T : Over S) (V : T.left.Opens) : Over.mk (V.ι ≫ T.hom) ⟶ T :=
  Over.homMk V.ι

/-- Factorizations on the members of an open cover glue. -/
lemma fac_of_openCover (hmono : IsMonoElement F ξ) (hZ : ZariskiSheaf F)
    {T T' : Over S} {η : F.obj (op T)} (a : T' ⟶ T) (𝒰 : T'.left.OpenCover.{u})
    (h : ∀ i, Fac ξ η ((Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T'.hom) ⟶ T') ≫ a)) :
    Fac ξ η a := by
  choose h hh using h
  have compat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (h i).left =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (h j).left := by
    intro i j
    let Z : Over S := Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T'.hom)
    let p₁ : Z ⟶ Over.mk (𝒰.f i ≫ T'.hom) := Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j))
    have hw : pullback.snd (𝒰.f i) (𝒰.f j) ≫ 𝒰.f j ≫ T'.hom = Z.hom := by
      change _ = pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T'.hom
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
    let p₂ : Z ⟶ Over.mk (𝒰.f j ≫ T'.hom) := Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j)) hw
    have hp : p₁ ≫ (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T'.hom) ⟶ T') =
        p₂ ≫ (Over.homMk (𝒰.f j) : Over.mk (𝒰.f j ≫ T'.hom) ⟶ T') :=
      Over.OverMorphism.ext pullback.condition
    have : p₁ ≫ h i = p₂ ≫ h j := by
      apply hmono
      rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hh,
        hh, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
        ← op_comp, ← Category.assoc, ← Category.assoc, hp]
    exact congrArg CommaMorphism.left this
  let g : T'.left ⟶ U.left := 𝒰.glueMorphisms (fun i ↦ (h i).left) compat
  have hg : ∀ i, 𝒰.f i ≫ g = (h i).left := fun i ↦ 𝒰.ι_glueMorphisms _ compat i
  have hw : g ≫ U.hom = T'.hom := by
    refine 𝒰.hom_ext _ _ fun i ↦ ?_
    rw [← Category.assoc, hg, Over.w (h i)]
    rfl
  refine ⟨Over.homMk g hw, ?_⟩
  apply (hZ T' 𝒰).isSeparatedFor.ext
  rintro Y f ⟨i⟩
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  have : (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T'.hom) ⟶ T') ≫ Over.homMk g hw = h i :=
    Over.OverMorphism.ext (hg i)
  rw [this, hh]

/-- Factorizations on an open neighbourhood of every point glue. -/
lemma fac_of_forall_opens (hmono : IsMonoElement F ξ) (hZ : ZariskiSheaf F)
    {T T' : Over S} {η : F.obj (op T)} (a : T' ⟶ T)
    (h : ∀ t' : T'.left, ∃ V : T'.left.Opens, t' ∈ V ∧ Fac ξ η (ιOver T' V ≫ a)) :
    Fac ξ η a := by
  choose V hV hfac using h
  let 𝒱 : T'.left.OpenCover := Scheme.Cover.mkOfCovers T'.left (fun t ↦ ((V t : T'.left.Opens) :
    Scheme.{u})) (fun t ↦ (V t).ι) (fun t ↦ ⟨t, ⟨t, hV t⟩, rfl⟩)
  exact fac_of_openCover hmono hZ a 𝒱 hfac

variable (ξ) in
/-- `η` factors through `ξ` on an open neighbourhood of `t`. -/
def LocFac {T : Over S} (η : F.obj (op T)) (t : T.left) : Prop :=
  ∃ V : T.left.Opens, t ∈ V ∧ Fac ξ η (ιOver T V)

lemma LocFac.pullback {T T' : Over S} {η : F.obj (op T)} (a : T' ⟶ T) {t' : T'.left}
    (h : LocFac ξ η (a.left t')) : LocFac ξ (F.map a.op η) t' := by
  obtain ⟨V, hV, hfac⟩ := h
  refine ⟨a.left ⁻¹ᵁ V, hV, ?_⟩
  rw [fac_map_iff]
  have hw : (a.left ∣_ V) ≫ V.ι ≫ T.hom = (a.left ⁻¹ᵁ V).ι ≫ T'.hom := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w a]
  have : ιOver T' (a.left ⁻¹ᵁ V) ≫ a =
      (Over.homMk (a.left ∣_ V) hw : Over.mk ((a.left ⁻¹ᵁ V).ι ≫ T'.hom) ⟶
        Over.mk (V.ι ≫ T.hom)) ≫ ιOver T V :=
    Over.OverMorphism.ext (morphismRestrict_ι a.left V).symm
  rw [this]
  exact fac_comp _ hfac

/-- The image of an open immersion `c : X ⟶ T`, as an open subscheme of `T`, maps to `X`. -/
def opensRangeToSource {T X : Over S} (c : X ⟶ T) [IsOpenImmersion c.left] :
    Over.mk (c.left.opensRange.ι ≫ T.hom) ⟶ X :=
  Over.homMk c.left.isoOpensRange.inv (by
    change c.left.isoOpensRange.inv ≫ X.hom = c.left.opensRange.ι ≫ T.hom
    rw [← Over.w c, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp])

/-- The inclusion of the image of an open immersion `c` factors through `c`. -/
lemma ιOver_opensRange {T X : Over S} (c : X ⟶ T) [IsOpenImmersion c.left] :
    ιOver T c.left.opensRange = opensRangeToSource c ≫ c :=
  Over.OverMorphism.ext (Scheme.Hom.isoOpensRange_inv_comp c.left).symm

lemma LocFac.of_isOpenImmersion {T X : Over S} {η : F.obj (op T)} (c : X ⟶ T)
    [IsOpenImmersion c.left] (hc : Fac ξ η c) {t : T.left} (ht : t ∈ Set.range c.left) :
    LocFac ξ η t := by
  refine ⟨c.left.opensRange, ht, ?_⟩
  rw [ιOver_opensRange]
  exact fac_comp _ hc

/-! ### The open locus of factorization (SGA 3, XI 3.1) -/

section Locus

variable (hmono : IsMonoElement F ξ) (hZ : ZariskiSheaf F) (hF : FaithfullyFlatSheaf F)
  (hloc : ∀ (T : Over S) (η : F.obj (op T)) (t : T.left), t ∈ W ξ η → LocFac ξ η t)
include hmono hZ hF hloc

lemma fac_iff_range_subset {T T' : Over S} (η : F.obj (op T)) (a : T' ⟶ T) :
    Fac ξ η a ↔ Set.range a.left ⊆ W ξ η := by
  refine ⟨range_subset_W_of_fac hmono hF, fun h ↦ ?_⟩
  apply fac_of_forall_opens hmono hZ a
  intro t'
  obtain ⟨V, hV, hfac⟩ := LocFac.pullback a (hloc T η _ (h ⟨t', rfl⟩))
  exact ⟨V, hV, (fac_map_iff η a _).mp hfac⟩

omit hZ in
lemma isOpen_W {T : Over S} (η : F.obj (op T)) : IsOpen (W ξ η) := by
  rw [isOpen_iff_forall_mem_open]
  intro t ht
  obtain ⟨V, hV, hfac⟩ := hloc T η t ht
  refine ⟨V, ?_, V.2, hV⟩
  have := range_subset_W_of_fac hmono hF hfac
  rwa [show (ιOver T V).left = V.ι from rfl, Scheme.Opens.range_ι] at this

end Locus

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing
