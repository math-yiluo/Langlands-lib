import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Gluing closed subschemes along an open cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ClosedSubschemeGluing

variable {X : Scheme.{u}} (P : ∀ ⦃Z : Scheme.{u}⦄, (Z ⟶ X) → Prop)
  (hP : ∀ ⦃Z Z' : Scheme.{u}⦄ (a : Z' ⟶ Z) ⦃z : Z ⟶ X⦄, P z → P (a ≫ z))

/-- The subfunctor of the points of `X` satisfying the restriction-stable
condition `P`. -/
def subfunctor : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj Z := {z : Z.unop ⟶ X // P z}
  map a := TypeCat.ofHom fun z => ⟨a.unop ≫ z.1, hP a.unop z.2⟩
  map_id _ := TypeCat.homEquiv.injective (funext fun z =>
    Subtype.ext (Category.id_comp z.1))
  map_comp a b := TypeCat.homEquiv.injective (funext fun z =>
    Subtype.ext (Category.assoc b.unop a.unop z.1))

@[simp] lemma subfunctor_map_coe {Z Z' : Scheme.{u}ᵒᵖ} (a : Z ⟶ Z')
    (z : (subfunctor P hP).obj Z) :
    ((subfunctor P hP).map a z).1 = a.unop ≫ z.1 := rfl

variable {P}

/-- A restriction-stable condition on points which is local on the source
defines a Zariski sheaf. -/
theorem isSheaf_subfunctor
    (hloc : ∀ ⦃Z : Scheme.{u}⦄ (z : Z ⟶ X),
      (∀ p : Z, ∃ U : Z.Opens, p ∈ U ∧ P (U.ι ≫ z)) → P z) :
    Presheaf.IsSheaf Scheme.zariskiTopology (subfunctor P hP) := by
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y R hR x hx
  obtain ⟨(𝓤 : OpenCover Y), rfl⟩ := exists_cover_of_mem_pretopology hR
  let e : Y ⟶ X := 𝓤.glueMorphisms (fun j => (x (𝓤.f j) (.mk j)).1) (by
    intro i j
    exact congrArg Subtype.val
      (hx (pullback.fst (𝓤.f i) (𝓤.f j)) (pullback.snd _ _) (.mk i) (.mk j)
        pullback.condition))
  have he : ∀ j, 𝓤.f j ≫ e = (x (𝓤.f j) (.mk j)).1 := fun j =>
    𝓤.ι_glueMorphisms _ _ j
  have hPe : P e := by
    refine hloc e fun p => ?_
    obtain ⟨q, hq⟩ := 𝓤.covers p
    refine ⟨(𝓤.f (𝓤.idx p)).opensRange, ⟨q, hq⟩, ?_⟩
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, he]
    exact hP _ (x (𝓤.f (𝓤.idx p)) (.mk _)).2
  refine ⟨⟨e, hPe⟩, ?_, ?_⟩
  · rintro Z f ⟨j⟩
    exact Subtype.ext (he j)
  · intro e' h
    apply Subtype.ext
    apply 𝓤.hom_ext
    intro j
    rw [he]
    exact congrArg Subtype.val (h (𝓤.f j) (.mk j))

variable (P) in
/-- The chart condition for a closed subscheme: a point of `V` lands in
`P` after the open immersion `v` exactly when it factors through `c`. -/
def IsChart {V L : Scheme.{u}} (v : V ⟶ X) (c : L ⟶ V) : Prop :=
  ∀ ⦃Z : Scheme.{u}⦄ (z : Z ⟶ V), P (z ≫ v) ↔ ∃ a : Z ⟶ L, a ≫ c = z

section Charts

variable {V L : Scheme.{u}} {v : V ⟶ X} [IsOpenImmersion v] {c : L ⟶ V}
  [IsClosedImmersion c] (hc : IsChart P v c)

omit [IsOpenImmersion v] [IsClosedImmersion c] in
include hc in
lemma isChart_self : P (c ≫ v) :=
  (hc c).mpr ⟨𝟙 _, Category.id_comp c⟩

/-- The chart map from the points of `L` to the subfunctor. -/
def chart : yoneda.obj L ⟶ subfunctor P hP :=
  yonedaEquiv.symm ⟨c ≫ v, isChart_self hc⟩

omit [IsOpenImmersion v] [IsClosedImmersion c] in
lemma chart_app_coe {T : Scheme.{u}} (a : T ⟶ L) :
    ((chart hP hc).app (op T) a).1 = a ≫ c ≫ v := rfl

omit [IsClosedImmersion c] in
include hP hc in
/-- On the open preimage of `v`, a point satisfying `P` factors through the
chart. -/
lemma exists_factor {T : Scheme.{u}} (y : T ⟶ X) (hy : P y) :
    ∃ φ : (y ⁻¹ᵁ v.opensRange : Scheme.{u}) ⟶ L,
      φ ≫ c ≫ v = (y ⁻¹ᵁ v.opensRange).ι ≫ y := by
  let W := y ⁻¹ᵁ v.opensRange
  have hW : Set.range (W.ι ≫ y) ⊆ Set.range v := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  let w : (W : Scheme.{u}) ⟶ V := IsOpenImmersion.lift v (W.ι ≫ y) hW
  have hw : w ≫ v = W.ι ≫ y := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ := (hc w).mp (by rw [hw]; exact hP _ hy)
  exact ⟨φ, by rw [← Category.assoc, hφ, hw]⟩

theorem isOpenImmersion_chart : IsOpenImmersion.presheaf (chart hP hc) := by
  apply MorphismProperty.relative.of_exists
  intro T g
  let y := yonedaEquiv g
  have hg : ∀ {T' : Scheme.{u}} (a : T' ⟶ T), (g.app (op T') a).1 = a ≫ y.1 :=
    fun a => congrArg Subtype.val (map_yonedaEquiv g a).symm
  let W := y.1 ⁻¹ᵁ v.opensRange
  obtain ⟨φ, hφ⟩ := exists_factor hP hc y.1 y.2
  refine ⟨W, yoneda.map φ, W.ι, ?_, inferInstance⟩
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨T'⟩
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext a
    apply Subtype.ext
    change (a ≫ φ) ≫ c ≫ v = (g.app (op T') (a ≫ W.ι)).1
    rw [hg, Category.assoc, hφ, Category.assoc]
  · rintro a a' ⟨-, h⟩
    exact (cancel_mono W.ι).mp h
  · intro x₂ x₃ hx
    change T' ⟶ L at x₂
    change T' ⟶ T at x₃
    have hx' : x₂ ≫ c ≫ v = x₃ ≫ y.1 := by
      have := congrArg Subtype.val hx
      change x₂ ≫ c ≫ v = (g.app (op T') x₃).1 at this
      rw [this, hg]
    have hrange : Set.range x₃ ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      refine ⟨c (x₂ t), ?_⟩
      change (x₂ ≫ c ≫ v) t = (x₃ ≫ y.1) t
      rw [hx']
    refine ⟨IsOpenImmersion.lift W.ι x₃ hrange, ?_, IsOpenImmersion.lift_fac _ _ _⟩
    change IsOpenImmersion.lift W.ι x₃ hrange ≫ φ = x₂
    rw [← cancel_mono (c ≫ v), Category.assoc, hφ, ← Category.assoc,
      IsOpenImmersion.lift_fac, hx']

end Charts

section Gluing

variable {ι : Type u} {V L : ι → Scheme.{u}} (v : ∀ i, V i ⟶ X)
  [∀ i, IsOpenImmersion (v i)] (c : ∀ i, L i ⟶ V i) [∀ i, IsClosedImmersion (c i)]
  (hc : ∀ i, IsChart P (v i) (c i)) (hcov : ∀ x : X, ∃ i, x ∈ Set.range (v i))

omit [∀ i, IsClosedImmersion (c i)] in
include hcov in
theorem isLocallySurjective_chart :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun i => chart hP (hc i)) := by
  constructor
  intro T ξ
  let W : ι → T.Opens := fun i => ξ.1 ⁻¹ᵁ (v i).opensRange
  let 𝒲 : T.OpenCover := Scheme.Cover.mkOfCovers ι (fun i => (W i : Scheme.{u}))
    (fun i => (W i).ι) (fun x => by
      obtain ⟨i, hi⟩ := hcov (ξ.1 x)
      exact ⟨i, ⟨x, hi⟩, rfl⟩)
  refine GrothendieckTopology.superset_covering _ ?_ 𝒲.mem_grothendieckTopology
  intro Y g hg
  obtain ⟨(i : ι), a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  obtain ⟨φ, hφ⟩ := exists_factor hP (hc i) ξ.1 ξ.2
  refine ⟨(Sigma.ι (fun i => yoneda.obj (L i)) i).app (op Y) (a ≫ φ), ?_⟩
  show (Sigma.ι (fun i => yoneda.obj (L i)) i ≫ Sigma.desc fun i => chart hP (hc i)).app (op Y)
    (a ≫ φ) = (subfunctor P hP).map (a ≫ (W i).ι).op ξ
  erw [Sigma.ι_comp_desc]
  apply Subtype.ext
  change (a ≫ φ) ≫ c i ≫ v i = (a ≫ (W i).ι) ≫ ξ.1
  exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) hφ).trans (Category.assoc _ _ _).symm)

include hP hc hcov in
/-- **Gluing closed subschemes.** A restriction-stable condition on points
of `X` which is local on the source, and which is represented on each member
of an open cover of `X` by a closed subscheme, is represented by a closed
subscheme of `X`. -/
theorem exists_isClosedImmersion
    (hloc : ∀ ⦃Z : Scheme.{u}⦄ (z : Z ⟶ X),
      (∀ p : Z, ∃ U : Z.Opens, p ∈ U ∧ P (U.ι ≫ z)) → P z) :
    ∃ (L₀ : Scheme.{u}) (c₀ : L₀ ⟶ X), IsClosedImmersion c₀ ∧
      ∀ ⦃Z : Scheme.{u}⦄ (z : Z ⟶ X), P z ↔ ∃ a : Z ⟶ L₀, a ≫ c₀ = z := by
  let F : Sheaf Scheme.zariskiTopology (Type u) :=
    ⟨subfunctor P hP, isSheaf_subfunctor hP hloc⟩
  have := isLocallySurjective_chart hP v c hc hcov
  let e := LocalRepresentability.representableBy (F := F)
    (fun i => isOpenImmersion_chart hP (hc i))
  let c₀ := (e.homEquiv (𝟙 _)).1
  have hc₀ : P c₀ := (e.homEquiv (𝟙 _)).2
  have key : ∀ ⦃Z : Scheme.{u}⦄ (a : Z ⟶ _), (e.homEquiv a).1 = a ≫ c₀ := fun Z a => by
    rw [e.homEquiv_eq]
    rfl
  have hfac : ∀ ⦃Z : Scheme.{u}⦄ (z : Z ⟶ X), P z ↔ ∃ a, a ≫ c₀ = z := by
    intro Z z
    refine ⟨fun h => ⟨e.homEquiv.symm (⟨z, h⟩ : (subfunctor P hP).obj (op Z)), ?_⟩, ?_⟩
    · exact (key _).symm.trans (congrArg Subtype.val
        (e.homEquiv.apply_symm_apply (⟨z, h⟩ : (subfunctor P hP).obj (op Z))))
    · rintro ⟨a, rfl⟩
      exact hP a hc₀
  have : Mono c₀ := ⟨fun a a' h => e.homEquiv.injective (Subtype.ext (by
    rw [key, key]; exact h))⟩
  refine ⟨_, c₀, ?_, hfac⟩
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers ι V v (fun x => by
    obtain ⟨i, y, hy⟩ := hcov x
    exact ⟨i, y, hy⟩)
  refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun (i : ι) => ?_
  change IsClosedImmersion (pullback.snd c₀ (v i))
  obtain ⟨a, ha⟩ := (hfac (c i ≫ v i)).mp (isChart_self (hc i))
  obtain ⟨b, hb⟩ := (hc i (pullback.snd c₀ (v i))).mp (by
    rw [← pullback.condition]
    exact hP _ hc₀)
  let iso : pullback c₀ (v i) ≅ L i :=
    { hom := b
      inv := pullback.lift a (c i) ha
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [← cancel_mono c₀, Category.assoc, Category.assoc, pullback.lift_fst_assoc,
            ha, reassoc_of% hb, Category.id_comp, pullback.condition]
        · rw [Category.assoc, pullback.lift_snd, hb, Category.id_comp]
      inv_hom_id := by
        rw [← cancel_mono (c i), Category.assoc, hb, pullback.lift_snd, Category.id_comp] }
  have : pullback.snd c₀ (v i) = iso.hom ≫ c i := hb.symm
  rw [this]
  have : IsIso iso.hom := iso.isIso_hom
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion iso.hom (c i)).mpr
    inferInstance

end Gluing

end AlgebraicGeometry.Scheme.ClosedSubschemeGluing
