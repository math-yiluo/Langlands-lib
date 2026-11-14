import Langlands.AlgebraicGeometry.ClosedSubschemeGluing
import Langlands.GroupScheme.HomScheme.AdmissibleSchemeLocality

/-! # Gluing monic representatives of actual subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.ClosedSubschemeGluing

variable {X : Scheme.{u}} {P : ∀ ⦃Z : Scheme.{u}⦄, (Z ⟶ X) → Prop}
  (hP : ∀ ⦃Z Z' : Scheme.{u}⦄ (a : Z' ⟶ Z) ⦃z : Z ⟶ X⦄, P z → P (a ≫ z))

section Charts

variable {V L : Scheme.{u}} {v : V ⟶ X} [IsOpenImmersion v] {c : L ⟶ V}
  [Mono c] (hc : IsChart P v c)

/-- A monic local representative gives an open chart of the condition
subfunctor over the ambient open subscheme. -/
theorem isOpenImmersion_chart_of_mono : IsOpenImmersion.presheaf (chart hP hc) := by
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

include hP in
/-- A source-local subfunctor of a scheme with monic representatives over
an ambient open cover has a global monic scheme representative. -/
theorem exists_mono
    {ι : Type u} {V L : ι → Scheme.{u}} (v : ∀ i, V i ⟶ X)
    [∀ i, IsOpenImmersion (v i)] (c : ∀ i, L i ⟶ V i) [∀ i, Mono (c i)]
    (hc : ∀ i, IsChart P (v i) (c i)) (hcov : ∀ x : X, ∃ i, x ∈ Set.range (v i))
    (hloc : ∀ ⦃Z : Scheme.{u}⦄ (z : Z ⟶ X),
      (∀ p : Z, ∃ U : Z.Opens, p ∈ U ∧ P (U.ι ≫ z)) → P z) :
    ∃ (L₀ : Scheme.{u}) (c₀ : L₀ ⟶ X), Mono c₀ ∧
      ∀ ⦃Z : Scheme.{u}⦄ (z : Z ⟶ X), P z ↔ ∃ a : Z ⟶ L₀, a ≫ c₀ = z := by
  let F : Sheaf Scheme.zariskiTopology (Type u) :=
    ⟨subfunctor P hP, isSheaf_subfunctor hP hloc⟩
  have := isLocallySurjective_chart hP v c hc hcov
  let e := LocalRepresentability.representableBy (F := F)
    (fun i => isOpenImmersion_chart_of_mono hP (hc i))
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
  exact ⟨_, c₀, inferInstance, hfac⟩

end AlgebraicGeometry.Scheme.ClosedSubschemeGluing

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} (F : SubgroupFunctor G)

/-- Monic representability of a Zariski-local subgroup descends along a
Zariski open cover of the base. -/
theorem exists_isRepresentedBy_of_openCover (hF : IsZariskiLocal F)
    (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ i, ∃ (H : GroupScheme (𝒰.X i))
      (j : H ⟶ (GroupScheme.baseChange (𝒰.f i)).obj G),
        (F.baseChange (𝒰.f i)).IsRepresentedBy j) :
    ∃ (H : GroupScheme S) (j : H ⟶ G), F.IsRepresentedBy j := by
  choose H j hj using h
  let c : ∀ i, (H i).X.left ⟶ pullback G.X.hom (𝒰.f i) :=
    fun i => (j i).hom.hom.left
  have : ∀ i, Mono (j i).hom.hom := fun i => (hj i).1
  have : ∀ i, Mono (c i) := fun i => inferInstance
  let 𝒱 : G.X.left.OpenCover := 𝒰.pullback₁ G.X.hom
  have hchart (i : 𝒰.I₀) :
      Scheme.ClosedSubschemeGluing.IsChart (fun _ x => F.schemeCondition x)
        (𝒱.f i) (c i) := by
    intro Z z
    exact (F.schemeCondition_baseChange_iff (𝒰.f i) z).trans
      (schemeCondition_iff_exists_of_isRepresentedBy
        (F.baseChange (𝒰.f i)) (hj i) z)
  obtain ⟨L₀, c₀, hc₀, hfac⟩ :=
    Scheme.ClosedSubschemeGluing.exists_mono
      (P := fun _ x => F.schemeCondition x)
      (fun _ _ a z hz => F.schemeCondition_comp z a hz)
      (fun i : 𝒰.I₀ => 𝒱.f i) c hchart
      (fun x => ⟨𝒱.idx x, 𝒱.covers x⟩)
      (fun Z z hz => by
        choose U hU hPU using hz
        let 𝒲 : Z.OpenCover := Scheme.Cover.mkOfCovers Z
          (fun p => (U p : Scheme.{u})) (fun p => (U p).ι)
          (fun p => ⟨p, ⟨p, hU p⟩, rfl⟩)
        exact (F.schemeCondition_iff_openCover hF z 𝒲).mpr hPU)
  have : Mono c₀ := hc₀
  let i₀ : Over.mk (c₀ ≫ G.X.hom) ⟶ G.X := Over.homMk c₀ rfl
  have : Mono i₀ := Over.mono_of_mono_left _
  have hi₀ : ∀ (T : Over S) (x : T ⟶ G.X),
      x ∈ F.carrier T ↔
        ∃ y : T ⟶ Over.mk (c₀ ≫ G.X.hom), y ≫ i₀ = x := by
    intro T x
    rw [← F.schemeCondition_iff_mem x, hfac x.left]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
      change a ≫ c₀ ≫ G.X.hom = T.hom
      rw [← Category.assoc, ha, Over.w x]
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg CommaMorphism.left hy⟩
  exact ⟨_, F.representingHom i₀ hi₀,
    F.isRepresentedBy_representingHom i₀ hi₀⟩

/-- A chosen monic group-scheme representative obtained by Zariski descent. -/
def gluedRepresentative (hF : IsZariskiLocal F) (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ i, ∃ (H : GroupScheme (𝒰.X i))
      (j : H ⟶ (GroupScheme.baseChange (𝒰.f i)).obj G),
        (F.baseChange (𝒰.f i)).IsRepresentedBy j) :
    Σ H : GroupScheme S, {j : H ⟶ G // F.IsRepresentedBy j} :=
  ⟨(F.exists_isRepresentedBy_of_openCover hF 𝒰 h).choose,
    ⟨(F.exists_isRepresentedBy_of_openCover hF 𝒰 h).choose_spec.choose,
      (F.exists_isRepresentedBy_of_openCover hF 𝒰 h).choose_spec.choose_spec⟩⟩

end Langlands.GroupScheme.SubgroupFunctor
