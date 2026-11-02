import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Over

/-! # A Zariski-plus-affine criterion for fppf sheaves on a slice of schemes -/

universe w u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.OverFppfSheaf

variable {S : Scheme.{u}} (G : (Over S)ᵒᵖ ⥤ Type w)

/-- Values of a presheaf on `Over S` depend on morphisms only through their underlying
morphisms of schemes. -/
lemma map_congr_left {Z W : Over S} {α β : Z ⟶ W} (h : α.left = β.left) :
    G.map α.op = G.map β.op := by
  rw [Over.OverMorphism.ext h]

lemma map_apply_congr_left {Z W : Over S} {α β : Z ⟶ W} (h : α.left = β.left)
    (x : G.obj (op W)) : G.map α.op x = G.map β.op x := by
  rw [map_congr_left G h]

lemma map_map_apply {Z W Y : Over S} (a : Z ⟶ W) (b : W ⟶ Y) (c : Z ⟶ Y)
    (h : a.left ≫ b.left = c.left) (x : G.obj (op Y)) :
    G.map a.op (G.map b.op x) = G.map c.op x := by
  rw [← types_comp_apply (G.map b.op) (G.map a.op), ← G.map_comp, ← op_comp]
  exact map_apply_congr_left G (by simpa using h) x

/-- Transport along an equality of structure morphisms. -/
def tr {V : Scheme.{u}} {s s' : V ⟶ S} (h : s = s') :
    G.obj (op (Over.mk s')) → G.obj (op (Over.mk s)) :=
  G.map (Over.homMk (𝟙 V) (by simp [h]) : Over.mk s ⟶ Over.mk s').op

@[simp]
lemma tr_rfl {V : Scheme.{u}} {s : V ⟶ S} (x : G.obj (op (Over.mk s))) :
    tr G (rfl : s = s) x = x := by
  have : (Over.homMk (𝟙 V) (by simp) : Over.mk s ⟶ Over.mk s) = 𝟙 _ := by
    ext; simp
  simp [tr, this]

lemma sigma_eq_iff {V : Scheme.{u}} {s s' : V ⟶ S} (x : G.obj (op (Over.mk s)))
    (x' : G.obj (op (Over.mk s'))) :
    (⟨s, x⟩ : Σ s : V ⟶ S, G.obj (op (Over.mk s))) = ⟨s', x'⟩ ↔
      ∃ h : s = s', tr G h x' = x := by
  constructor
  · intro h
    obtain ⟨rfl, hx⟩ := Sigma.mk.inj_iff.1 h
    exact ⟨rfl, by rw [eq_of_heq hx, tr_rfl]⟩
  · rintro ⟨rfl, rfl⟩
    rw [tr_rfl]

/-- An equation between values of `G` only depends on the underlying morphisms of schemes,
and the structure morphism of the common source may be replaced by an equal one. -/
lemma map_eq_map_of_eq {Z : Over S} {a : Z.left ⟶ S} (ha : a = Z.hom) {Y₁ Y₂ : Over S}
    (u₁ : Over.mk a ⟶ Y₁) (u₂ : Over.mk a ⟶ Y₂) (v₁ : Z ⟶ Y₁) (v₂ : Z ⟶ Y₂)
    (h₁ : v₁.left = u₁.left) (h₂ : v₂.left = u₂.left) {x₁ : G.obj (op Y₁)}
    {x₂ : G.obj (op Y₂)} (h : G.map u₁.op x₁ = G.map u₂.op x₂) :
    G.map v₁.op x₁ = G.map v₂.op x₂ := by
  let e : Z ⟶ Over.mk a := Over.homMk (𝟙 _) (by simp [ha])
  rw [← map_map_apply G e u₁ v₁ (by simp [e, h₁]), ← map_map_apply G e u₂ v₂ (by simp [e, h₂]), h]

/-- Points of the extension of `G` over a scheme. -/
abbrev Pt (V : Scheme.{u}) : Type (max u w) := Σ s : V ⟶ S, G.obj (op (Over.mk s))

/-- The extension of `G` to all schemes: a point over `V` is a structure morphism
`V ⟶ S` together with a section of `G` over the resulting object of `Over S`. -/
def ext : Scheme.{u}ᵒᵖ ⥤ Type (max u w) where
  obj V := Pt G V.unop
  map {V W} g := TypeCat.ofHom fun y ↦
    ⟨g.unop ≫ y.1,
      G.map (Over.homMk g.unop : Over.mk (g.unop ≫ y.1) ⟶ Over.mk y.1).op y.2⟩
  map_id V := by
    refine ConcreteCategory.hom_ext _ _ ?_
    rintro ⟨s, x⟩
    exact (sigma_eq_iff G _ _).2 ⟨Category.id_comp s, rfl⟩
  map_comp g h := by
    refine ConcreteCategory.hom_ext _ _ ?_
    rintro ⟨s, x⟩
    refine (sigma_eq_iff G _ _).2 ⟨Category.assoc _ _ _, ?_⟩
    change G.map _ (G.map _ (G.map _ x)) = G.map _ x
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    exact map_apply_congr_left G (by simp) x

lemma ext_map_mk {V W : Scheme.{u}} (g : W ⟶ V) (s : V ⟶ S) (x : G.obj (op (Over.mk s))) :
    (ext G).map g.op (⟨s, x⟩ : Pt G V) =
      (⟨g ≫ s, G.map (Over.homMk g : Over.mk (g ≫ s) ⟶ Over.mk s).op x⟩ : Pt G W) :=
  rfl

lemma ext_map_mk_eq_mk_iff {V W : Scheme.{u}} (g : W ⟶ V) (s : V ⟶ S)
    (x : G.obj (op (Over.mk s))) (s' : W ⟶ S) (x' : G.obj (op (Over.mk s'))) :
    (ext G).map g.op (⟨s, x⟩ : Pt G V) = (⟨s', x'⟩ : Pt G W) ↔
      ∃ h : g ≫ s = s', G.map (Over.homMk g (by simp [h]) : Over.mk s' ⟶ Over.mk s).op x = x' := by
  refine (sigma_eq_iff G _ _).trans (exists_congr fun h ↦ ?_)
  subst h
  exact (Eq.congr_left (tr_rfl G x')).trans eq_comm

lemma ext_map_mk_eq_map_mk_iff {W V₁ V₂ : Scheme.{u}} (g₁ : W ⟶ V₁) (g₂ : W ⟶ V₂)
    (s₁ : V₁ ⟶ S) (s₂ : V₂ ⟶ S) (x₁ : G.obj (op (Over.mk s₁))) (x₂ : G.obj (op (Over.mk s₂))) :
    (ext G).map g₁.op (⟨s₁, x₁⟩ : Pt G V₁) = (ext G).map g₂.op (⟨s₂, x₂⟩ : Pt G V₂) ↔
      ∃ h : g₁ ≫ s₁ = g₂ ≫ s₂,
        G.map (Over.homMk g₁ : Over.mk (g₁ ≫ s₁) ⟶ Over.mk s₁).op x₁ =
          G.map (Over.homMk g₂ h.symm : Over.mk (g₁ ≫ s₁) ⟶ Over.mk s₂).op x₂ := by
  refine (sigma_eq_iff G _ _).trans (exists_congr fun h ↦ ?_)
  rw [eq_comm]
  exact Eq.congr_right (map_map_apply G _ _ _ (by simp) _)

lemma map_homMk_id_apply {Z : Over S} (h : 𝟙 Z.left ≫ Z.hom = Z.hom) (x : G.obj (op Z)) :
    G.map (Over.homMk (𝟙 Z.left) h : Z ⟶ Z).op x = x := by
  rw [map_apply_congr_left G (α := Over.homMk (𝟙 Z.left) h) (β := 𝟙 Z) (by simp) x]
  simp

section Transfer

variable (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]

/-- The family on the underlying sieve of schemes induced by a family of `G` on a sieve
of an object of `Over S`. -/
def extFamily {Y : Over S} {R : Sieve Y} (x : Presieve.FamilyOfElements G R.arrows) :
    Presieve.FamilyOfElements (ext G) (Sieve.overEquiv Y R).arrows :=
  fun _ f hf ↦ ⟨f ≫ Y.hom, x (Over.homMk f) ((Sieve.overEquiv_iff _ _).1 hf)⟩

lemma extFamily_compatible {Y : Over S} {R : Sieve Y} {x : Presieve.FamilyOfElements G R.arrows}
    (hx : x.Compatible) : (extFamily G x).Compatible := by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ w
  refine (ext_map_mk_eq_map_mk_iff G _ _ _ _ _ _).2 ⟨(reassoc_of% w) Y.hom, ?_⟩
  exact hx _ _ _ _ (by ext; simpa using w)

lemma extFamily_isAmalgamation_iff {Y : Over S} {R : Sieve Y}
    {x : Presieve.FamilyOfElements G R.arrows} (hx : x.Compatible) (t : G.obj (op Y)) :
    (extFamily G x).IsAmalgamation (⟨Y.hom, t⟩ : Pt G Y.left) ↔ x.IsAmalgamation t := by
  constructor
  · intro ht Z g hg
    have hg' : Sieve.overEquiv Y R g.left := ⟨Z, g, 𝟙 _, hg, (Category.id_comp _).symm⟩
    have e₁ := sigma_mk_injective (ht g.left hg')
    let e : Z ⟶ Over.mk (g.left ≫ Y.hom) := Over.homMk (𝟙 Z.left) (by simp)
    have key : ∀ (g' : Z ⟶ Y) (hg'' : R g'), g' = g → x g' hg'' = x g hg := by
      rintro _ _ rfl; rfl
    rw [← key (e ≫ Over.homMk g.left) (R.downward_closed ((Sieve.overEquiv_iff _ _).1 hg') e)
      (by ext; simp [e]), hx.to_sieveCompatible _ _ ((Sieve.overEquiv_iff _ _).1 hg'), ← e₁]
    exact (map_map_apply G e _ g (by simp [e]) t).symm
  · intro ht Z f hf
    exact congrArg (Sigma.mk _) (ht _ _)

/-- If the extension of `G` is a sheaf for a subcanonical topology `J` on schemes,
then `G` is a sheaf for the induced topology on `Over S`. -/
theorem isSheaf_over_of_isSheaf_ext (h : Presieve.IsSheaf J (ext G)) :
    Presieve.IsSheaf (J.over S) G := by
  intro Y R hR x hx
  rw [GrothendieckTopology.mem_over_iff] at hR
  have hS := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J)
    (yoneda.obj S) _ hR
  obtain ⟨⟨s, y⟩, hy, -⟩ := h _ hR (extFamily G x) (extFamily_compatible G hx)
  have hs : s = Y.hom := hS.isSeparatedFor (fun _ f _ ↦ f ≫ Y.hom) s Y.hom
    (fun _ f hf ↦ congrArg Sigma.fst (hy f hf)) (fun _ _ _ ↦ rfl)
  have hy' : (extFamily G x).IsAmalgamation (⟨Y.hom, tr G hs.symm y⟩ : Pt G Y.left) := by
    rwa [(sigma_eq_iff G _ _).2 ⟨hs.symm, rfl⟩]
  refine ⟨tr G hs.symm y, (extFamily_isAmalgamation_iff G hx _).1 hy', fun t ht ↦ ?_⟩
  exact eq_of_heq (Sigma.mk.inj_iff.1 ((h _ hR).isSeparatedFor _ _ _
    ((extFamily_isAmalgamation_iff G hx t).2 ht) hy')).2

/-- Given a gluing `s₀` of the structure morphisms of a family of the extension of `G`,
the induced family of `G` over `Over.mk s₀`. -/
def overFamily {V : Scheme.{u}} {R : Sieve V} (x : Presieve.FamilyOfElements (ext G) R.arrows)
    (s₀ : V ⟶ S) (hs : ∀ ⦃Z : Scheme.{u}⦄ (f : Z ⟶ V) (hf : R f), f ≫ s₀ = (x f hf).1) :
    Presieve.FamilyOfElements G ((Sieve.overEquiv (Over.mk s₀)).symm R).arrows :=
  fun Z g hg ↦
    have hg' : R g.left := (Sieve.overEquiv_symm_iff _ _).1 hg
    G.map (Over.homMk (𝟙 Z.left) (by
      rw [Category.id_comp, ← hs g.left hg']
      simpa using Over.w g) : Z ⟶ Over.mk (x g.left hg').1).op (x g.left hg').2

lemma overFamily_compatible {V : Scheme.{u}} {R : Sieve V}
    {x : Presieve.FamilyOfElements (ext G) R.arrows} (hx : x.Compatible)
    (s₀ : V ⟶ S) (hs : ∀ ⦃Z : Scheme.{u}⦄ (f : Z ⟶ V) (hf : R f), f ≫ s₀ = (x f hf).1) :
    (overFamily G x s₀ hs).Compatible := by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ w
  have h₁' : R f₁.left := (Sieve.overEquiv_symm_iff _ _).1 h₁
  have h₂' : R f₂.left := (Sieve.overEquiv_symm_iff _ _).1 h₂
  have e := hx (f₁ := f₁.left) (f₂ := f₂.left) g₁.left g₂.left h₁' h₂'
    (by simpa using congrArg CommaMorphism.left w)
  obtain ⟨_, e⟩ := (ext_map_mk_eq_map_mk_iff G _ _ _ _ (x _ h₁').2 (x _ h₂').2).1 e
  dsimp only [overFamily]
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  refine map_eq_map_of_eq G ?_ _ _ _ _ (by simp) (by simp) e
  rw [← hs _ h₁']
  simpa using Over.w (g₁ ≫ f₁)

lemma isAmalgamation_mk_of_overFamily {V : Scheme.{u}} {R : Sieve V}
    {x : Presieve.FamilyOfElements (ext G) R.arrows}
    (s₀ : V ⟶ S) (hs : ∀ ⦃Z : Scheme.{u}⦄ (f : Z ⟶ V) (hf : R f), f ≫ s₀ = (x f hf).1)
    {t : G.obj (op (Over.mk s₀))} (ht : (overFamily G x s₀ hs).IsAmalgamation t) :
    x.IsAmalgamation (⟨s₀, t⟩ : Pt G V) := by
  intro Z f hf
  refine (ext_map_mk_eq_mk_iff G _ _ _ _ _).2 ⟨hs f hf, ?_⟩
  refine (ht (Over.homMk f (hs f hf) : Over.mk (x f hf).1 ⟶ Over.mk s₀) hf).trans ?_
  exact map_homMk_id_apply G _ _

lemma overFamily_isAmalgamation_of_mk {V : Scheme.{u}} {R : Sieve V}
    {x : Presieve.FamilyOfElements (ext G) R.arrows}
    (s₀ : V ⟶ S) (hs : ∀ ⦃Z : Scheme.{u}⦄ (f : Z ⟶ V) (hf : R f), f ≫ s₀ = (x f hf).1)
    {t : G.obj (op (Over.mk s₀))} (ht : x.IsAmalgamation (⟨s₀, t⟩ : Pt G V)) :
    (overFamily G x s₀ hs).IsAmalgamation t := by
  intro Z g hg
  obtain ⟨_, e⟩ := (ext_map_mk_eq_mk_iff G _ _ _ _ _).1
    (ht g.left ((Sieve.overEquiv_symm_iff _ _).1 hg))
  dsimp only [overFamily]
  rw [← e, map_map_apply G _ _ g (by simp)]

/-- If `G` is a sheaf for the topology on `Over S` induced by a subcanonical topology `J`,
then its extension is a `J`-sheaf. -/
theorem isSheaf_ext_of_isSheaf_over (h : Presieve.IsSheaf (J.over S) G) :
    Presieve.IsSheaf J (ext G) := by
  intro V R hR x hx
  have hS := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J)
    (yoneda.obj S) _ hR
  let z : Presieve.FamilyOfElements (yoneda.obj S) R.arrows := fun _ f hf ↦ (x f hf).1
  have hz : z.Compatible := fun _ _ _ g₁ g₂ _ _ h₁ h₂ w ↦
    congrArg Sigma.fst (hx g₁ g₂ h₁ h₂ w)
  obtain ⟨s₀, hs₀, -⟩ := hS z hz
  have hR' := GrothendieckTopology.overEquiv_symm_mem_over J (Over.mk s₀) R hR
  obtain ⟨t, ht, -⟩ := h _ hR' (overFamily G x s₀ hs₀) (overFamily_compatible G hx s₀ hs₀)
  refine ⟨⟨s₀, t⟩, isAmalgamation_mk_of_overFamily G s₀ hs₀ ht, ?_⟩
  rintro ⟨s₁, t₁⟩ ht₁
  have hs₁ : ∀ ⦃Z : Scheme.{u}⦄ (f : Z ⟶ V) (hf : R f), f ≫ s₁ = (x f hf).1 :=
    fun _ f hf ↦ congrArg Sigma.fst (ht₁ f hf)
  obtain rfl : s₁ = s₀ := hS.isSeparatedFor z s₁ s₀ hs₁ hs₀
  exact congrArg (Sigma.mk s₁) ((h _ hR').isSeparatedFor _ _ _
    (overFamily_isAmalgamation_of_mk G s₁ hs₀ ht₁) ht)

end Transfer

/-- The singleton sheaf condition for the extension of `G` along `p` follows from the
singleton sheaf condition of `S` and of `G` along all lifts of `p` to `Over S`. -/
theorem isSheafFor_singleton_ext {V W : Scheme.{u}} (p : W ⟶ V)
    (hS : Presieve.IsSheafFor (yoneda.obj S) (.singleton p))
    (hG : ∀ s : V ⟶ S, Presieve.IsSheafFor G
      (.singleton (Over.homMk p : Over.mk (p ≫ s) ⟶ Over.mk s))) :
    Presieve.IsSheafFor (ext G) (.singleton p) := by
  rw [Presieve.isSheafFor_singleton] at hS ⊢
  rintro ⟨s', y⟩ hy
  obtain ⟨s, hs, hs_uniq⟩ := hS s' (fun p₁ p₂ h ↦ congrArg Sigma.fst (hy p₁ p₂ h))
  have hs' : p ≫ s = s' := hs
  subst hs'
  obtain ⟨z, hz, hz_uniq⟩ := Presieve.isSheafFor_singleton.1 (hG s) y (by
    intro Z p₁ p₂ hp
    obtain ⟨_, e⟩ := (ext_map_mk_eq_map_mk_iff G _ _ _ _ y y).1
      (hy p₁.left p₂.left (by simpa using congrArg CommaMorphism.left hp))
    exact map_eq_map_of_eq G (by simpa using Over.w p₁) _ _ p₁ p₂ (by simp) (by simp) e)
  refine ⟨⟨s, z⟩, (ext_map_mk_eq_mk_iff G _ _ _ _ _).2 ⟨rfl, hz⟩, ?_⟩
  rintro ⟨s₁, z₁⟩ h₁
  obtain ⟨h, h'⟩ := (ext_map_mk_eq_mk_iff G _ _ _ _ _).1 h₁
  obtain rfl : s₁ = s := hs_uniq s₁ h
  exact congrArg (Sigma.mk s₁) (hz_uniq z₁ h')

set_option backward.isDefEq.respectTransparency.types false in
/-- **Site reduction.** A presheaf of types on `Over S` is an fppf sheaf as soon as it is
a Zariski sheaf and satisfies the singleton sheaf condition along every lift to `Over S` of a
flat surjective morphism of affine schemes. -/
theorem isSheaf_fppfTopology_over
    (hzar : Presieve.IsSheaf (Scheme.zariskiTopology.over S) G)
    (haff : ∀ {R R' : CommRingCat.{u}} (φ : R ⟶ R'), Flat (Spec.map φ) →
      Surjective (Spec.map φ) → ∀ s : Spec R ⟶ S, Presieve.IsSheafFor G
        (.singleton (Over.homMk (Spec.map φ) : Over.mk (Spec.map φ ≫ s) ⟶ Over.mk s))) :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) G := by
  refine isSheaf_over_of_isSheaf_ext G _
    (Presieve.isSheaf_of_le _ Scheme.fppfTopology_le_fpqcTopology ?_)
  rw [Scheme.fpqcTopology_eq_propQCTopology, isSheaf_type_propQCTopology_iff]
  refine ⟨isSheaf_ext_of_isSheaf_over G _ hzar, fun {R R'} φ hf hs ↦ ?_⟩
  have : Flat (Spec.map φ) := hf
  have : Surjective (Spec.map φ) := hs
  have : IsRegularEpi (Spec.map φ) := isRegularEpi_of_flat_of_surjective_of_isAffine _
  exact isSheafFor_singleton_ext G _
    (.singleton_of_isRepresentable_of_effectiveEpi _ _) (haff φ hf hs)

end Langlands.AlgebraicGeometry.OverFppfSheaf
