import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # The classifying morphism of a flat proper equivalence relation

Let `f : X ⟶ S` be separated and let `H` be a Hilbert scheme of `X` over `S`: a scheme
`πH : H ⟶ S` with an ideal sheaf `W` on `X ×_S H` whose pullbacks classify the flat closed
subschemes of `X ×_S T`, locally of finite presentation over `T`. Let `i : Z ⟶ X` be a
monomorphism over `S`, and `s t : R ⟶ Z` an equivalence relation on `Z` with `s` flat, proper
and locally of finite presentation. The family `R ⟶ X ×_S Z`, `r ↦ (i (t r), s r)`, is then
a closed immersion, flat over `Z`, so it is classified by a morphism `φ : Z ⟶ H`. This file
shows that two points `x y : T ⟶ Z` are related exactly when `x ≫ φ = y ≫ φ`. It also shows
that every point of `Z ×_H D` comes from `R`. Here `D` is the universal closed subscheme. This
is the first step of the proof of Nitsure, *Construction of Hilbert and Quot schemes*,
Theorem 6.8.
-/

universe u

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.FlatEquivalenceRelation

open _root_.AlgebraicGeometry

section Ideals

/-- A morphism factors through a closed immersion `e` exactly when its kernel contains the
kernel of `e`. -/
theorem ker_le_ker_iff_exists {R X T : Scheme.{u}} (e : R ⟶ X) [IsClosedImmersion e]
    (g : T ⟶ X) : e.ker ≤ g.ker ↔ ∃ r : T ⟶ R, r ≫ e = g := by
  constructor
  · intro H
    exact ⟨IsClosedImmersion.lift e g H, IsClosedImmersion.lift_fac e g H⟩
  · rintro ⟨r, rfl⟩
    exact Scheme.Hom.le_ker_comp r e

/-- The pullback of `I` along `m` is contained in the kernel of `g` exactly when `I` is
contained in the kernel of `g ≫ m`. -/
theorem comap_le_ker_iff {X Y T : Scheme.{u}} (I : Y.IdealSheafData) (m : X ⟶ Y) (g : T ⟶ X) :
    I.comap m ≤ g.ker ↔ I ≤ (g ≫ m).ker := by
  rw [← Scheme.IdealSheafData.map_bot g, ← Scheme.IdealSheafData.map_bot (g ≫ m),
    Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.le_map_iff_comap_le,
    Scheme.IdealSheafData.comap_comp]

/-- The pullback of `I` along `m` vanishes exactly when `I` is contained in the kernel of `m`. -/
theorem comap_eq_bot_iff {X Y : Scheme.{u}} (I : Y.IdealSheafData) (m : X ⟶ Y) :
    I.comap m = ⊥ ↔ I ≤ m.ker := by
  rw [← le_bot_iff, ← Scheme.Hom.ker_eq_bot_of_isIso (𝟙 X), comap_le_ker_iff, Category.id_comp]

/-- An ideal sheaf `I` is contained in `J` if every morphism whose kernel contains `J` has
kernel containing `I`. -/
theorem le_of_forall_le_ker {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : ∀ (T : Scheme.{u}) (g : T ⟶ X), J ≤ g.ker → I ≤ g.ker) : I ≤ J := by
  have := h J.subscheme J.subschemeι (by rw [Scheme.IdealSheafData.ker_subschemeι])
  rwa [Scheme.IdealSheafData.ker_subschemeι] at this

end Ideals

section BaseChange

/-- The morphism `X ×_S T' ⟶ X ×_S T` induced by a morphism `u : T' ⟶ T` over `S`. -/
noncomputable abbrev bc {X S T T' : Scheme.{u}} (f : X ⟶ S) (sT : T ⟶ S) (sT' : T' ⟶ S)
    (u : T' ⟶ T) (hu : u ≫ sT = sT') : pullback f sT' ⟶ pullback f sT :=
  pullback.map f sT' f sT (𝟙 X) u (𝟙 S) (by simp) (by simp [hu])

theorem bc_comp {X S T T' T'' : Scheme.{u}} (f : X ⟶ S) (sT : T ⟶ S) (sT' : T' ⟶ S)
    (sT'' : T'' ⟶ S) (u : T' ⟶ T) (hu : u ≫ sT = sT') (v : T'' ⟶ T') (hv : v ≫ sT' = sT'') :
    bc f sT' sT'' v hv ≫ bc f sT sT' u hu =
      bc f sT sT'' (v ≫ u) (by rw [Category.assoc, hu, hv]) := by
  apply pullback.hom_ext <;> simp

theorem bc_id {X S T : Scheme.{u}} (f : X ⟶ S) (sT : T ⟶ S) :
    bc f sT sT (𝟙 T) (Category.id_comp _) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

theorem bc_congr {X S T T' : Scheme.{u}} (f : X ⟶ S) (sT : T ⟶ S) (sT' : T' ⟶ S)
    {u v : T' ⟶ T} (huv : u = v) (hu : u ≫ sT = sT') (hv : v ≫ sT = sT') :
    bc f sT sT' u hu = bc f sT sT' v hv := by
  subst huv; rfl

end BaseChange

/-- A Hilbert scheme of `f : X ⟶ S`: a scheme `H` over `S` with an ideal sheaf `W` on
`X ×_S H` whose pullbacks give a bijection from the morphisms `T ⟶ H` over `S` onto the ideal
sheaves on `X ×_S T` with flat closed subscheme, locally of finite presentation over `T`. These
are the first two clauses of `HilbertSchemeUniversalFamilyStatement`. -/
structure Classifier {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The classifying scheme. -/
  H : Scheme.{u}
  /-- Its structure morphism. -/
  πH : H ⟶ S
  /-- The universal ideal sheaf. -/
  W : (pullback f πH).IdealSheafData
  family : ∀ (T : Scheme.{u}) (sT : T ⟶ S) (g : T ⟶ H) (hg : g ≫ πH = sT),
    Flat ((W.comap (bc f πH sT g hg)).subschemeι ≫ pullback.snd f sT) ∧
      LocallyOfFinitePresentation ((W.comap (bc f πH sT g hg)).subschemeι ≫ pullback.snd f sT)
  unique : ∀ (T : Scheme.{u}) (sT : T ⟶ S) (I : (pullback f sT).IdealSheafData),
    Flat (I.subschemeι ≫ pullback.snd f sT) →
      LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f sT) →
        ∃! g : T ⟶ H, ∃ hg : g ≫ πH = sT, W.comap (bc f πH sT g hg) = I

namespace Classifier

variable {X S : Scheme.{u}} {f : X ⟶ S} (C : Classifier f)

/-- Two morphisms to the Hilbert scheme with the same pullback of the universal ideal agree. -/
theorem eq_of_comap_eq {T : Scheme.{u}} {sT : T ⟶ S} {g₁ g₂ : T ⟶ C.H} (h₁ : g₁ ≫ C.πH = sT)
    (h₂ : g₂ ≫ C.πH = sT) (h : C.W.comap (bc f C.πH sT g₁ h₁) = C.W.comap (bc f C.πH sT g₂ h₂)) :
    g₁ = g₂ :=
  (C.unique T sT _ (C.family T sT g₁ h₁).1 (C.family T sT g₁ h₁).2).unique ⟨h₁, rfl⟩
    ⟨h₂, h.symm⟩

/-- The universal closed subscheme. -/
noncomputable abbrev D : Scheme.{u} := C.W.subscheme

/-- The inclusion of the universal closed subscheme. -/
noncomputable abbrev ιD : C.D ⟶ pullback f C.πH := C.W.subschemeι

/-- The universal closed subscheme, as a family over the Hilbert scheme. -/
noncomputable abbrev pD : C.D ⟶ C.H := C.ιD ≫ pullback.snd f C.πH

theorem flat_pD : Flat C.pD := by
  have := (C.family C.H C.πH (𝟙 _) (Category.id_comp _)).1
  rwa [bc_id, Scheme.IdealSheafData.comap_id] at this

theorem locallyOfFinitePresentation_pD : LocallyOfFinitePresentation C.pD := by
  have := (C.family C.H C.πH (𝟙 _) (Category.id_comp _)).2
  rwa [bc_id, Scheme.IdealSheafData.comap_id] at this

theorem isProper_pD [IsProper f] : IsProper C.pD := by
  dsimp only [pD]; infer_instance

end Classifier

/-- The relation on `T`-points of `Z` defined by a pair `s t : R ⟶ Z`. -/
def Rel {R Z : Scheme.{u}} (s t : R ⟶ Z) {T : Scheme.{u}} (x y : T ⟶ Z) : Prop :=
  ∃ ρ : T ⟶ R, ρ ≫ s = x ∧ ρ ≫ t = y

theorem Rel.comp {R Z T T' : Scheme.{u}} {s t : R ⟶ Z} {x y : T ⟶ Z} (h : Rel s t x y)
    (u : T' ⟶ T) : Rel s t (u ≫ x) (u ≫ y) := by
  obtain ⟨ρ, hs, ht⟩ := h
  exact ⟨u ≫ ρ, by rw [Category.assoc, hs], by rw [Category.assoc, ht]⟩

section Family

variable {X S Z R : Scheme.{u}} {f : X ⟶ S} {p : Z ⟶ S} (s t : R ⟶ Z) (i : Z ⟶ X)
  (hi : i ≫ f = p) (h : s ≫ p = t ≫ p)

/-- The family `R ⟶ X ×_S Z`, `r ↦ (i (t r), s r)`. -/
noncomputable def family : R ⟶ pullback f p :=
  pullback.lift (t ≫ i) s (by rw [Category.assoc, hi, h])

@[reassoc (attr := simp)]
theorem family_fst : family s t i hi h ≫ pullback.fst f p = t ≫ i := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem family_snd : family s t i hi h ≫ pullback.snd f p = s := pullback.lift_snd _ _ _

theorem mono_family [Mono i] [Mono (pullback.lift s t h)] : Mono (family s t i hi h) := by
  constructor
  intro T a b hab
  have h1 : a ≫ s = b ≫ s := by
    simpa using congrArg (· ≫ pullback.snd f p) hab
  have h2 : a ≫ t = b ≫ t := by
    rw [← cancel_mono i]
    simpa using congrArg (· ≫ pullback.fst f p) hab
  rw [← cancel_mono (pullback.lift s t h)]
  apply pullback.hom_ext <;> simpa

theorem isClosedImmersion_family [Mono i] [Mono (pullback.lift s t h)] [IsSeparated f]
    [IsProper s] : IsClosedImmersion (family s t i hi h) := by
  have := mono_family s t i hi h
  have : IsProper (family s t i hi h ≫ pullback.snd f p) := by
    rw [family_snd]; infer_instance
  have : IsProper (family s t i hi h) :=
    IsProper.of_comp (f := family s t i hi h) (g := pullback.snd f p)
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩

theorem subschemeι_ker_family [IsClosedImmersion (family s t i hi h)] :
    (family s t i hi h).ker.subschemeι ≫ pullback.snd f p =
      inv (family s t i hi h).toImage ≫ s := by
  rw [IsIso.eq_inv_comp, ← Category.assoc]
  exact (congrArg (· ≫ pullback.snd f p) (family s t i hi h).toImage_imageι).trans
    (family_snd s t i hi h)

theorem flat_ker_family [IsClosedImmersion (family s t i hi h)] [Flat s] :
    Flat ((family s t i hi h).ker.subschemeι ≫ pullback.snd f p) := by
  rw [subschemeι_ker_family]; infer_instance

theorem locallyOfFinitePresentation_ker_family [IsClosedImmersion (family s t i hi h)]
    [LocallyOfFinitePresentation s] :
    LocallyOfFinitePresentation ((family s t i hi h).ker.subschemeι ≫ pullback.snd f p) := by
  rw [subschemeι_ker_family]; infer_instance

end Family

/-- The graph `Z ⟶ X ×_S H` of the classifying morphism. -/
noncomputable def graph₀ {X S Z : Scheme.{u}} {f : X ⟶ S} (C : Classifier f) {p : Z ⟶ S}
    (i : Z ⟶ X) (hi : i ≫ f = p) (φ : Z ⟶ C.H) (hφ : φ ≫ C.πH = p) : Z ⟶ pullback f C.πH :=
  pullback.lift i φ (by rw [hi, hφ])

@[reassoc (attr := simp)]
theorem graph₀_fst {X S Z : Scheme.{u}} {f : X ⟶ S} (C : Classifier f) {p : Z ⟶ S}
    (i : Z ⟶ X) (hi : i ≫ f = p) (φ : Z ⟶ C.H) (hφ : φ ≫ C.πH = p) :
    graph₀ C i hi φ hφ ≫ pullback.fst f C.πH = i := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graph₀_snd {X S Z : Scheme.{u}} {f : X ⟶ S} (C : Classifier f) {p : Z ⟶ S}
    (i : Z ⟶ X) (hi : i ≫ f = p) (φ : Z ⟶ C.H) (hφ : φ ≫ C.πH = p) :
    graph₀ C i hi φ hφ ≫ pullback.snd f C.πH = φ := pullback.lift_snd _ _ _

section Classifying

variable {X S Z R : Scheme.{u}} {f : X ⟶ S} (C : Classifier f) {p : Z ⟶ S} {s t : R ⟶ Z}
  {i : Z ⟶ X} {hi : i ≫ f = p} {h : s ≫ p = t ≫ p}
  [IsClosedImmersion (family s t i hi h)]
  {φ : Z ⟶ C.H} {hφ : φ ≫ C.πH = p}

/-- The pullback of the family `R ⟶ X ×_S Z` along `z : T ⟶ Z`. -/
noncomputable abbrev famAt (s t : R ⟶ Z) (i : Z ⟶ X) (hi : i ≫ f = p) (h : s ≫ p = t ≫ p)
    {T : Scheme.{u}} (sT : T ⟶ S) (z : T ⟶ Z) (hz : z ≫ p = sT) :
    (pullback f sT).IdealSheafData :=
  (family s t i hi h).ker.comap (bc f p sT z hz)

omit [IsClosedImmersion (family s t i hi h)] in
theorem comap_bc_comp (hW : C.W.comap (bc f C.πH p φ hφ) = (family s t i hi h).ker)
    {T : Scheme.{u}} (sT : T ⟶ S) (z : T ⟶ Z) (hz : z ≫ p = sT) :
    C.W.comap (bc f C.πH sT (z ≫ φ) (by rw [Category.assoc, hφ, hz])) =
      famAt s t i hi h sT z hz := by
  rw [famAt, ← hW, ← Scheme.IdealSheafData.comap_comp, bc_comp]

theorem famAt_le_ker_iff {T T' : Scheme.{u}} (sT : T ⟶ S) (z : T ⟶ Z) (hz : z ≫ p = sT)
    (g : T' ⟶ pullback f sT) :
    famAt s t i hi h sT z hz ≤ g.ker ↔
      ∃ r : T' ⟶ R, r ≫ s = (g ≫ pullback.snd f sT) ≫ z ∧
        r ≫ t ≫ i = g ≫ pullback.fst f sT := by
  rw [famAt, comap_le_ker_iff, ker_le_ker_iff_exists]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_, ?_⟩
    · have := congrArg (· ≫ pullback.snd f p) hr
      simpa using this
    · have := congrArg (· ≫ pullback.fst f p) hr
      simpa using this
  · rintro ⟨r, hrs, hrt⟩
    refine ⟨r, ?_⟩
    apply pullback.hom_ext
    · simp [hrt]
    · simp [hrs]

variable (hEq : ∀ T : Scheme.{u}, Equivalence (@Rel R Z s t T))
include hEq

theorem famAt_le_of_rel [Mono i] {T : Scheme.{u}} (sT : T ⟶ S) (x y : T ⟶ Z)
    (hx : x ≫ p = sT) (hy : y ≫ p = sT) (hxy : Rel s t x y) :
    famAt s t i hi h sT x hx ≤ famAt s t i hi h sT y hy := by
  refine le_of_forall_le_ker fun T' g hg => ?_
  rw [famAt_le_ker_iff] at hg ⊢
  obtain ⟨r, hrs, hrt⟩ := hg
  have h1 : Rel s t ((g ≫ pullback.snd f sT) ≫ y) (r ≫ t) := ⟨r, hrs, rfl⟩
  obtain ⟨r', hr's, hr't⟩ := (hEq T').trans (hxy.comp (g ≫ pullback.snd f sT)) h1
  exact ⟨r', hr's, by rw [← Category.assoc, hr't, Category.assoc, hrt]⟩

/-- **The classifying morphism detects the relation.** Two points `x y : T ⟶ Z` are related
exactly when they have the same image under the classifying morphism `φ`. -/
theorem rel_iff [Mono i] (hW : C.W.comap (bc f C.πH p φ hφ) = (family s t i hi h).ker)
    {T : Scheme.{u}} (x y : T ⟶ Z) : Rel s t x y ↔ x ≫ φ = y ≫ φ := by
  constructor
  · intro hxy
    have hy : y ≫ p = x ≫ p := by
      obtain ⟨ρ, hs, ht⟩ := hxy
      rw [← hs, ← ht, Category.assoc, Category.assoc, h]
    have he : famAt s t i hi h (x ≫ p) x rfl = famAt s t i hi h (x ≫ p) y hy :=
      le_antisymm (famAt_le_of_rel hEq _ x y rfl hy hxy)
        (famAt_le_of_rel hEq _ y x hy rfl ((hEq T).symm hxy))
    refine C.eq_of_comap_eq (sT := x ≫ p) (by rw [Category.assoc, hφ])
      (by rw [Category.assoc, hφ, hy]) ?_
    rw [comap_bc_comp C hW _ x rfl, comap_bc_comp C hW _ y hy, he]
  · intro hxy
    have hy : y ≫ p = x ≫ p := by rw [← hφ, ← Category.assoc, ← hxy, Category.assoc]
    have he : famAt s t i hi h (x ≫ p) x rfl = famAt s t i hi h (x ≫ p) y hy := by
      rw [← comap_bc_comp C hW _ x rfl, ← comap_bc_comp C hW _ y hy,
        bc_congr f C.πH (x ≫ p) hxy]
    let g : T ⟶ pullback f (x ≫ p) :=
      pullback.lift (x ≫ i) (𝟙 T) (by rw [Category.assoc, hi, Category.id_comp])
    obtain ⟨r, hrs, hrt⟩ := (hEq T).refl x
    have hle : famAt s t i hi h (x ≫ p) x rfl ≤ g.ker := by
      rw [famAt_le_ker_iff]
      exact ⟨r, by simp [g, hrs], by rw [← Category.assoc, hrt]; simp [g]⟩
    rw [he, famAt_le_ker_iff] at hle
    obtain ⟨r', hr's, hr't⟩ := hle
    refine (hEq T).symm ⟨r', by simpa [g] using hr's, ?_⟩
    rw [← cancel_mono i]
    simpa [g] using hr't

theorem t_comp_eq_s_comp [Mono i] (hW : C.W.comap (bc f C.πH p φ hφ) = (family s t i hi h).ker) :
    t ≫ φ = s ≫ φ :=
  ((rel_iff C hEq hW s t).mp ⟨𝟙 R, Category.id_comp _, Category.id_comp _⟩).symm

theorem le_ker_graph₀ (hW : C.W.comap (bc f C.πH p φ hφ) = (family s t i hi h).ker) :
    C.W ≤ (graph₀ C i hi φ hφ).ker := by
  let Δ : Z ⟶ pullback f p := pullback.lift i (𝟙 Z) (by rw [hi, Category.id_comp])
  have hΔ : Δ ≫ bc f C.πH p φ hφ = graph₀ C i hi φ hφ := by
    apply pullback.hom_ext <;> simp [Δ, graph₀]
  rw [← hΔ, ← comap_le_ker_iff, hW, ker_le_ker_iff_exists]
  obtain ⟨r, hrs, hrt⟩ := (hEq Z).refl (𝟙 Z)
  refine ⟨r, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, family_fst, ← Category.assoc, hrt, Category.id_comp]; simp [Δ]
  · rw [Category.assoc, family_snd, hrs]; simp [Δ]

/-- The graph of the classifying morphism, as a morphism into the universal closed
subscheme. -/
noncomputable def graph (hW : C.W.comap (bc f C.πH p φ hφ) = (family s t i hi h).ker) :
    Z ⟶ C.D :=
  IsClosedImmersion.lift C.ιD (graph₀ C i hi φ hφ)
    (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_ker_graph₀ C hEq hW)

@[reassoc (attr := simp)]
theorem graph_ιD (hW : C.W.comap (bc f C.πH p φ hφ) = (family s t i hi h).ker) :
    graph C hEq hW ≫ C.ιD = graph₀ C i hi φ hφ :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem graph_pD (hW : C.W.comap (bc f C.πH p φ hφ) = (family s t i hi h).ker) :
    graph C hEq hW ≫ C.pD = φ := by
  simp [Classifier.pD]

/-- **Points of `Z ×_H D` come from `R`.** If `a : T ⟶ Z` and `b : T ⟶ D` lie over the same
point of `H`, then `b` is the graph of `t ∘ c` for some `c : T ⟶ R` with `s ∘ c = a`. -/
theorem exists_factor [Mono i] (hW : C.W.comap (bc f C.πH p φ hφ) = (family s t i hi h).ker)
    {T : Scheme.{u}} (a : T ⟶ Z) (b : T ⟶ C.D) (hab : a ≫ φ = b ≫ C.pD) :
    ∃ c : T ⟶ R, c ≫ s = a ∧ c ≫ t ≫ graph C hEq hW = b := by
  let g : T ⟶ pullback f p := pullback.lift (b ≫ C.ιD ≫ pullback.fst f C.πH) a (by
    rw [Category.assoc, Category.assoc, pullback.condition, ← hφ, ← Category.assoc a, hab]
    simp [Classifier.pD])
  have hg : g ≫ bc f C.πH p φ hφ = b ≫ C.ιD := by
    apply pullback.hom_ext
    · simp [g]
    · simp [g, hab]
  have hle : (family s t i hi h).ker ≤ g.ker := by
    rw [← hW, comap_le_ker_iff, hg]
    have := Scheme.Hom.le_ker_comp b C.ιD
    rwa [Scheme.IdealSheafData.ker_subschemeι] at this
  obtain ⟨c, hc⟩ := (ker_le_ker_iff_exists _ g).mp hle
  have hcs : c ≫ s = a := by simpa [g] using congrArg (· ≫ pullback.snd f p) hc
  have hct : c ≫ t ≫ i = b ≫ C.ιD ≫ pullback.fst f C.πH := by
    simpa [g] using congrArg (· ≫ pullback.fst f p) hc
  refine ⟨c, hcs, ?_⟩
  rw [← cancel_mono C.ιD]
  apply pullback.hom_ext
  · simp [hct]
  · have := t_comp_eq_s_comp C hEq hW
    simp only [Category.assoc, graph_ιD_assoc, graph₀_snd]
    rw [this, ← Category.assoc, hcs, hab]

end Classifying

end Langlands.AlgebraicGeometry.FlatEquivalenceRelation
