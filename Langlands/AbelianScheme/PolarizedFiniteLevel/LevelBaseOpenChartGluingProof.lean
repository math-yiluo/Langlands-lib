import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelBaseOpenChartGluingStatement
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Gluing open charts on level bases -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

namespace LevelBase

variable {n : ℕ}

/-- The source of an open immersion into a level base, as a level base. -/
abbrev ofOpenImmersion (S : LevelBase n) {W : Scheme.{0}} (g : W ⟶ S.obj)
    [IsOpenImmersion g] : LevelBase n :=
  ⟨W, isLocallyNoetherian_of_isOpenImmersion g,
    by simpa only [map_natCast] using S.level_isUnit.map g.appTop.hom⟩

@[simp]
theorem ofOpenImmersion_obj (S : LevelBase n) {W : Scheme.{0}} (g : W ⟶ S.obj)
    [IsOpenImmersion g] : (S.ofOpenImmersion g).obj = W :=
  rfl

/-- Two sections of a Zariski sheaf agreeing on an open cover are equal. -/
theorem IsZariskiSheaf.ext {F : (LevelBase n)ᵒᵖ ⥤ Type 1} (hF : IsZariskiSheaf F)
    (S : LevelBase n) {κ : Type} (U : κ → S.obj.Opens) (hU : iSup U = ⊤)
    {t₁ t₂ : F.obj (op S)}
    (h : ∀ k, F.map (S.openι (U k)).op t₁ = F.map (S.openι (U k)).op t₂) : t₁ = t₂ := by
  obtain ⟨t, -, ht⟩ := hF S κ U hU (fun k => F.map (S.openι (U k)).op t₁) (by
    intro k l
    simp only [← Functor.map_comp_apply, ← op_comp, openLE_openι])
  exact (ht t₁ fun k => rfl).trans (ht t₂ fun k => (h k).symm).symm

end LevelBase

namespace OpenChartGluing

open LevelBase

variable {n : ℕ} {F : (LevelBase n)ᵒᵖ ⥤ Type 1} {ι : Type} {X : ι → LevelBase n}
  (a : ∀ i, uliftYoneda.{1}.obj (X i) ⟶ F)

/-- The value of the chart `a i` on a morphism into `X i`. -/
abbrev val (i : ι) {W : LevelBase n} (g : W ⟶ X i) : F.obj (op W) :=
  (a i).app (op W) (ULift.up g)

theorem val_comp (i : ι) {W V : LevelBase n} (g : W ⟶ V) (h : V ⟶ X i) :
    val a i (g ≫ h) = F.map g.op (val a i h) := by
  have := ConcreteCategory.congr_hom ((a i).naturality g.op)
    (show (uliftYoneda.{1}.obj (X i)).obj (op V) from ULift.up h)
  simp at this
  exact this

/-- The universal point of the chart `a i`. -/
def ξ (i : ι) : F.obj (op (X i)) :=
  val a i (𝟙 (X i))

theorem val_eq (i : ι) {W : LevelBase n} (g : W ⟶ X i) : val a i g = F.map g.op (ξ a i) := by
  rw [ξ, ← val_comp, Category.comp_id]

theorem map_mem_range (j : ι) {W V : LevelBase n} (g : W ⟶ V) {y : F.obj (op V)}
    (hy : y ∈ Set.range ((a j).app (op V))) :
    F.map g.op y ∈ Set.range ((a j).app (op W)) := by
  obtain ⟨⟨h⟩, rfl⟩ := hy
  exact ⟨ULift.up (g ≫ h), val_comp a j g h⟩

variable (ha : ∀ i, IsOpenChart (a i))

include ha in
theorem val_injective (i : ι) {W : LevelBase n} {g h : W ⟶ X i}
    (e : val a i g = val a i h) : g = h :=
  congrArg ULift.down ((ha i).1 (op W) e)

/-- The open of `X i` over which the universal point of chart `i` lies in chart `j`. -/
def Uo (i j : ι) : (X i).obj.Opens :=
  ((ha j).2 (X i) (ξ a i)).choose

theorem mem_range_val_iff (i j : ι) {W : LevelBase n} (g : W ⟶ X i) :
    val a i g ∈ Set.range ((a j).app (op W)) ↔
      Set.range g.hom.base ⊆ (Uo a ha i j : Set (X i).obj) := by
  rw [val_eq]
  exact ((ha j).2 (X i) (ξ a i)).choose_spec W g

theorem range_subset (i j : ι) {W : LevelBase n} (g : W.obj ⟶ (X i).obj)
    (hg : val a i (homMk g) ∈ Set.range ((a j).app (op W))) :
    Set.range g ⊆ Set.range (Uo a ha i j).ι := by
  rw [Scheme.Opens.range_ι]
  exact (mem_range_val_iff a ha i j (homMk g)).1 hg

theorem Uo_self (i : ι) : Uo a ha i i = ⊤ := by
  have h := (mem_range_val_iff a ha i i (𝟙 (X i))).1 ⟨_, rfl⟩
  refine top_le_iff.mp fun x _ => h ⟨x, ?_⟩
  rfl

/-- The inclusion of `Uo i j` into `X i`, as a morphism of level bases. -/
abbrev incl (i j : ι) : (X i).ofOpen (Uo a ha i j) ⟶ X i :=
  (X i).openι (Uo a ha i j)

theorem val_incl_mem (i j : ι) :
    val a i (incl a ha i j) ∈ Set.range ((a j).app (op ((X i).ofOpen (Uo a ha i j)))) := by
  rw [mem_range_val_iff]
  exact (Scheme.Opens.range_ι _).le

/-- The transition morphism `Uo i j ⟶ X j`. -/
def φ (i j : ι) : (X i).ofOpen (Uo a ha i j) ⟶ X j :=
  (val_incl_mem a ha i j).choose.down

theorem val_φ (i j : ι) : val a j (φ a ha i j) = val a i (incl a ha i j) :=
  (val_incl_mem a ha i j).choose_spec

/-- The transition morphism as a morphism of schemes. -/
def φs (i j : ι) : (Uo a ha i j).toScheme ⟶ (X j).obj :=
  (φ a ha i j).hom

theorem range_φ (i j : ι) :
    Set.range (φs a ha i j) ⊆ Set.range (Uo a ha j i).ι := by
  rw [Scheme.Opens.range_ι]
  exact (mem_range_val_iff a ha j i (φ a ha i j)).1 (by rw [val_φ]; exact ⟨_, rfl⟩)

theorem val_comp_φ (i j : ι) {W : LevelBase n} (q : W.obj ⟶ (Uo a ha i j).toScheme) :
    val a j (homMk (q ≫ φs a ha i j)) = val a i (homMk (q ≫ (Uo a ha i j).ι)) := by
  have h₁ : (homMk (q ≫ φs a ha i j) : W ⟶ X j) =
      (homMk q : W ⟶ (X i).ofOpen (Uo a ha i j)) ≫ φ a ha i j := rfl
  have h₂ : (homMk (q ≫ (Uo a ha i j).ι) : W ⟶ X i) =
      (homMk q : W ⟶ (X i).ofOpen (Uo a ha i j)) ≫ incl a ha i j := rfl
  rw [h₁, h₂, val_comp, val_comp, val_φ]

/-- The gluing transition map `Uo i j ⟶ Uo j i`. -/
def t (i j : ι) : (Uo a ha i j).toScheme ⟶ (Uo a ha j i).toScheme :=
  IsOpenImmersion.lift (Uo a ha j i).ι (φs a ha i j) (range_φ a ha i j)

@[reassoc (attr := simp)]
theorem t_ι (i j : ι) : t a ha i j ≫ (Uo a ha j i).ι = φs a ha i j :=
  IsOpenImmersion.lift_fac _ _ _

theorem φ_self (i : ι) : φ a ha i i = incl a ha i i :=
  val_injective a ha i (val_φ a ha i i)

theorem t_self (i : ι) : t a ha i i = 𝟙 _ := by
  rw [← cancel_mono (Uo a ha i i).ι, t_ι, Category.id_comp, φs, φ_self]
  rfl

/-- The base point `Uo i j ×_{X i} Uo i k ⟶ X i`. -/
abbrev π (i j k : ι) : pullback (Uo a ha i j).ι (Uo a ha i k).ι ⟶ (X i).obj :=
  pullback.fst _ _ ≫ (Uo a ha i j).ι

/-- The triple intersection as a level base. -/
abbrev P (i j k : ι) : LevelBase n :=
  (X i).ofOpenImmersion (π a ha i j k)

theorem range_fst_φ (i j k : ι) :
    Set.range (pullback.fst (Uo a ha i j).ι (Uo a ha i k).ι ≫ φs a ha i j) ⊆
      Set.range (Uo a ha j k).ι := by
  apply range_subset a ha j k (W := P a ha i j k)
  rw [val_comp_φ, pullback.condition]
  have : (homMk (pullback.snd (Uo a ha i j).ι (Uo a ha i k).ι ≫ (Uo a ha i k).ι) :
      P a ha i j k ⟶ X i) = (homMk (pullback.snd _ _) :
        P a ha i j k ⟶ (X i).ofOpen (Uo a ha i k)) ≫ incl a ha i k := rfl
  rw [this, val_comp]
  exact map_mem_range a k _ (val_incl_mem a ha i k)

/-- The triple-overlap transition map. -/
def t' (i j k : ι) :
    pullback (Uo a ha i j).ι (Uo a ha i k).ι ⟶ pullback (Uo a ha j k).ι (Uo a ha j i).ι :=
  pullback.lift
    (IsOpenImmersion.lift (Uo a ha j k).ι
      (pullback.fst _ _ ≫ φs a ha i j) (range_fst_φ a ha i j k))
    (pullback.fst _ _ ≫ t a ha i j) (by simp)

theorem t'_snd (i j k : ι) :
    t' a ha i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t a ha i j :=
  pullback.lift_snd _ _ _

theorem t'_π (i j k : ι) :
    t' a ha i j k ≫ π a ha j k i = pullback.fst _ _ ≫ φs a ha i j := by
  rw [π, t', pullback.lift_fst_assoc, IsOpenImmersion.lift_fac]

theorem val_t'_π (i j k : ι) {W : LevelBase n}
    (p : W.obj ⟶ pullback (Uo a ha i j).ι (Uo a ha i k).ι) :
    val a j (homMk (p ≫ t' a ha i j k ≫ π a ha j k i)) = val a i (homMk (p ≫ π a ha i j k)) := by
  rw [t'_π, ← Category.assoc, val_comp_φ, Category.assoc]

theorem cocycle_π (i j k : ι) :
    (t' a ha i j k ≫ t' a ha j k i ≫ t' a ha k i j) ≫ π a ha i j k = π a ha i j k := by
  apply congrArg InducedCategory.Hom.hom
    (val_injective a ha i (W := P a ha i j k) (g := homMk _) (h := homMk _) ?_)
  have h₁ := val_t'_π a ha k i j (W := P a ha i j k) (t' a ha i j k ≫ t' a ha j k i)
  have h₂ := val_t'_π a ha j k i (W := P a ha i j k) (t' a ha i j k)
  have h₃ := val_t'_π a ha i j k (W := P a ha i j k) (𝟙 _)
  simp only [Category.assoc, Category.id_comp] at h₁ h₂ h₃
  simp only [Category.assoc]
  rw [h₁, h₂, h₃]

theorem cocycle (i j k : ι) :
    t' a ha i j k ≫ t' a ha j k i ≫ t' a ha k i j = 𝟙 _ := by
  have h := cocycle_π a ha i j k
  apply pullback.hom_ext
  · rw [← cancel_mono (Uo a ha i j).ι]
    simpa only [Category.assoc, Category.id_comp] using h
  · rw [← cancel_mono (Uo a ha i k).ι]
    simp only [Category.assoc, Category.id_comp, ← pullback.condition]
    simpa only [Category.assoc] using h

/-- The gluing datum of the charts. -/
def glueData : Scheme.GlueData where
  J := ι
  U i := (X i).obj
  V p := (Uo a ha p.1 p.2).toScheme
  f i j := (Uo a ha i j).ι
  f_id i := Uo_self a ha i ▸ (Scheme.topIso _).isIso_hom
  f_hasPullback := inferInstance
  f_open := inferInstance
  t i j := t a ha i j
  t_id i := t_self a ha i
  t' i j k := t' a ha i j k
  t_fac i j k := t'_snd a ha i j k
  cocycle i j k := cocycle a ha i j k

/-- The glued scheme. -/
abbrev Yg : Scheme.{0} :=
  (glueData a ha).glued

/-- The chart inclusions into the glued scheme. -/
abbrev ιg (i : ι) : (X i).obj ⟶ Yg a ha :=
  (glueData a ha).ι i

instance (i : ι) : IsOpenImmersion (ιg a ha i) :=
  (glueData a ha).ι_isOpenImmersion i

instance isLocallyNoetherian_Yg : IsLocallyNoetherian (Yg a ha) :=
  (isLocallyNoetherian_iff_openCover (glueData a ha).openCover).2 fun i =>
    (X i).locallyNoetherian

theorem isUnit_Yg : IsUnit (n : Γ(Yg a ha, ⊤)) := by
  apply RingedSpace.isUnit_of_isUnit_germ
  intro x hx
  obtain ⟨i, y, rfl⟩ := (glueData a ha).ι_jointly_surjective x
  rw [map_natCast]
  apply isUnit_of_map_unit (((glueData a ha).ι i).stalkMap y).hom
  rw [map_natCast]
  have h := (X i).level_isUnit.map ((X i).obj.presheaf.germ ⊤ y trivial).hom
  rw [map_natCast] at h
  exact h

/-- The glued scheme as a level base. -/
abbrev Ylb : LevelBase n :=
  ⟨Yg a ha, isLocallyNoetherian_Yg a ha, isUnit_Yg a ha⟩

/-- The chart inclusions as morphisms of level bases. -/
abbrev jlb (i : ι) : X i ⟶ Ylb a ha :=
  homMk (ιg a ha i)

/-- Two morphisms to charts with the same image in `F` agree in the glued scheme. -/
theorem comp_ι_eq (i j : ι) {W : LevelBase n} (g : W.obj ⟶ (X i).obj)
    (h : W.obj ⟶ (X j).obj) (e : val a i (homMk g) = val a j (homMk h)) :
    g ≫ ιg a ha i = h ≫ ιg a ha j := by
  have hg := range_subset a ha i j g ⟨ULift.up (homMk h), e.symm⟩
  obtain ⟨q, hq₁⟩ : ∃ q, q ≫ (Uo a ha i j).ι = g := ⟨_, IsOpenImmersion.lift_fac _ _ hg⟩
  have hq₂ : q ≫ φs a ha i j = h := by
    have := val_comp_φ a ha i j q
    rw [hq₁, e] at this
    exact congrArg InducedCategory.Hom.hom (val_injective a ha j this)
  rw [← hq₁, ← hq₂, Category.assoc, Category.assoc, ← t_ι, Category.assoc]
  exact congrArg (q ≫ ·) ((glueData a ha).glue_condition i j).symm

/-- Two morphisms to charts that agree in the glued scheme have the same image in `F`. -/
theorem val_eq_of_comp_eq (i j : ι) {W : LevelBase n} (g : W ⟶ X i) (h : W ⟶ X j)
    (e : g.hom ≫ ιg a ha i = h.hom ≫ ιg a ha j) : val a i g = val a j h := by
  let q : W.obj ⟶ (Uo a ha i j).toScheme :=
    PullbackCone.IsLimit.lift ((glueData a ha).vPullbackConeIsLimit i j) g.hom h.hom e
  have hq₁ : q ≫ (Uo a ha i j).ι = g.hom :=
    PullbackCone.IsLimit.lift_fst _ _ _ _
  have hq₂ : q ≫ t a ha i j ≫ (Uo a ha j i).ι = h.hom :=
    PullbackCone.IsLimit.lift_snd _ _ _ _
  rw [t_ι] at hq₂
  change val a i (homMk g.hom) = val a j (homMk h.hom)
  rw [← hq₁, ← hq₂, val_comp_φ]

/-- The open of the glued scheme covered by chart `i`. -/
abbrev Vo (i : ι) : (Ylb a ha).obj.Opens :=
  (ιg a ha i).opensRange

theorem iSup_Vo : iSup (Vo a ha) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨i, y, rfl⟩ := (glueData a ha).ι_jointly_surjective x
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, y, rfl⟩

/-- The identification of the open `Vo i` with the chart `X i`. -/
def ρ (i : ι) : (Ylb a ha).ofOpen (Vo a ha i) ⟶ X i :=
  homMk (ιg a ha i).isoOpensRange.inv

/-- The inverse identification of the chart `X i` with the open `Vo i`. -/
def ρinv (i : ι) : X i ⟶ (Ylb a ha).ofOpen (Vo a ha i) :=
  homMk (ιg a ha i).isoOpensRange.hom

/-- The chart section over `Vo i`. -/
def s (i : ι) : F.obj (op ((Ylb a ha).ofOpen (Vo a ha i))) :=
  val a i (ρ a ha i)

theorem s_compat (i j : ι) :
    F.map ((Ylb a ha).openLE (inf_le_left : Vo a ha i ⊓ Vo a ha j ≤ Vo a ha i)).op (s a ha i) =
      F.map ((Ylb a ha).openLE (inf_le_right : Vo a ha i ⊓ Vo a ha j ≤ Vo a ha j)).op
        (s a ha j) := by
  rw [s, s, ← val_comp, ← val_comp]
  apply val_eq_of_comp_eq a ha i j
  change ((Yg a ha).homOfLE (inf_le_left : Vo a ha i ⊓ Vo a ha j ≤ Vo a ha i) ≫
      (ιg a ha i).isoOpensRange.inv) ≫ ιg a ha i =
    ((Yg a ha).homOfLE (inf_le_right : Vo a ha i ⊓ Vo a ha j ≤ Vo a ha j) ≫
      (ιg a ha j).isoOpensRange.inv) ≫ ιg a ha j
  simp only [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, Scheme.homOfLE_ι]

variable (hF : IsZariskiSheaf F)

include hF in
theorem exists_σ : ∃ σ : F.obj (op (Ylb a ha)),
    ∀ i, F.map ((Ylb a ha).openι (Vo a ha i)).op σ = s a ha i :=
  (hF (Ylb a ha) ι (Vo a ha) (iSup_Vo a ha) (s a ha) (s_compat a ha)).exists

/-- The section of `F` over the glued level base glued from the chart sections. -/
def σ : F.obj (op (Ylb a ha)) :=
  (exists_σ a ha hF).choose

theorem σ_spec (i : ι) : F.map ((Ylb a ha).openι (Vo a ha i)).op (σ a ha hF) = s a ha i :=
  (exists_σ a ha hF).choose_spec i

theorem map_jlb_σ (i : ι) : F.map (jlb a ha i).op (σ a ha hF) = ξ a i := by
  have hj : jlb a ha i = ρinv a ha i ≫ (Ylb a ha).openι (Vo a ha i) := by
    ext1
    exact (Scheme.Hom.isoOpensRange_hom_ι (ιg a ha i)).symm
  have hid : ρinv a ha i ≫ ρ a ha i = 𝟙 _ := by
    ext1
    exact (ιg a ha i).isoOpensRange.hom_inv_id
  rw [hj, op_comp, Functor.map_comp_apply, σ_spec, s, val_eq,
    ← Functor.map_comp_apply, ← op_comp, hid, op_id, Functor.map_id_apply]

/-- The comparison from the functor of points of the glued level base to `F`. -/
def e₀ : uliftYoneda.{1}.obj (Ylb a ha) ⟶ F :=
  uliftYonedaEquiv.symm (σ a ha hF)

theorem e₀_app (W : LevelBase n) (k : W ⟶ Ylb a ha) :
    (e₀ a ha hF).app (op W) (ULift.up k) = F.map k.op (σ a ha hF) := by
  simp [e₀]

theorem e₀_app_comp (i : ι) {W : LevelBase n} (g : W.obj ⟶ (X i).obj) :
    (e₀ a ha hF).app (op W) (ULift.up (homMk (g ≫ ιg a ha i))) = val a i (homMk g) := by
  rw [e₀_app]
  have : (homMk (g ≫ ιg a ha i) : W ⟶ Ylb a ha) = homMk g ≫ jlb a ha i := rfl
  rw [this, op_comp, Functor.map_comp_apply, map_jlb_σ, val_eq]

theorem fac (i : ι) : uliftYoneda.{1}.map (jlb a ha i) ≫ e₀ a ha hF = a i := by
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map, e₀_app, map_jlb_σ]
  rfl

theorem e₀_injective (T : LevelBase n) : Function.Injective ((e₀ a ha hF).app (op T)) := by
  rintro ⟨g⟩ ⟨h⟩ hgh
  change T ⟶ Ylb a ha at g h
  rw [e₀_app, e₀_app] at hgh
  refine congrArg ULift.up (InducedCategory.hom_ext ?_)
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨i, y, hy⟩ : ∃ (i : ι) (y : (X i).obj), ιg a ha i y = g.hom x :=
    (glueData a ha).ι_jointly_surjective (g.hom x)
  obtain ⟨j, z, hz⟩ : ∃ (j : ι) (z : (X j).obj), ιg a ha j z = h.hom x :=
    (glueData a ha).ι_jointly_surjective (h.hom x)
  let U : T.obj.Opens := g.hom ⁻¹ᵁ Vo a ha i ⊓ h.hom ⁻¹ᵁ Vo a ha j
  refine ⟨U, ⟨⟨y, hy⟩, ⟨z, hz⟩⟩, ?_⟩
  have hg : Set.range (U.ι ≫ g.hom) ⊆ Set.range (ιg a ha i) := by
    rintro _ ⟨p, rfl⟩
    exact p.2.1
  have hh : Set.range (U.ι ≫ h.hom) ⊆ Set.range (ιg a ha j) := by
    rintro _ ⟨p, rfl⟩
    exact p.2.2
  obtain ⟨g', hg'⟩ : ∃ g', g' ≫ ιg a ha i = U.ι ≫ g.hom :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hg⟩
  obtain ⟨h', hh'⟩ : ∃ h', h' ≫ ιg a ha j = U.ι ≫ h.hom :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hh⟩
  rw [← hg', ← hh']
  apply comp_ι_eq a ha i j (W := T.ofOpenImmersion U.ι)
  rw [← e₀_app_comp a ha hF, ← e₀_app_comp a ha hF, hg', hh', e₀_app, e₀_app]
  have h₁ : (homMk (U.ι ≫ g.hom) : T.ofOpenImmersion U.ι ⟶ Ylb a ha) =
      (homMk U.ι : T.ofOpenImmersion U.ι ⟶ T) ≫ g := rfl
  have h₂ : (homMk (U.ι ≫ h.hom) : T.ofOpenImmersion U.ι ⟶ Ylb a ha) =
      (homMk U.ι : T.ofOpenImmersion U.ι ⟶ T) ≫ h := rfl
  rw [h₁, h₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hgh]

variable (hcov : IsOpenChartCover a)

include hcov in
theorem e₀_surjective (T : LevelBase n) : Function.Surjective ((e₀ a ha hF).app (op T)) := by
  intro ζ
  choose i U hxU hU using hcov T ζ
  have hmem : ∀ x, ∃ gx : T.ofOpen (U x) ⟶ X (i x),
      val a (i x) gx = F.map (T.openι (U x)).op ζ := by
    intro x
    obtain ⟨⟨gx⟩, hgx⟩ := (hU x (T.ofOpen (U x)) (T.openι (U x))).2 (Scheme.Opens.range_ι (U x)).le
    exact ⟨gx, hgx⟩
  choose g hg using hmem
  let gs : ∀ x, (U x).toScheme ⟶ (X (i x)).obj := fun x => (g x).hom
  let 𝒰 : T.obj.OpenCover :=
    { I₀ := T.obj
      X x := U x
      f x := (U x).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ⟨x, by simpa using hxU x⟩, inferInstance⟩ }
  have hcompat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ gs x ≫ ιg a ha (i x) =
      pullback.snd (𝒰.f x) (𝒰.f y) ≫ gs y ≫ ιg a ha (i y) := by
    intro x y
    rw [← Category.assoc, ← Category.assoc]
    apply comp_ι_eq a ha (i x) (i y)
      (W := T.ofOpenImmersion (pullback.fst (U x).ι (U y).ι ≫ (U x).ι))
    have e₁ : (homMk (pullback.fst (U x).ι (U y).ι ≫ gs x) :
        T.ofOpenImmersion (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) ⟶ X (i x)) =
        (homMk (pullback.fst (U x).ι (U y).ι) :
          T.ofOpenImmersion (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) ⟶ T.ofOpen (U x)) ≫
          g x := rfl
    have e₂ : (homMk (pullback.snd (U x).ι (U y).ι ≫ gs y) :
        T.ofOpenImmersion (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) ⟶ X (i y)) =
        (homMk (pullback.snd (U x).ι (U y).ι) :
          T.ofOpenImmersion (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) ⟶ T.ofOpen (U y)) ≫
          g y := rfl
    rw [e₁, e₂, val_comp, val_comp]
    rw [hg x, hg y, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
    have hc : (homMk (pullback.fst (U x).ι (U y).ι) :
        T.ofOpenImmersion (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) ⟶ T.ofOpen (U x)) ≫
          T.openι (U x) =
        (homMk (pullback.snd (U x).ι (U y).ι) :
          T.ofOpenImmersion (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) ⟶ T.ofOpen (U y)) ≫
          T.openι (U y) := by
      ext1
      exact pullback.condition
    rw [hc]
  refine ⟨ULift.up (homMk (𝒰.glueMorphisms _ hcompat)), ?_⟩
  rw [e₀_app]
  refine IsZariskiSheaf.ext hF T U
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩) fun x => ?_
  rw [← Functor.map_comp_apply, ← op_comp]
  have : T.openι (U x) ≫ homMk (𝒰.glueMorphisms _ hcompat) =
      (homMk (gs x ≫ ιg a ha (i x)) : T.ofOpen (U x) ⟶ Ylb a ha) := by
    ext1
    exact 𝒰.ι_glueMorphisms _ hcompat x
  rw [this, ← e₀_app, e₀_app_comp, ← hg x]
  rfl

include hcov in
theorem isIso_e₀ : IsIso (e₀ a ha hF) := by
  have : ∀ T, IsIso ((e₀ a ha hF).app T) := fun T =>
    (isIso_iff_bijective _).2 ⟨e₀_injective a ha hF T.unop, e₀_surjective a ha hF hcov T.unop⟩
  exact NatIso.isIso_of_isIso_app _

end OpenChartGluing

open OpenChartGluing in
/-- Stacks Project, Lemma 26.15.4 (tag 01JJ), on the level base category. -/
theorem levelBaseOpenChartGluing : LevelBaseOpenChartGluingStatement := by
  intro n F hF ι X a ha hcov
  have := isIso_e₀ a ha hF hcov
  refine ⟨Ylb a ha, asIso (e₀ a ha hF), jlb a ha, fun i => ?_, fun y => ?_, fun i => fac a ha hF i⟩
  · exact inferInstanceAs (IsOpenImmersion (ιg a ha i))
  · obtain ⟨i, x, hx⟩ := (glueData a ha).ι_jointly_surjective y
    exact ⟨i, x, hx⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
