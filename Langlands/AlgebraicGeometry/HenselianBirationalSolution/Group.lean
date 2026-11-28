import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Division

/-! # The group law on the glued scheme

Solve `c e = c` at the closed point of the base. This produces a section `e` on the whole base
because an open neighbourhood of the closed point is the whole base. By associativity, `e` is a
right identity on the image of right translation by `c`. The image is dense, so `e` is a right
identity everywhere. Local right inverses then give the left identity and two-sided inverses.
Uniqueness lets the local inverses glue.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology NeronModelInfra GroupLawOverBase

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}
  [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g]
  [QuasiCompact g] (H : GlueHyp m) [S.IsSeparated] (hL : HasSectionLifts g)

omit [S.IsSeparated] in
/-- The point given by a section of the glued scheme. -/
abbrev unitPt (e : SchemeHomOver (𝟙 S) (toS H)) {T : Scheme.{u}} (t : T ⟶ S) :
    SchemeHomOver t (toS H) := schemeHomOverComp t (Category.comp_id t) e

omit [S.IsSeparated] in
@[simp]
theorem comp_unitPt (e : SchemeHomOver (𝟙 S) (toS H)) {T T' : Scheme.{u}}
    {t : T ⟶ S} {t' : T' ⟶ S} (f : T' ⟶ T) (hf : f ≫ t = t') :
    schemeHomOverComp f hf (unitPt H e t) = unitPt H e t' :=
  Subtype.ext (by simp only [schemeHomOverComp_coe, ← Category.assoc, hf])

omit [IsReduced Y] [Smooth g] [IsSeparated g] [AlgebraicGeometry.IsNoetherian Y] [Surjective g]
  [QuasiCompact g] [S.IsSeparated] in
theorem rightMap_dense (c : Sect g) (hs : IsStrictDomain m) : IsDominant (rightMap m c) := by
  have hr := Scheme.image_preimage_eq_of_isPullback
    (isPullback_sectionPairRight_restrict m c.1 c.2) Set.univ
  rw [Set.preimage_univ, Set.image_univ, Set.image_univ] at hr
  constructor
  rw [DenseRange, hr]
  exact FibreGenerizationDense.dense
    (FibreGenerizationDense.preimage_of_isPullback (isPullback_sectionPairRight c.1 c.2) hs.right_snd)

include hL in
/-- If `c e = c` for a section of `Y`, then `e` is a right identity. -/
theorem mulPts_unit_of_section (c : Sect g) (e : SchemeHomOver (𝟙 S) (toS H))
    (he : mulPts H hL (chartPt H none c) e = chartPt H none c)
    {T : Scheme.{u}} {t : T ⟶ S} (x : SchemeHomOver t (toS H)) :
    mulPts H hL x (unitPt H e t) = x := by
  let u : SchemeHomOver (toS H) (toS H) := ⟨𝟙 _, Category.id_comp _⟩
  let q := (rightDom m c).ι ≫ g
  let a : SchemeHomOver q g := ⟨(rightDom m c).ι, rfl⟩
  let b : SchemeHomOver q g := schemeHomOverComp q (Category.comp_id q) c
  let j : SchemeHomOver q (toS H) := chartPt H none ⟨rightMap m c, rightMap_comp m c⟩
  have hmul : mulPts H hL (chartPt H none a) (chartPt H none b) = j := by
    have ha : 𝟙 _ ≫ (rightDom m c).ι = a.1 := Category.id_comp _
    have hb : ((𝟙 _ ≫ (rightDom m c).ι) ≫ g ≫ c.1) = b.1 := congrArg (· ≫ g ≫ c.1) ha
    have hd : m.Defined a.1 b.1 (a.2.trans b.2.symm) := (rightDom_defined m c (𝟙 _)).of_eq ha hb
    rw [mulPts_in_chart H hL none a b hd]
    apply congrArg (chartPt H none)
    apply Subtype.ext
    calc
      m.mulPt a.1 b.1 _ hd =
          m.mulPt (𝟙 _ ≫ (rightDom m c).ι) ((𝟙 _ ≫ (rightDom m c).ι) ≫ g ≫ c.1)
            _ (rightDom_defined m c (𝟙 _)) := m.mulPt_congr ha.symm hb.symm
      _ = 𝟙 _ ≫ rightMap m c := (rightMap_eq m c (𝟙 _)).symm
      _ = rightMap m c := Category.id_comp _
  have hb : mulPts H hL (chartPt H none b) (unitPt H e q) = chartPt H none b := by
    have hb_chart : schemeHomOverComp q (Category.comp_id q) (chartPt H none c) = chartPt H none b :=
      Subtype.ext (Category.assoc _ _ _).symm
    simpa only [comp_mulPts, hb_chart] using congrArg (schemeHomOverComp q (Category.comp_id q)) he
  have hj : mulPts H hL j (unitPt H e q) = j := by
    rw [← hmul, mulPts_assoc, hb]
  have hu : mulPts H hL u (unitPt H e (toS H)) = u := by
    have : IsDominant (ch H none) := ⟨dense_of_genericPoints_subset (genericPoints_range_ch H)⟩
    have : IsDominant (rightMap m c) := rightMap_dense c H.strict
    have : IsDominant j.1 := inferInstanceAs (IsDominant (rightMap m c ≫ ch H none))
    apply Subtype.ext
    apply ext_of_isDominant j.1
    have huj : schemeHomOverComp j.1 j.2 u = j := Subtype.ext (Category.comp_id _)
    change (schemeHomOverComp j.1 j.2 (mulPts H hL u (unitPt H e (toS H)))).1 =
      (schemeHomOverComp j.1 j.2 u).1
    simpa only [comp_mulPts, comp_unitPt, huj] using congrArg Subtype.val hj
  have hux : schemeHomOverComp x.1 x.2 u = x := Subtype.ext (Category.comp_id _)
  simpa only [comp_mulPts, comp_unitPt, hux] using congrArg (schemeHomOverComp x.1 x.2) hu

include hL in
theorem exists_right_identity (c : Sect g) (s₀ : S) (hs₀ : ∀ s : S, s ⤳ s₀) :
    ∃ e : SchemeHomOver (𝟙 S) (toS H), ∀ {T : Scheme.{u}} {t : T ⟶ S}
      (x : SchemeHomOver t (toS H)), mulPts H hL x (unitPt H e t) = x := by
  let a := chartPt H none c
  obtain ⟨Q, j, hj, z, hs, hz⟩ := exists_local_division H hL a a s₀
  have htop : j.opensRange = ⊤ :=
    eq_top_iff.mpr fun s _ => j.opensRange.isOpen.stableUnderGeneralization (hs₀ s) hs
  have : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j htop
  have hi : inv j ≫ j ≫ 𝟙 S = 𝟙 S := IsIso.inv_hom_id_assoc _ _
  let e := schemeHomOverComp (inv j) hi z
  have ha : schemeHomOverComp (inv j) hi (schemeHomOverComp j rfl a) = a :=
    Subtype.ext (IsIso.inv_hom_id_assoc _ _)
  have he : mulPts H hL a e = a := by
    simpa only [comp_mulPts, ha] using congrArg (schemeHomOverComp (inv j) hi) hz
  exact ⟨e, fun x => mulPts_unit_of_section H hL c e he x⟩

include hL in
/-- Local division supplies a solution on each member of an open cover. -/
theorem division_cover {T : Scheme.{u}} {t : T ⟶ S} (x y : SchemeHomOver t (toS H)) :
    ∃ (U : T.OpenCover.{u}) (z : ∀ i : U.I₀, SchemeHomOver (U.f i ≫ t) (toS H)),
      ∀ i, mulPts H hL (schemeHomOverComp (U.f i) rfl x) (z i) = schemeHomOverComp (U.f i) rfl y := by
  choose Q j hj z hp hz using exists_local_division H hL x y
  let U : T.OpenCover.{u} := {
    I₀ := T
    X := Q
    f := j
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun p => ⟨p, hp p⟩, hj⟩ }
  exact ⟨U, z, hz⟩

omit [S.IsSeparated] in
theorem points_ext_of_cover {T : Scheme.{u}} {t : T ⟶ S} (U : T.OpenCover.{u})
    {x y : SchemeHomOver t (toS H)}
    (h : ∀ i : U.I₀, schemeHomOverComp (U.f i) rfl x = schemeHomOverComp (U.f i) rfl y) :
    x = y :=
  Subtype.ext (U.hom_ext x.1 y.1 fun i => congrArg Subtype.val (h i))

section Inverse

variable (e : SchemeHomOver (𝟙 S) (toS H))
  (he : ∀ {T : Scheme.{u}} {t : T ⟶ S} (x : SchemeHomOver t (toS H)),
    mulPts H hL x (unitPt H e t) = x)

include he in
/-- Given a right inverse `b` of `a`, local right inverses of `b` show that `e a = a` and `b a = e`. -/
theorem left_of_right_inverse {T : Scheme.{u}} {t : T ⟶ S} (a b : SchemeHomOver t (toS H))
    (hab : mulPts H hL a b = unitPt H e t) :
    mulPts H hL (unitPt H e t) a = a ∧ mulPts H hL b a = unitPt H e t := by
  obtain ⟨U, d, hd⟩ := division_cover H hL b (unitPt H e t)
  have h (i : U.I₀) :
      let a' := schemeHomOverComp (U.f i) rfl a
      let b' := schemeHomOverComp (U.f i) rfl b
      let e' := unitPt H e (U.f i ≫ t)
      mulPts H hL e' a' = a' ∧ mulPts H hL b' a' = e' := by
    dsimp only
    let a' := schemeHomOverComp (U.f i) rfl a
    let b' := schemeHomOverComp (U.f i) rfl b
    let e' := unitPt H e (U.f i ≫ t)
    have hab' : mulPts H hL a' b' = e' := by
      simpa only [comp_mulPts, comp_unitPt] using congrArg (schemeHomOverComp (U.f i) rfl) hab
    have hbd' : mulPts H hL b' (d i) = e' := by simpa only [comp_unitPt] using hd i
    have ha : a' = mulPts H hL e' (d i) := by
      rw [← hab', mulPts_assoc, hbd', he]
    change mulPts H hL e' a' = a' ∧ mulPts H hL b' a' = e'
    constructor
    · conv_lhs => rw [ha, ← mulPts_assoc, he]
      exact ha.symm
    · rw [ha, ← mulPts_assoc, he, hbd']
  exact ⟨points_ext_of_cover H U fun i => by simpa only [comp_mulPts, comp_unitPt] using (h i).1,
    points_ext_of_cover H U fun i => by simpa only [comp_mulPts, comp_unitPt] using (h i).2⟩

include he in
theorem unit_mulPts {T : Scheme.{u}} {t : T ⟶ S} (a : SchemeHomOver t (toS H)) :
    mulPts H hL (unitPt H e t) a = a := by
  obtain ⟨U, b, hb⟩ := division_cover H hL a (unitPt H e t)
  apply points_ext_of_cover H U
  intro i
  have hi := (left_of_right_inverse H hL e he (schemeHomOverComp (U.f i) rfl a) (b i)
    (by simpa only [comp_unitPt] using hb i)).1
  simpa only [comp_mulPts, comp_unitPt] using hi

include he in
theorem right_inverse_unique {T : Scheme.{u}} {t : T ⟶ S} {a b b' : SchemeHomOver t (toS H)}
    (hb : mulPts H hL a b = unitPt H e t) (hb' : mulPts H hL a b' = unitPt H e t) :
    b = b' := by
  have h := (left_of_right_inverse H hL e he a b hb).2
  calc b = mulPts H hL b (unitPt H e t) := (he b).symm
    _ = mulPts H hL b (mulPts H hL a b') := by rw [hb']
    _ = mulPts H hL (mulPts H hL b a) b' := (mulPts_assoc H hL _ _ _).symm
    _ = b' := by rw [h, unit_mulPts H hL e he]

include he in
theorem exists_right_inverse {T : Scheme.{u}} {t : T ⟶ S} (a : SchemeHomOver t (toS H)) :
    ∃ b : SchemeHomOver t (toS H), mulPts H hL a b = unitPt H e t := by
  obtain ⟨U, b, hb⟩ := division_cover H hL a (unitPt H e t)
  have compatible (i j : U.I₀) :
      pullback.fst (U.f i) (U.f j) ≫ (b i).1 = pullback.snd (U.f i) (U.f j) ≫ (b j).1 := by
    let l := pullback.fst (U.f i) (U.f j)
    let r := pullback.snd (U.f i) (U.f j)
    let q := l ≫ U.f i ≫ t
    have hq : r ≫ U.f j ≫ t = q := (pullback.condition_assoc _).symm
    let a' := schemeHomOverComp (l ≫ U.f i) (Category.assoc _ _ _ : _ = q) a
    let b₁ := schemeHomOverComp l (rfl : _ = q) (b i)
    let b₂ := schemeHomOverComp r hq (b j)
    have ha₁ : schemeHomOverComp l (rfl : _ = q) (schemeHomOverComp (U.f i) rfl a) = a' :=
      Subtype.ext (Category.assoc _ _ _).symm
    have ha₂ : schemeHomOverComp r hq (schemeHomOverComp (U.f j) rfl a) = a' := by
      apply Subtype.ext
      simp only [schemeHomOverComp_coe, ← Category.assoc, a', l, r, pullback.condition]
    have hb₁ : mulPts H hL a' b₁ = unitPt H e q := by
      simpa only [comp_mulPts, comp_unitPt, ha₁] using
        congrArg (schemeHomOverComp l (rfl : _ = q)) (hb i)
    have hb₂ : mulPts H hL a' b₂ = unitPt H e q := by
      simpa only [comp_mulPts, comp_unitPt, ha₂] using congrArg (schemeHomOverComp r hq) (hb j)
    exact congrArg Subtype.val (right_inverse_unique H hL e he hb₁ hb₂)
  let inv := U.glueMorphisms (fun i => (b i).1) compatible
  have hinv (i : U.I₀) : U.f i ≫ inv = (b i).1 := U.ι_glueMorphisms _ _ i
  have hover : inv ≫ toS H = t := by
    apply U.hom_ext
    intro i
    rw [← Category.assoc, hinv, (b i).2]
  refine ⟨⟨inv, hover⟩, points_ext_of_cover H U ?_⟩
  intro i
  have hi : schemeHomOverComp (U.f i) rfl ⟨inv, hover⟩ = b i := Subtype.ext (hinv i)
  simpa only [comp_mulPts, hi] using hb i

include he in
/-- Multiplication, the identity, and the inverse on points give the relative group law. -/
def relativeGroupLaw : RelativeGroupLaw S (toS H) where
  mul _ := mulPts H hL
  one := unitPt H e
  inv _ x := (exists_right_inverse H hL e he x).choose
  mul_assoc _ := mulPts_assoc H hL
  one_mul _ := unit_mulPts H hL e he
  mul_one _ := he
  inv_mul_cancel _ x := (left_of_right_inverse H hL e he x _
    (exists_right_inverse H hL e he x).choose_spec).2
  mul_natural _ _ := comp_mulPts H hL

end Inverse

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
