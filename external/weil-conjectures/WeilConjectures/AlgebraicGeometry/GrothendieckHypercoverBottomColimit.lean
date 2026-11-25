/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverComparisonCocone
import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverLocalPrimitives
import WeilConjectures.AlgebraicGeometry.GrothendieckInjectiveHypercoverRow
import WeilConjectures.Algebra.Homology.TotalComplexRowResolution
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-! # The colimit of the explicit hypercover comparison maps -/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Preadditive

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

attribute [local instance] FiniteSplitEtaleHypercover.instHasColimitsOfSize

/- The following finite staircase uses the resolution degree as its first index.
Its only geometric input is detection by local primitives; source objects in A
are arbitrary throughout. The bicomplex identities are the categorical versions
of the calculation in WeilConjectures.AlgebraicGeometry.HypercoverBottomRefinement. -/
section Staircase
variable {A}

private noncomputable def staircase (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  ((sectionComplexFunctor A U).mapHomologicalComplex (.up ℕ)).obj I

private noncomputable def staircaseMap {U V : FiniteSplitEtaleHypercover X}
    (f : V.Refinement U) (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    staircase U I ⟶ staircase V I :=
  (NatTrans.mapHomologicalComplex (sectionRefinement A f) (.up ℕ)).app I

private lemma totalπ_naturality
    {K L : HomologicalComplex₂ A (.up ℕ) (.up ℕ)}
    (φ : K ⟶ L) (n p q : ℕ) :
    (HomologicalComplex₂.total.map φ (.up ℕ)).f n ≫ L.totalπ n p q =
      K.totalπ n p q ≫ (φ.f p).f q := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  rw [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ιTotal_totalπ,
    HomologicalComplex₂.ιTotal_totalπ_assoc]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp

private lemma vanishesFrom_map
    {K L : HomologicalComplex₂ A (.up ℕ) (.up ℕ)}
    (φ : K ⟶ L) {B : A} {n : ℕ} (x : B ⟶ (K.total (.up ℕ)).X n)
    {j : ℕ} (hx : K.VanishesFrom x j) :
    L.VanishesFrom (x ≫ (HomologicalComplex₂.total.map φ (.up ℕ)).f n) j := by
  intro p q hp
  rw [Category.assoc, totalπ_naturality, ← Category.assoc, hx p q hp, zero_comp]

private lemma staircase_step
    {K L : HomologicalComplex₂ A (.up ℕ) (.up ℕ)}
    (φ : K ⟶ L) {B : A} {m k : ℕ} (hk : k ≤ m)
    (x : B ⟶ (K.total (.up ℕ)).X (m + 1))
    (hx : K.VanishesFrom x (k + 2))
    (z : B ⟶ (L.X k).X (m - k))
    (hz : z ≫ (L.d k (k + 1)).f (m - k) =
      (x ≫ K.totalπ (m + 1) (k + 1) (m - k)) ≫ (φ.f (k + 1)).f (m - k)) :
    L.VanishesFrom
      (x ≫ (HomologicalComplex₂.total.map φ (.up ℕ)).f (m + 1) -
        (z ≫ L.ιTotal (.up ℕ) k (m - k) m (by change k + (m - k) = m; omega)) ≫
          (L.total (.up ℕ)).d m (m + 1)) (k + 1) := by
  have hx' := vanishesFrom_map φ x hx
  intro p q hp
  rw [sub_comp, Category.assoc, Category.assoc, Category.assoc,
    HomologicalComplex₂.ιTotal_d_totalπ,
    dite_eq_right (show ¬ (k = p ∧ m - k + 1 = q) by omega)]
  simp only [comp_zero, smul_zero, add_zero]
  by_cases hp' : p = k + 1 ∧ m - k = q
  · obtain ⟨rfl, rfl⟩ := hp'
    rw [dite_eq_left ⟨rfl, rfl⟩]
    simp only [HomologicalComplex₂.XXIsoOfEq, eqToIso_refl, Iso.refl_hom,
      Category.comp_id]
    rw [totalπ_naturality, ← Category.assoc, ← hz, sub_self]
  · rw [dite_eq_right (fun h ↦ hp' ⟨h.1.symm, h.2⟩), comp_zero, comp_zero, sub_zero]
    by_cases hp'' : p = k + 1
    · subst hp''
      rw [HomologicalComplex₂.totalπ_eq_zero _ _ _ _ (by omega), comp_zero, comp_zero]
    · simpa only [Category.assoc] using hx' p q (by omega)


private def LocalPrimitives : Prop :=
  ∀ (S : ShortComplex (Sheaf X.smallEtaleTopology A)), S.Exact →
    ∀ (U : FiniteSplitEtaleHypercover X) (n : ℕ) (B T : A)
      (x : B ⟶ S.X₂.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk n)))))
      (_ : x ≫ S.g.hom.app _ = 0) (g : B ⟶ T),
    (∀ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U) (B' : A)
      (π : B' ⟶ B)
      (l : B' ⟶ S.X₁.obj.obj (op (V.simplicial.obj (op (SimplexCategory.mk n))))),
      l ≫ S.f.hom.app _ = π ≫ x ≫ S.X₂.obj.map
        (f.app (op (SimplexCategory.mk n))).op → π ≫ g = 0) → g = 0

omit [IsGrothendieckAbelian A] in
private lemma staircaseMap_id (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    staircaseMap (𝟙 U.simplicial) I = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  change (I.X p).obj.map (𝟙 _) = 𝟙 _
  simp

omit [IsGrothendieckAbelian A] in
private lemma staircaseMap_comp {U V W : FiniteSplitEtaleHypercover X}
    (f : V.Refinement U) (g : W.Refinement V)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    staircaseMap (g ≫ f) I = staircaseMap f I ≫ staircaseMap g I := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  change (I.X p).obj.map (g.app _ ≫ f.app _).op =
    (I.X p).obj.map (f.app _).op ≫ (I.X p).obj.map (g.app _).op
  rw [op_comp, Functor.map_comp]

private lemma total_staircase_id (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    HomologicalComplex₂.total.map (staircaseMap (𝟙 U.simplicial) I) (.up ℕ) = 𝟙 _ := by
  rw [staircaseMap_id, HomologicalComplex₂.total.map_id]

private lemma total_staircase_comp {U V W : FiniteSplitEtaleHypercover X}
    (f : V.Refinement U) (g : W.Refinement V)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    HomologicalComplex₂.total.map (staircaseMap (g ≫ f) I) (.up ℕ) =
      HomologicalComplex₂.total.map (staircaseMap f I) (.up ℕ) ≫
        HomologicalComplex₂.total.map (staircaseMap g I) (.up ℕ) := by
  rw [staircaseMap_comp, HomologicalComplex₂.total.map_comp]


set_option backward.isDefEq.respectTransparency false in
private theorem detect_staircase_one
    (hlocal : LocalPrimitives (X := X) (A := A))
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F)
    (m : ℕ) (U : FiniteSplitEtaleHypercover X) (B : A)
    (x : B ⟶ ((staircase U I.cocomplex).total (.up ℕ)).X (m + 1))
    (hdx : (staircase U I.cocomplex).VanishesFrom
      (x ≫ ((staircase U I.cocomplex).total (.up ℕ)).d (m + 1) (m + 2)) 2)
    (T : A) (g : B ⟶ T)
    (hkill : ∀ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
      (B' : A) (π : B' ⟶ B)
      (w : B' ⟶ ((staircase V I.cocomplex).total (.up ℕ)).X m),
      (staircase V I.cocomplex).VanishesFrom
        (π ≫ x ≫ (HomologicalComplex₂.total.map (staircaseMap f I.cocomplex)
          (.up ℕ)).f (m + 1) -
          w ≫ ((staircase V I.cocomplex).total (.up ℕ)).d m (m + 1)) 1 →
      π ≫ g = 0) : g = 0 := by
  suffices H : ∀ (j : ℕ) (U : FiniteSplitEtaleHypercover X) (B : A)
      (x : B ⟶ ((staircase U I.cocomplex).total (.up ℕ)).X (m + 1)),
      (staircase U I.cocomplex).VanishesFrom
        (x ≫ ((staircase U I.cocomplex).total (.up ℕ)).d (m + 1) (m + 2)) 2 →
      (staircase U I.cocomplex).VanishesFrom x (j + 1) →
      ∀ (T : A) (g : B ⟶ T),
      (∀ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
        (B' : A) (π : B' ⟶ B)
        (w : B' ⟶ ((staircase V I.cocomplex).total (.up ℕ)).X m),
        (staircase V I.cocomplex).VanishesFrom
          (π ≫ x ≫ (HomologicalComplex₂.total.map (staircaseMap f I.cocomplex)
            (.up ℕ)).f (m + 1) -
            w ≫ ((staircase V I.cocomplex).total (.up ℕ)).d m (m + 1)) 1 →
        π ≫ g = 0) → g = 0 from
    H (m + 1) U B x hdx
      (HomologicalComplex₂.vanishesFrom_of_lt x _ (by omega)) T g hkill
  intro j
  induction j with
  | zero =>
      intro U B x _ hx T g hkill
      have h := hkill U (𝟙 U.simplicial) B (𝟙 B) 0 (by
        simpa only [total_staircase_id, HomologicalComplex.id_f, Category.comp_id,
          Category.id_comp, zero_comp, sub_zero] using hx)
      simpa only [Category.id_comp] using h
  | succ j ih =>
      intro U B x hdx hx T g hkill
      by_cases hj : j ≤ m
      · let K := staircase U I.cocomplex
        have hd : (x ≫ K.totalπ (m + 1) (j + 1) (m - j)) ≫
            (K.d (j + 1) (j + 2)).f (m - j) = 0 := by
          have hh := hdx (j + 2) (m - j) (by omega)
          change (x ≫ (K.total (.up ℕ)).d (m + 1) (m + 2)) ≫
            K.totalπ (m + 2) (j + 2) (m - j) = 0 at hh
          rw [Category.assoc, K.comp_d_totalπ_succ x (j + 1) (m - j)
            (fun q' ↦ hx _ _ le_rfl)] at hh
          exact hh
        let S := ShortComplex.mk (I.cocomplex.d j (j + 1))
          (I.cocomplex.d (j + 1) (j + 2)) (I.cocomplex.d_comp_d j (j + 1) (j + 2))
        apply hlocal S (I.exact_succ j) U (m - j) B T
          (x ≫ K.totalπ (m + 1) (j + 1) (m - j)) hd g
        intro V f B' π z hz
        let L := staircase V I.cocomplex
        let τ := HomologicalComplex₂.total.map (staircaseMap f I.cocomplex) (.up ℕ)
        let w₁ := z ≫ L.ιTotal (.up ℕ) j (m - j) m (by simp; omega)
        let y := π ≫ x ≫ τ.f (m + 1) - w₁ ≫ (L.total (.up ℕ)).d m (m + 1)
        have hy : L.VanishesFrom y (j + 1) := by
          have hh := staircase_step (staircaseMap f I.cocomplex) hj (π ≫ x)
            (K.vanishesFrom_comp π hx) z (by
              change z ≫ S.f.hom.app _ = ((π ≫ x) ≫
                K.totalπ (m + 1) (j + 1) (m - j)) ≫
                  S.X₂.obj.map (f.app (op (SimplexCategory.mk (m - j)))).op
              simpa only [Category.assoc] using hz)
          simpa only [y, w₁, Category.assoc] using hh
        have hdy : L.VanishesFrom
            (y ≫ (L.total (.up ℕ)).d (m + 1) (m + 2)) 2 := by
          have hh := vanishesFrom_map (staircaseMap f I.cocomplex)
            (x ≫ (K.total (.up ℕ)).d (m + 1) (m + 2)) hdx
          have hh' := L.vanishesFrom_comp π hh
          convert hh' using 1
          simp only [y, sub_comp, Category.assoc, HomologicalComplex.d_comp_d,
            comp_zero, sub_zero]
          rw [τ.comm (m + 1) (m + 2)]
        apply ih V B' y hdy hy T (π ≫ g)
        intro W f' B'' ρ w₂ hw₂
        let σ := HomologicalComplex₂.total.map (staircaseMap f' I.cocomplex) (.up ℕ)
        have h := hkill W (f' ≫ f) B'' (ρ ≫ π) (ρ ≫ w₁ ≫ σ.f m + w₂) (by
          convert hw₂ using 1
          simp only [total_staircase_comp, HomologicalComplex.comp_f, add_comp,
            sub_comp, y, Category.assoc]
          rw [← σ.comm m (m + 1)]
          simp only [comp_sub]
          dsimp only [τ, σ]
          abel)
        simpa only [Category.assoc] using h
      · exact ih U B x hdx
          (HomologicalComplex₂.vanishesFrom_of_lt x _ (by omega)) T g hkill

private noncomputable def staircaseAugmentation
    {F : Sheaf X.smallEtaleTopology A}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) :
    (sectionComplexFunctor A U).obj F ⟶ (staircase U I.cocomplex).X 0 :=
  (sectionComplexFunctor A U).map (I.ι.f 0)

private lemma staircaseAugmentation_d
    {F : Sheaf X.smallEtaleTopology A}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) :
    staircaseAugmentation I U ≫ (staircase U I.cocomplex).d 0 1 = 0 := by
  change (sectionComplexFunctor A U).map (I.ι.f 0) ≫
    (sectionComplexFunctor A U).map (I.cocomplex.d 0 1) = 0
  rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero]

private noncomputable def staircaseBottom
    {F : Sheaf X.smallEtaleTopology A}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) :
    (sectionComplexFunctor A U).obj F ⟶ (staircase U I.cocomplex).total (.up ℕ) :=
  (staircase U I.cocomplex).toTotalOfAugmentation
    (staircaseAugmentation I U) (staircaseAugmentation_d I U)

private lemma staircaseAugmentation_mono
    {F : Sheaf X.smallEtaleTopology A}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) (q : ℕ) :
    Mono ((staircaseAugmentation I U).f q) := by
  let ev : Sheaf X.smallEtaleTopology A ⥤ A :=
    sheafToPresheaf _ _ ⋙
      (evaluation _ _).obj (op (U.simplicial.obj (op (SimplexCategory.mk q))))
  change Mono (ev.map (I.ι.f 0))
  infer_instance

private lemma staircaseBottom_mono
    {F : Sheaf X.smallEtaleTopology A}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) (q : ℕ) :
    Mono ((staircaseBottom I U).f q) := by
  have : Mono ((staircaseBottom I U).f q ≫
      (staircase U I.cocomplex).totalπ q 0 q) := by
    change Mono (((staircase U I.cocomplex).toTotalOfAugmentation _ _).f q ≫ _)
    rw [HomologicalComplex₂.toTotalOfAugmentation_f_totalπ_zero]
    exact staircaseAugmentation_mono I U q
  exact mono_of_mono ((staircaseBottom I U).f q)
    ((staircase U I.cocomplex).totalπ q 0 q)

set_option backward.isDefEq.respectTransparency false in
private theorem staircase_lift_bottom
    {F : Sheaf X.smallEtaleTopology A}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) {B : A} {m : ℕ}
    (x : B ⟶ ((staircase U I.cocomplex).total (.up ℕ)).X m)
    (hx : (staircase U I.cocomplex).VanishesFrom x 1)
    (hdx : x ≫ ((staircase U I.cocomplex).total (.up ℕ)).d m (m + 1) ≫
      (staircase U I.cocomplex).totalπ (m + 1) 1 m = 0) :
    ∃ l : B ⟶ ((sectionComplexFunctor A U).obj F).X m,
      x = l ≫ (staircaseBottom I U).f m := by
  let K := staircase U I.cocomplex
  have hd : (x ≫ K.totalπ m 0 m) ≫ (K.d 0 1).f m = 0 := by
    simpa only [HomologicalComplex₂.comp_d_totalπ_succ x 0 m
      (fun q' ↦ hx _ _ le_rfl)] using hdx
  let ev : Sheaf X.smallEtaleTopology A ⥤ A :=
    sheafToPresheaf _ _ ⋙
      (evaluation _ _).obj (op (U.simplicial.obj (op (SimplexCategory.mk m))))
  have hker := isLimitForkMapOfIsLimit' ev I.ι_f_zero_comp_complex_d I.isLimitKernelFork
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hker (x ≫ K.totalπ m 0 m) hd
  refine ⟨l, ?_⟩
  rw [HomologicalComplex₂.eq_totalπ_ιTotal_of_vanishesFrom_one hx]
  change (x ≫ K.totalπ m 0 m) ≫ _ =
    l ≫ (staircaseAugmentation I U).f m ≫ _
  have hl' : l ≫ (staircaseAugmentation I U).f m = x ≫ K.totalπ m 0 m := hl
  rw [← Category.assoc, hl']


private theorem detect_staircase_cochain
    (hlocal : LocalPrimitives (X := X) (A := A))
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F)
    (m : ℕ) (U : FiniteSplitEtaleHypercover X) (B : A)
    (x : B ⟶ ((staircase U I.cocomplex).total (.up ℕ)).X (m + 1))
    (hdx : (staircase U I.cocomplex).VanishesFrom
      (x ≫ ((staircase U I.cocomplex).total (.up ℕ)).d (m + 1) (m + 2)) 1)
    (T : A) (g : B ⟶ T)
    (hkill : ∀ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
      (B' : A) (π : B' ⟶ B)
      (l : B' ⟶ ((sectionComplexFunctor A V).obj F).X (m + 1))
      (w : B' ⟶ ((staircase V I.cocomplex).total (.up ℕ)).X m),
      π ≫ x ≫ (HomologicalComplex₂.total.map (staircaseMap f I.cocomplex)
          (.up ℕ)).f (m + 1) = l ≫ (staircaseBottom I V).f (m + 1) +
          w ≫ ((staircase V I.cocomplex).total (.up ℕ)).d m (m + 1) →
      π ≫ g = 0) : g = 0 := by
  apply detect_staircase_one hlocal I m U B x
    (fun p q hp ↦ hdx p q (by omega)) T g
  intro V f B' π w hw
  let L := staircase V I.cocomplex
  let τ := HomologicalComplex₂.total.map (staircaseMap f I.cocomplex) (.up ℕ)
  let y := π ≫ x ≫ τ.f (m + 1) - w ≫ (L.total (.up ℕ)).d m (m + 1)
  have hd : y ≫ (L.total (.up ℕ)).d (m + 1) (m + 2) ≫
      L.totalπ (m + 2) 1 (m + 1) = 0 := by
    have hh := vanishesFrom_map (staircaseMap f I.cocomplex)
      (x ≫ ((staircase U I.cocomplex).total (.up ℕ)).d (m + 1) (m + 2)) hdx
    have he : y ≫ (L.total (.up ℕ)).d (m + 1) (m + 2) =
        π ≫ (x ≫ ((staircase U I.cocomplex).total (.up ℕ)).d (m + 1) (m + 2)) ≫
          τ.f (m + 2) := by
      simp only [y, sub_comp, Category.assoc, HomologicalComplex.d_comp_d,
        comp_zero, sub_zero]
      rw [τ.comm (m + 1) (m + 2)]
    rw [← Category.assoc, he, Category.assoc]
    rw [hh 1 (m + 1) le_rfl, comp_zero]
  obtain ⟨l, hl⟩ := staircase_lift_bottom I V y hw hd
  exact hkill V f B' π l w (sub_eq_iff_eq_add.mp hl)

private noncomputable def cycleClass {K : CochainComplex A ℕ} {B : A} {n : ℕ}
    (x : B ⟶ K.X n) (hx : x ≫ K.d n (n + 1) = 0) : B ⟶ K.homology n :=
  K.liftCycles x (n + 1) (by simp) hx ≫ K.homologyπ n

omit [IsGrothendieckAbelian A] in
private theorem cycleClass_precomp {K : CochainComplex A ℕ} {B B' : A} {n : ℕ}
    (π : B' ⟶ B) (x : B ⟶ K.X n) (hx : x ≫ K.d n (n + 1) = 0) :
    cycleClass (π ≫ x) (by rw [Category.assoc, hx, comp_zero]) =
      π ≫ cycleClass x hx := by
  have h : K.liftCycles (π ≫ x) (n + 1) (by simp)
      (by rw [Category.assoc, hx, comp_zero]) =
      π ≫ K.liftCycles x (n + 1) (by simp) hx := by
    apply (cancel_mono (K.iCycles n)).mp
    simp only [Category.assoc, HomologicalComplex.liftCycles_i]
  simpa only [cycleClass, Category.assoc] using
    congrArg (fun z ↦ z ≫ K.homologyπ n) h

omit [IsGrothendieckAbelian A] in
private theorem cycleClass_naturality {K L : CochainComplex A ℕ} {B : A} {n : ℕ}
    (φ : K ⟶ L) (x : B ⟶ K.X n) (hx : x ≫ K.d n (n + 1) = 0) :
    cycleClass (x ≫ φ.f n) (by rw [Category.assoc, φ.comm, ← Category.assoc,
      hx, zero_comp]) = cycleClass x hx ≫ HomologicalComplex.homologyMap φ n := by
  have h := K.liftCycles_comp_cyclesMap x (n + 1) (by simp) hx φ
  simpa only [cycleClass, Category.assoc, HomologicalComplex.homologyπ_naturality] using
    congrArg (fun z ↦ z ≫ L.homologyπ n) h.symm

omit [IsGrothendieckAbelian A] in
private theorem cycleClass_sub_boundary {K : CochainComplex A ℕ} {B : A} {m : ℕ}
    (x : B ⟶ K.X (m + 1)) (hx : x ≫ K.d (m + 1) (m + 2) = 0)
    (w : B ⟶ K.X m) :
    cycleClass (x - w ≫ K.d m (m + 1)) (by
      rw [sub_comp, Category.assoc, HomologicalComplex.d_comp_d, comp_zero, hx, sub_self]) =
      cycleClass x hx := by
  apply (K.liftCycles_comp_homologyπ_eq_iff_up_to_refinements m (m + 1) (m + 2)
    (by simp) (by simp) _ _ _ _).2
  refine ⟨B, 𝟙 B, inferInstance, -w, ?_⟩
  simp only [Category.id_comp, neg_comp]
  abel


private theorem class_zero_of_bottom_zero
    (hlocal : LocalPrimitives (X := X) (A := A))
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) (m : ℕ)
    (T : A)
    (r : ∀ U : FiniteSplitEtaleHypercover X,
      ((staircase U I.cocomplex).total (.up ℕ)).homology (m + 1) ⟶ T)
    (hr : ∀ (U V : FiniteSplitEtaleHypercover X) (f : V.Refinement U),
      HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map (staircaseMap f I.cocomplex) (.up ℕ)) (m + 1) ≫
        r V = r U)
    (hbottom : ∀ U : FiniteSplitEtaleHypercover X,
      HomologicalComplex.homologyMap (staircaseBottom I U) (m + 1) ≫ r U = 0)
    (U : FiniteSplitEtaleHypercover X) (B : A)
    (x : B ⟶ ((staircase U I.cocomplex).total (.up ℕ)).X (m + 1))
    (hx : x ≫ ((staircase U I.cocomplex).total (.up ℕ)).d (m + 1) (m + 2) = 0) :
    cycleClass x hx ≫ r U = 0 := by
  apply detect_staircase_cochain hlocal I m U B x
    (fun p q _ ↦ by rw [hx, zero_comp]) T (cycleClass x hx ≫ r U)
  intro V f B' π l w he
  let K := (staircase U I.cocomplex).total (.up ℕ)
  let L := (staircase V I.cocomplex).total (.up ℕ)
  let τ := HomologicalComplex₂.total.map (staircaseMap f I.cocomplex) (.up ℕ)
  let ε := staircaseBottom I V
  have hz : (π ≫ x ≫ τ.f (m + 1)) ≫ L.d (m + 1) (m + 2) = 0 := by
    calc
      _ = π ≫ (x ≫ K.d (m + 1) (m + 2)) ≫ τ.f (m + 2) := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ π ≫ x ≫ z) (τ.comm (m + 1) (m + 2))
      _ = 0 := by
        have hxK : x ≫ K.d (m + 1) (m + 2) = 0 := hx
        rw [hxK, zero_comp, comp_zero]
  have hsub : π ≫ x ≫ τ.f (m + 1) - w ≫ L.d m (m + 1) = l ≫ ε.f (m + 1) :=
    sub_eq_iff_eq_add.mpr he
  have hlz : (l ≫ ε.f (m + 1)) ≫ L.d (m + 1) (m + 2) = 0 := by
    rw [← hsub]
    simpa only [sub_comp, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
      sub_zero] using hz
  have hl : l ≫ ((sectionComplexFunctor A V).obj F).d (m + 1) (m + 2) = 0 := by
    have : Mono (ε.f (m + 2)) := staircaseBottom_mono I V (m + 2)
    apply (cancel_mono (ε.f (m + 2))).mp
    calc
      _ = (l ≫ ε.f (m + 1)) ≫ L.d (m + 1) (m + 2) := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ l ≫ z) (ε.comm (m + 1) (m + 2)).symm
      _ = 0 := hlz
      _ = 0 ≫ ε.f (m + 2) := by simp
  have hc := cycleClass_sub_boundary (π ≫ x ≫ τ.f (m + 1)) hz w
  have hc' : cycleClass (l ≫ ε.f (m + 1)) hlz =
      cycleClass (π ≫ x ≫ τ.f (m + 1)) hz := by
    change cycleClass (π ≫ x ≫ τ.f (m + 1) - w ≫ L.d m (m + 1)) _ = _ at hc
    simpa only [hsub] using hc
  calc
    π ≫ (cycleClass x hx ≫ r U) =
        cycleClass (π ≫ x ≫ τ.f (m + 1)) hz ≫ r V := by
      have hn := cycleClass_naturality τ (π ≫ x)
        (by rw [Category.assoc, hx, comp_zero])
      have hp := cycleClass_precomp π x hx
      calc
        _ = (π ≫ cycleClass x hx) ≫
            HomologicalComplex.homologyMap τ (m + 1) ≫ r V := by
          rw [Category.assoc, hr U V f]
        _ = _ := by
          rw [← hp]
          simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ r V) hn.symm
    _ = cycleClass (l ≫ ε.f (m + 1)) hlz ≫ r V := by rw [hc']
    _ = cycleClass l hl ≫
        HomologicalComplex.homologyMap (staircaseBottom I V) (m + 1) ≫ r V := by
      rw [cycleClass_naturality]
      exact Category.assoc _ _ _
    _ = 0 := by rw [hbottom V, comp_zero]

private noncomputable def staircaseFlipIso (U : FiniteSplitEtaleHypercover X)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    (staircase U I).total (.up ℕ) ≅
      (resolutionDoubleComplex A U I).total (.up ℕ) := by
  unfold resolutionDoubleComplex
  exact ((staircase U I).totalFlipIso (.up ℕ)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma staircaseBottom_flip
    {F : Sheaf X.smallEtaleTopology A}
    (I : InjectiveResolution F) (U : FiniteSplitEtaleHypercover X) :
    staircaseBottom I U ≫ (staircaseFlipIso U I.cocomplex).hom =
      bottomInclusion A U I := by
  unfold staircaseBottom staircaseFlipIso bottomInclusion resolutionDoubleComplex
  apply HomologicalComplex.hom_ext
  intro n
  dsimp only [id, Iso.symm_hom]
  simp only [HomologicalComplex.comp_f, HomologicalComplex₂.toTotalOfAugmentation,
    Category.assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_inv]
  have hs : ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) 0 n = 1 := by
    change (-1 : ℤˣ) ^ (0 * n) = 1
    simp
  rw [hs, one_smul]
  rfl

private lemma totalFlipIso_inv_naturality
    {K L : HomologicalComplex₂ A (.up ℕ) (.up ℕ)}
    (φ : K ⟶ L) :
    HomologicalComplex₂.total.map φ (.up ℕ) ≫ (L.totalFlipIso (.up ℕ)).inv =
      (K.totalFlipIso (.up ℕ)).inv ≫ HomologicalComplex₂.total.map
        ((HomologicalComplex₂.flipFunctor _ _ _).map φ) (.up ℕ) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_inv_assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_inv,
    Linear.comp_units_smul, Linear.units_smul_comp,
    HomologicalComplex₂.ιTotal_map]
  rfl

private lemma staircaseFlipIso_refinement
    {U V : FiniteSplitEtaleHypercover X} (f : V.Refinement U)
    (I : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ) :
    HomologicalComplex₂.total.map (staircaseMap f I) (.up ℕ) ≫
        (staircaseFlipIso V I).hom =
      (staircaseFlipIso U I).hom ≫ totalRefinement A f I := by
  unfold staircaseFlipIso totalRefinement resolutionDoubleComplex
  exact totalFlipIso_inv_naturality (staircaseMap f I)


private lemma topQuasiIso (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) :
    QuasiIso (resolutionAugmentation A U I.cocomplex) := by
  apply resolutionAugmentation_quasiIso A _ U I
  intro V G hG
  have := hG
  exact injective_row_quasiIso A V G

private noncomputable def staircaseComparison (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) (q : ℕ) :
    ((staircase U I.cocomplex).total (.up ℕ)).homology q ⟶
      ((terminalSections A).rightDerived q).obj F := by
  have := topQuasiIso U I
  exact HomologicalComplex.homologyMap (staircaseFlipIso U I.cocomplex).hom q ≫
    totalComparisonAt A U I q

private lemma staircaseComparison_isIso (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) (q : ℕ) :
    IsIso (staircaseComparison U I q) := by
  have := topQuasiIso U I
  unfold staircaseComparison
  infer_instance

private lemma staircaseComparison_refinement {U V : FiniteSplitEtaleHypercover X}
    (f : V.Refinement U) {F : Sheaf X.smallEtaleTopology A}
    (I : InjectiveResolution F) (q : ℕ) :
    HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map (staircaseMap f I.cocomplex) (.up ℕ)) q ≫
      staircaseComparison V I q = staircaseComparison U I q := by
  have := topQuasiIso U I
  have := topQuasiIso V I
  unfold staircaseComparison
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    staircaseFlipIso_refinement, HomologicalComplex.homologyMap_comp,
    Category.assoc, totalComparisonAt_refinement]

private lemma staircaseComparison_bottom (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology A) (q : ℕ) :
    HomologicalComplex.homologyMap (staircaseBottom (injectiveResolution F) U) q ≫
      staircaseComparison U (injectiveResolution F) q = (canonicalComparison A U q).app F := by
  unfold staircaseComparison
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, staircaseBottom_flip]
  rfl

omit [IsGrothendieckAbelian A] in
private lemma cycleClass_iCycles {K : CochainComplex A ℕ} (n : ℕ) :
    cycleClass (K.iCycles n) (K.iCycles_d n (n + 1)) = K.homologyπ n := by
  have h : K.liftCycles (K.iCycles n) (n + 1) (by simp)
      (K.iCycles_d n (n + 1)) = 𝟙 _ := by
    apply (cancel_mono (K.iCycles n)).mp
    simp only [HomologicalComplex.liftCycles_i, Category.id_comp]
  simp only [cycleClass, h, Category.id_comp]

private theorem comparison_images
    (hlocal : LocalPrimitives (X := X) (A := A))
    (F : Sheaf X.smallEtaleTopology A) (m : ℕ) :
    (⨆ U : HomotopyIndex X, imageSubobject ((comparisonCocone A F (m + 1)).ι.app U)) =
      ⊤ := by
  classical
  let I := injectiveResolution F
  let M : Subobject (((terminalSections A).rightDerived (m + 1)).obj F) :=
    ⨆ U : HomotopyIndex X, imageSubobject ((comparisonCocone A F (m + 1)).ι.app U)
  let b := cokernel.π M.arrow
  have hb (U : FiniteSplitEtaleHypercover X) : (canonicalComparison A U (m + 1)).app F ≫
      b = 0 := by
    have hle : imageSubobject ((comparisonCocone A F (m + 1)).ι.app ⟨op U⟩) ≤ M :=
      le_iSup (fun V : HomotopyIndex X ↦
        imageSubobject ((comparisonCocone A F (m + 1)).ι.app V)) ⟨op U⟩
    change (comparisonCocone A F (m + 1)).ι.app ⟨op U⟩ ≫ b = 0
    rw [← imageSubobject_arrow_comp ((comparisonCocone A F (m + 1)).ι.app ⟨op U⟩),
      ← Subobject.ofLE_arrow hle]
    simp only [Category.assoc, b, cokernel.condition, comp_zero]
  let r (U : FiniteSplitEtaleHypercover X) := staircaseComparison U I (m + 1) ≫ b
  have hr (U V : FiniteSplitEtaleHypercover X) (f : V.Refinement U) :
      HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map (staircaseMap f I.cocomplex) (.up ℕ)) (m + 1) ≫
        r V = r U := by
    dsimp only [r]
    rw [← Category.assoc, staircaseComparison_refinement]
  have hbottom (U : FiniteSplitEtaleHypercover X) :
      HomologicalComplex.homologyMap (staircaseBottom I U) (m + 1) ≫ r U = 0 := by
    dsimp only [r, I]
    rw [← Category.assoc, staircaseComparison_bottom, hb]
  let U : FiniteSplitEtaleHypercover X :=
    (Classical.choice (IsFiltered.nonempty (C := HomotopyIndex X))).as.unop
  let K := (staircase U I.cocomplex).total (.up ℕ)
  have h := class_zero_of_bottom_zero hlocal I m _ r hr hbottom U (K.cycles (m + 1))
    (K.iCycles (m + 1)) (K.iCycles_d (m + 1) (m + 2))
  rw [cycleClass_iCycles] at h
  have := staircaseComparison_isIso U I (m + 1)
  have hz : r U = 0 := (cancel_epi (K.homologyπ (m + 1))).mp (by simpa using h)
  have hz' : b = 0 := (cancel_epi (staircaseComparison U I (m + 1))).mp (by
    simpa only [comp_zero] using hz)
  have : Epi M.arrow := Abelian.epi_of_cokernel_π_eq_zero _ hz'
  simpa only [Subobject.mk_arrow] using (Subobject.epi_iff_mk_eq_top M.arrow).mp this
private lemma staircaseBottom_refinement
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F)
    {U V : FiniteSplitEtaleHypercover X} (f : V.Refinement U) :
    staircaseBottom I U ≫
        HomologicalComplex₂.total.map (staircaseMap f I.cocomplex) (.up ℕ) =
      (sectionRefinement A f).app F ≫ staircaseBottom I V := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, staircaseBottom,
    HomologicalComplex₂.toTotalOfAugmentation, Category.assoc,
    HomologicalComplex₂.ιTotal_map]
  have h := congrArg (fun g ↦ g ≫
    (staircase V I.cocomplex).ιTotal (.up ℕ) 0 n n (by simp))
    ((I.ι.f 0).hom.naturality (f.app (op (SimplexCategory.mk n))).op)
  simp only [Category.assoc] at h
  convert h.symm using 1 <;> rfl


set_option backward.isDefEq.respectTransparency false in
private theorem detect_bottom_kernel
    (hlocal : LocalPrimitives (X := X) (A := A))
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) (m : ℕ)
    (U : FiniteSplitEtaleHypercover X) (B : A)
    (x : B ⟶ ((sectionComplexFunctor A U).obj F).X (m + 2))
    (hx : x ≫ ((sectionComplexFunctor A U).obj F).d (m + 2) (m + 3) = 0)
    (hzero : cycleClass x hx ≫
      HomologicalComplex.homologyMap (staircaseBottom I U) (m + 2) = 0)
    (T : A) (g : B ⟶ T)
    (hkill : ∀ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U)
      (B' : A) (π : B' ⟶ B),
      π ≫ cycleClass x hx ≫ (cohomologyRefinement A f (m + 2)).app F = 0 → π ≫ g = 0) :
    g = 0 := by
  let C := (sectionComplexFunctor A U).obj F
  let K := (staircase U I.cocomplex).total (.up ℕ)
  let ε := staircaseBottom I U
  have hxε : (x ≫ ε.f (m + 2)) ≫ K.d (m + 2) (m + 3) = 0 := by
    calc
      _ = (x ≫ C.d (m + 2) (m + 3)) ≫ ε.f (m + 3) := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ x ≫ z) (ε.comm (m + 2) (m + 3))
      _ = 0 := by rw [show x ≫ C.d (m + 2) (m + 3) = 0 from hx, zero_comp]
  have hc : cycleClass (x ≫ ε.f (m + 2)) hxε = 0 := by
    rw [cycleClass_naturality]
    exact hzero
  obtain ⟨B₁, π, hπ, y, hy⟩ :=
    (K.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
      (m + 1) (m + 2) (m + 3) (by simp) (by simp) _ hxε).mp hc
  have := hπ
  apply (cancel_epi π).mp
  simp only [comp_zero]
  have hdy : (staircase U I.cocomplex).VanishesFrom
      (y ≫ K.d (m + 1) (m + 2)) 1 := by
    rw [← hy]
    simpa only [ε, staircaseBottom, Category.assoc] using
      (staircase U I.cocomplex).vanishesFrom_toTotalOfAugmentation
        (staircaseAugmentation I U) (staircaseAugmentation_d I U) (π ≫ x)
  apply detect_staircase_cochain hlocal I m U B₁ y hdy T (π ≫ g)
  intro V f B' ρ l w he
  let D := (sectionComplexFunctor A V).obj F
  let L := (staircase V I.cocomplex).total (.up ℕ)
  let τ := HomologicalComplex₂.total.map (staircaseMap f I.cocomplex) (.up ℕ)
  let δ := staircaseBottom I V
  let α := (sectionRefinement A f).app F
  have hnat : ε.f (m + 2) ≫ τ.f (m + 2) = α.f (m + 2) ≫ δ.f (m + 2) :=
    congrArg (fun z ↦ z.f (m + 2)) (staircaseBottom_refinement I f)
  have hd : (ρ ≫ π) ≫ x ≫ α.f (m + 2) = l ≫ D.d (m + 1) (m + 2) := by
    have := staircaseBottom_mono I V (m + 2)
    apply (cancel_mono (δ.f (m + 2))).mp
    calc
      _ = ρ ≫ (π ≫ x ≫ ε.f (m + 2)) ≫ τ.f (m + 2) := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ ρ ≫ π ≫ x ≫ z) hnat.symm
      _ = (ρ ≫ y ≫ τ.f (m + 1)) ≫ L.d (m + 1) (m + 2) := by
        rw [hy]
        simpa only [Category.assoc] using
          congrArg (fun z ↦ ρ ≫ y ≫ z) (τ.comm (m + 1) (m + 2)).symm
      _ = (l ≫ D.d (m + 1) (m + 2)) ≫ δ.f (m + 2) := by
        have he' : ρ ≫ y ≫ τ.f (m + 1) =
            l ≫ δ.f (m + 1) + w ≫ L.d m (m + 1) := he
        rw [he']
        simp only [add_comp, Category.assoc, HomologicalComplex.d_comp_d,
          comp_zero, add_zero]
        simpa only [Category.assoc] using
          congrArg (fun z ↦ l ≫ z) (δ.comm (m + 1) (m + 2))
  have hclass : (ρ ≫ π) ≫ cycleClass x hx ≫
      (cohomologyRefinement A f (m + 2)).app F = 0 := by
    change (ρ ≫ π) ≫ cycleClass x hx ≫
      HomologicalComplex.homologyMap α (m + 2) = 0
    rw [← Category.assoc, ← cycleClass_precomp, ← cycleClass_naturality]
    simpa only [cycleClass, Category.assoc] using
      D.liftCycles_homologyπ_eq_zero_of_boundary _ (m + 3) (by simp) l hd
  simpa only [Category.assoc] using hkill V f B' (ρ ≫ π) hclass

private theorem comparison_kernels
    (hlocal : LocalPrimitives (X := X) (A := A))
    (F : Sheaf X.smallEtaleTopology A) (m : ℕ) (U : HomotopyIndex X) :
    kernelSubobject ((comparisonCocone A F (m + 2)).ι.app U) ≤
      ⨆ (V : HomotopyIndex X) (f : U ⟶ V),
        kernelSubobject ((homotopyCohomologyDiagram A F (m + 2)).map f) := by
  classical
  let I := injectiveResolution F
  let C := (sectionComplexFunctor A U.as.unop).obj F
  let D := homotopyCohomologyDiagram A F (m + 2)
  let c := (comparisonCocone A F (m + 2)).ι.app U
  let M := kernelSubobject c
  let N : Subobject (D.obj U) := ⨆ (V : HomotopyIndex X) (f : U ⟶ V),
    kernelSubobject (D.map f)
  let b := cokernel.π N.arrow
  suffices hz : M.arrow ≫ b = 0 from
    Subobject.le_of_comm (Abelian.monoLift N.arrow M.arrow hz)
      (Abelian.monoLift_comp N.arrow M.arrow hz)
  obtain ⟨B, π, hπ, x, hx, he⟩ :=
    C.eq_liftCycles_homologyπ_up_to_refinements M.arrow (m + 3) (by simp)
  have := hπ
  have he' : π ≫ M.arrow = cycleClass x hx := he
  apply (cancel_epi π).mp
  simp only [comp_zero]
  rw [← Category.assoc, he']
  have hzero : cycleClass x hx ≫
      HomologicalComplex.homologyMap (staircaseBottom I U.as.unop) (m + 2) = 0 := by
    have := staircaseComparison_isIso U.as.unop I (m + 2)
    apply (cancel_mono (staircaseComparison U.as.unop I (m + 2))).mp
    rw [Category.assoc, staircaseComparison_bottom, ← he', Category.assoc]
    change π ≫ M.arrow ≫ c = 0 ≫ _
    simp only [M, kernelSubobject_arrow_comp, comp_zero, zero_comp]
  apply detect_bottom_kernel hlocal I m U.as.unop B x hx hzero _ (cycleClass x hx ≫ b)
  intro V f B' ρ hzero'
  let f' : (show Index X from V) ⟶ (show Index X from U.as.unop) := ⟨f⟩
  let fq : U ⟶ (⟨op V⟩ : HomotopyIndex X) :=
    (CategoryTheory.Quotient.functor _).map f'.op
  have hz : (ρ ≫ cycleClass x hx) ≫ D.map fq = 0 := by
    change (ρ ≫ cycleClass x hx) ≫ (cohomologyRefinement A f (m + 2)).app F = 0
    simpa only [Category.assoc] using hzero'
  have hle : kernelSubobject (D.map fq) ≤ N :=
    le_iSup_of_le (⟨op V⟩ : HomotopyIndex X)
      (le_iSup (fun f : U ⟶ (⟨op V⟩ : HomotopyIndex X) ↦ kernelSubobject (D.map f)) fq)
  have hk : kernel.ι (D.map fq) ≫ b = 0 := by
    rw [← kernelSubobject_arrow', Category.assoc, ← Subobject.ofLE_arrow hle]
    simp only [Category.assoc, b, cokernel.condition, comp_zero]
  rw [← Category.assoc, ← kernel.lift_ι (D.map fq) (ρ ≫ cycleClass x hx) hz,
    Category.assoc, hk, comp_zero]

end Staircase

private theorem mono_homology_one
    (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ))
    {L : CochainComplex A ℕ} (ε : L ⟶ K.X 0) (hε : ε ≫ K.d 0 1 = 0)
    (h₀ : Mono (ε.f 1))
    (h₁ : ∀ q, (ShortComplex.mk (ε.f q) ((K.d 0 1).f q)
      (K.comp_f_d_f_eq_zero ε hε q)).Exact) :
    Mono (HomologicalComplex.homologyMap (K.toTotalOfAugmentation ε hε) 1) := by
  rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _ 0 1 2
    (by simp) (by simp)]
  intro B x hx y hy
  have hy' : y ≫ (K.total (.up ℕ)).d 0 1 =
      x ≫ (K.toTotalOfAugmentation ε hε).f 1 := hy.symm
  have hv : K.VanishesFrom y 1 := K.vanishesFrom_of_lt y 1 (by omega)
  obtain ⟨B', π, hπ, l, hl⟩ := K.exists_eq_comp_ε (hε := hε) h₁ hv (by
    rw [← Category.assoc, hy']
    exact K.vanishesFrom_toTotalOfAugmentation ε hε x 1 0 le_rfl)
  refine ⟨B', π, hπ, l, ?_⟩
  have := h₀
  have he := K.comp_d_totalπ_zero y
  rw [← Category.assoc, hy', Category.assoc, Category.assoc,
    HomologicalComplex₂.toTotalOfAugmentation_f_totalπ_zero] at he
  rw [← cancel_mono (ε.f 1)]
  calc (π ≫ x) ≫ ε.f 1 =
        π ≫ (y ≫ K.totalπ 0 0 0) ≫ (K.X 0).d 0 1 := by
          simpa only [Category.assoc] using congrArg (fun g ↦ π ≫ g) he
    _ = (l ≫ L.d 0 1) ≫ ε.f 1 := by
          rw [← Category.assoc, hl, Category.assoc, ε.comm, Category.assoc]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mono_bottomInclusion_one (U : FiniteSplitEtaleHypercover X)
    {F : Sheaf X.smallEtaleTopology A} (I : InjectiveResolution F) :
    Mono (HomologicalComplex.homologyMap (bottomInclusion A U I) 1) := by
  have hex (q : ℕ) :
      (ShortComplex.mk ((staircaseAugmentation I U).f q)
        (((staircase U I.cocomplex).d 0 1).f q)
        ((staircase U I.cocomplex).comp_f_d_f_eq_zero
          (staircaseAugmentation I U) (staircaseAugmentation_d I U) q)).Exact := by
    let E : Sheaf X.smallEtaleTopology A ⥤ A :=
      sheafToPresheaf _ _ ⋙ (evaluation _ _).obj
        (op (U.simplicial.obj (op (SimplexCategory.mk q))))
    exact ShortComplex.exact_of_f_is_kernel _
      (isLimitForkMapOfIsLimit' E I.ι_f_zero_comp_complex_d I.isLimitKernelFork)
  have hm := mono_homology_one A (staircase U I.cocomplex)
    (staircaseAugmentation I U) (staircaseAugmentation_d I U)
    (staircaseAugmentation_mono I U 1) hex
  change Mono (HomologicalComplex.homologyMap (staircaseBottom I U) 1) at hm
  rw [← staircaseBottom_flip I U, HomologicalComplex.homologyMap_comp]
  infer_instance


set_option backward.isDefEq.respectTransparency false in
private theorem mono_canonicalComparison_one (U : FiniteSplitEtaleHypercover X)
    (F : Sheaf X.smallEtaleTopology A) :
    Mono ((canonicalComparison A U 1).app F) := by
  have hrow (V : FiniteSplitEtaleHypercover X) (G : Sheaf X.smallEtaleTopology A)
      (h : Injective G) : QuasiIso (sectionAugmentation A V G) := by
    have := h
    exact injective_row_quasiIso A V G
  have := resolutionAugmentation_quasiIso A hrow U (injectiveResolution F)
  have := mono_bottomInclusion_one A U (injectiveResolution F)
  change Mono (comparisonAt A U (injectiveResolution F) 1)
  unfold comparisonAt
  infer_instance

private theorem epi_desc_of_images
    {J : Type (u + 1)} [Category.{u} J] [IsFiltered J] (D : J ⥤ A) (c : Cocone D)
    (himage : (⨆ j, imageSubobject (c.ι.app j)) = ⊤) :
    Epi (colimit.desc D c) := by
  have hi : imageSubobject (colimit.desc D c) = ⊤ := by
    apply top_le_iff.mp
    rw [← himage]
    apply iSup_le
    intro j
    rw [← colimit.ι_desc c j]
    exact imageSubobject_comp_le _ _
  have : Epi (image.ι (colimit.desc D c)) :=
    (Subobject.epi_iff_mk_eq_top _).mpr hi
  have : Epi (factorThruImage (colimit.desc D c) ≫ image.ι (colimit.desc D c)) :=
    inferInstance
  simpa only [image.fac] using this


private theorem mono_desc_of_kernel_refinements
    {J : Type (u + 1)} [Category.{u} J] [IsFiltered J] (D : J ⥤ A) (c : Cocone D)
    (hker : ∀ j, kernelSubobject (c.ι.app j) ≤
      ⨆ (j' : J) (f : j ⟶ j'), kernelSubobject (D.map f)) :
    Mono (colimit.desc D c) := by
  let : AB5OfSize.{u, u + 1} A :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} A
  have hz (j : J) : kernel.ι (c.ι.app j) ≫ colimit.ι D j = 0 := by
    have hk : kernelSubobject (c.ι.app j) ≤ kernelSubobject (colimit.ι D j) := by
      refine (hker j).trans ?_
      refine iSup_le (fun j' ↦ iSup_le (fun f ↦ ?_))
      apply le_kernelSubobject
      rw [← colimit.w D f, ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]
    rw [← kernelSubobject_arrow', Category.assoc]
    rw [← Subobject.ofLE_arrow hk, Category.assoc, kernelSubobject_arrow_comp,
      comp_zero, comp_zero]
  let L : (J ⥤ A) ⥤ A := colim
  have hzero : L.map (kernel.ι c.ι) = 0 := by
    apply colimit.hom_ext
    intro j
    change colimit.ι _ j ≫ colimMap (kernel.ι c.ι) = _
    rw [ι_colimMap]
    let E := (evaluation J A).obj j
    let e := PreservesKernel.iso E c.ι
    apply (cancel_epi e.inv).mp
    change e.inv ≫ E.map (kernel.ι c.ι) ≫ colimit.ι D j = _
    rw [← Category.assoc, PreservesKernel.iso_inv_ι]
    change kernel.ι (c.ι.app j) ≫ colimit.ι D j = _
    simp only [hz, comp_zero]
  have hk : kernel.ι (L.map c.ι) = 0 := by
    rw [← PreservesKernel.iso_inv_ι L c.ι, hzero, comp_zero]
  have : Mono (L.map c.ι) := Abelian.mono_of_kernel_ι_eq_zero _ hk
  have : Mono (colimMap c.ι) := this
  have : IsConnected J := IsFiltered.isConnected J
  let e : colimit ((Functor.const J).obj c.pt) ≅ c.pt :=
    (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone J c.pt)
  have he : colimMap c.ι ≫ e.hom = colimit.desc D c := by
    apply colimit.hom_ext
    intro j
    simp [e]
  rw [← he]
  infer_instance

/-- Finite refinement makes the positive-degree bottom comparison a colimit isomorphism.
Source: Stacks Project, Hypercoverings, Tag 01H0, first proof; the finite staircase
argument of blueprint lem-sc-hypercover-bottom-refinement-descent.
(auxiliary; not a blueprint node).

Proof: use the explicit section bicomplex of an injective resolution and flip
its indices so that resolution degree is first. The signed total flip is
compatible with refinement and with the bottom inclusion. Injective-row
acyclicity identifies its total cohomology with derived terminal sections.

A finite descending staircase removes the leading positive resolution-degree
component by subtracting the differential of a local primitive. The primitive
detector permits both refinement of the hypercover and precomposition by a
map of source objects; it detects zero maps without requiring one refinement
that works for an arbitrary whole source object. Induction combines these
zero-detection statements. In resolution degree zero, the evaluated initial
kernel of the injective resolution gives the unique lift to F.

Apply the staircase first to cycles. Any map out of derived terminal sections
that kills all bottom comparison images vanishes; thus their supremum is top.
Apply it to a bounding cochain to show, in degrees at least two, that each
comparison kernel lies below the supremum of refinement-map kernels. In degree
one the bottom map on homology is already monic, by the evaluated initial
kernel and the fact that a bounding cochain has only one component.

The homotopy cohomology diagram is filtered. Every refinement kernel dies in
its colimit, and AB5 sends its comparison-kernel natural transformation to
zero. Connectedness identifies the colimit of the constant target with that
target, proving the displayed mediator monic. Its image contains all comparison
images, so it is epic and hence invertible. Degree zero is treated separately
in GrothendieckHypercoverZero. Empty covers and zero coefficient objects are
included by the local primitive argument. -/
theorem isIso_colimit_comparison_positive (F : Sheaf X.smallEtaleTopology A) (q : ℕ) :
    IsIso (colimit.desc (homotopyCohomologyDiagram A F (q + 1))
      (comparisonCocone A F (q + 1))) := by
  have hlocal : LocalPrimitives (X := X) (A := A) :=
    eq_zero_of_refinement_primitives A
  have : Mono (colimit.desc (homotopyCohomologyDiagram A F (q + 1))
      (comparisonCocone A F (q + 1))) :=
    mono_desc_of_kernel_refinements A _ _ (by
      intro U
      cases q with
      | zero =>
          have : Mono ((comparisonCocone A F 1).ι.app U) :=
            mono_canonicalComparison_one A U.as.unop F
          have hk : kernelSubobject ((comparisonCocone A F 1).ι.app U) = ⊥ := by
            rw [← Subobject.mk_arrow
              (kernelSubobject ((comparisonCocone A F 1).ι.app U)),
              Subobject.mk_eq_bot_iff_zero]
            apply (cancel_mono ((comparisonCocone A F 1).ι.app U)).mp
            simp only [kernelSubobject_arrow_comp, zero_comp]
          rw [hk]
          exact bot_le
      | succ q => exact comparison_kernels hlocal F q U)
  have : Epi (colimit.desc (homotopyCohomologyDiagram A F (q + 1))
      (comparisonCocone A F (q + 1))) :=
    epi_desc_of_images A _ _ (comparison_images hlocal F q)
  exact isIso_of_mono_of_epi _

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck
