import Langlands.AlgebraicGeometry.Modules.TensorSections
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Modules.SectionLocusComparison
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.SchemeModule.LineBundleDescent

variable {X : Scheme.{u}} (M : X.Modules)

theorem trivializesOn_iff_bijective (s : GlobalSections M) (U : X.Opens) :
    TrivializesOn M s U ↔ ∀ V : X.Opens, V ≤ U → Function.Bijective ((sectionHom M s).app V) := by
  unfold TrivializesOn
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  constructor
  · intro h V hV
    have := h (U.ι ⁻¹ᵁ V)
    rw [ConcreteCategory.isIso_iff_bijective] at this
    have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; simpa using hV
    exact e ▸ this
  · intro h W
    rw [ConcreteCategory.isIso_iff_bijective]
    exact h (U.ι ''ᵁ W) (U.ι_image_le W)


variable {Y : Scheme.{u}}

lemma hom_app_map {A B : Y.Modules} (φ : A ⟶ B) {V W : Y.Opens} (h : W ≤ V) (a : Γ(A, V)) :
    φ.app W (A.presheaf.map (homOfLE h).op a) = B.presheaf.map (homOfLE h).op (φ.app V a) :=
  PresheafOfModules.naturality_apply φ.val (homOfLE h).op a

lemma map_map_apply (A : Y.Modules) {V W W' : Y.Opens} (h : W ≤ V) (h' : W' ≤ W)
    (a : Γ(A, V)) :
    A.presheaf.map (homOfLE h').op (A.presheaf.map (homOfLE h).op a) =
      A.presheaf.map (homOfLE (h'.trans h)).op a := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma map_id_apply (A : Y.Modules) {V : Y.Opens} (h : V ≤ V) (a : Γ(A, V)) :
    A.presheaf.map (homOfLE h).op a = a := by
  have e : (homOfLE h).op = 𝟙 (Opposite.op V) := rfl
  rw [e, CategoryTheory.Functor.map_id]
  rfl

/-- A section over `V` whose restriction to `V ⊓ U` lies in the image of `φ`. -/
def RangeOnMem {A B : Y.Modules} (φ : A ⟶ B) (U V : Y.Opens) (σ : Γ(B, V)) : Prop :=
  ∃ a : Γ(A, V ⊓ U), φ.app _ a = B.presheaf.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op σ

section RangeOnMem

variable {A B : Y.Modules} (φ : A ⟶ B) (U : Y.Opens)

lemma RangeOnMem.add {V : Y.Opens} {σ τ : Γ(B, V)} (hσ : RangeOnMem φ U V σ)
    (hτ : RangeOnMem φ U V τ) : RangeOnMem φ U V (σ + τ) := by
  obtain ⟨a, ha⟩ := hσ
  obtain ⟨b, hb⟩ := hτ
  exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩

lemma RangeOnMem.zero (V : Y.Opens) : RangeOnMem φ U V 0 :=
  ⟨0, by rw [map_zero, map_zero]⟩

lemma RangeOnMem.smul {V : Y.Opens} (r : Γ(Y, V)) {σ : Γ(B, V)} (hσ : RangeOnMem φ U V σ) :
    RangeOnMem φ U V (r • σ) := by
  obtain ⟨a, ha⟩ := hσ
  refine ⟨Y.presheaf.map (homOfLE (show V ⊓ U ≤ V from inf_le_left)).op r • a, ?_⟩
  rw [Scheme.Modules.Hom.app_smul, ha]
  exact (Scheme.Modules.map_smul B _ r σ).symm

lemma RangeOnMem.map {V W : Y.Opens} (h : W ≤ V) {σ : Γ(B, V)} (hσ : RangeOnMem φ U V σ) :
    RangeOnMem φ U W (B.presheaf.map (homOfLE h).op σ) := by
  obtain ⟨a, ha⟩ := hσ
  have hle : W ⊓ U ≤ V ⊓ U := inf_le_inf_right U h
  refine ⟨A.presheaf.map (homOfLE hle).op a, ?_⟩
  rw [hom_app_map, ha, map_map_apply, map_map_apply]

lemma RangeOnMem.of_app_eq {V W : Y.Opens} (hW₁ : V ⊓ U ≤ W) (hW₂ : W ≤ V) {σ : Γ(B, V)}
    (a : Γ(A, W)) (ha : φ.app W a = B.presheaf.map (homOfLE hW₂).op σ) :
    RangeOnMem φ U V σ :=
  ⟨A.presheaf.map (homOfLE hW₁).op a, by rw [hom_app_map, ha, map_map_apply]⟩

lemma RangeOnMem.exists_app_eq {V : Y.Opens} (hV : V ≤ U) {σ : Γ(B, V)}
    (hσ : RangeOnMem φ U V σ) : ∃ a : Γ(A, V), φ.app V a = σ := by
  obtain ⟨a, ha⟩ := hσ
  refine ⟨A.presheaf.map (homOfLE (le_inf le_rfl hV)).op a, ?_⟩
  rw [hom_app_map, ha, map_map_apply, map_id_apply]

/-- If `φ` is injective on all opens inside `U`, membership is local. -/
lemma RangeOnMem.of_cover (hφ : ∀ V ≤ U, Function.Injective (φ.app V)) {V : Y.Opens}
    (σ : Γ(B, V)) (h : ∀ x ∈ V, ∃ W : Y.Opens, ∃ hW : W ≤ V, x ∈ W ∧
      RangeOnMem φ U W (B.presheaf.map (homOfLE hW).op σ)) :
    RangeOnMem φ U V σ := by
  let ι' := {W : Y.Opens // ∃ hW : W ≤ V, RangeOnMem φ U W (B.presheaf.map (homOfLE hW).op σ)}
  let Ws : ι' → Y.Opens := fun j ↦ j.1 ⊓ U
  have hWs : ∀ j : ι', Ws j ≤ V ⊓ U := fun j ↦ inf_le_inf_right U j.2.1
  choose a ha using fun j : ι' ↦ j.2.2
  have ha' : ∀ j : ι', φ.app (Ws j) (a j) =
      B.presheaf.map (homOfLE ((hWs j).trans inf_le_left)).op σ := by
    intro j
    rw [ha j, map_map_apply]
  let SA : TopCat.Sheaf Ab Y := ⟨A.presheaf, A.isSheaf⟩
  let SB : TopCat.Sheaf Ab Y := ⟨B.presheaf, B.isSheaf⟩
  have hcov : V ⊓ U ≤ iSup Ws := by
    intro x hx
    obtain ⟨W, hW, hxW, hmem⟩ := h x hx.1
    exact Opens.mem_iSup.mpr ⟨⟨W, hW, hmem⟩, hxW, hx.2⟩
  have hcomp : TopCat.Presheaf.IsCompatible SA.1 Ws a := by
    intro j l
    have hjl : Ws j ⊓ Ws l ≤ U := inf_le_left.trans inf_le_right
    apply hφ _ hjl
    change φ.app _ (A.presheaf.map (homOfLE inf_le_left).op (a j)) =
      φ.app _ (A.presheaf.map (homOfLE inf_le_right).op (a l))
    rw [hom_app_map, hom_app_map, ha', ha', map_map_apply, map_map_apply]
  obtain ⟨g, hg, -⟩ := SA.existsUnique_gluing' Ws (V ⊓ U) (fun j ↦ homOfLE (hWs j)) hcov a hcomp
  refine ⟨g, ?_⟩
  apply SB.eq_of_locally_eq' Ws (V ⊓ U) (fun j ↦ homOfLE (hWs j)) hcov
  intro j
  change B.presheaf.map (homOfLE (hWs j)).op (φ.app _ g) =
    B.presheaf.map (homOfLE (hWs j)).op (B.presheaf.map (homOfLE inf_le_left).op σ)
  rw [← hom_app_map, hg j, ha', map_map_apply]

end RangeOnMem

/-- Sections whose restriction to each `V ⊓ U i` lies in the image of `φ i`. -/
def rangeOnSubmodule {ι : Type*} {A B : Y.Modules} (φ : ι → (A ⟶ B)) (U : ι → Y.Opens) :
    PresheafOfModules.Submodule B.val where
  obj V :=
    { carrier := {σ | ∀ i, RangeOnMem (φ i) (U i) V.unop σ}
      add_mem' := fun hσ hτ i ↦ RangeOnMem.add (φ i) (U i) (hσ i) (hτ i)
      zero_mem' := fun i ↦ RangeOnMem.zero (φ i) (U i) V.unop
      smul_mem' := fun r _ hσ i ↦ RangeOnMem.smul (φ i) (U i) r (hσ i) }
  map f _ hσ i := RangeOnMem.map (φ i) (U i) (leOfHom f.unop) (hσ i)

/-- The sheaf submodule of sections whose restriction to each `V ⊓ U i` lies in the image
of `φ i`. -/
def rangeOn {ι : Type*} {A B : Y.Modules} (φ : ι → (A ⟶ B)) (U : ι → Y.Opens)
    (hφ : ∀ i, ∀ V ≤ U i, Function.Injective ((φ i).app V)) : SheafOfModules.Submodule B where
  toSubmodule := rangeOnSubmodule φ U
  isSheaf V σ hσ i := by
    refine RangeOnMem.of_cover (φ i) (U i) (hφ i) σ fun x hx ↦ ?_
    obtain ⟨W, f, hf, hxW⟩ := hσ x hx
    exact ⟨W, leOfHom f, hxW, hf i⟩

lemma sectionHom_pushforward_app {Y' : Scheme.{u}} (π : Y' ⟶ Y) (F : Y'.Modules)
    (t : GlobalSections F) (V : Y.Opens) (a : Γ(Y, V)) :
    (sectionHom ((Scheme.Modules.pushforward π).obj F) t).app V a =
      (sectionHom F t).app (π ⁻¹ᵁ V) (π.app V a) := by
  refine (sectionHom_app _ _ V a).trans ?_
  refine Eq.trans ?_ (sectionHom_app F t (π ⁻¹ᵁ V) (π.app V a)).symm
  rfl

lemma sectionHom_app_of_eq_smul (s t : GlobalSections M) {W : X.Opens} (c : Γ(X, W))
    (h : M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op t =
      c • M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op s) (d : Γ(X, W)) :
    (sectionHom M t).app W d = (sectionHom M s).app W (d * c) := by
  rw [sectionHom_app, sectionHom_app, h, mul_smul]

lemma trivializesOn_of_eq_smul (s t : GlobalSections M) {V : X.Opens} (hs : TrivializesOn M s V)
    (c : Γ(X, V)) (hc : IsUnit c)
    (h : M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op t =
      c • M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s) :
    TrivializesOn M t V := by
  rw [trivializesOn_iff_bijective] at hs ⊢
  intro W hW
  let c' : Γ(X, W) := X.presheaf.map (homOfLE hW).op c
  have hc' : IsUnit c' := hc.map (X.presheaf.map (homOfLE hW).op).hom
  have hW' : M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op t =
      c' • M.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op s := by
    rw [← map_map_apply M (show V ≤ ⊤ from le_top) hW, h, Scheme.Modules.map_smul,
      map_map_apply]
  have key := sectionHom_app_of_eq_smul M s t c' hW'
  refine ⟨fun d d' hd ↦ ?_, fun m ↦ ?_⟩
  · rw [key d, key d'] at hd
    exact hc'.mul_left_injective ((hs W hW).1 hd)
  · obtain ⟨d, rfl⟩ := (hs W hW).2 m
    let e : Γ(X, W) := (show Γ(X, W) from d) * ((hc'.unit⁻¹ : (Γ(X, W))ˣ) : Γ(X, W))
    refine ⟨e, ?_⟩
    rw [key e]
    congr 1
    change (show Γ(X, W) from d) * ((hc'.unit⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)) * c' = d
    rw [mul_assoc, IsUnit.val_inv_mul, mul_one]

lemma nonempty_iso_of_trivializesOn {s : GlobalSections M} {U : X.Opens}
    (h : TrivializesOn M s U) :
    Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (sectionHom M s)) := h
  exact ⟨(asIso ((Scheme.Modules.restrictFunctor U.ι).map (sectionHom M s))).symm ≪≫
    Scheme.Modules.restrictUnitIso U.ι⟩

end Langlands.SchemeModule.LineBundleDescent

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.SchemeModule.LineBundleDescent

variable {Y : Scheme.{u}}

/-- A family of sections of a module sheaf on `Y'` whose trivialization loci are the preimages
of an open cover of `Y`, and whose pairwise transition functions come from `Y`, descends to a
line bundle on `Y` along a morphism that is injective on sections and surjective. -/
theorem exists_lineBundle_of_descent {Y' : Scheme.{u}} (π : Y' ⟶ Y)
    (hinj : ∀ V : Y.Opens, Function.Injective (π.app V))
    (hsurj : Function.Surjective π.base)
    (F : Y'.Modules) {ι : Type*} (U : ι → Y.Opens) (hU : ∀ y : Y, ∃ i, y ∈ U i)
    (t : ι → GlobalSections F)
    (hloc : ∀ i, trivializationOpen F (t i) = π ⁻¹ᵁ U i)
    (htrans : ∀ k i, ∃ a : Γ(Y, U i),
      (sectionHom F (t i)).app (π ⁻¹ᵁ U i) (π.app (U i) a) =
        F.presheaf.map (homOfLE (show π ⁻¹ᵁ U i ≤ ⊤ from le_top)).op (t k)) :
    ∃ M : LineBundle Y, ∃ s : ι → GlobalSections M.obj,
      ∀ k, trivializationOpen M.obj (s k) = U k := by
  let P := (Scheme.Modules.pushforward π).obj F
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ι → (structureModule Y ⟶ P), ∀ i, ψ i = sectionHom P (t i) :=
    ⟨fun i ↦ sectionHom P (t i), fun _ ↦ rfl⟩
  have hψapp : ∀ i V (a : Γ(Y, V)),
      (ψ i).app V a = (sectionHom F (t i)).app (π ⁻¹ᵁ V) (π.app V a) := by
    intro i V a
    rw [hψdef]
    exact sectionHom_pushforward_app π F (t i) V a
  have htriv : ∀ i, TrivializesOn F (t i) (π ⁻¹ᵁ U i) := fun i ↦
    (maximalTrivialization Y' F (t i) _).mpr (hloc i).ge
  have hbijF : ∀ i, ∀ V ≤ U i, Function.Bijective ((sectionHom F (t i)).app (π ⁻¹ᵁ V)) :=
    fun i V hV ↦ (trivializesOn_iff_bijective F (t i) _).mp (htriv i) _ (fun x hx ↦ hV hx)
  have hψ : ∀ i, ∀ V ≤ U i, Function.Injective ((ψ i).app V) := by
    intro i V hV a b hab
    exact hinj V ((hbijF i V hV).1 ((hψapp i V a).symm.trans (hab.trans (hψapp i V b))))
  let N := rangeOn ψ U hψ
  let M : Y.Modules := N.toSheafOfModules
  have hmem : ∀ k, ∀ i, RangeOnMem (ψ i) (U i) ⊤ (show Γ(P, ⊤) from t k) := by
    intro k i
    obtain ⟨a, ha⟩ := htrans k i
    refine RangeOnMem.of_app_eq (ψ i) (U i) (W := U i) inf_le_right le_top a ?_
    rw [hψapp]
    exact ha
  let s : ι → GlobalSections M := fun k ↦
    (⟨show Γ(P, ⊤) from t k, hmem k⟩ : N.obj (Opposite.op ⊤))
  let ιN : M ⟶ P := N.ι
  have hιinj : ∀ V, Function.Injective (ιN.app V) := fun V a b h ↦ Subtype.ext h
  have hcomp : ∀ k, ψ k = sectionHom M (s k) ≫ ιN := by
    intro k
    rw [hψdef, ← sectionHom_naturality]
    rfl
  have happ : ∀ k V (a : Γ(Y, V)),
      ιN.app V ((sectionHom M (s k)).app V a) = (ψ k).app V a := by
    intro k V a
    rw [hcomp k, Scheme.Modules.Hom.comp_app]
    rfl
  have hbij : ∀ k, ∀ V ≤ U k, Function.Bijective ((sectionHom M (s k)).app V) := by
    intro k V hV
    refine ⟨fun a b hab ↦ hψ k V hV ?_, fun σ ↦ ?_⟩
    · exact (happ k V a).symm.trans ((congrArg (ιN.app V) hab).trans (happ k V b))
    · obtain ⟨a, ha⟩ := RangeOnMem.exists_app_eq (ψ k) (U k) hV (σ.2 k)
      exact ⟨a, hιinj V ((happ k V a).trans ha)⟩
  have htrivM : ∀ k, TrivializesOn M (s k) (U k) := fun k ↦
    (trivializesOn_iff_bijective M (s k) (U k)).mpr (hbij k)
  have hM : IsLocallyFreeRankOne M := by
    intro y
    obtain ⟨k, hk⟩ := hU y
    exact ⟨U k, hk, nonempty_iso_of_trivializesOn _ (htrivM k)⟩
  refine ⟨⟨M, hM⟩, s, fun k ↦ le_antisymm ?_
    ((maximalTrivialization Y M (s k) (U k)).mp (htrivM k))⟩
  intro x hx
  obtain ⟨i, hi⟩ := hU x
  let W := trivializationOpen M (s k)
  let V : Y.Opens := W ⊓ U i
  have hVW : V ≤ W := inf_le_left
  have hVi : V ≤ U i := inf_le_right
  have hW : TrivializesOn M (s k) W := (maximalTrivialization Y M (s k) W).mpr le_rfl
  obtain ⟨b, hb⟩ := ((trivializesOn_iff_bijective M (s k) W).mp hW V hVW).2
    (M.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (s i))
  have eq1 : (sectionHom F (t k)).app (π ⁻¹ᵁ V) (π.app V b) =
      F.presheaf.map (homOfLE (show π ⁻¹ᵁ V ≤ ⊤ from le_top)).op (t i) := by
    exact (hψapp k V b).symm.trans ((happ k V b).symm.trans
      ((congrArg (ιN.app V) hb).trans (hom_app_map ιN (show V ≤ ⊤ from le_top) (s i))))
  obtain ⟨a, ha⟩ := htrans k i
  have hπV : π ⁻¹ᵁ V ≤ π ⁻¹ᵁ U i := fun y hy ↦ hVi hy
  let c : Γ(Y', π ⁻¹ᵁ V) := Y'.presheaf.map (homOfLE hπV).op (π.app (U i) a)
  have eq2 : F.presheaf.map (homOfLE (show π ⁻¹ᵁ V ≤ ⊤ from le_top)).op (t k) =
      c • F.presheaf.map (homOfLE (show π ⁻¹ᵁ V ≤ ⊤ from le_top)).op (t i) := by
    rw [← map_map_apply F (show π ⁻¹ᵁ U i ≤ ⊤ from le_top) hπV (t k), ← ha, sectionHom_app,
      Scheme.Modules.map_smul, map_map_apply]
  let e : Γ(Y', π ⁻¹ᵁ V) := π.app V b
  have eq1' : e • F.presheaf.map (homOfLE (show π ⁻¹ᵁ V ≤ ⊤ from le_top)).op (t k) =
      F.presheaf.map (homOfLE (show π ⁻¹ᵁ V ≤ ⊤ from le_top)).op (t i) :=
    (sectionHom_app F (t k) (π ⁻¹ᵁ V) e).symm.trans eq1
  have hunit : e * c = 1 := by
    apply (hbijF i V hVi).1
    calc (sectionHom F (t i)).app (π ⁻¹ᵁ V) (e * c)
        = (e * c) • F.presheaf.map (homOfLE (show π ⁻¹ᵁ V ≤ ⊤ from le_top)).op (t i) :=
          sectionHom_app F (t i) (π ⁻¹ᵁ V) (e * c)
      _ = e • F.presheaf.map (homOfLE (show π ⁻¹ᵁ V ≤ ⊤ from le_top)).op (t k) := by
          rw [mul_smul, ← eq2]
      _ = (1 : Γ(Y', π ⁻¹ᵁ V)) •
            F.presheaf.map (homOfLE (show π ⁻¹ᵁ V ≤ ⊤ from le_top)).op (t i) := by
          rw [eq1', one_smul]
      _ = (sectionHom F (t i)).app (π ⁻¹ᵁ V) (1 : Γ(Y', π ⁻¹ᵁ V)) :=
          (sectionHom_app F (t i) (π ⁻¹ᵁ V) 1).symm
  have hc : IsUnit c := IsUnit.of_mul_eq_one_right e hunit
  have htk : TrivializesOn F (t k) (π ⁻¹ᵁ V) :=
    trivializesOn_of_eq_smul F (t i) (t k)
      ((maximalTrivialization Y' F (t i) _).mpr (hπV.trans (hloc i).ge)) c hc eq2
  have hle : π ⁻¹ᵁ V ≤ π ⁻¹ᵁ U k :=
    ((maximalTrivialization Y' F (t k) _).mp htk).trans (hloc k).le
  obtain ⟨y, rfl⟩ := hsurj x
  exact hle (show π.base y ∈ V from ⟨hx, hi⟩)

end Langlands.AlgebraicGeometry.Picard
