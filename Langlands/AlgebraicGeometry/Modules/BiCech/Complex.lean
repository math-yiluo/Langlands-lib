import Langlands.AlgebraicGeometry.Modules.BiCech.Sections

/-!
# The bi-Čech resolution

For a `BiCover P` (morphisms `f : P ⟶ X`, `g : P ⟶ Y` and ordered affine covers `𝒰`, `𝒱` of
`X`, `Y`) and an `𝒪_P`-module `F`, the degree-`n` term of the bi-Čech complex is the finite
biproduct, over bidegrees `p + q = n` and strictly increasing tuples `s`, `t` of lengths `p + 1`,
`q + 1`, of the modules `sheafOn F (f⁻¹(𝒰.inter s) ∩ g⁻¹(𝒱.inter t))`. The differential is
`δ₁ + (-1)^p δ₂`, the alternating Čech differential in `s` plus the signed one in `t`, and the
augmentation collects the units `F ⟶ sheafOn F (biOpen s t)`. On sections over an open `V`
these are the operators `DT` and `augT` of `BiCech.Sections`; local exactness there gives
that the augmentation `F[0] ⟶ bicechComplex 𝒲 F` is a quasi-isomorphism.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.BiCech

open CechResolution

variable {P : Scheme.{u}} (𝒲 : BiCover P) (F : P.Modules)

/-- The index type of the degree-`n` term: bidegrees `(p, q)` with `p + q = n` and tuples
`s`, `t` of lengths `p + 1`, `q + 1`. -/
abbrev TIdx (n : ℕ) : Type u :=
  Σ pq : Finset.antidiagonal n, 𝒲.𝒰.Idx pq.1.1 × 𝒲.𝒱.Idx pq.1.2

/-- The index with bidegree `(p, q)` and tuples `s`, `t`. -/
abbrev tidx {n p q : ℕ} (h : p + q = n) (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) : TIdx 𝒲 n :=
  ⟨⟨(p, q), Finset.mem_antidiagonal.2 h⟩, s, t⟩

/-- The summand attached to an index. -/
abbrev summand {n : ℕ} (x : TIdx 𝒲 n) : P.Modules := sheafOn F (biOpen 𝒲 x.2.1 x.2.2)

/-- The degree-`n` term `⨁_{p + q = n, s, t} sheafOn F (biOpen s t)`. -/
abbrev term (n : ℕ) : P.Modules := ⨁ summand 𝒲 F (n := n)

/-- The projection onto the `(s, t)`-summand. -/
abbrev πT {n p q : ℕ} (h : p + q = n) (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) :
    term 𝒲 F n ⟶ sheafOn F (biOpen 𝒲 s t) :=
  biproduct.π (summand 𝒲 F) (tidx 𝒲 h s t)

variable {𝒲}

lemma biOpen_le_face₁ {p q : ℕ} (s : 𝒲.𝒰.Idx (p + 1)) (t : 𝒲.𝒱.Idx q) (j : Fin (p + 2)) :
    biOpen 𝒲 s t ≤ biOpen 𝒲 (𝒲.𝒰.face s j) t :=
  inf_le_inf_right _ (𝒲.f.preimage_mono (𝒲.𝒰.inter_le_inter_face s j))

lemma biOpen_le_face₂ {p q : ℕ} (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx (q + 1)) (j : Fin (q + 2)) :
    biOpen 𝒲 s t ≤ biOpen 𝒲 s (𝒲.𝒱.face t j) :=
  inf_le_inf_left _ (𝒲.g.preimage_mono (𝒲.𝒱.inter_le_inter_face t j))

variable (𝒲)

/-- The `δ₁`-component into the `(s, t)`-summand of degree `n + 1`. -/
def horC (n : ℕ) : (p q : ℕ) → p + q = n + 1 → (s : 𝒲.𝒰.Idx p) → (t : 𝒲.𝒱.Idx q) →
    (term 𝒲 F n ⟶ sheafOn F (biOpen 𝒲 s t))
  | 0, _, _, _, _ => 0
  | p + 1, q, h, s, t => ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (πT 𝒲 F (by omega : p + q = n) (𝒲.𝒰.face s j) t ≫ res F (biOpen_le_face₁ s t j))

/-- The `δ₂`-component into the `(s, t)`-summand of degree `n + 1`. -/
def verC (n : ℕ) : (p q : ℕ) → p + q = n + 1 → (s : 𝒲.𝒰.Idx p) → (t : 𝒲.𝒱.Idx q) →
    (term 𝒲 F n ⟶ sheafOn F (biOpen 𝒲 s t))
  | _, 0, _, _, _ => 0
  | p, q + 1, h, s, t => ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (πT 𝒲 F (by omega : p + q = n) s (𝒲.𝒱.face t j) ≫ res F (biOpen_le_face₂ s t j))

/-- The differential `δ₁ + (-1)^p δ₂` of the bi-Čech complex. -/
def D (n : ℕ) : term 𝒲 F n ⟶ term 𝒲 F (n + 1) :=
  biproduct.lift fun y =>
    horC 𝒲 F n y.1.1.1 y.1.1.2 (Finset.mem_antidiagonal.1 y.1.2) y.2.1 y.2.2 +
      ((-1 : ℤ) ^ y.1.1.1) •
        verC 𝒲 F n y.1.1.1 y.1.1.2 (Finset.mem_antidiagonal.1 y.1.2) y.2.1 y.2.2

/-- The augmentation `F ⟶ term 0`, collecting the units. -/
def ε : F ⟶ term 𝒲 F 0 :=
  biproduct.lift fun y => unit F (biOpen 𝒲 y.2.1 y.2.2)

section Elementwise

variable {𝒲 F}

lemma zero_app_apply {M N : P.Modules} (V : P.Opens) (x : Γ(M, V)) :
    (0 : M ⟶ N).app V x = 0 :=
  map_zero (evalApp V x)

lemma add_app_apply {M N : P.Modules} (f g : M ⟶ N) (V : P.Opens) (x : Γ(M, V)) :
    (f + g).app V x = f.app V x + g.app V x :=
  map_add (evalApp V x) f g

/-- The components of a section of the degree-`n` term over `V`. -/
def toT {n : ℕ} (V : P.Opens) (x : Γ(term 𝒲 F n, V)) : TSec 𝒲 F n V := fun _ _ h s t =>
  (πT 𝒲 F h s t).app V x

lemma toT_injective {n : ℕ} (V : P.Opens) :
    Function.Injective (toT (𝒲 := 𝒲) (F := F) (n := n) V) := by
  intro x y hxy
  refine biproduct_ext_app _ fun i => ?_
  obtain ⟨⟨⟨p, q⟩, hm⟩, s, t⟩ := i
  exact congrFun (congrFun (congrFun (congrFun (congrFun hxy p) q)
    (Finset.mem_antidiagonal.1 hm)) s) t

lemma toT_surjective {n : ℕ} (V : P.Opens) :
    Function.Surjective (toT (𝒲 := 𝒲) (F := F) (n := n) V) := by
  intro c
  obtain ⟨x, hx⟩ := biproduct_exists_app (summand 𝒲 F (n := n)) V
    fun i => c i.1.1.1 i.1.1.2 (Finset.mem_antidiagonal.1 i.1.2) i.2.1 i.2.2
  exact ⟨x, funext fun p => funext fun q => funext fun h => funext fun s => funext fun t =>
    hx (tidx 𝒲 h s t)⟩

lemma toT_zero {n : ℕ} (V : P.Opens) (p q : ℕ) (h : p + q = n) (s : 𝒲.𝒰.Idx p)
    (t : 𝒲.𝒱.Idx q) : toT (𝒲 := 𝒲) (F := F) V 0 p q h s t = 0 :=
  map_zero _

lemma horC_app {n : ℕ} (V : P.Opens) (x : Γ(term 𝒲 F n, V)) (p q : ℕ) (h : p + q = n + 1)
    (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) :
    (horC 𝒲 F n p q h s t).app V x = horT (toT V x) p q h s t := by
  rcases p with _ | p
  · exact zero_app_apply V x
  · simp only [horC, sum_app_apply, zsmul_app_apply, comp_app_apply]
    change _ = δ₁ (toT V x p q (by omega)) s t
    rw [δ₁_apply]
    rfl

lemma verC_app {n : ℕ} (V : P.Opens) (x : Γ(term 𝒲 F n, V)) (p q : ℕ) (h : p + q = n + 1)
    (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) :
    (verC 𝒲 F n p q h s t).app V x = verT (toT V x) p q h s t := by
  rcases q with _ | q
  · exact zero_app_apply V x
  · simp only [verC, sum_app_apply, zsmul_app_apply, comp_app_apply]
    change _ = δ₂ (toT V x p q (by omega)) s t
    rw [δ₂_apply]
    rfl

variable (𝒲 F) in
lemma D_πT {n p q : ℕ} (h : p + q = n + 1) (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q) :
    D 𝒲 F n ≫ πT 𝒲 F h s t = horC 𝒲 F n p q h s t + ((-1 : ℤ) ^ p) • verC 𝒲 F n p q h s t :=
  biproduct.lift_π _ _

lemma toT_D {n : ℕ} (V : P.Opens) (x : Γ(term 𝒲 F n, V)) :
    toT V ((D 𝒲 F n).app V x) = DT (toT V x) := by
  funext p q h s t
  refine (congrArg (fun φ => φ.app V x) (D_πT 𝒲 F h s t)).trans ?_
  dsimp only
  rw [add_app_apply, zsmul_app_apply, horC_app, verC_app]
  rfl

lemma toT_ε (V : P.Opens) (m : Γ(F, V)) : toT V ((ε 𝒲 F).app V m) = augT m := by
  funext p q h s t
  change (ε 𝒲 F ≫ biproduct.π (summand 𝒲 F) (tidx 𝒲 h s t)).app V m = _
  rw [ε, biproduct.lift_π]
  rfl

end Elementwise

lemma D_D (n : ℕ) : D 𝒲 F n ≫ D 𝒲 F (n + 1) = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  refine toT_injective V ?_
  funext p q h s t
  rw [comp_app_apply, toT_D, toT_D, zero_app_apply, toT_zero]
  exact congrFun (congrFun (DT_DT _ p q h) s) t

lemma ε_D : ε 𝒲 F ≫ D 𝒲 F 0 = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext m
  refine toT_injective V ?_
  funext p q h s t
  rw [comp_app_apply, toT_D, toT_ε, zero_app_apply, toT_zero]
  exact congrFun (congrFun (DT_augT m p q h) s) t

/-- The bi-Čech complex as an `ℕ`-indexed cochain complex of `𝒪_P`-modules. -/
def bicechComplex : CochainComplex P.Modules ℕ :=
  CochainComplex.of (term 𝒲 F) (D 𝒲 F) (D_D 𝒲 F)

lemma bicechComplex_d (n : ℕ) : (bicechComplex 𝒲 F).d n (n + 1) = D 𝒲 F n :=
  CochainComplex.of_d (term 𝒲 F) (D 𝒲 F) n

/-- The augmentation as a morphism of cochain complexes `F[0] ⟶ bicechComplex 𝒲 F`. -/
def bicechAug : (CochainComplex.single₀ P.Modules).obj F ⟶ bicechComplex 𝒲 F :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨ε 𝒲 F, by
    rw [bicechComplex_d]
    exact ε_D 𝒲 F⟩

/-- The augmented bi-Čech complex `F ⟶ K⁰ ⟶ K¹`. -/
def augSc : ShortComplex P.Modules :=
  ShortComplex.mk (ε 𝒲 F) (D 𝒲 F 0) (ε_D 𝒲 F)

/-- The bi-Čech complex `Kⁿ ⟶ Kⁿ⁺¹ ⟶ Kⁿ⁺²`. -/
def bicechSc (n : ℕ) : ShortComplex P.Modules :=
  ShortComplex.mk (D 𝒲 F n) (D 𝒲 F (n + 1)) (D_D 𝒲 F n)

section Exactness

variable {𝒲}

lemma inter_single {X : Scheme.{u}} {𝒰 : X.OrderedAffineCover} (k : 𝒰.ι) :
    𝒰.inter (single k) = 𝒰.U k :=
  le_antisymm (iInf_le _ 0) (le_iInf fun _ => le_rfl)

lemma exists_mem_biOpen (x : P) :
    ∃ (a : 𝒲.𝒰.ι) (b : 𝒲.𝒱.ι), x ∈ 𝒲.f ⁻¹ᵁ 𝒲.𝒰.U a ⊓ 𝒲.g ⁻¹ᵁ 𝒲.𝒱.U b := by
  obtain ⟨a, ha⟩ := exists_mem_U (𝒰 := 𝒲.𝒰) (𝒲.f x)
  obtain ⟨b, hb⟩ := exists_mem_U (𝒰 := 𝒲.𝒱) (𝒲.g x)
  exact ⟨a, b, ⟨ha, hb⟩⟩

variable (𝒲)

theorem exact_bicechSc (n : ℕ) : (bicechSc 𝒲 F n).Exact := by
  refine exact_of_locally _ fun V (c : Γ(term 𝒲 F (n + 1), V)) hc x hx => ?_
  obtain ⟨a, b, hab⟩ := exists_mem_biOpen (𝒲 := 𝒲) x
  set W := V ⊓ (𝒲.f ⁻¹ᵁ 𝒲.𝒰.U a ⊓ 𝒲.g ⁻¹ᵁ 𝒲.𝒱.U b)
  have hW : W ≤ V := inf_le_left
  have hWa : W ≤ 𝒲.f ⁻¹ᵁ 𝒲.𝒰.U a := inf_le_right.trans inf_le_left
  have hWb : W ≤ 𝒲.g ⁻¹ᵁ 𝒲.𝒱.U b := inf_le_right.trans inf_le_right
  set c' := (term 𝒲 F (n + 1)).presheaf.map (homOfLE hW).op c
  have hc' : (D 𝒲 F (n + 1)).app W c' = 0 := by
    rw [app_map_apply, show (D 𝒲 F (n + 1)).app V c = 0 from hc, map_zero]
  have hcomp : ∀ p q (h : p + q = n + 1 + 1), DT (toT W c') p q h = 0 := by
    intro p q h
    funext s t
    rw [← toT_D, hc', toT_zero]
    rfl
  obtain ⟨b', hb'⟩ := toT_surjective W (preimT hWa hWb (toT W c'))
  refine ⟨W, hW, ⟨hx, hab⟩, b', toT_injective W ?_⟩
  change toT W ((D 𝒲 F n).app W b') = toT W c'
  rw [toT_D, hb']
  funext p q h
  exact DT_preimT hWa hWb _ hcomp p q h

theorem exact_augSc : (augSc 𝒲 F).Exact := by
  refine exact_of_locally _ fun V (c : Γ(term 𝒲 F 0, V)) hc x hx => ?_
  obtain ⟨a, b, hab⟩ := exists_mem_biOpen (𝒲 := 𝒲) x
  set W := V ⊓ (𝒲.f ⁻¹ᵁ 𝒲.𝒰.U a ⊓ 𝒲.g ⁻¹ᵁ 𝒲.𝒱.U b)
  have hW : W ≤ V := inf_le_left
  have hWa : W ≤ 𝒲.f ⁻¹ᵁ 𝒲.𝒰.U a := inf_le_right.trans inf_le_left
  have hWb : W ≤ 𝒲.g ⁻¹ᵁ 𝒲.𝒱.U b := inf_le_right.trans inf_le_right
  set c' := (term 𝒲 F 0).presheaf.map (homOfLE hW).op c
  have hc' : (D 𝒲 F 0).app W c' = 0 := by
    rw [app_map_apply, show (D 𝒲 F 0).app V c = 0 from hc, map_zero]
  have hcomp : ∀ p q (h : p + q = 0 + 1), DT (toT W c') p q h = 0 := by
    intro p q h
    funext s t
    rw [← toT_D, hc', toT_zero]
    rfl
  obtain ⟨m, hm⟩ := augT_eq_of_DT_eq_zero hWa hWb (toT W c') hcomp
  refine ⟨W, hW, ⟨hx, hab⟩, m, toT_injective W ?_⟩
  change toT W ((ε 𝒲 F).app W m) = toT W c'
  rw [toT_ε, hm]

theorem mono_ε : Mono (ε 𝒲 F) := by
  refine mono_of_app_injective _ fun V m m' hmm' => ?_
  have h := congrArg (toT V) hmm'
  rw [toT_ε, toT_ε] at h
  have hcover : V ≤ ⨆ ab : 𝒲.𝒰.ι × 𝒲.𝒱.ι, bo 𝒲 V (single ab.1) (single ab.2) := by
    intro z hz
    obtain ⟨a, b, hab⟩ := exists_mem_biOpen (𝒲 := 𝒲) z
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), ?_⟩
    rw [bo_eq, biOpen, inter_single, inter_single]
    exact ⟨hab, hz⟩
  exact TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, F.isSheaf⟩
    (fun ab : 𝒲.𝒰.ι × 𝒲.𝒱.ι => bo 𝒲 V (single ab.1) (single ab.2)) V
    (fun ab => homOfLE (bo_le V _ _)) hcover m m'
    fun ab => congrFun (congrFun (congrFun (congrFun (congrFun h 0) 0) rfl) (single ab.1))
      (single ab.2)

set_option backward.isDefEq.respectTransparency false in
/-- The augmentation `F[0] ⟶ bicechComplex 𝒲 F` is a quasi-isomorphism. -/
theorem quasiIso_bicechAug : QuasiIso (bicechAug 𝒲 F) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨exact_augSc 𝒲 F, mono_ε 𝒲 F⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [augSc, bicechAug])
        (by simpa [augSc, bicechComplex] using (bicechComplex_d 𝒲 F 0).symm)
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
      refine (ShortComplex.exact_iff_of_iso ?_).1 (exact_bicechSc 𝒲 F n)
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [bicechSc, bicechComplex]) (by simp [bicechSc, bicechComplex])
    · exact CochainComplex.exactAt_succ_single_obj _ _

end Exactness

end Langlands.AlgebraicGeometry.Modules.BiCech
