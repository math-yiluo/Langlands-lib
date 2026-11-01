import Langlands.AlgebraicGeometry.Picard.QuasiAffineLineBundleFiniteSectionStatement
import Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingProof
import Langlands.AlgebraicGeometry.Modules.SectionCoefficients

/-! # Sections of a quasi-affine line bundle generating at finitely many points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Langlands.SchemeModule Langlands.SchemeModule.SectionClearing Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.QuasiAffineFiniteSection

variable {X : Scheme.{u}}

/-! ### Chart lemmas -/

section Chart

variable {M : X.Modules} {T : X.Opens} (Ψ : M.restrict T.ι ≅ structureSheaf T.toScheme)

/-- Coordinates send zero to zero. -/
lemma chartE_zero (W : X.Opens) (hW : W ≤ T) : chartE Ψ W hW 0 = 0 := by
  have h := chartE_smul Ψ W hW 0 0
  rwa [zero_smul, zero_mul] at h

/-- Coordinates are injective. -/
lemma chartE_injective (W : X.Opens) (hW : W ≤ T) : Function.Injective (chartE Ψ W hW) :=
  Function.LeftInverse.injective (chartF_chartE Ψ W hW)

/-- The section with coordinate `z` is `z` times the section with coordinate one. -/
lemma chartF_eq_smul (W : X.Opens) (hW : W ≤ T) (z : Γ(X, W)) :
    chartF Ψ W hW z = z • chartF Ψ W hW 1 := by
  apply chartE_injective Ψ W hW
  rw [chartE_smul, chartE_chartF, chartE_chartF, mul_one]

/-- The section with a given coordinate commutes with restriction. -/
lemma chartF_res (W₁ W₂ : X.Opens) (h₁ : W₁ ≤ T) (h : W₂ ≤ W₁) (z : Γ(X, W₁)) :
    M.presheaf.map (homOfLE h).op (chartF Ψ W₁ h₁ z) =
      chartF Ψ W₂ (h.trans h₁) (X.presheaf.map (homOfLE h).op z) := by
  apply chartE_injective Ψ W₂ (h.trans h₁)
  rw [chartE_res Ψ W₁ W₂ h₁ h, chartE_chartF, chartE_chartF]

/-- `chartF` is bijective. -/
lemma chartF_bijective (W : X.Opens) (hW : W ≤ T) : Function.Bijective (chartF Ψ W hW) :=
  ⟨Function.LeftInverse.injective (chartE_chartF Ψ W hW),
    Function.RightInverse.surjective (chartF_chartE Ψ W hW)⟩

end Chart

/-! ### Clearing a module section on a basic open -/

section Clearing

variable (M : X.Modules) (f : Γ(X, ⊤))

/-- The restriction of the global function `f` to an open. -/
abbrev fres (W : X.Opens) : Γ(X, W) := X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op f

/-- Restricting `f ^ k • d` restricts `d`. -/
lemma map_fres_pow_smul {W₁ W₂ : X.Opens} (h : W₂ ≤ W₁) (k : ℕ) (d : Γ(M, W₁)) :
    M.presheaf.map (homOfLE h).op ((fres f W₁) ^ k • d) =
      (fres f W₂) ^ k • M.presheaf.map (homOfLE h).op d := by
  rw [Scheme.Modules.map_smul, map_pow, presheaf_map_map]

/-- Multiplying a local solution by a power of `f` gives a local solution. -/
lemma good_smul {V : X.Opens} {n : ℕ} {b : Γ(M, V)} {t : Γ(M, X.basicOpen f)}
    (hb : M.presheaf.map (homOfLE (inf_le_left : V ⊓ X.basicOpen f ≤ V)).op b =
      (fres f (V ⊓ X.basicOpen f)) ^ n •
        M.presheaf.map (homOfLE (inf_le_right : V ⊓ X.basicOpen f ≤ X.basicOpen f)).op t)
    (k : ℕ) :
    M.presheaf.map (homOfLE (inf_le_left : V ⊓ X.basicOpen f ≤ V)).op ((fres f V) ^ k • b) =
      (fres f (V ⊓ X.basicOpen f)) ^ (n + k) •
        M.presheaf.map (homOfLE (inf_le_right : V ⊓ X.basicOpen f ≤ X.basicOpen f)).op t := by
  rw [map_fres_pow_smul, hb, smul_smul, ← pow_add, add_comm]

/-- On an affine open inside a trivializing open, a power of `f` clears `t`. -/
lemma exists_local {T : X.Opens} (Ψ : M.restrict T.ι ≅ structureSheaf T.toScheme)
    {V : X.Opens} (hV : IsAffineOpen V) (hVT : V ≤ T) (t : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (b : Γ(M, V)),
      M.presheaf.map (homOfLE (inf_le_left : V ⊓ X.basicOpen f ≤ V)).op b =
        (fres f (V ⊓ X.basicOpen f)) ^ n •
          M.presheaf.map (homOfLE (inf_le_right : V ⊓ X.basicOpen f ≤ X.basicOpen f)).op t := by
  have hB : X.basicOpen (fres f V) = V ⊓ X.basicOpen f := Scheme.basicOpen_res X f _
  let z : Γ(X, V ⊓ X.basicOpen f) := chartE Ψ (V ⊓ X.basicOpen f) (inf_le_left.trans hVT)
    (M.presheaf.map (homOfLE (inf_le_right : V ⊓ X.basicOpen f ≤ X.basicOpen f)).op t)
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X V hV (fres f V)
    (X.presheaf.map (homOfLE hB.le).op z)
  have hy' : X.presheaf.map (homOfLE (inf_le_left : V ⊓ X.basicOpen f ≤ V)).op y =
      (fres f (V ⊓ X.basicOpen f)) ^ n * z := by
    have := congrArg (fun w => X.presheaf.map (homOfLE hB.ge).op w) hy
    dsimp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] at this
    simp only [map_mul, map_pow, presheaf_map_map, presheaf_map_id] at this
    exact this
  refine ⟨n, chartF Ψ V hVT y, chartE_injective Ψ (V ⊓ X.basicOpen f) (inf_le_left.trans hVT) ?_⟩
  rw [chartF_res, chartE_chartF, chartE_smul, hy']

/-- A section vanishing on `W ⊓ D(f)` over a quasi-compact `W` inside a trivializing open is
killed by a power of `f`. -/
lemma exists_pow_smul_eq_zero {T : X.Opens} (Ψ : M.restrict T.ι ≅ structureSheaf T.toScheme)
    {W : X.Opens} (hW : W ≤ T) (hWc : IsCompact (W : Set X)) (d : Γ(M, W))
    (hd : M.presheaf.map (homOfLE (inf_le_left : W ⊓ X.basicOpen f ≤ W)).op d = 0) :
    ∃ k : ℕ, (fres f W) ^ k • d = 0 := by
  have hB : X.basicOpen (fres f W) = W ⊓ X.basicOpen f := Scheme.basicOpen_res X f _
  have h0 : (chartE Ψ W hW d) |_ (X.basicOpen (fres f W)) = 0 := by
    change X.presheaf.map (homOfLE (X.basicOpen_le _)).op (chartE Ψ W hW d) = 0
    rw [← chartE_res Ψ W _ hW (X.basicOpen_le _)]
    have : M.presheaf.map (homOfLE (X.basicOpen_le (fres f W))).op d = 0 := by
      rw [← modules_map_map M (inf_le_left : W ⊓ X.basicOpen f ≤ W) hB.le, hd, map_zero]
    rw [this, chartE_zero]
  obtain ⟨k, hk⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hWc _ _ h0
  refine ⟨k, chartE_injective Ψ W hW ?_⟩
  rw [chartE_smul, chartE_zero, hk]

/-- On a quasi-compact quasi-separated scheme, for a module sheaf locally isomorphic to the
structure module, every section over the basic open of a global function `f` becomes the
restriction of a global section after multiplication by a power of `f`. -/
theorem exists_global_smul_pow [CompactSpace X] [QuasiSeparatedSpace X]
    (hM : ∀ x : X, ∃ T : X.Opens, x ∈ T ∧
      Nonempty (M.restrict T.ι ≅ structureSheaf T.toScheme))
    (t : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (a : Γ(M, ⊤)),
      M.presheaf.map (homOfLE (le_top : X.basicOpen f ≤ ⊤)).op a =
        (fres f (X.basicOpen f)) ^ n • t := by
  choose T hxT hΨ using hM
  have hV : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ T x := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVT⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hxT x) (T x).2
    exact ⟨V, hV, hxV, hVT⟩
  choose V hVa hxV hVT using hV
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).2) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have hcov : ∀ y : X, ∃ i : s, y ∈ V i.1 := fun y => by
    have hy := hs (Set.mem_univ y)
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    exact ⟨⟨x, hx⟩, hyx⟩
  -- Step 1: local solutions with a common exponent.
  have h1 : ∀ i : s, ∀ᶠ n in Filter.atTop, ∃ b : Γ(M, V i.1),
      M.presheaf.map (homOfLE (inf_le_left : V i.1 ⊓ X.basicOpen f ≤ V i.1)).op b =
        (fres f (V i.1 ⊓ X.basicOpen f)) ^ n •
          M.presheaf.map
            (homOfLE (inf_le_right : V i.1 ⊓ X.basicOpen f ≤ X.basicOpen f)).op t :=
    fun i => by
      obtain ⟨n₀, b₀, hb₀⟩ := exists_local M f (hΨ i.1).some (hVa i.1) (hVT i.1) t
      refine Filter.eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      exact ⟨_, good_smul M f hb₀ k⟩
  obtain ⟨e, he⟩ := (Filter.eventually_all.2 h1).exists
  choose b hb using he
  -- Step 2: kill the differences on the overlaps.
  have h2 : ∀ ij : s × s, ∀ᶠ k in Filter.atTop,
      (fres f (V ij.1.1 ⊓ V ij.2.1)) ^ k •
        (M.presheaf.map (homOfLE (inf_le_left : V ij.1.1 ⊓ V ij.2.1 ≤ V ij.1.1)).op (b ij.1) -
          M.presheaf.map (homOfLE (inf_le_right : V ij.1.1 ⊓ V ij.2.1 ≤ V ij.2.1)).op
            (b ij.2)) = 0 := fun ij => by
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := ij
    have hcpt : IsCompact ((V i ⊓ V j : X.Opens) : Set X) :=
      (hVa i).isCompact.inter_of_isOpen (hVa j).isCompact (V i).2 (V j).2
    have hd : M.presheaf.map
        (homOfLE (inf_le_left : V i ⊓ V j ⊓ X.basicOpen f ≤ V i ⊓ V j)).op
        (M.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b ⟨i, hi⟩) -
          M.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b ⟨j, hj⟩)) = 0 := by
      rw [map_sub, modules_map_map, modules_map_map]
      have e1 := congrArg (fun z => M.presheaf.map
        (homOfLE (show V i ⊓ V j ⊓ X.basicOpen f ≤ V i ⊓ X.basicOpen f from
          inf_le_inf_right _ inf_le_left)).op z) (hb ⟨i, hi⟩)
      have e2 := congrArg (fun z => M.presheaf.map
        (homOfLE (show V i ⊓ V j ⊓ X.basicOpen f ≤ V j ⊓ X.basicOpen f from
          inf_le_inf_right _ inf_le_right)).op z) (hb ⟨j, hj⟩)
      simp only [modules_map_map, map_fres_pow_smul] at e1 e2
      rw [e1, e2, sub_self]
    obtain ⟨k₀, hk₀⟩ := exists_pow_smul_eq_zero M f (hΨ i).some (inf_le_left.trans (hVT i))
      hcpt _ hd
    refine Filter.eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, mul_comm, mul_smul, hk₀, smul_zero]
  obtain ⟨k, hk⟩ := (Filter.eventually_all.2 h2).exists
  -- Step 3: glue.
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  let a' : ∀ i : s, Γ(M, V i.1) := fun i => (fres f (V i.1)) ^ k • b i
  have hcompat : TopCat.Presheaf.IsCompatible F.1 (fun i : s => V i.1) a' := by
    intro i j
    have := hk (i, j)
    rw [smul_sub, sub_eq_zero, ← map_fres_pow_smul, ← map_fres_pow_smul] at this
    exact this
  have hcover : (⊤ : X.Opens) ≤ iSup (fun i : s => V i.1) := by
    intro y _
    obtain ⟨i, hi⟩ := hcov y
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨a, ha, -⟩ := F.existsUnique_gluing' (fun i : s => V i.1) ⊤
    (fun i => homOfLE le_top) hcover a' hcompat
  refine ⟨e + k, a, ?_⟩
  have hcoverU : X.basicOpen f ≤ iSup (fun i : s => V i.1 ⊓ X.basicOpen f) := by
    intro y hy
    obtain ⟨i, hi⟩ := hcov y
    exact Opens.mem_iSup.2 ⟨i, hi, hy⟩
  refine F.eq_of_locally_eq' (fun i : s => V i.1 ⊓ X.basicOpen f) (X.basicOpen f)
    (fun i => homOfLE inf_le_right) hcoverU _ _ (fun i => ?_)
  change M.presheaf.map (homOfLE inf_le_right).op
      (M.presheaf.map (homOfLE le_top).op a) =
    M.presheaf.map (homOfLE inf_le_right).op ((fres f (X.basicOpen f)) ^ (e + k) • t)
  have hai : M.presheaf.map (homOfLE (le_top : V i.1 ≤ ⊤)).op a = a' i := ha i
  rw [modules_map_map, map_fres_pow_smul,
    ← modules_map_map M (le_top : V i.1 ≤ ⊤) inf_le_left, hai]
  exact good_smul M f (hb i) k

end Clearing

/-! ### A section generating at one point -/

/-- On a quasi-affine scheme, every point lies in the generation open of some global
section of a line bundle. -/
theorem exists_mem_trivializationOpen [X.IsQuasiAffine] (L : LineBundle X) (x : X) :
    ∃ s : GlobalSections L.obj, x ∈ trivializationOpen L.obj s := by
  obtain ⟨T, hxT, ⟨e⟩⟩ := L.property x
  let Ψ : L.obj.restrict T.ι ≅ structureSheaf T.toScheme := e
  obtain ⟨_, ⟨_, ⟨f, -, rfl⟩, rfl⟩, hxf, hfT⟩ :=
    (Scheme.IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open hxT T.2
  have hfT' : X.basicOpen f ≤ T := hfT
  have hM : ∀ y : X, ∃ T : X.Opens, y ∈ T ∧
      Nonempty (L.obj.restrict T.ι ≅ structureSheaf T.toScheme) := fun y => by
    obtain ⟨T, hyT, ⟨e⟩⟩ := L.property y
    exact ⟨T, hyT, ⟨e⟩⟩
  obtain ⟨n, a, ha⟩ :=
    exists_global_smul_pow L.obj f hM (chartF Ψ (X.basicOpen f) hfT' 1)
  refine ⟨a, le_trivializationOpen_of_bijective L.obj a (B := X.basicOpen f) ?_ hxf⟩
  intro V hV
  have hVT : V ≤ T := hV.trans hfT'
  have hres : sectionRes L.obj a V = (fres f V) ^ n • chartF Ψ V hVT 1 := by
    rw [← sectionRes_res L.obj a hV]
    change L.obj.presheaf.map (homOfLE hV).op
      (L.obj.presheaf.map (homOfLE (le_top : X.basicOpen f ≤ ⊤)).op a) = _
    rw [ha, map_fres_pow_smul, chartF_res, map_one]
  have hunit : IsUnit ((fres f V) ^ n) := by
    refine IsUnit.pow n ?_
    have hB := X.toRingedSpace.isUnit_res_basicOpen f
    have := hB.map (X.presheaf.map (homOfLE hV).op).hom
    change IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op ≫
      X.presheaf.map (homOfLE hV).op) f) at this
    rw [← Functor.map_comp] at this
    exact this
  obtain ⟨u, hu⟩ := hunit
  have hfun : (fun c : Γ(X, V) ↦ (sectionHom L.obj a).app V c) =
      chartF Ψ V hVT ∘ (fun c : Γ(X, V) ↦ c * (u : Γ(X, V))) := by
    funext c
    rw [Function.comp_apply, LineBundleDescent.sectionHom_app]
    change c • sectionRes L.obj a V = _
    rw [hres, smul_smul, hu, ← chartF_eq_smul]
  change Function.Bijective (fun c : Γ(X, V) ↦ (sectionHom L.obj a).app V c)
  rw [hfun]
  exact (chartF_bijective Ψ V hVT).comp (Units.mulRight u).bijective

/-! ### Adding a multiple of a second section -/

/-- In a local ring, a unit plus a nonunit is a unit. -/
lemma isUnit_add_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : IsUnit a) (hb : ¬IsUnit b) : IsUnit (a + b) := by
  by_contra h
  have hb' : -b ∈ nonunits R := by rwa [mem_nonunits_iff, IsUnit.neg_iff]
  have := IsLocalRing.nonunits_add h hb'
  rw [add_neg_cancel_right] at this
  exact this ha

/-- Adding a multiple `g • s'` with `g` vanishing at `x` preserves generation at `x`. -/
theorem mem_trivializationOpen_add_smul_of_mem (L : LineBundle X) {s : GlobalSections L.obj}
    (s' : GlobalSections L.obj) {g : Γ(X, ⊤)} {x : X}
    (hs : x ∈ trivializationOpen L.obj s) (hg : x ∉ X.basicOpen g) :
    x ∈ trivializationOpen L.obj (s + g • s') := by
  set U := trivializationOpen L.obj s
  obtain ⟨c, hc⟩ := exists_smul_sectionRes_eq (M := L.obj) (le_refl U) (sectionRes L.obj s' U)
  have hrel : (1 + fres g U * c) • sectionRes L.obj s U = sectionRes L.obj (s + g • s') U := by
    rw [add_smul, one_smul, mul_smul, hc]
    simp only [sectionRes, map_add, Scheme.Modules.map_smul]
  have hB := basicOpen_coeff_eq (M := L.obj) (le_refl U) hrel
  have hx : x ∈ X.basicOpen (1 + fres g U * c) := by
    rw [Scheme.mem_basicOpen X _ x hs, map_add, map_one, map_mul]
    refine isUnit_add_of_not_isUnit isUnit_one ?_
    intro h
    apply hg
    rw [Scheme.mem_basicOpen_top X g x]
    have := isUnit_of_mul_isUnit_left h
    rwa [TopCat.Presheaf.germ_res_apply] at this
  rw [hB] at hx
  exact hx.2

/-- If `s` does not generate at `x` but `s'` and `g` do, then `s + g • s'` generates at `x`. -/
theorem mem_trivializationOpen_add_smul_of_not_mem (L : LineBundle X)
    {s s' : GlobalSections L.obj} {g : Γ(X, ⊤)} {x : X}
    (hs : x ∉ trivializationOpen L.obj s) (hg : x ∈ X.basicOpen g)
    (hs' : x ∈ trivializationOpen L.obj s') :
    x ∈ trivializationOpen L.obj (s + g • s') := by
  set U := trivializationOpen L.obj s'
  obtain ⟨c, hc⟩ := exists_smul_sectionRes_eq (M := L.obj) (le_refl U) (sectionRes L.obj s U)
  have hcB := basicOpen_coeff_eq (M := L.obj) (le_refl U) hc
  have hrel : (c + fres g U) • sectionRes L.obj s' U = sectionRes L.obj (s + g • s') U := by
    rw [add_smul, hc]
    simp only [sectionRes, map_add, Scheme.Modules.map_smul]
  have hB := basicOpen_coeff_eq (M := L.obj) (le_refl U) hrel
  have hx : x ∈ X.basicOpen (c + fres g U) := by
    rw [Scheme.mem_basicOpen X _ x hs', map_add, add_comm]
    refine isUnit_add_of_not_isUnit ?_ ?_
    · rw [TopCat.Presheaf.germ_res_apply]
      exact (Scheme.mem_basicOpen_top X g x).1 hg
    · intro h
      have hxc : x ∈ X.basicOpen c := (Scheme.mem_basicOpen X c x hs').2 h
      rw [hcB] at hxc
      exact hs hxc.2
  rw [hB] at hx
  exact hx.2

/-! ### Finite sets -/

/-- The global functions vanishing at a point. -/
def vanishingSet (x : X) : Set Γ(X, ⊤) := {g | x ∉ X.basicOpen g}

/-- On a quasi-affine scheme, let `y ≠ x` be points such that the vanishing set of `y` is
contained in that of `x` only if the two vanishing sets agree. Then some global function is
nonzero at `x` and zero at `y`. -/
lemma exists_separating [X.IsQuasiAffine] {x y : X} (hxy : y ≠ x)
    (h : vanishingSet y ⊆ vanishingSet x → vanishingSet x ⊆ vanishingSet y) :
    ∃ g : Γ(X, ⊤), x ∈ X.basicOpen g ∧ y ∉ X.basicOpen g := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have h1 : vanishingSet y ⊆ vanishingSet x := fun g hg hxg => hg (hcon g hxg)
  have h2 := h h1
  apply hxy
  apply Inseparable.eq
  rw [inseparable_iff_forall_isOpen]
  intro W hW
  constructor
  · intro hyW
    obtain ⟨_, ⟨_, ⟨g, -, rfl⟩, rfl⟩, hyg, hgW⟩ :=
      (Scheme.IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open hyW hW
    refine hgW ?_
    by_contra hxg
    exact h2 hxg hyg
  · intro hxW
    obtain ⟨_, ⟨_, ⟨g, -, rfl⟩, rfl⟩, hxg, hgW⟩ :=
      (Scheme.IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open hxW hW
    exact hgW (hcon g hxg)

/-- Every finite set of points of a quasi-affine scheme lies in the generation open of a
single global section of a line bundle. -/
theorem exists_forall_mem_trivializationOpen [X.IsQuasiAffine] (L : LineBundle X)
    (E : Finset X) :
    ∃ s : GlobalSections L.obj, ∀ x ∈ E, x ∈ trivializationOpen L.obj s := by
  classical
  induction E using Finset.strongInduction with
  | H E ih =>
    rcases E.eq_empty_or_nonempty with rfl | hE
    · exact ⟨0, by simp⟩
    obtain ⟨x, hxE, hmin⟩ := E.exists_minimalFor vanishingSet hE
    obtain ⟨s, hs⟩ := ih (E.erase x) (Finset.erase_ssubset hxE)
    by_cases hx : x ∈ trivializationOpen L.obj s
    · refine ⟨s, fun y hy => ?_⟩
      by_cases hyx : y = x
      · rw [hyx]
        exact hx
      · exact hs y (Finset.mem_erase.2 ⟨hyx, hy⟩)
    obtain ⟨s', hs'⟩ := exists_mem_trivializationOpen L x
    have hsep : ∀ y ∈ E.erase x, ∃ g : Γ(X, ⊤), x ∈ X.basicOpen g ∧ y ∉ X.basicOpen g := by
      intro y hy
      obtain ⟨hyx, hyE⟩ := Finset.mem_erase.1 hy
      exact exists_separating hyx (hmin hyE)
    choose! g hgx hgy using hsep
    let G : Γ(X, ⊤) := ∏ y ∈ E.erase x, g y
    have hGx : x ∈ X.basicOpen G := by
      refine Finset.prod_induction g (fun r => x ∈ X.basicOpen r) (fun r r' hr hr' => ?_) ?_ hgx
      · rw [Scheme.basicOpen_mul]
        exact ⟨hr, hr'⟩
      · rw [Scheme.basicOpen_one]
        trivial
    have hGy : ∀ y ∈ E.erase x, y ∉ X.basicOpen G := by
      intro y hy hyG
      have hG : G = g y * ∏ z ∈ (E.erase x).erase y, g z := (Finset.mul_prod_erase _ g hy).symm
      rw [hG, Scheme.basicOpen_mul] at hyG
      exact hgy y hy hyG.1
    refine ⟨s + G • s', fun y hy => ?_⟩
    by_cases hyx : y = x
    · rw [hyx]
      exact mem_trivializationOpen_add_smul_of_not_mem L hx hGx hs'
    · have hy' : y ∈ E.erase x := Finset.mem_erase.2 ⟨hyx, hy⟩
      exact mem_trivializationOpen_add_smul_of_mem L s' (hs y hy') (hGy y hy')

end Langlands.AlgebraicGeometry.Picard.QuasiAffineFiniteSection

namespace Langlands.AlgebraicGeometry.Picard

open QuasiAffineFiniteSection

/-- Every finite subset of a quasi-affine scheme lies in the generation open of a global
section of any line bundle. -/
theorem quasiAffineLineBundleFiniteSection :
    QuasiAffineLineBundleFiniteSectionStatement.{u} := by
  intro X _ L E hE
  obtain ⟨s, hs⟩ := exists_forall_mem_trivializationOpen L hE.toFinset
  exact ⟨s, fun x hx => hs x (hE.mem_toFinset.2 hx)⟩

end Langlands.AlgebraicGeometry.Picard
