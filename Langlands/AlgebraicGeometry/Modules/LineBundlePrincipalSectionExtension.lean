import Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingProof

/-! # Extending line-bundle sections from a global principal open -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule.PrincipalSectionExtension

open SectionClearing

variable {X : Scheme.{u}} (L : LineBundle X) (f : Γ(X, ⊤))

private abbrev res {V W : X.Opens} (h : W ≤ V) : Γ(L.obj, V) →+ Γ(L.obj, W) :=
  (L.obj.presheaf.map (homOfLE h).op).hom

private abbrev fres (W : X.Opens) : Γ(X, W) :=
  X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op f

private lemma res_res {V W Z : X.Opens} (h : W ≤ V) (h' : Z ≤ W) (s : Γ(L.obj, V)) :
    res L h' (res L h s) = res L (h'.trans h) s :=
  modules_map_map L.obj h h' s

private lemma fres_res {V W : X.Opens} (h : W ≤ V) :
    X.presheaf.map (homOfLE h).op (fres f V) = fres f W :=
  presheaf_map_map X le_top h f

private lemma res_pow_smul {V W : X.Opens} (h : W ≤ V) (n : ℕ) (s : Γ(L.obj, V)) :
    res L h (fres f V ^ n • s) = fres f W ^ n • res L h s := by
  rw [res, Scheme.Modules.map_smul, map_pow, fres_res]

private lemma chart_zero {T : X.Opens}
    (e : L.obj.restrict T.ι ≅ structureModule T.toScheme) (W : X.Opens) (hW : W ≤ T) :
    chartE e W hW 0 = 0 := by
  have h := chartE_smul e W hW 0 0
  rwa [zero_smul, zero_mul] at h

private lemma extend_on_chart {T V : X.Opens}
    (e : L.obj.restrict T.ι ≅ structureModule T.toScheme)
    (hV : IsAffineOpen V) (hVT : V ≤ T) (s : Γ(L.obj, X.basicOpen f)) :
    ∃ (n : ℕ) (b : Γ(L.obj, V)),
      res L inf_le_left b =
        fres f (V ⊓ X.basicOpen f) ^ n • res L inf_le_right s := by
  let D := X.basicOpen f
  have hB : X.basicOpen (fres f V) = V ⊓ D := by
    rw [Scheme.basicOpen_res]
  let z := chartE e (V ⊓ D) (inf_le_left.trans hVT) (res L inf_le_right s)
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X V hV (fres f V)
    (X.presheaf.map (homOfLE hB.le).op z)
  have hy' : X.presheaf.map (homOfLE (inf_le_left : V ⊓ D ≤ V)).op y =
      fres f (V ⊓ D) ^ n * z := by
    have h := congrArg (fun a => X.presheaf.map (homOfLE hB.ge).op a) hy
    dsimp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] at h
    simpa only [map_mul, map_pow, presheaf_map_map, presheaf_map_id] using h
  refine ⟨n, chartF e V hVT y, ?_⟩
  apply (Function.LeftInverse.injective (chartF_chartE e (V ⊓ D)
    (inf_le_left.trans hVT)))
  rw [res, chartE_res e V (V ⊓ D) hVT inf_le_left,
    chartE_chartF e V hVT y, chartE_smul, ← hy']

private lemma kill_on_chart {T W : X.Opens}
    (e : L.obj.restrict T.ι ≅ structureModule T.toScheme) (hWT : W ≤ T)
    (hWc : IsCompact (W : Set X)) (b : Γ(L.obj, W))
    (hb : res L (inf_le_left : W ⊓ X.basicOpen f ≤ W) b = 0) :
    ∃ n : ℕ, fres f W ^ n • b = 0 := by
  have hB : X.basicOpen (fres f W) = W ⊓ X.basicOpen f := by
    rw [Scheme.basicOpen_res]
  have h0 : (chartE e W hWT b) |_ (X.basicOpen (fres f W)) = 0 := by
    change X.presheaf.map (homOfLE (X.basicOpen_le _)).op _ = 0
    rw [← chartE_res e W _ hWT (X.basicOpen_le _)]
    have hb' : res L (X.basicOpen_le (fres f W)) b = 0 := by
      rw [← res_res L inf_le_left hB.le, hb, map_zero]
    rw [show L.obj.presheaf.map (homOfLE (X.basicOpen_le (fres f W))).op b = 0 from hb',
      chart_zero]
  obtain ⟨n, hn⟩ :=
    exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hWc _ _ h0
  refine ⟨n, (Function.LeftInverse.injective (chartF_chartE e W hWT)) ?_⟩
  rw [chartE_smul, chart_zero, hn]

private lemma good_later (s : Γ(L.obj, X.basicOpen f)) {V : X.Opens} {n : ℕ}
    (b : Γ(L.obj, V))
    (hb : res L inf_le_left b =
      fres f (V ⊓ X.basicOpen f) ^ n • res L inf_le_right s) (k : ℕ) :
    res L inf_le_left (fres f V ^ k • b) =
      fres f (V ⊓ X.basicOpen f) ^ (n + k) • res L inf_le_right s := by
  rw [res_pow_smul, hb, smul_smul, ← pow_add, Nat.add_comm k n]

private lemma kill_later {W : X.Opens} {b : Γ(L.obj, W)} {n : ℕ}
    (hb : fres f W ^ n • b = 0) {k : ℕ} (hk : n ≤ k) :
    fres f W ^ k • b = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, mul_comm, mul_smul, hb, smul_zero]

/-- A section of a line bundle on `D(f)` extends globally after multiplication
by some power of the global function `f`, on a compact quasi-separated scheme. -/
theorem exists_global [CompactSpace X] [QuasiSeparatedSpace X]
    (s : Γ(L.obj, X.basicOpen f)) :
    ∃ (n : ℕ) (t : GlobalSections L.obj),
      res L (X.basicOpen_le f) t = fres f (X.basicOpen f) ^ n • s := by
  choose T hxT he using L.property
  let e (x : X) := (he x).some
  have hV : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ T x := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVT⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hxT x) (T x).2
    exact ⟨V, hV, hxV, hVT⟩
  choose V hVa hxV hVT using hV
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).2) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have hcov : ∀ y : X, ∃ i : I, y ∈ V i.1 := fun y => by
    have hy := hI (Set.mem_univ y)
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    exact ⟨⟨x, hx⟩, hyx⟩
  let D := X.basicOpen f
  have h1 : ∀ i : I, ∀ᶠ n in Filter.atTop, ∃ b : Γ(L.obj, V i.1),
      res L inf_le_left b = fres f (V i.1 ⊓ D) ^ n • res L inf_le_right s := fun i => by
    obtain ⟨n₀, b₀, hb₀⟩ := extend_on_chart L f (e i.1) (hVa i.1) (hVT i.1) s
    refine Filter.eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact ⟨_, good_later L f s b₀ hb₀ k⟩
  obtain ⟨n, hn⟩ := (Filter.eventually_all.2 h1).exists
  choose b hb using hn
  have h2 : ∀ ij : I × I, ∀ᶠ k in Filter.atTop,
      fres f (V ij.1.1 ⊓ V ij.2.1) ^ k •
        (res L inf_le_left (b ij.1) - res L inf_le_right (b ij.2)) = 0 := fun ij => by
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := ij
    have hcpt : IsCompact ((V i ⊓ V j : X.Opens) : Set X) :=
      (hVa i).isCompact.inter_of_isOpen (hVa j).isCompact (V i).2 (V j).2
    have hd : res L (inf_le_left : V i ⊓ V j ⊓ D ≤ V i ⊓ V j)
        (res L inf_le_left (b ⟨i, hi⟩) - res L inf_le_right (b ⟨j, hj⟩)) = 0 := by
      rw [map_sub, res_res, res_res]
      have e1 := congrArg (res L
        (show V i ⊓ V j ⊓ D ≤ V i ⊓ D from inf_le_inf_right D inf_le_left)) (hb ⟨i, hi⟩)
      have e2 := congrArg (res L
        (show V i ⊓ V j ⊓ D ≤ V j ⊓ D from inf_le_inf_right D inf_le_right)) (hb ⟨j, hj⟩)
      dsimp only at e1 e2
      rw [res_pow_smul, res_res, res_res] at e1 e2
      rw [e1, e2, sub_self]
    obtain ⟨k₀, hk₀⟩ := kill_on_chart L f (e i) (inf_le_left.trans (hVT i)) hcpt _ hd
    exact Filter.eventually_atTop.2 ⟨k₀, fun k hk => kill_later L f hk₀ hk⟩
  obtain ⟨k, hk⟩ := (Filter.eventually_all.2 h2).exists
  let F : TopCat.Sheaf Ab X := ⟨L.obj.presheaf, L.obj.isSheaf⟩
  let a' : ∀ i : I, Γ(L.obj, V i.1) := fun i => fres f (V i.1) ^ k • b i
  have hcompat : TopCat.Presheaf.IsCompatible F.1 (fun i : I => V i.1) a' := by
    intro i j
    have h := hk (i, j)
    rw [smul_sub, sub_eq_zero] at h
    change res L inf_le_left (fres f (V i.1) ^ k • b i) =
      res L inf_le_right (fres f (V j.1) ^ k • b j)
    simpa only [res_pow_smul] using h
  have hcover : (⊤ : X.Opens) ≤ iSup (fun i : I => V i.1) := by
    intro y _
    obtain ⟨i, hi⟩ := hcov y
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' (fun i : I => V i.1) ⊤
    (fun i => homOfLE le_top) hcover a' hcompat
  refine ⟨n + k, t, ?_⟩
  have hcoverD : D ≤ iSup (fun i : I => V i.1 ⊓ D) := by
    intro y hy
    obtain ⟨i, hi⟩ := hcov y
    exact Opens.mem_iSup.2 ⟨i, hi, hy⟩
  refine F.eq_of_locally_eq' (fun i : I => V i.1 ⊓ D) D (fun i => homOfLE inf_le_right)
    hcoverD _ _ (fun i => ?_)
  change res L inf_le_right (res L le_top t) =
    res L inf_le_right (fres f D ^ (n + k) • s)
  have hti : res L (le_top : V i.1 ≤ ⊤) t = a' i := ht i
  rw [res_res, res_pow_smul, ← res_res L (le_top : V i.1 ≤ ⊤) inf_le_left, hti]
  exact good_later L f s (b i) (hb i) k

/-- A chosen denominator-cleared global extension, recording its exponent and
its restriction equality. -/
def extension [CompactSpace X] [QuasiSeparatedSpace X]
    (s : Γ(L.obj, X.basicOpen f)) :
    {p : ℕ × GlobalSections L.obj //
      L.obj.presheaf.map (homOfLE (X.basicOpen_le f)).op p.2 =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ p.1 • s} :=
  ⟨⟨(exists_global L f s).choose, (exists_global L f s).choose_spec.choose⟩,
    (exists_global L f s).choose_spec.choose_spec⟩

end Langlands.SchemeModule.PrincipalSectionExtension
