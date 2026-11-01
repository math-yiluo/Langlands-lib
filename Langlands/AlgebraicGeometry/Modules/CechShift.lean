import Langlands.Cohomology.CechRefine
import Langlands.AlgebraicGeometry.Modules.CechDegreeOne

/-!
# Dimension shifting for ordered Čech cochains of Čech-acyclic modules

Let `M` be an `𝒪_P`-module whose Čech complexes for standard covers of affine opens are exact
(`AffineVanishing.IsCechAcyclic M`), and let `0 ⟶ M ⟶ I ⟶ Q ⟶ 0` be its embedding into the
chosen injective module `I = Injective.under M`. Then `Q` is again Čech-acyclic, `I` is flasque
so that its ordered Čech complexes for finite families are exact, and `I ⟶ Q` is surjective on
sections over affine opens. For a finite family `V` of opens whose finite intersections are
affine, a Čech cocycle `z` of `M` therefore becomes a coboundary `d t` in `I`, and `z` is a
coboundary as soon as the cocycle `π t` of `Q` is one (`exists_d_eq_of_shift`).

Two consequences are proved by induction on the degree, applying the induction hypothesis to
`Q`:

* `exists_d_eq_of_refine`: if a finite family `W` covering `P` refines `V`, a cocycle of `M` on
  `V` whose refinement to `W` is a coboundary is a coboundary on `V`;
* `exactAt_of_isZero`: if `V` covers `P` and `Hⁿ⁺¹(P, M) = 0` for `f : P ⟶ Spec R`, then the
  ordered Čech complex of `M` for `V` is exact in degree `n + 1`.

Finally, `exists_refine_sub_eq_d` shows that for a family `V` of affine opens, every
`1`-cocycle on a finite refinement covering `P` is cohomologous to the refinement of a
`1`-cocycle on `V`.
-/

universe w w' u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules.CechShift

open Langlands.Cohomology CechDegreeOne

section Presheaf

variable {T : TopCat.{u}} {ι : Type w} {U : ι → Opens T}

/-- The restrictions of one global section form a Čech `0`-cocycle. -/
lemma d_zero_res_top (F : TopCat.Presheaf AddCommGrpCat.{u} T) (s : F.obj (op ⊤)) :
    Cech.d F U 0 (fun _ => Cech.res le_top s) = 0 := by
  funext τ
  rw [Cech.d_apply, Fin.sum_univ_two]
  simp only [Cech.res_res, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    Pi.zero_apply]
  exact add_neg_eq_zero.2 rfl

/-- A Čech `0`-cocycle of a sheaf for a family covering the whole space is given by the
restrictions of a global section. -/
lemma exists_top_of_d_zero (F : TopCat.Sheaf AddCommGrpCat.{u} T) (hcov : ⊤ ≤ iSup U)
    {u : Cech.C F.1 U 0} (hu : Cech.d F.1 U 0 u = 0) :
    ∃ s : F.1.obj (op ⊤), ∀ σ, Cech.res le_top s = u σ := by
  have hσ : ∀ σ : Fin 1 → ι, σ = fun _ => σ 0 :=
    fun σ => funext fun i => congrArg σ (Subsingleton.elim i 0)
  have hcov' : (⊤ : Opens T) ≤ ⨆ σ : Fin 1 → ι, Cech.inter U σ := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov hx)
    exact Opens.mem_iSup.2 ⟨fun _ => i, (Cech.inter_const_one i).ge hi⟩
  refine Cech.exists_gluing F (fun σ : Fin 1 → ι => Cech.inter U σ) (fun _ => le_top) hcov' u
    fun σ σ' => ?_
  have h₁ : Cech.inter U σ ⊓ Cech.inter U σ' ≤ Cech.inter U (fun _ : Fin 1 => σ 0) :=
    inf_le_left.trans (le_of_eq (congrArg (Cech.inter U) (hσ σ)))
  have h₂ : Cech.inter U σ ⊓ Cech.inter U σ' ≤ Cech.inter U (fun _ : Fin 1 => σ' 0) :=
    inf_le_right.trans (le_of_eq (congrArg (Cech.inter U) (hσ σ')))
  calc Cech.res inf_le_left (u σ) = Cech.res h₁ (u fun _ => σ 0) :=
        Cech.res_congr _ _ (hσ σ) u _ _
    _ = Cech.res h₂ (u fun _ => σ' 0) :=
        AffineVanishing.res_eq_res_of_d_zero_eq_zero hu _ _ _ _
    _ = Cech.res inf_le_right (u σ') := (Cech.res_congr _ _ (hσ σ') u _ _).symm

end Presheaf

variable {P : Scheme.{u}}

section Modules

variable (M : P.Modules) {ι : Type w} (V : ι → P.Opens)

/-- The map of Čech cochains induced by the embedding of `M` into its injective hull. -/
noncomputable abbrev mapι (p : ℕ) :
    Cech.C M.presheaf V p →+ Cech.C (Injective.under M).presheaf V p :=
  Cech.map V (Injective.ι M).mapPresheaf p

/-- The map of Čech cochains induced by the projection of the injective hull of `M` onto the
cokernel of the embedding. -/
noncomputable abbrev mapπ (p : ℕ) :
    Cech.C (Injective.under M).presheaf V p →+ Cech.C (cokernel (Injective.ι M)).presheaf V p :=
  Cech.map V (cokernel.π (Injective.ι M)).mapPresheaf p

variable {M V}

lemma mapπ_mapι (p : ℕ) (c : Cech.C M.presheaf V p) : mapπ M V p (mapι M V p c) = 0 := by
  funext σ
  exact π_app_ι_app M _ (c σ)

lemma mapι_injective (p : ℕ) : Function.Injective (mapι M V p) := by
  intro a b h
  funext σ
  exact ι_app_injective M _ (congrFun h σ)

lemma exists_mapι_eq {p : ℕ} (b : Cech.C (Injective.under M).presheaf V p)
    (hb : mapπ M V p b = 0) : ∃ a, mapι M V p a = b := by
  choose a ha using fun σ => exists_ι_app_eq M (b σ) (congrFun hb σ)
  exact ⟨a, funext ha⟩

lemma exists_mapπ_eq (hM : AffineVanishing.IsCechAcyclic M) {p : ℕ}
    (hV : ∀ σ : Fin (p + 1) → ι, IsAffineOpen (Cech.inter V σ))
    (c : Cech.C (cokernel (Injective.ι M)).presheaf V p) : ∃ b, mapπ M V p b = c := by
  choose b hb using fun σ => π_app_surjective M hM (hV σ) (c σ)
  exact ⟨b, funext hb⟩

variable (M V) in
/-- The ordered Čech complex of the injective hull for a finite family is exact in positive
degrees, since injective modules are flasque. -/
lemma exactAt_injective [Finite ι] (p : ℕ) : Cech.ExactAt (Injective.under M).presheaf V p := by
  have : TopCat.Presheaf.IsFlasque
      ((PushforwardInjectiveAcyclic.toAbSheaf P).obj (Injective.under M)).1 :=
    PushforwardInjectiveAcyclic.isFlasque_of_injective (Injective.under M)
  exact Cech.exactAt_of_isFlasque ((PushforwardInjectiveAcyclic.toAbSheaf P).obj
    (Injective.under M)) V p

/-- The dimension shift: if `ι z = d t` for a Čech `(p + 2)`-cochain `z` of `M`, and the image
`π t` of `t` in the cokernel is a coboundary `d r`, then `z` is a coboundary. The finite
intersections of `p + 1` members of `V` must be affine, so that `r` lifts along `π`. -/
theorem exists_d_eq_of_shift (hM : AffineVanishing.IsCechAcyclic M) {p : ℕ}
    (hV : ∀ σ : Fin (p + 1) → ι, IsAffineOpen (Cech.inter V σ))
    {z : Cech.C M.presheaf V (p + 2)} {t : Cech.C (Injective.under M).presheaf V (p + 1)}
    (ht : Cech.d _ V (p + 1) t = mapι M V (p + 2) z)
    {r : Cech.C (cokernel (Injective.ι M)).presheaf V p}
    (hr : Cech.d _ V p r = mapπ M V (p + 1) t) :
    ∃ y : Cech.C M.presheaf V (p + 1), Cech.d _ V (p + 1) y = z := by
  obtain ⟨r', rfl⟩ := exists_mapπ_eq hM hV r
  obtain ⟨y, hy⟩ := exists_mapι_eq (t - Cech.d _ V p r') (by
    rw [map_sub, ← Cech.d_map, hr, sub_self])
  refine ⟨y, mapι_injective (p + 2) ?_⟩
  rw [← Cech.d_map, hy, map_sub, Cech.d_d, sub_zero, ht]

end Modules

section Refine

variable {ι : Type w} {V : ι → P.Opens} {κ : Type w'} {W : κ → P.Opens} {β : κ → ι}
  (hβ : ∀ j, W j ≤ V (β j))

/-- Refinement injectivity for Čech-acyclic modules: let `V` be a finite family of opens whose
finite intersections are affine and `W` a finite family covering `P` and refining `V`. A
Čech `(p + 1)`-cocycle of `M` on `V` whose refinement to `W` is a coboundary is a coboundary. -/
theorem exists_d_eq_of_refine [Finite ι] [Finite κ]
    (hV : ∀ (n : ℕ) (σ : Fin (n + 1) → ι), IsAffineOpen (Cech.inter V σ))
    (hcov : ⊤ ≤ iSup W) (p : ℕ) :
    ∀ (M : P.Modules), AffineVanishing.IsCechAcyclic M →
      ∀ z : Cech.C M.presheaf V (p + 1), Cech.d _ V (p + 1) z = 0 →
      ∀ c : Cech.C M.presheaf W p, Cech.refine _ V W β hβ (p + 1) z = Cech.d _ W p c →
      ∃ y : Cech.C M.presheaf V p, Cech.d _ V p y = z := by
  induction p with
  | zero =>
    intro M _ z hz c hc
    exact Cech.exists_d_eq_of_refine_eq_d ((PushforwardInjectiveAcyclic.toAbSheaf P).obj M) hβ
      hcov hz hc
  | succ p ih =>
    intro M hM z hz c hc
    obtain ⟨t, ht⟩ := exactAt_injective M V (p + 1) (mapι M V (p + 2) z) (by
      rw [Cech.d_map, hz, map_zero])
    obtain ⟨s, hs⟩ := exactAt_injective M W p
      (Cech.refine _ V W β hβ (p + 1) t - mapι M W (p + 1) c) (by
        rw [map_sub, Cech.d_refine, ht, Cech.d_map, ← hc, Cech.map_refine, sub_self])
    obtain ⟨r, hr⟩ := ih (cokernel (Injective.ι M))
      (AffineVanishing.isCechAcyclic_X₃ (PushforwardInjectiveAcyclic.injectiveSc_shortExact M) hM)
      (mapπ M V (p + 1) t) (by rw [Cech.d_map, ht, mapπ_mapι])
      (mapπ M W p s) (by
        rw [← Cech.map_refine, Cech.d_map, hs, map_sub, mapπ_mapι, sub_zero])
    exact exists_d_eq_of_shift hM (hV p) ht hr

/-- Degree-one refinement surjectivity: let the members of `V` be affine and let a finite family
`W` cover `P` and refine `V`. Every `1`-cocycle of a Čech-acyclic module `M` on `W` is, up to a
coboundary, the refinement of a `1`-cocycle on `V`. -/
theorem exists_refine_sub_eq_d [Finite κ] {M : P.Modules} (hM : AffineVanishing.IsCechAcyclic M)
    (hV : ∀ σ : Fin 1 → ι, IsAffineOpen (Cech.inter V σ)) (hcov : ⊤ ≤ iSup W)
    {w : Cech.C M.presheaf W 1} (hw : Cech.d _ W 1 w = 0) :
    ∃ w' : Cech.C M.presheaf V 1, Cech.d _ V 1 w' = 0 ∧
      ∃ g : Cech.C M.presheaf W 0, Cech.refine _ V W β hβ 1 w' - w = Cech.d _ W 0 g := by
  obtain ⟨t, ht⟩ := exactAt_injective M W 0 (mapι M W 1 w) (by rw [Cech.d_map, hw, map_zero])
  have hdt : Cech.d _ W 0 (mapπ M W 0 t) = 0 := by rw [Cech.d_map, ht, mapπ_mapι]
  obtain ⟨q, hq⟩ : ∃ q : Γ(cokernel (Injective.ι M), ⊤),
      ∀ σ, Cech.res le_top q = mapπ M W 0 t σ :=
    exists_top_of_d_zero ((PushforwardInjectiveAcyclic.toAbSheaf P).obj
      (cokernel (Injective.ι M))) hcov hdt
  obtain ⟨s, hs⟩ := exists_mapπ_eq hM hV (fun σ => Cech.res le_top q)
  obtain ⟨w', hw'⟩ := exists_mapι_eq (Cech.d _ V 0 s) (by
    rw [← Cech.d_map, hs]
    exact d_zero_res_top (cokernel (Injective.ι M)).presheaf q)
  have hw'' : mapι M V 1 w' = Cech.d _ V 0 s := hw'
  obtain ⟨g, hg⟩ := exists_mapι_eq (Cech.refine _ V W β hβ 0 s - t) (by
    rw [map_sub, Cech.map_refine, hs]
    funext σ
    rw [Pi.sub_apply, Cech.refine_apply, Cech.res_res, ← hq σ]
    exact sub_self _)
  refine ⟨w', mapι_injective 2 ?_, g, mapι_injective 1 ?_⟩
  · rw [← Cech.d_map, hw'', Cech.d_d, map_zero]
  · rw [← Cech.d_map, hg, map_sub, map_sub, Cech.map_refine, hw'', Cech.d_refine, ← ht]

end Refine

section Vanishing

variable {ι : Type w} {V : ι → P.Opens}

/-- Derived vanishing implies Čech vanishing: let `V` be a finite family of opens covering `P`
whose finite intersections are affine. If `Hᵖ⁺¹(P, M) = 0` for a Čech-acyclic module `M`, then
the ordered Čech complex of `M` for `V` is exact in degree `p + 1`. -/
theorem exactAt_of_isZero {R : CommRingCat.{u}} (f : P ⟶ Spec R) [Finite ι]
    (hV : ∀ (n : ℕ) (σ : Fin (n + 1) → ι), IsAffineOpen (Cech.inter V σ))
    (hcov : ⊤ ≤ iSup V) (p : ℕ) :
    ∀ (M : P.Modules), AffineVanishing.IsCechAcyclic M →
      IsZero ((DerivedSections.relativeCohomology f (p + 1)).obj M) →
      Cech.ExactAt M.presheaf V p := by
  let := HasDerivedCategory.standard P.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let F := DerivedSections.relativeGlobalSections f
  induction p with
  | zero =>
    intro M _ h₁ z hz
    obtain ⟨t, ht⟩ := exactAt_injective M V 0 (mapι M V 1 z) (by
      rw [Cech.d_map, hz, map_zero])
    have hdt : Cech.d _ V 0 (mapπ M V 0 t) = 0 := by rw [Cech.d_map, ht, mapπ_mapι]
    obtain ⟨q, hq⟩ := exists_top_of_d_zero
      ((PushforwardInjectiveAcyclic.toAbSheaf P).obj (cokernel (Injective.ι M))) hcov hdt
    have hS := PushforwardInjectiveAcyclic.injectiveSc_shortExact M
    have hE := (DerivedPlus.shortExact_map_of_isZero_rightDerived_one F hS h₁).epi_g
    obtain ⟨T, hT'⟩ : ∃ T : Γ(Injective.under M, ⊤), (cokernel.π (Injective.ι M)).app ⊤ T = q :=
      (ModuleCat.epi_iff_surjective _).1 hE q
    obtain ⟨y, hy⟩ := exists_mapι_eq (t - fun _ => Cech.res le_top T) (by
      rw [map_sub]
      funext σ
      change mapπ M V 0 t σ - (cokernel.π (Injective.ι M)).app _ (Cech.res le_top T) = 0
      rw [app_res, hT']
      exact sub_eq_zero.2 (hq σ).symm)
    refine ⟨y, mapι_injective 1 ?_⟩
    rw [← Cech.d_map, hy, map_sub, d_zero_res_top, sub_zero, ht]
  | succ p ih =>
    intro M hM h z hz
    have hS := PushforwardInjectiveAcyclic.injectiveSc_shortExact M
    obtain ⟨t, ht⟩ := exactAt_injective M V (p + 1) (mapι M V (p + 2) z) (by
      rw [Cech.d_map, hz, map_zero])
    have hQ : IsZero ((DerivedSections.relativeCohomology f (p + 1)).obj
        (cokernel (Injective.ι M))) := by
      have := DerivedPlus.mono_rightDerivedδ_of_isZero F hS (p + 1) (p + 2) rfl
        (F.isZero_rightDerived_obj_injective_succ p (Injective.under M))
      have hQ' : IsZero ((F.rightDerived (p + 1)).obj (cokernel (Injective.ι M))) :=
        IsZero.of_mono (DerivedPlus.rightDerivedδ F hS (p + 1) (p + 2) rfl) h
      exact hQ'
    obtain ⟨r, hr⟩ := ih (cokernel (Injective.ι M))
      (AffineVanishing.isCechAcyclic_X₃ hS hM) hQ (mapπ M V (p + 1) t) (by
        rw [Cech.d_map, ht, mapπ_mapι])
    exact exists_d_eq_of_shift hM (hV p) ht hr

end Vanishing

end Langlands.AlgebraicGeometry.Modules.CechShift
