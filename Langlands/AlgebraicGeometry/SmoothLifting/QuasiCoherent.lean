import Langlands.AlgebraicGeometry.SmoothLifting.DataIndep

/-! # Lifts along square-zero thickenings form a quasi-coherent module

For a smooth morphism `f`, the module of lifts based at `e` behaves like the global sections of a
quasi-coherent sheaf on `Spec C`: restriction to `C[1/c]` is a localization at the powers of `c`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace Langlands.AlgebraicGeometry.SmoothLifting

variable {X S : Scheme.{u}} {f : X ⟶ S} {C : CommRingCat.{u}} {I : Ideal C}
  {x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X} {s : Spec C ⟶ S}

/-- If two global lifts agree on `C[1/c]`, then some power of `c` identifies them in the module
of lifts. -/
theorem exists_pow_lin_eq_of_restr [Smooth f] (hI : SqZero I) (e : GLift f I x₀ s) (c : C)
    (x x' : GLift f I x₀ s) (h : restrC (Loc c) x.1 = restrC (Loc c) x'.1) :
    ∃ n : ℕ, LiftModule.lin hI e x e (c ^ n) 0 = LiftModule.lin hI e x' e (c ^ n) 0 := by
  classical
  obtain ⟨m, chs, hspan⟩ := exists_charts hI e.2.h₀
  have hT : ∀ i, ∃ M : ℕ, ∀ b, algebraMap C (Loc (chs i).g) c ^ M *
      ((chs i).grep hI _ (isUnit_loc _) x.2 b - (chs i).grep hI _ (isUnit_loc _) x'.2 b) = 0 := by
    intro i
    refine (chs i).exists_torsion_loc hI (chs i).g c (isUnit_loc _) (x.2.isLift _)
      (x'.2.isLift _) (res (chs i).g (Loc ((chs i).g * c))
        (isUnit_loc_of_dvd (dvd_mul_right _ _))) ?_
    have e1 := restr_restrC (res c (Loc ((chs i).g * c)) (isUnit_loc_of_dvd (dvd_mul_left c _)))
      x.1
    have e2 := restr_restrC (res c (Loc ((chs i).g * c)) (isUnit_loc_of_dvd (dvd_mul_left c _)))
      x'.1
    rw [restr_restrC, restr_restrC, ← e1, ← e2, h]
  choose M hM using hT
  refine ⟨Finset.univ.sup M, Subtype.ext ?_⟩
  refine IsGlobalLift.ext_grep hI chs hspan (LiftModule.lin hI e x e _ 0).2
    (LiftModule.lin hI e x' e _ 0).2 fun i b => ?_
  rw [LiftModule.grep_lin, LiftModule.grep_lin]
  have hle : M i ≤ Finset.univ.sup M := Finset.le_sup (Finset.mem_univ i)
  have h0 := hM i b
  rw [map_pow, ← Nat.sub_add_cancel hle, pow_add]
  linear_combination algebraMap C (Loc (chs i).g) c ^ (Finset.univ.sup M - M i) * h0

/-- Pairwise agreement of the local extensions on triple overlaps, and the resulting torsion. -/
theorem exists_pair_torsion [Smooth f] (hI : SqZero I) (e : GLift f I x₀ s) (c : C)
    {y : Spec (CommRingCat.of (Loc c)) ⟶ X} (hy : IsLift f I x₀ s (Loc c) y) (N : ℕ)
    (ch₁ ch₂ : Chart f I x₀ s) {z₁ : Spec (CommRingCat.of (Loc ch₁.g)) ⟶ X}
    {z₂ : Spec (CommRingCat.of (Loc ch₂.g)) ⟶ X} (hz₁ : IsLift f I x₀ s (Loc ch₁.g) z₁)
    (hz₂ : IsLift f I x₀ s (Loc ch₂.g) z₂)
    (h₁ : ∀ b, ch₁.repL hI (dvd_mul_right ch₁.g c) (rr (dvd_mul_right ch₁.g c) z₁) (hz₁.rr _) b =
      ch₁.repL hI (dvd_mul_right ch₁.g c) (rr (dvd_mul_right ch₁.g c)
        (restrC (Loc ch₁.g) e.1)) ((e.2.isLift _).rr _) b +
      algebraMap C (Loc (ch₁.g * c)) c ^ N *
        (ch₁.repL hI (dvd_mul_right ch₁.g c) (rr (dvd_mul_left c ch₁.g) y) (hy.rr _) b -
          ch₁.repL hI (dvd_mul_right ch₁.g c) (rr (dvd_mul_right ch₁.g c)
            (restrC (Loc ch₁.g) e.1)) ((e.2.isLift _).rr _) b))
    (h₂ : ∀ b, ch₂.repL hI (dvd_mul_right ch₂.g c) (rr (dvd_mul_right ch₂.g c) z₂) (hz₂.rr _) b =
      ch₂.repL hI (dvd_mul_right ch₂.g c) (rr (dvd_mul_right ch₂.g c)
        (restrC (Loc ch₂.g) e.1)) ((e.2.isLift _).rr _) b +
      algebraMap C (Loc (ch₂.g * c)) c ^ N *
        (ch₂.repL hI (dvd_mul_right ch₂.g c) (rr (dvd_mul_left c ch₂.g) y) (hy.rr _) b -
          ch₂.repL hI (dvd_mul_right ch₂.g c) (rr (dvd_mul_right ch₂.g c)
            (restrC (Loc ch₂.g) e.1)) ((e.2.isLift _).rr _) b)) :
    ∃ M : ℕ, ∀ b, algebraMap C (Loc (ch₁.g * ch₂.g)) c ^ M *
      (ch₁.repL hI (dvd_mul_right _ _) (rr (dvd_mul_right ch₁.g ch₂.g) z₁) (hz₁.rr _) b -
        ch₁.repL hI (dvd_mul_right _ _) (rr (dvd_mul_left ch₂.g ch₁.g) z₂) (hz₂.rr _) b) = 0 := by
  have d₁ : ch₁.g * c ∣ ch₁.g * ch₂.g * c := ⟨ch₂.g, by ring⟩
  have d₂ : ch₂.g * c ∣ ch₁.g * ch₂.g * c := ⟨ch₁.g, by ring⟩
  have d3 : ch₁.g * ch₂.g ∣ ch₁.g * ch₂.g * c := dvd_mul_right _ _
  have u₁ : IsUnit (algebraMap C (Loc (ch₁.g * ch₂.g * c)) ch₁.g) :=
    isUnit_loc_of_dvd ((dvd_mul_right _ _).trans d₁)
  have u₂ : IsUnit (algebraMap C (Loc (ch₁.g * ch₂.g * c)) ch₂.g) :=
    isUnit_loc_of_dvd ((dvd_mul_right _ _).trans d₂)
  have p₁ := fun b => ch₁.push_pair hI (dvd_refl _) d₁ (e.2.isLift _) hz₁ hy N h₁ b
  have p₂ := fun b => ch₂.push_pair hI (dvd_refl _) d₂ (e.2.isLift _) hz₂ hy N h₂ b
  -- the base and `y` restricted to the triple overlap
  have eb₁ : rr ((dvd_mul_right ch₁.g c).trans d₁) (restrC (Loc ch₁.g) e.1) =
      restrC (Loc (ch₁.g * ch₂.g * c)) e.1 := restr_restrC _ _
  have eb₂ : rr ((dvd_mul_right ch₂.g c).trans d₂) (restrC (Loc ch₂.g) e.1) =
      restrC (Loc (ch₁.g * ch₂.g * c)) e.1 := restr_restrC _ _
  have hE := e.2.isLift (Loc (ch₁.g * ch₂.g * c))
  have hY := hy.rr ((dvd_mul_left c ch₁.g).trans d₁)
  -- `z₂` on the triple overlap is a chart-`ch₂` combination, hence a chart-`ch₁` one
  have hc₂ : rr ((dvd_mul_right ch₂.g c).trans d₂) z₂ =
      ch₂.comb _ hI u₂ (restrC (Loc (ch₁.g * ch₂.g * c)) e.1) hE (fun _ : Unit =>
        rr ((dvd_mul_left c ch₁.g).trans d₁) y) (fun _ => hY)
        (fun _ => algebraMap C (Loc (ch₁.g * ch₂.g * c)) c ^ N) := by
    refine ch₂.eq_comb_of_rep hI u₂ (hz₂.rr _) _ _ _ _ _ fun b => ?_
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
    have := p₂ b
    rw [Chart.repL, Chart.repL, Chart.repL, ch₂.rep_congr hI _ ((e.2.isLift _).rr _) hE eb₂ b]
      at this
    exact this
  have hc₂' := hc₂.trans (ch₂.comb_eq _ hI ch₁ u₂ u₁ _ _ _ _ _)
  have hzeq : rr d3 (rr (dvd_mul_right ch₁.g ch₂.g) z₁) =
      rr d3 (rr (dvd_mul_left ch₂.g ch₁.g) z₂) := by
    rw [rr_rr _ _ ((dvd_mul_right ch₁.g c).trans d₁), rr_rr _ _ ((dvd_mul_right ch₂.g c).trans d₂),
      hc₂']
    refine ch₁.eq_comb_of_rep hI u₁ (hz₁.rr _) _ _ _ _ _ fun b => ?_
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
    have := p₁ b
    rw [Chart.repL, Chart.repL, Chart.repL, ch₁.rep_congr hI _ ((e.2.isLift _).rr _) hE eb₁ b]
      at this
    exact this
  obtain ⟨M, hM⟩ := ch₁.exists_torsion_loc hI (ch₁.g * ch₂.g) c (isUnit_loc_of_dvd
    (dvd_mul_right _ _)) (hz₁.rr _) (hz₂.rr _) _ hzeq
  exact ⟨M, hM⟩

/-- Gluing of the corrected local extensions: a global lift whose restriction to each
`C[1/gᵢ]` is `base + c^M (zᵢ - base)`. -/
theorem exists_glue_corrected [Smooth f] (hI : SqZero I) (e : GLift f I x₀ s) (c : C) {m : ℕ}
    (chs : Fin m → Chart f I x₀ s) (hspan : Ideal.span (Set.range fun i => (chs i).g) = ⊤)
    (z : ∀ i, Spec (CommRingCat.of (Loc (chs i).g)) ⟶ X)
    (hz : ∀ i, IsLift f I x₀ s (Loc (chs i).g) (z i)) (M : ℕ)
    (hM : ∀ i j b, algebraMap C (Loc ((chs i).g * (chs j).g)) c ^ M *
      ((chs i).repL hI (dvd_mul_right _ _) (rr (dvd_mul_right (chs i).g (chs j).g) (z i))
          ((hz i).rr _) b -
        (chs i).repL hI (dvd_mul_right _ _) (rr (dvd_mul_left (chs j).g (chs i).g) (z j))
          ((hz j).rr _) b) = 0) :
    ∃ x : GLift f I x₀ s, ∀ i, restrC (Loc (chs i).g) x.1 =
      (chs i).comb _ hI (isUnit_loc _) (restrC _ e.1) (e.2.isLift _) (fun _ : Unit => z i)
        (fun _ => hz i) (fun _ => algebraMap C (Loc (chs i).g) c ^ M) := by
  let w : ∀ i, Spec (CommRingCat.of (Loc (chs i).g)) ⟶ X := fun i =>
    (chs i).comb _ hI (isUnit_loc _) (restrC _ e.1) (e.2.isLift _) (fun _ : Unit => z i)
      (fun _ => hz i) (fun _ => algebraMap C (Loc (chs i).g) c ^ M)
  have hw : ∀ i, IsLift f I x₀ s _ (w i) := fun i => (chs i).comb_isLift _ hI _ _ _ _ _ _
  have hcompat : ∀ i j, rr (dvd_mul_right (chs i).g (chs j).g) (w i) =
      rr (dvd_mul_left (chs j).g (chs i).g) (w j) := by
    intro i j
    have dij : (chs i).g ∣ (chs i).g * (chs j).g := dvd_mul_right _ _
    have dji : (chs j).g ∣ (chs i).g * (chs j).g := dvd_mul_left _ _
    have ui : IsUnit (algebraMap C (Loc ((chs i).g * (chs j).g)) (chs i).g) := isUnit_loc_of_dvd dij
    have uj : IsUnit (algebraMap C (Loc ((chs i).g * (chs j).g)) (chs j).g) := isUnit_loc_of_dvd dji
    have hE := e.2.isLift (Loc ((chs i).g * (chs j).g))
    have ebi : rr dij (restrC (Loc (chs i).g) e.1) = restrC (Loc ((chs i).g * (chs j).g)) e.1 :=
      restr_restrC _ _
    have ebj : rr dji (restrC (Loc (chs j).g) e.1) = restrC (Loc ((chs i).g * (chs j).g)) e.1 :=
      restr_restrC _ _
    have ej : rr dji (w j) = (chs j).comb _ hI uj (restrC (Loc ((chs i).g * (chs j).g)) e.1) hE
        (fun _ : Unit => rr dji (z j)) (fun _ => (hz j).rr dji)
        (fun _ => algebraMap C (Loc ((chs i).g * (chs j).g)) c ^ M) := by
      refine ((chs j).comb_restr hI _ (isUnit_loc _) uj _ _ _ _ _).trans ?_
      exact (chs j).comb_congr hI uj _ _ ebj _ _ rfl
        (funext fun _ => by rw [map_pow, AlgHom.commutes])
    have ej' := ej.trans ((chs j).comb_eq _ hI (chs i) uj ui _ _ _ _ _)
    refine (chs i).eq_of_rep hI ui ((hw i).rr dij) ((hw j).rr dji) fun b => ?_
    rw [(chs i).rep_congr hI ui ((hw j).rr dji) ((chs i).comb_isLift _ hI ui _ _ _ _ _) ej' b,
      (chs i).rep_rr hI dij (isUnit_loc _) ui (hw i) b,
      (chs i).rep_comb_apply hI (isUnit_loc _) _ _ _ _ _ (hw i) b,
      (chs i).rep_comb_apply hI ui _ _ _ _ _ _ b]
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton, map_add, map_mul,
      map_sub, map_pow, AlgHom.commutes]
    rw [← (chs i).rep_rr hI dij (isUnit_loc _) ui (e.2.isLift _) b,
      ← (chs i).rep_rr hI dij (isUnit_loc _) ui (hz i) b,
      (chs i).rep_congr hI ui ((e.2.isLift _).rr dij) hE ebi b]
    have h0 := hM i j b
    simp only [Chart.repL] at h0
    linear_combination h0
  obtain ⟨x, hx⟩ := exists_glue (fun i => (chs i).g) hspan w hcompat
  exact ⟨⟨x, isLift_of_cover (fun i => (chs i).g) hspan x fun i => by rw [hx i]; exact hw i⟩, hx⟩

/-- **Quasi-coherence, surjectivity**: every lift on `C[1/c]` becomes the restriction of a global
lift after multiplication by a power of `c`. -/
theorem exists_restr_eq_pow_lin [Smooth f] (hI : SqZero I) (e : GLift f I x₀ s) (c : C)
    (y : Spec (CommRingCat.of (Loc c)) ⟶ X) (hy : IsLift f I x₀ s (Loc c) y) :
    ∃ (n : ℕ) (x : GLift f I x₀ s), restrC (Loc c) x.1 =
      (LiftModule.lin (hI.map (algebraMap C (Loc c))) (GLift.res (Loc c) e) ⟨y, hy⟩
        (GLift.res (Loc c) e) (algebraMap C (Loc c) c ^ n) 0).1 := by
  classical
  obtain ⟨m, chs, hspan⟩ := exists_charts hI e.2.h₀
  have hLE := fun i => (chs i).exists_extension_loc hI (chs i).g c (isUnit_loc _)
    (isUnit_loc_of_dvd (dvd_mul_right _ _)) (e.2.isLift (Loc (chs i).g))
    (hy.rr (dvd_mul_left c (chs i).g))
    (res (chs i).g (Loc ((chs i).g * c)) (isUnit_loc_of_dvd (dvd_mul_right _ _)))
  choose N₀ hN₀ using hLE
  let N := Finset.univ.sup N₀
  choose z hz hzeq using fun i => hN₀ i N (Finset.le_sup (Finset.mem_univ i))
  have hT := fun i j => exists_pair_torsion hI e c hy N (chs i) (chs j) (hz i) (hz j)
    (hzeq i) (hzeq j)
  choose M₀ hM₀ using hT
  let M := Finset.univ.sup fun p : Fin m × Fin m => M₀ p.1 p.2
  have hM : ∀ i j b, algebraMap C (Loc ((chs i).g * (chs j).g)) c ^ M *
      ((chs i).repL hI (dvd_mul_right _ _) (rr (dvd_mul_right (chs i).g (chs j).g) (z i))
          ((hz i).rr _) b -
        (chs i).repL hI (dvd_mul_right _ _) (rr (dvd_mul_left (chs j).g (chs i).g) (z j))
          ((hz j).rr _) b) = 0 := fun i j b => by
    have hle : M₀ i j ≤ M :=
      Finset.le_sup (f := fun p : Fin m × Fin m => M₀ p.1 p.2) (Finset.mem_univ (i, j))
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, hM₀ i j b, mul_zero]
  obtain ⟨x, hx⟩ := exists_glue_corrected hI e c chs hspan z hz M hM
  refine ⟨N + M, x, ?_⟩
  have hspan' : Ideal.span (Set.range fun i => ((chs i).bc (Loc c)).g) = ⊤ := by
    change Ideal.span (Set.range fun i => algebraMap C (Loc c) (chs i).g) = ⊤
    rw [Set.range_comp' (algebraMap C (Loc c)) (fun i => (chs i).g), ← Ideal.map_span, hspan,
      Ideal.map_top]
  have hL := (x.2).res (Loc c)
  have hR := (LiftModule.lin (hI.map (algebraMap C (Loc c))) (GLift.res (Loc c) e) ⟨y, hy⟩
    (GLift.res (Loc c) e) (algebraMap C (Loc c) c ^ (N + M)) 0).2
  refine IsGlobalLift.ext_of_charts (fun i => (chs i).bc (Loc c)) hspan' fun i => ?_
  let T := Localization.Away (algebraMap C (Loc c) (chs i).g)
  have hgT' : IsUnit (algebraMap (Loc c) T (algebraMap C (Loc c) (chs i).g)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hgT : IsUnit (algebraMap C T (chs i).g) := by
    rw [IsScalarTower.algebraMap_apply C (Loc c) T]; exact hgT'
  let ρT : Loc c →ₐ[C] T := IsScalarTower.toAlgHom C (Loc c) T
  -- the relevant lifts on `T`, as lifts of the original data
  have hxT : IsLift f I x₀ s T (Spec.map (CommRingCat.ofHom (algebraMap (Loc c) T)) ≫
      restrC (Loc c) x.1) := by
    rw [restrC_restrC]; exact x.2.isLift T
  have heT : IsLift f I x₀ s T (Spec.map (CommRingCat.ofHom (algebraMap (Loc c) T)) ≫
      restrC (Loc c) e.1) := by
    rw [restrC_restrC]; exact e.2.isLift T
  have hyT : IsLift f I x₀ s T (Spec.map (CommRingCat.ofHom (algebraMap (Loc c) T)) ≫ y) :=
    hy.restrict ρT
  refine ((chs i).bc (Loc c)).eq_of_rep (hI.map _) hgT' (hL.isLift _) (hR.isLift _) fun b => ?_
  -- representative values on `T` in the original chart
  have hu : IsUnit (algebraMap C T ((chs i).g * c)) := by
    rw [map_mul]
    exact hgT.mul (isUnit_of_algHom ρT (isUnit_loc c))
  let res' : Loc ((chs i).g * c) →ₐ[C] T := res _ T hu
  let resg : Loc (chs i).g →ₐ[C] T := res _ T hgT
  have hET := e.2.isLift T
  let vE := ((chs i).rep T hI hgT (restrC T e.1) hET).hom b
  let vY := ((chs i).rep T hI hgT _ hyT).hom b
  have hZT := (hz i).restrict resg
  let vZ := ((chs i).rep T hI hgT _ hZT).hom b
  -- (C2): the local extension on `T`
  have hC2 : vZ = vE + algebraMap C T c ^ N * (vY - vE) := by
    have em : restr resg (z i) = restr res' (restr (res (chs i).g (Loc ((chs i).g * c))
        (isUnit_loc_of_dvd (dvd_mul_right _ _))) (z i)) :=
      (restr_restr (res (chs i).g (Loc ((chs i).g * c)) (isUnit_loc_of_dvd (dvd_mul_right _ _)))
        res' resg (algHom_loc_ext (chs i).g _ _) (z i)).symm
    have hz' := (hz i).restrict (res (chs i).g (Loc ((chs i).g * c))
      (isUnit_loc_of_dvd (dvd_mul_right _ _)))
    have v1 : vZ = res' (((chs i).rep _ hI (isUnit_loc_of_dvd (dvd_mul_right _ _)) _ hz').hom b) :=
      ((chs i).rep_congr hI hgT hZT (hz'.restrict res') em b).trans
        ((chs i).rep_restr_apply hI res' _ hgT hz' _ b)
    rw [v1, hzeq i b, map_add, map_mul, map_sub, map_pow, AlgHom.commutes]
    have eE : res' (((chs i).rep _ hI (isUnit_loc_of_dvd (dvd_mul_right _ _)) _
        ((e.2.isLift _).restrict (res (chs i).g (Loc ((chs i).g * c))
          (isUnit_loc_of_dvd (dvd_mul_right _ _))))).hom b) = vE := by
      rw [← (chs i).rep_restr_apply hI res' _ hgT _ (((e.2.isLift _).restrict _).restrict res') b]
      exact (chs i).rep_congr hI hgT _ hET ((congrArg (restr res') (restr_restrC
        (res (chs i).g (Loc ((chs i).g * c)) (isUnit_loc_of_dvd (dvd_mul_right _ _))) e.1)).trans
        (restr_restrC res' e.1)) b
    have eY : res' (((chs i).rep _ hI (isUnit_loc_of_dvd (dvd_mul_right _ _)) _
        (hy.rr (dvd_mul_left c (chs i).g))).hom b) = vY := by
      rw [← (chs i).rep_restr_apply hI res' _ hgT _ ((hy.rr _).restrict res') b]
      exact (chs i).rep_congr hI hgT _ hyT (restr_restr
        (res c (Loc ((chs i).g * c)) (isUnit_loc_of_dvd (dvd_mul_left c (chs i).g))) res' ρT
        (algHom_loc_ext c _ _) y) b
    rw [eE, eY]
  -- (C1): the glued lift on `T`
  have hw := (chs i).comb_isLift _ hI (isUnit_loc _) (restrC (Loc (chs i).g) e.1) (e.2.isLift _)
    (fun _ : Unit => z i) (fun _ => hz i) (fun _ => algebraMap C (Loc (chs i).g) c ^ M)
  have hC1 : ((chs i).rep T hI hgT _ hxT).hom b = vE + algebraMap C T c ^ M * (vZ - vE) := by
    have em : Spec.map (CommRingCat.ofHom (algebraMap (Loc c) T)) ≫ restrC (Loc c) x.1 =
        restr resg ((chs i).comb _ hI (isUnit_loc _) (restrC (Loc (chs i).g) e.1)
          (e.2.isLift _) (fun _ : Unit => z i) (fun _ => hz i)
          (fun _ => algebraMap C (Loc (chs i).g) c ^ M)) := by
      rw [← hx i]
      exact (restrC_restrC _ _).trans (restr_restrC resg x.1).symm
    rw [(chs i).rep_congr hI hgT hxT (hw.restrict resg) em b,
      (chs i).rep_restr_apply hI resg (isUnit_loc _) hgT hw _ b,
      (chs i).rep_comb_apply hI (isUnit_loc _) _ _ _ _ _ hw b]
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton, map_add,
      map_mul, map_sub, map_pow, AlgHom.commutes]
    have eE : resg (((chs i).rep _ hI (isUnit_loc _) _ (e.2.isLift (Loc (chs i).g))).hom b) =
        vE := by
      rw [← (chs i).rep_restr_apply hI resg (isUnit_loc _) hgT (e.2.isLift _)
        ((e.2.isLift _).restrict resg) b]
      exact (chs i).rep_congr hI hgT _ hET (restr_restrC resg e.1) b
    have eZ : resg (((chs i).rep _ hI (isUnit_loc _) _ (hz i)).hom b) = vZ :=
      ((chs i).rep_restr_apply hI resg (isUnit_loc _) hgT (hz i) hZT b).symm
    rw [eE, eZ]
  -- conversion of the left side to the original chart
  refine (congrArg (fun F => CommRingCat.Hom.hom F b)
    ((chs i).rep_bc (Loc c) hI hgT hgT' hxT (hL.isLift _))).trans ?_
  refine (hC1.trans ?_)
  rw [hC2]
  -- the right side: the chart combination of the base-changed data
  refine Eq.trans ?_ (((chs i).bc (Loc c)).rep_congr (hI.map _) hgT'
    (((chs i).bc (Loc c)).comb_isLift _ (hI.map _) hgT' _ _ _ _ _) (hR.isLift _)
    (gcomb_restr _ _ _ _ _ _ hgT').symm b)
  rw [((chs i).bc (Loc c)).rep_comb_apply (hI.map _) hgT' _ _ _ _ _ _ b]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, zero_mul,
    add_zero, map_pow]
  have eY' := congrArg (fun F => CommRingCat.Hom.hom F b)
    ((chs i).rep_bc (Loc c) hI hgT hgT' hyT
      (((isLift_iff_isGlobalLift (Loc c) y).mp hy).isLift _))
  have eE'' : ((chs i).rep T hI hgT _ heT).hom b = vE :=
    (chs i).rep_congr hI hgT heT hET (restrC_restrC _ e.1) b
  have hRb : ∀ hw, (((chs i).bc (Loc c)).rep T (hI.map (algebraMap C (Loc c))) hgT'
      (restrC (C := CommRingCat.of (Loc c)) T (GLift.res (Loc c) e).1) hw).hom b = vE :=
    fun hw => (congrArg (fun F => CommRingCat.Hom.hom F b)
      ((chs i).rep_bc (Loc c) hI hgT hgT' heT hw)).trans eE''
  simp only at eY'
  rw [eY', hRb, ← IsScalarTower.algebraMap_apply]
  change vE + algebraMap C T c ^ M * (vE + algebraMap C T c ^ N * (vY - vE) - vE) =
    vE + algebraMap C T c ^ (N + M) * (vY - vE)
  ring

/-! ### Restriction as a linear map, and quasi-coherence as a localization -/

section ResLin

/-- The module structure of lifts over a ring given as a type. -/
instance LiftModule.instModuleOf {T : Type u} [CommRing T] {J : Ideal (CommRingCat.of T)}
    {y₀ : Spec (CommRingCat.of (CommRingCat.of T ⧸ J)) ⟶ X} {t : Spec (CommRingCat.of T) ⟶ S}
    (hJ : SqZero J) (e : GLift f J y₀ t) : Module T (LiftModule hJ e) :=
  LiftModule.instModuleLift hJ e

variable (T : Type u) [CommRing T] [Algebra C T]

/-- Lifts on a `C`-algebra `T` form a `C`-module by restriction of scalars. -/
instance LiftModule.instModuleBc {hI' : SqZero (bcI (I := I) T)}
    {e' : GLift f (bcI (I := I) T) (bcx₀ x₀ T) (bcs s T)} : Module C (LiftModule hI' e') :=
  Module.compHom _ (algebraMap C T)

theorem LiftModule.smul_bc_def {hI' : SqZero (bcI (I := I) T)}
    {e' : GLift f (bcI (I := I) T) (bcx₀ x₀ T) (bcs s T)} (a : C) (x : LiftModule hI' e') :
    a • x = (algebraMap C T a) • x := rfl

instance LiftModule.isScalarTower_bc {hI' : SqZero (bcI (I := I) T)}
    {e' : GLift f (bcI (I := I) T) (bcx₀ x₀ T) (bcs s T)} :
    IsScalarTower C T (LiftModule hI' e') :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The restriction-of-scalars module structure when the base ring is given as a type. -/
instance LiftModule.instModuleBcOf {B : Type u} [CommRing B] {J : Ideal (CommRingCat.of B)}
    {y₀ : Spec (CommRingCat.of (CommRingCat.of B ⧸ J)) ⟶ X} {t : Spec (CommRingCat.of B) ⟶ S}
    [Algebra B T] {hJ' : SqZero (bcI (I := J) T)}
    {e' : GLift f (bcI (I := J) T) (bcx₀ y₀ T) (bcs t T)} : Module B (LiftModule hJ' e') :=
  Module.compHom _ (algebraMap B T)

instance LiftModule.isScalarTower_bcOf {B : Type u} [CommRing B] {J : Ideal (CommRingCat.of B)}
    {y₀ : Spec (CommRingCat.of (CommRingCat.of B ⧸ J)) ⟶ X} {t : Spec (CommRingCat.of B) ⟶ S}
    [Algebra B T] {hJ' : SqZero (bcI (I := J) T)}
    {e' : GLift f (bcI (I := J) T) (bcx₀ y₀ T) (bcs t T)} :
    IsScalarTower B T (LiftModule hJ' e') :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem LiftModule.res_lin (hI : SqZero I) (e : GLift f I x₀ s) (x y : GLift f I x₀ s)
    (a b : C) :
    GLift.res T (LiftModule.lin hI e x y a b) =
      LiftModule.lin (hI.map (algebraMap C T)) (GLift.res T e) (GLift.res T x)
        (GLift.res T y) (algebraMap C T a) (algebraMap C T b) := by
  apply Subtype.ext
  change restrC T (gcomb hI e.2 _ ![a, b]) = gcomb (hI.map _) (e.2.res T) _ _
  rw [gcomb_res T hI]
  have hc : (fun k => algebraMap C (CommRingCat.of T) (![a, b] k)) =
      ![algebraMap C T a, algebraMap C T b] := by
    funext k; fin_cases k <;> rfl
  rw [hc]
  refine gcomb_congr _ _ _ rfl _ _ ?_ _
  funext k; fin_cases k <;> rfl

/-- **Restriction of lifts** to a `C`-algebra `T`, as a `C`-linear map. -/
def LiftModule.resLin (hI : SqZero I) (e : GLift f I x₀ s) :
    LiftModule hI e →ₗ[C] LiftModule (hI.map (algebraMap C T)) (GLift.res T e) where
  toFun x := GLift.res T x
  map_add' x y := by
    refine (LiftModule.res_lin T hI e x y 1 1).trans ?_
    rw [map_one]
    rfl
  map_smul' a x := by
    refine (LiftModule.res_lin T hI e x e a 0).trans ?_
    rw [map_zero]
    rfl

@[simp] theorem LiftModule.resLin_val (hI : SqZero I) (e : GLift f I x₀ s) (x : LiftModule hI e) :
    ((LiftModule.resLin T hI e x : LiftModule _ _) : GLift _ _ _ _).1 =
      restrC T (x : GLift f I x₀ s).1 := rfl

end ResLin

/-- **Quasi-coherence**: restriction of lifts to `C[1/c]` is a localization at the powers of `c`. -/
instance LiftModule.isLocalizedModule_resLin [Smooth f] (hI : SqZero I) (e : GLift f I x₀ s)
    (c : C) : IsLocalizedModule (Submonoid.powers c) (LiftModule.resLin (Loc c) hI e) where
  map_units x := by
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Loc c) x
    have : ⇑(algebraMap C (Module.End C (LiftModule (hI.map (algebraMap C (Loc c)))
        (GLift.res (Loc c) e))) x) = fun y => u • y := by
      funext y
      rw [Module.algebraMap_end_apply, LiftModule.smul_bc_def, Units.smul_def, hu]
    rw [this]
    exact MulAction.bijective u
  surj y := by
    obtain ⟨n, x, hx⟩ := exists_restr_eq_pow_lin hI e c y.1 y.2
    refine ⟨⟨x, ⟨c ^ n, n, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    refine Eq.trans ?_ hx.symm
    rw [Submonoid.smul_def, LiftModule.smul_bc_def, map_pow]
    rfl
  exists_of_eq {x x'} h := by
    obtain ⟨n, hn⟩ := exists_pow_lin_eq_of_restr hI e c x x'
      (congrArg (fun z : LiftModule _ _ => (z : GLift _ _ _ _).1) h)
    exact ⟨⟨c ^ n, n, rfl⟩, hn⟩

/-! ### Lifts of data with the same lifts -/

section Congr

variable {I₂ : Ideal C} {x₀₂ : Spec (CommRingCat.of (C ⧸ I₂)) ⟶ X} {s₂ : Spec C ⟶ S}

/-- Two data with the same global lifts have isomorphic modules of lifts, by the identity on
lifts. -/
def LiftModule.equivOfIff (hI : SqZero I) (hI₂ : SqZero I₂) (e : GLift f I x₀ s)
    (e₂ : GLift f I₂ x₀₂ s₂) (h : ∀ y, IsGlobalLift f I x₀ s y ↔ IsGlobalLift f I₂ x₀₂ s₂ y)
    (he : e.1 = e₂.1) : LiftModule hI e ≃ₗ[C] LiftModule hI₂ e₂ where
  toFun x := ⟨x.1, (h _).mp x.2⟩
  invFun x := ⟨x.1, (h _).mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' x y := by
    apply Subtype.ext
    change gcomb hI e.2 _ _ = gcomb hI₂ e₂.2 _ _
    rw [gcomb_data_indep hI hI₂ e.2 ((h _).mp e.2) _ (fun k => (h _).mp (by
      fin_cases k; exacts [x.2, y.2]))]
    refine gcomb_congr hI₂ _ _ he _ _ ?_ _
    funext k; fin_cases k <;> rfl
  map_smul' a x := by
    apply Subtype.ext
    change gcomb hI e.2 _ _ = gcomb hI₂ e₂.2 _ _
    rw [gcomb_data_indep hI hI₂ e.2 ((h _).mp e.2) _ (fun k => (h _).mp (by
      fin_cases k; exacts [x.2, e.2]))]
    refine gcomb_congr hI₂ _ _ he _ _ ?_ _
    funext k; fin_cases k
    · rfl
    · exact he

@[simp] theorem LiftModule.equivOfIff_val (hI : SqZero I) (hI₂ : SqZero I₂) (e : GLift f I x₀ s)
    (e₂ : GLift f I₂ x₀₂ s₂) (h : ∀ y, IsGlobalLift f I x₀ s y ↔ IsGlobalLift f I₂ x₀₂ s₂ y)
    (he : e.1 = e₂.1) (x : LiftModule hI e) :
    ((LiftModule.equivOfIff hI hI₂ e e₂ h he x : LiftModule hI₂ e₂) : GLift f I₂ x₀₂ s₂).1 =
      (x : GLift f I x₀ s).1 := rfl

end Congr

end Langlands.AlgebraicGeometry.SmoothLifting
