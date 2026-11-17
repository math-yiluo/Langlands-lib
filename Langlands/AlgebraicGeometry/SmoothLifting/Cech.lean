import Langlands.AlgebraicGeometry.SmoothLifting.Charts
import Langlands.AlgebraicGeometry.AffinePointGluing

/-! # Gluing chart lifts by a partition of unity

Over a finite family of charts whose elements `gᵢ` generate the unit ideal of `C`, local lifts
on `C[1/gᵢ]` are corrected by a partition of unity so that they agree on overlaps, and are then
glued to a lift on `Spec C`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace Langlands.AlgebraicGeometry.SmoothLifting

section Loc

variable {C : CommRingCat.{u}}

/-- The localization `C[1/c]`. -/
abbrev Loc (c : C) : Type u := Localization.Away c

theorem isUnit_loc (c : C) : IsUnit (algebraMap C (Loc c) c) :=
  IsLocalization.Away.algebraMap_isUnit c

theorem isUnit_loc_of_dvd {c c' : C} (h : c ∣ c') : IsUnit (algebraMap C (Loc c') c) := by
  obtain ⟨d, rfl⟩ := h
  exact isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact isUnit_loc (c * d))

/-- The restriction map `C[1/c] → T` to a `C`-algebra in which `c` is a unit. -/
def res (c : C) (T : Type u) [CommRing T] [Algebra C T] (h : IsUnit (algebraMap C T c)) :
    Loc c →ₐ[C] T :=
  IsLocalization.liftAlgHom (M := Submonoid.powers c) (f := Algebra.ofId C T) (by
    rintro ⟨_, n, rfl⟩
    simpa using h.pow n)

theorem algHom_loc_ext (c : C) {T : Type u} [CommRing T] [Algebra C T]
    (ρ₁ ρ₂ : Loc c →ₐ[C] T) : ρ₁ = ρ₂ :=
  (IsLocalization.algHom_subsingleton (Submonoid.powers c)).elim _ _

end Loc

section Lifts

variable {X S : Scheme.{u}} {f : X ⟶ S} {C : CommRingCat.{u}} {I : Ideal C}
  {x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X} {s : Spec C ⟶ S}

/-- Restriction of a morphism along a `C`-algebra map. -/
abbrev restr {R R' : Type u} [CommRing R] [Algebra C R] [CommRing R'] [Algebra C R']
    (ρ : R →ₐ[C] R') (y : Spec (CommRingCat.of R) ⟶ X) : Spec (CommRingCat.of R') ⟶ X :=
  Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ y

theorem restr_restr {R R' R'' : Type u} [CommRing R] [Algebra C R] [CommRing R'] [Algebra C R']
    [CommRing R''] [Algebra C R''] (ρ : R →ₐ[C] R') (ρ' : R' →ₐ[C] R'') (ρ'' : R →ₐ[C] R'')
    (h : ρ'.comp ρ = ρ'') (y : Spec (CommRingCat.of R) ⟶ X) :
    restr ρ' (restr ρ y) = restr ρ'' y := by
  rw [restr, restr, restr, ← Category.assoc, ← Spec.map_comp, ← h]
  rfl

theorem Chart.rep_restr_apply (hI : SqZero I) (ch : Chart f I x₀ s) {R R' : Type u} [CommRing R]
    [Algebra C R] [CommRing R'] [Algebra C R'] (ρ : R →ₐ[C] R') (hg : IsUnit (algebraMap C R ch.g))
    (hg' : IsUnit (algebraMap C R' ch.g)) {y : Spec (CommRingCat.of R) ⟶ X}
    (hy : IsLift f I x₀ s R y) (hy' : IsLift f I x₀ s R' (restr ρ y)) (b : Γ(X, ch.U)) :
    (ch.rep R' hI hg' (restr ρ y) hy').hom b = ρ ((ch.rep R hI hg y hy).hom b) := by
  have := ch.rep_restrict hI ρ hg hg' hy
  exact congrArg (fun F : Γ(X, ch.U) ⟶ CommRingCat.of R' => F.hom b) this

theorem Chart.eq_of_rep (hI : SqZero I) (ch : Chart f I x₀ s) {R : Type u} [CommRing R]
    [Algebra C R] (hg : IsUnit (algebraMap C R ch.g)) {y y' : Spec (CommRingCat.of R) ⟶ X}
    (hy : IsLift f I x₀ s R y) (hy' : IsLift f I x₀ s R y')
    (h : ∀ b, (ch.rep R hI hg y hy).hom b = (ch.rep R hI hg y' hy').hom b) : y = y' := by
  rw [← ch.rep_spec R hI hg y hy, ← ch.rep_spec R hI hg y' hy']
  congr 2
  ext b
  exact h b

theorem Chart.rep_comb_apply {ι : Type} [Fintype ι] (hI : SqZero I) (ch : Chart f I x₀ s)
    {R : Type u} [CommRing R] [Algebra C R] (hg : IsUnit (algebraMap C R ch.g))
    (y₀ : Spec (CommRingCat.of R) ⟶ X) (hy₀ : IsLift f I x₀ s R y₀)
    (y : ι → (Spec (CommRingCat.of R) ⟶ X)) (hy : ∀ k, IsLift f I x₀ s R (y k)) (c : ι → R)
    (h : IsLift f I x₀ s R (ch.comb R hI hg y₀ hy₀ y hy c)) (b : Γ(X, ch.U)) :
    (ch.rep R hI hg _ h).hom b = (ch.rep R hI hg y₀ hy₀).hom b +
      ∑ k, c k * ((ch.rep R hI hg (y k) (hy k)).hom b - (ch.rep R hI hg y₀ hy₀).hom b) := by
  have : ch.rep R hI hg _ h = CommRingCat.ofHom (affComb (redIdeal I R) (hI.map _)
      (ch.rep R hI hg y₀ hy₀).hom (fun k => (ch.rep R hI hg (y k) (hy k)).hom)
      (fun k b => ch.rep_sub_mem R hI hg _ _ hy₀ (hy k) b) c) :=
    chartRep_eq _ _ _ rfl
  rw [this]
  rfl

theorem Chart.exists_lift [Smooth f] (hI : SqZero I)
    (h₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s)
    (ch : Chart f I x₀ s) (R : Type u) [CommRing R] [Algebra C R]
    (hg : IsUnit (algebraMap C R ch.g)) : ∃ y, IsLift f I x₀ s R y := by
  obtain ⟨φ, h1, h2⟩ := ch.exists_hom R hI h₀ hg
  exact ⟨_, ch.isLift_of_hom R hg φ h1 h2⟩

theorem Chart.rep_congr (hI : SqZero I) (ch : Chart f I x₀ s) {R : Type u} [CommRing R]
    [Algebra C R] (hg : IsUnit (algebraMap C R ch.g)) {y y' : Spec (CommRingCat.of R) ⟶ X}
    (hy : IsLift f I x₀ s R y) (hy' : IsLift f I x₀ s R y') (h : y = y') (b : Γ(X, ch.U)) :
    (ch.rep R hI hg y hy).hom b = (ch.rep R hI hg y' hy').hom b := by
  subst h; rfl

theorem isUnit_of_algHom {R R' : Type u} [CommRing R] [Algebra C R] [CommRing R'] [Algebra C R']
    (ρ : R →ₐ[C] R') {c : C} (h : IsUnit (algebraMap C R c)) : IsUnit (algebraMap C R' c) := by
  have := h.map ρ
  rwa [ρ.commutes] at this

theorem Chart.ψ_restr (ch : Chart f I x₀ s) {R R' : Type u} [CommRing R] [Algebra C R]
    [CommRing R'] [Algebra C R'] (ρ : R →ₐ[C] R') (hg : IsUnit (algebraMap C R ch.g))
    (hg' : IsUnit (algebraMap C R' ch.g)) :
    ch.ψ R hg ≫ CommRingCat.ofHom ρ.toRingHom = ch.ψ R' hg' := by
  have e3 : strMap (C := C) R ≫ CommRingCat.ofHom ρ.toRingHom = strMap (C := C) R' := by
    ext c
    change ρ (algebraMap C R c) = algebraMap C R' c
    exact ρ.commutes c
  refine (chartRep_eq _ _ _ ?_).symm
  rw [Spec.map_comp, Category.assoc, Chart.ψ, chartRep_spec, ← Category.assoc, ← Spec.map_comp,
    e3]

/-- The extension lemma on localizations, in a chart. -/
theorem Chart.exists_extension_loc [Smooth f] (hI : SqZero I) (ch : Chart f I x₀ s) (c e : C)
    (hg : IsUnit (algebraMap C (Loc c) ch.g)) (hg' : IsUnit (algebraMap C (Loc (c * e)) ch.g))
    {y : Spec (CommRingCat.of (Loc c)) ⟶ X} (hy : IsLift f I x₀ s (Loc c) y)
    {y' : Spec (CommRingCat.of (Loc (c * e))) ⟶ X} (hy' : IsLift f I x₀ s (Loc (c * e)) y')
    (ρ : Loc c →ₐ[C] Loc (c * e)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ (z : Spec (CommRingCat.of (Loc c)) ⟶ X)
      (hz : IsLift f I x₀ s (Loc c) z), ∀ b,
      (ch.rep _ hI hg' (restr ρ z) (hz.restrict ρ)).hom b =
        (ch.rep _ hI hg' (restr ρ y) (hy.restrict ρ)).hom b +
        algebraMap C (Loc (c * e)) e ^ N * ((ch.rep _ hI hg' y' hy').hom b -
          (ch.rep _ hI hg' (restr ρ y) (hy.restrict ρ)).hom b) := by
  classical
  have hθ : ch.θ.hom.Smooth := Smooth.smooth_appLE f ch.hV ch.hU ch.hUV
  let _ : Algebra Γ(S, ch.V) Γ(X, ch.U) := ch.θ.hom.toAlgebra
  let _ : Algebra Γ(S, ch.V) (Loc c) := (ch.ψ (Loc c) hg).hom.toAlgebra
  let _ : Algebra Γ(S, ch.V) (Loc (c * e)) := (ch.ψ (Loc (c * e)) hg').hom.toAlgebra
  have : Algebra.FinitePresentation Γ(S, ch.V) Γ(X, ch.U) := hθ.finitePresentation
  have hψ := ch.ψ_restr ρ hg hg'
  let ρA : Loc c →ₐ[Γ(S, ch.V)] Loc (c * e) :=
    { ρ.toRingHom with
      commutes' := fun a => congrArg (fun F : Γ(S, ch.V) ⟶ _ => F.hom a) hψ }
  let β : Γ(X, ch.U) →ₐ[Γ(S, ch.V)] Loc c :=
    { (ch.rep _ hI hg y hy).hom with
      commutes' := fun a => congrArg (fun F : Γ(S, ch.V) ⟶ _ => F.hom a)
        (ch.rep_θ _ hI hg y hy) }
  let β' : Γ(X, ch.U) →ₐ[Γ(S, ch.V)] Loc (c * e) :=
    { (ch.rep _ hI hg' y' hy').hom with
      commutes' := fun a => congrArg (fun F : Γ(S, ch.V) ⟶ _ => F.hom a)
        (ch.rep_θ _ hI hg' y' hy') }
  set J := redIdeal I (Loc c)
  have hmap : J.map ρA = redIdeal I (Loc (c * e)) := by
    change Ideal.map (ρ : Loc c →+* Loc (c * e)) (Ideal.map (algebraMap C (Loc c)) I) = _
    rw [Ideal.map_map, ρ.comp_algebraMap]
  have h1 : ∀ r, ρA r = 0 → ∃ m : ℕ, algebraMap C (Loc c) e ^ m * r = 0 :=
    fun r hr => away_ker_torsion c e ρ r hr
  have h2 : ∀ r' ∈ J.map ρA, ∃ (n : ℕ) (y : Loc c), y ∈ J ∧
      ρA (algebraMap C (Loc c) e) ^ n * r' = ρA y :=
    fun r' hr' => away_map_surj c e I ρ r' hr'
  have hβρ : ∀ b, ρA (β b) = (ch.rep _ hI hg' (restr ρ y) (hy.restrict ρ)).hom b := fun b =>
    (ch.rep_restr_apply hI ρ hg hg' hy (hy.restrict ρ) b).symm
  have hβ : ∀ b, β' b - ρA (β b) ∈ J.map ρA := by
    intro b
    rw [hmap, hβρ]
    exact ch.rep_sub_mem _ hI hg' _ _ (hy.restrict ρ) hy' b
  obtain ⟨N₀, hN⟩ := exists_extension J (hI.map _) ρA (algebraMap C (Loc c) e) h1 h2 β β' hβ
  refine ⟨N₀, fun N hN' => ?_⟩
  obtain ⟨γ, hγJ, hγρ⟩ := hN N hN'
  let φ : Γ(X, ch.U) ⟶ CommRingCat.of (Loc c) := CommRingCat.ofHom γ.toRingHom
  have h1' : ch.θ ≫ φ = ch.ψ _ hg := by
    ext a; exact γ.commutes a
  have h2' : φ ≫ redMap I (Loc c) = ch.φ₀ _ hg := by
    ext b
    have hb := Ideal.Quotient.eq.mpr (hγJ b)
    have hr := congrArg (fun F : Γ(X, ch.U) ⟶ _ => F.hom b) (ch.rep_red _ hI hg y hy)
    exact hb.trans hr
  have hz := ch.isLift_of_hom _ hg φ h1' h2'
  refine ⟨_, hz, fun b => ?_⟩
  have hrep : ch.rep _ hI hg _ hz = φ := chartRep_eq _ _ _ rfl
  rw [ch.rep_restr_apply hI ρ hg hg' hz (hz.restrict ρ) b, hrep]
  have := hγρ b
  rw [hβρ] at this
  change ρA (γ b) = _
  rw [this]
  congr 2
  exact congrArg (· ^ N) (ρ.commutes e)

/-- The torsion lemma on localizations, in a chart. -/
theorem Chart.exists_torsion_loc [Smooth f] (hI : SqZero I) (ch : Chart f I x₀ s) (c e : C)
    (hg : IsUnit (algebraMap C (Loc c) ch.g))
    {y y' : Spec (CommRingCat.of (Loc c)) ⟶ X} (hy : IsLift f I x₀ s (Loc c) y)
    (hy' : IsLift f I x₀ s (Loc c) y') (ρ : Loc c →ₐ[C] Loc (c * e))
    (h : restr ρ y = restr ρ y') :
    ∃ M : ℕ, ∀ b, algebraMap C (Loc c) e ^ M *
      ((ch.rep _ hI hg y hy).hom b - (ch.rep _ hI hg y' hy').hom b) = 0 := by
  have hθ : ch.θ.hom.Smooth := Smooth.smooth_appLE f ch.hV ch.hU ch.hUV
  let _ : Algebra Γ(S, ch.V) Γ(X, ch.U) := ch.θ.hom.toAlgebra
  let _ : Algebra Γ(S, ch.V) (Loc c) := (ch.ψ (Loc c) hg).hom.toAlgebra
  have : Algebra.FinitePresentation Γ(S, ch.V) Γ(X, ch.U) := hθ.finitePresentation
  have hg' : IsUnit (algebraMap C (Loc (c * e)) ch.g) := isUnit_of_algHom ρ hg
  let L : Γ(X, ch.U) →ₐ[Γ(S, ch.V)] Loc c :=
    { (ch.rep _ hI hg y hy).hom with
      commutes' := fun a => congrArg (fun F : Γ(S, ch.V) ⟶ _ => F.hom a)
        (ch.rep_θ _ hI hg y hy) }
  let L' : Γ(X, ch.U) →ₐ[Γ(S, ch.V)] Loc c :=
    { (ch.rep _ hI hg y' hy').hom with
      commutes' := fun a => congrArg (fun F : Γ(S, ch.V) ⟶ _ => F.hom a)
        (ch.rep_θ _ hI hg y' hy') }
  refine exists_pow_mul_sub_eq_zero L L' (ρ : Loc c →+* Loc (c * e)) _
    (fun r hr => away_ker_torsion c e ρ r hr) fun b => ?_
  change ρ ((ch.rep _ hI hg y hy).hom b) = ρ ((ch.rep _ hI hg y' hy').hom b)
  rw [← ch.rep_restr_apply hI ρ hg hg' hy (hy.restrict ρ) b,
    ← ch.rep_restr_apply hI ρ hg hg' hy' (hy'.restrict ρ) b]
  exact ch.rep_congr hI hg' _ _ h b

end Lifts

section Glue

variable {C : CommRingCat.{u}} {X : Scheme.{u}}

theorem glue_compat {n : ℕ} (g : Fin n → C) (y : ∀ i, Spec (CommRingCat.of (Loc (g i))) ⟶ X)
    (hy : ∀ i j, restr (res (g i) (Loc (g i * g j)) (isUnit_loc_of_dvd (dvd_mul_right _ _)))
      (y i) = restr (res (g j) (Loc (g i * g j)) (isUnit_loc_of_dvd (dvd_mul_left _ _))) (y j))
    (i j : Fin n) (A : CommRingCat.{u})
    (t : Spec A ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap C (Loc (g i)))))
      (Spec.map (CommRingCat.ofHom (algebraMap C (Loc (g j)))))) :
    t ≫ pullback.fst _ _ ≫ y i = t ≫ pullback.snd _ _ ≫ y j := by
  let α := Spec.preimage (t ≫ pullback.fst _ _)
  let β := Spec.preimage (t ≫ pullback.snd _ _)
  have hα : Spec.map α = t ≫ pullback.fst _ _ := Spec.map_preimage _
  have hβ : Spec.map β = t ≫ pullback.snd _ _ := Spec.map_preimage _
  have hαβ : CommRingCat.ofHom (algebraMap C (Loc (g i))) ≫ α =
      CommRingCat.ofHom (algebraMap C (Loc (g j))) ≫ β := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hα, hβ, Category.assoc, Category.assoc, pullback.condition]
  let _ : Algebra C A := (CommRingCat.ofHom (algebraMap C (Loc (g i))) ≫ α).hom.toAlgebra
  have hαalg : ∀ c, α.hom (algebraMap C (Loc (g i)) c) = algebraMap C A c := fun c => rfl
  have hβalg : ∀ c, β.hom (algebraMap C (Loc (g j)) c) = algebraMap C A c := fun c =>
    (congrArg (fun F : C ⟶ A => F.hom c) hαβ).symm
  have ui : IsUnit (algebraMap C A (g i)) := by
    rw [← hαalg]; exact (isUnit_loc (g i)).map α.hom
  have uj : IsUnit (algebraMap C A (g j)) := by
    rw [← hβalg]; exact (isUnit_loc (g j)).map β.hom
  have uij : IsUnit (algebraMap C A (g i * g j)) := by rw [map_mul]; exact ui.mul uj
  let δ := res (g i * g j) A uij
  let αA : Loc (g i) →ₐ[C] A := { α.hom with commutes' := hαalg }
  let βA : Loc (g j) →ₐ[C] A := { β.hom with commutes' := hβalg }
  have eα : δ.comp (res (g i) (Loc (g i * g j)) (isUnit_loc_of_dvd (dvd_mul_right _ _))) = αA :=
    algHom_loc_ext _ _ _
  have eβ : δ.comp (res (g j) (Loc (g i * g j)) (isUnit_loc_of_dvd (dvd_mul_left _ _))) = βA :=
    algHom_loc_ext _ _ _
  have hα' : t ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (res (g i) (Loc (g i * g j))
          (isUnit_loc_of_dvd (dvd_mul_right _ _))).toRingHom) := by
    rw [← hα, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    exact (congrArg (fun F : Loc (g i) →ₐ[C] A => F x) eα).symm
  have hβ' : t ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom δ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (res (g j) (Loc (g i * g j))
          (isUnit_loc_of_dvd (dvd_mul_left _ _))).toRingHom) := by
    rw [← hβ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    exact (congrArg (fun F : Loc (g j) →ₐ[C] A => F x) eβ).symm
  rw [← Category.assoc, ← Category.assoc, hα', hβ', Category.assoc, Category.assoc]
  exact congrArg (Spec.map (CommRingCat.ofHom δ.toRingHom) ≫ ·) (hy i j)

/-- Morphisms on the members of a standard open cover `Spec C[1/gᵢ]` which agree on the
`Spec C[1/(gᵢ gⱼ)]` glue to a morphism on `Spec C`. -/
theorem exists_glue {n : ℕ} (g : Fin n → C) (hg : Ideal.span (Set.range g) = ⊤)
    (y : ∀ i, Spec (CommRingCat.of (Loc (g i))) ⟶ X)
    (hy : ∀ i j, restr (res (g i) (Loc (g i * g j)) (isUnit_loc_of_dvd (dvd_mul_right _ _)))
      (y i) = restr (res (g j) (Loc (g i * g j)) (isUnit_loc_of_dvd (dvd_mul_left _ _))) (y j)) :
    ∃ z : Spec C ⟶ X, ∀ i, Spec.map (CommRingCat.ofHom (algebraMap C (Loc (g i)))) ≫ z = y i := by
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop g hg).openCover
  exact ⟨𝒰.glueMorphisms y fun i j => AffinePoints.hom_ext fun A t => glue_compat g y hy i j A t,
    fun i => 𝒰.ι_glueMorphisms y _ i⟩

end Glue

section Verify

variable {X S : Scheme.{u}} {f : X ⟶ S} {C : CommRingCat.{u}} {I : Ideal C}
  {x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X} {s : Spec C ⟶ S}

/-- A morphism on `Spec C` restricting to lifts on a standard open cover is a lift. -/
theorem isLift_of_cover {n : ℕ} (g : Fin n → C) (hg : Ideal.span (Set.range g) = ⊤)
    (z : Spec C ⟶ X) (hz : ∀ i, IsLift f I x₀ s (Loc (g i))
      (Spec.map (CommRingCat.ofHom (algebraMap C (Loc (g i)))) ≫ z)) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ z = x₀ ∧ z ≫ f = s := by
  constructor
  · let gb : Fin n → CommRingCat.of (C ⧸ I) := fun i => Ideal.Quotient.mk I (g i)
    have hgb : Ideal.span (Set.range gb) = ⊤ := by
      have : Set.range gb = Ideal.Quotient.mk I '' Set.range g := (Set.range_comp _ _)
      rw [this, ← Ideal.map_span, hg, Ideal.map_top]
    let 𝒱 := (Scheme.affineOpenCoverOfSpanRangeEqTop gb hgb).openCover
    refine Scheme.Cover.hom_ext 𝒱 _ _ fun i => ?_
    change Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ I) (Localization.Away (gb i)))) ≫ _ =
      Spec.map (CommRingCat.ofHom (algebraMap (C ⧸ I) (Localization.Away (gb i)))) ≫ _
    let T := Localization.Away (gb i)
    have hu : IsUnit (((algebraMap (C ⧸ I) T).comp (Ideal.Quotient.mk I)) (g i)) :=
      IsLocalization.Away.algebraMap_isUnit (gb i)
    let κ : Loc (g i) →+* T := IsLocalization.Away.lift (g i) hu
    have hκ : ∀ c, κ (algebraMap C (Loc (g i)) c) = algebraMap (C ⧸ I) T (Ideal.Quotient.mk I c) :=
      fun c => IsLocalization.Away.lift_eq (g i) hu c
    have hκI : redIdeal I (Loc (g i)) ≤ RingHom.ker κ := by
      rw [redIdeal, Ideal.map_le_iff_le_comap]
      intro c hc
      change κ (algebraMap C (Loc (g i)) c) = 0
      rw [hκ, Ideal.Quotient.eq_zero_iff_mem.mpr hc, map_zero]
    let κb : CommRingCat.of (Loc (g i) ⧸ redIdeal I (Loc (g i))) ⟶ CommRingCat.of T :=
      CommRingCat.ofHom (Ideal.Quotient.lift _ κ hκI)
    have e1 : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        CommRingCat.ofHom (algebraMap (C ⧸ I) T) =
        CommRingCat.ofHom (algebraMap C (Loc (g i))) ≫ redMap I (Loc (g i)) ≫ κb := by
      ext c
      exact (hκ c).symm
    have e2 : redStruct I (Loc (g i)) ≫ κb = CommRingCat.ofHom (algebraMap (C ⧸ I) T) := by
      ext c
      exact hκ c
    rw [← Category.assoc, ← Spec.map_comp, e1, Spec.map_comp, Spec.map_comp, Category.assoc,
      Category.assoc, (hz i).1, ← Category.assoc, ← Spec.map_comp, e2]
  · let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop g hg).openCover
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun i => ?_
    change Spec.map (CommRingCat.ofHom (algebraMap C (Loc (g i)))) ≫ _ =
      Spec.map (CommRingCat.ofHom (algebraMap C (Loc (g i)))) ≫ _
    rw [← Category.assoc, (hz i).2]
    rfl

end Verify

section RR

variable {X S : Scheme.{u}} {f : X ⟶ S} {C : CommRingCat.{u}} {I : Ideal C}
  {x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X} {s : Spec C ⟶ S}

/-- Restriction from `Spec C[1/c']` along `C[1/c] → C[1/c']` for `c ∣ c'`. -/
abbrev rr {c c' : C} (h : c ∣ c') (y : Spec (CommRingCat.of (Loc c)) ⟶ X) :
    Spec (CommRingCat.of (Loc c')) ⟶ X :=
  restr (res c (Loc c') (isUnit_loc_of_dvd h)) y

theorem rr_rr {c c' c'' : C} (h : c ∣ c') (h' : c' ∣ c'') (h'' : c ∣ c'')
    (y : Spec (CommRingCat.of (Loc c)) ⟶ X) : rr h' (rr h y) = rr h'' y :=
  restr_restr _ _ _ (algHom_loc_ext _ _ _) y

theorem IsLift.rr {c c' : C} (h : c ∣ c') {y : Spec (CommRingCat.of (Loc c)) ⟶ X}
    (hy : IsLift f I x₀ s (Loc c) y) : IsLift f I x₀ s (Loc c') (rr h y) := hy.restrict _

theorem Chart.rep_rr (hI : SqZero I) (ch : Chart f I x₀ s) {c c' : C} (h : c ∣ c')
    (hg : IsUnit (algebraMap C (Loc c) ch.g)) (hg' : IsUnit (algebraMap C (Loc c') ch.g))
    {y : Spec (CommRingCat.of (Loc c)) ⟶ X} (hy : IsLift f I x₀ s (Loc c) y) (b : Γ(X, ch.U)) :
    (ch.rep _ hI hg' (rr h y) (hy.rr h)).hom b =
      res c (Loc c') (isUnit_loc_of_dvd h) ((ch.rep _ hI hg y hy).hom b) :=
  ch.rep_restr_apply hI _ hg hg' hy _ b

theorem Chart.eq_comb_of_rep {ι : Type} [Fintype ι] (hI : SqZero I) (ch : Chart f I x₀ s)
    {R : Type u} [CommRing R] [Algebra C R] (hg : IsUnit (algebraMap C R ch.g))
    {z : Spec (CommRingCat.of R) ⟶ X} (hz : IsLift f I x₀ s R z)
    (y₀ : Spec (CommRingCat.of R) ⟶ X) (hy₀ : IsLift f I x₀ s R y₀)
    (y : ι → (Spec (CommRingCat.of R) ⟶ X)) (hy : ∀ k, IsLift f I x₀ s R (y k)) (c : ι → R)
    (h : ∀ b, (ch.rep R hI hg z hz).hom b = (ch.rep R hI hg y₀ hy₀).hom b +
      ∑ k, c k * ((ch.rep R hI hg (y k) (hy k)).hom b - (ch.rep R hI hg y₀ hy₀).hom b)) :
    z = ch.comb R hI hg y₀ hy₀ y hy c :=
  ch.eq_of_rep hI hg hz (ch.comb_isLift R hI hg y₀ hy₀ y hy c) fun b => by
    rw [h b, ch.rep_comb_apply hI hg y₀ hy₀ y hy c _ b]

end RR

end Langlands.AlgebraicGeometry.SmoothLifting
