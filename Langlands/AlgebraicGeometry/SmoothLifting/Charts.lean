import Langlands.AlgebraicGeometry.SmoothLifting.AffineCombination

/-! # Lifts along a square-zero thickening, computed in affine charts

Fix a morphism `f : X ⟶ S`, a ring `C` with an ideal `I`, and a commutative square
`x₀ : Spec (C ⧸ I) ⟶ X`, `s : Spec C ⟶ S`. For a `C`-algebra `R`, a *lift on `R`* is a morphism
`Spec R ⟶ X` over `S` restricting to `x₀` on `Spec (R ⧸ I R)`. Over an affine chart `U ⊆ X` (lying
over an affine `V ⊆ S`) lifts are the same as ring maps `Γ(X, U) ⟶ R` over `Γ(S, V)` reducing to the
chart representative of `x₀`. Affine combinations of lifts computed in two different charts agree.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SmoothLifting

section ChartRep

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) {R : CommRingCat.{u}}

/-- A morphism `Spec R ⟶ X` landing in an affine open `U` comes from a ring map
`Γ(X, U) ⟶ R`. -/
def chartRep (y : Spec R ⟶ X) (h : ∀ x, y x ∈ U) : Γ(X, U) ⟶ R :=
  Spec.preimage (IsOpenImmersion.lift hU.fromSpec y (by
    rw [hU.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact h x))

theorem chartRep_spec (y : Spec R ⟶ X) (h : ∀ x, y x ∈ U) :
    Spec.map (chartRep hU y h) ≫ hU.fromSpec = y := by
  rw [chartRep, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem fromSpec_cancel {φ ψ : Γ(X, U) ⟶ R}
    (h : Spec.map φ ≫ hU.fromSpec = Spec.map ψ ≫ hU.fromSpec) : φ = ψ :=
  Spec.map_injective ((cancel_mono hU.fromSpec).mp h)

theorem chartRep_eq (y : Spec R ⟶ X) (h : ∀ x, y x ∈ U) {φ : Γ(X, U) ⟶ R}
    (hφ : Spec.map φ ≫ hU.fromSpec = y) : chartRep hU y h = φ :=
  fromSpec_cancel hU ((chartRep_spec hU y h).trans hφ.symm)

theorem fromSpec_mem (φ : Γ(X, U) ⟶ R) (x : Spec R) : (Spec.map φ ≫ hU.fromSpec) x ∈ U := by
  rw [Scheme.Hom.comp_apply, ← SetLike.mem_coe, ← hU.range_fromSpec]
  exact ⟨_, rfl⟩

theorem chartRep_comp (y : Spec R ⟶ X) (h : ∀ x, y x ∈ U) {R' : CommRingCat.{u}}
    (ρ : R ⟶ R') (h' : ∀ x, (Spec.map ρ ≫ y) x ∈ U) :
    chartRep hU (Spec.map ρ ≫ y) h' = chartRep hU y h ≫ ρ :=
  chartRep_eq hU _ _ (by rw [Spec.map_comp, Category.assoc, chartRep_spec])

end ChartRep

/-- `Spec` of a surjection with nil kernel is surjective on points. -/
theorem specMap_surjective {P Q : CommRingCat.{u}} (ε : P ⟶ Q) (hε : Function.Surjective ε.hom)
    (hker : RingHom.ker ε.hom ≤ nilradical P) : Function.Surjective (Spec.map ε) := by
  intro x
  have : x ∈ Set.range (PrimeSpectrum.comap ε.hom) := by
    rw [range_comap_of_surjective _ _ hε]
    exact fun a ha => @nilradical_le_prime _ _ x.asIdeal x.2 a (hker ha)
  obtain ⟨y, hy⟩ := this
  exact ⟨y, hy⟩

theorem SqZero.le_nilradical {R : Type*} [CommRing R] {J : Ideal R} (hJ : SqZero J) :
    J ≤ nilradical R := fun a ha => ⟨2, by rw [pow_two]; exact hJ a ha a ha⟩

section Setup

variable {X S : Scheme.{u}} (f : X ⟶ S) {C : CommRingCat.{u}} (I : Ideal C)
  (x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X) (s : Spec C ⟶ S)

/-- An affine chart adapted to the data `x₀`, `s`: affine opens `V ⊆ S` and `U ⊆ f⁻¹ V`, and an
element `g` of `C` whose basic open maps into `V` under `s` and into `U` under `x₀`. -/
structure Chart where
  /-- The affine open of the base. -/
  V : S.Opens
  hV : IsAffineOpen V
  /-- The affine open of the source. -/
  U : X.Opens
  hU : IsAffineOpen U
  hUV : U ≤ f ⁻¹ᵁ V
  /-- The element of `C` cutting out the chart domain. -/
  g : C
  hs : ∀ p : Spec C, g ∉ p.asIdeal → s p ∈ V
  hx : ∀ p : Spec (CommRingCat.of (C ⧸ I)), Ideal.Quotient.mk I g ∉ p.asIdeal → x₀ p ∈ U

variable (R : Type u) [CommRing R] [Algebra C R]

/-- The extension of `I` to a `C`-algebra `R`. -/
abbrev redIdeal : Ideal R := I.map (algebraMap C R)

/-- The reduction map `R ⟶ R ⧸ I R`. -/
def redMap : CommRingCat.of R ⟶ CommRingCat.of (R ⧸ redIdeal I R) :=
  CommRingCat.ofHom (Ideal.Quotient.mk _)

/-- The structure map `C ⧸ I ⟶ R ⧸ I R`. -/
def redStruct : CommRingCat.of (C ⧸ I) ⟶ CommRingCat.of (R ⧸ redIdeal I R) :=
  CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap C R) Ideal.le_comap_map)

/-- The structure map `C ⟶ R`. -/
def strMap : C ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap C R)

theorem strMap_redMap :
    strMap R ≫ redMap I R = CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ redStruct I R := by
  ext c; rfl

/-- A lift of `x₀` over `s` on the `C`-algebra `R`. -/
def IsLift (y : Spec (CommRingCat.of R) ⟶ X) : Prop :=
  Spec.map (redMap I R) ≫ y = Spec.map (redStruct I R) ≫ x₀ ∧ y ≫ f = Spec.map (strMap R) ≫ s

variable {f I x₀ s}

theorem redMap_surjective : Function.Surjective (redMap I R).hom := Ideal.Quotient.mk_surjective

theorem redMap_ker : RingHom.ker (redMap I R).hom = redIdeal I R := Ideal.mk_ker

theorem chart_x₀_mem (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g))
    (p : Spec (CommRingCat.of (R ⧸ redIdeal I R))) : (Spec.map (redStruct I R) ≫ x₀) p ∈ ch.U := by
  rw [Scheme.Hom.comp_apply]
  refine ch.hx _ fun hp => p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hp ?_)
  exact hg.map (Ideal.Quotient.mk (redIdeal I R))

theorem chart_s_mem (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g))
    (p : Spec (CommRingCat.of R)) : (Spec.map (strMap R) ≫ s) p ∈ ch.V := by
  rw [Scheme.Hom.comp_apply]
  exact ch.hs _ fun hp => p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hg)

theorem chart_lift_mem (hI : SqZero I) (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g))
    {y : Spec (CommRingCat.of R) ⟶ X}
    (hy : Spec.map (redMap I R) ≫ y = Spec.map (redStruct I R) ≫ x₀) (p : Spec (CommRingCat.of R)) :
    y p ∈ ch.U := by
  obtain ⟨q, rfl⟩ := specMap_surjective (redMap I R) (redMap_surjective R)
    (by rw [redMap_ker]; exact (hI.map _).le_nilradical) p
  rw [← Scheme.Hom.comp_apply, hy]
  exact chart_x₀_mem R ch hg q

/-- The ring map of the chart. -/
abbrev Chart.θ (ch : Chart f I x₀ s) : Γ(S, ch.V) ⟶ Γ(X, ch.U) := f.appLE ch.V ch.U ch.hUV

/-- The chart representative of `s` on `R`. -/
def Chart.ψ (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g)) :
    Γ(S, ch.V) ⟶ CommRingCat.of R :=
  chartRep ch.hV (Spec.map (strMap R) ≫ s) (chart_s_mem R ch hg)

/-- The chart representative of `x₀` on `R ⧸ I R`. -/
def Chart.φ₀ (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g)) :
    Γ(X, ch.U) ⟶ CommRingCat.of (R ⧸ redIdeal I R) :=
  chartRep ch.hU (Spec.map (redStruct I R) ≫ x₀) (chart_x₀_mem R ch hg)

theorem Chart.θ_φ₀ (h₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s)
    (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g)) :
    ch.θ ≫ ch.φ₀ R hg = ch.ψ R hg ≫ redMap I R := by
  refine fromSpec_cancel ch.hV ?_
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f ch.hV ch.hU,
    ← Category.assoc, Chart.φ₀, chartRep_spec, Category.assoc, h₀, Spec.map_comp,
    Category.assoc, Chart.ψ, chartRep_spec, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, strMap_redMap]

/-- Ring maps over the chart give lifts. -/
theorem Chart.isLift_of_hom (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g))
    (φ : Γ(X, ch.U) ⟶ CommRingCat.of R) (h1 : ch.θ ≫ φ = ch.ψ R hg)
    (h2 : φ ≫ redMap I R = ch.φ₀ R hg) : IsLift f I x₀ s R (Spec.map φ ≫ ch.hU.fromSpec) := by
  constructor
  · rw [← Category.assoc, ← Spec.map_comp, h2, Chart.φ₀, chartRep_spec]
  · rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f ch.hV ch.hU ch.hUV,
      ← Category.assoc, ← Spec.map_comp, h1, Chart.ψ, chartRep_spec]

/-- The chart representative of a lift. -/
def Chart.rep (hI : SqZero I) (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g))
    (y : Spec (CommRingCat.of R) ⟶ X) (hy : IsLift f I x₀ s R y) :
    Γ(X, ch.U) ⟶ CommRingCat.of R :=
  chartRep ch.hU y (chart_lift_mem R hI ch hg hy.1)

theorem Chart.rep_spec (hI : SqZero I) (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g))
    (y : Spec (CommRingCat.of R) ⟶ X) (hy : IsLift f I x₀ s R y) :
    Spec.map (ch.rep R hI hg y hy) ≫ ch.hU.fromSpec = y :=
  chartRep_spec _ _ _

theorem Chart.rep_θ (hI : SqZero I) (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g))
    (y : Spec (CommRingCat.of R) ⟶ X) (hy : IsLift f I x₀ s R y) :
    ch.θ ≫ ch.rep R hI hg y hy = ch.ψ R hg := by
  refine fromSpec_cancel ch.hV ?_
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f ch.hV ch.hU,
    ← Category.assoc, Chart.rep_spec, hy.2, Chart.ψ, chartRep_spec]

theorem Chart.rep_red (hI : SqZero I) (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g))
    (y : Spec (CommRingCat.of R) ⟶ X) (hy : IsLift f I x₀ s R y) :
    ch.rep R hI hg y hy ≫ redMap I R = ch.φ₀ R hg := by
  refine fromSpec_cancel ch.hU ?_
  rw [Spec.map_comp, Category.assoc, Chart.rep_spec, hy.1, Chart.φ₀, chartRep_spec]

theorem Chart.rep_sub_mem (hI : SqZero I) (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g))
    (y y' : Spec (CommRingCat.of R) ⟶ X) (hy : IsLift f I x₀ s R y) (hy' : IsLift f I x₀ s R y')
    (b : Γ(X, ch.U)) :
    (ch.rep R hI hg y' hy').hom b - (ch.rep R hI hg y hy).hom b ∈ redIdeal I R := by
  rw [← Ideal.Quotient.eq]
  have h := (ch.rep_red R hI hg y' hy').trans (ch.rep_red R hI hg y hy).symm
  exact congrArg (fun F : Γ(X, ch.U) ⟶ CommRingCat.of (R ⧸ redIdeal I R) => F.hom b) h

theorem SqZero.isNilpotent {R : Type*} [CommRing R] {J : Ideal R} (hJ : SqZero J) :
    IsNilpotent J :=
  ⟨2, by
    rw [pow_two]
    exact le_bot_iff.mp (Submodule.mul_le.mpr fun a ha b hb => by
      rw [hJ a ha b hb]; exact Submodule.zero_mem _)⟩

/-- Local existence of lifts over a chart, by formal smoothness of `Γ(S, V) → Γ(X, U)`. -/
theorem Chart.exists_hom [Smooth f] (hI : SqZero I)
    (h₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s)
    (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g)) :
    ∃ φ : Γ(X, ch.U) ⟶ CommRingCat.of R, ch.θ ≫ φ = ch.ψ R hg ∧ φ ≫ redMap I R = ch.φ₀ R hg := by
  have hθ : ch.θ.hom.Smooth := Smooth.smooth_appLE f ch.hV ch.hU ch.hUV
  let _ := ch.θ.hom.toAlgebra
  let _ := (ch.ψ R hg).hom.toAlgebra
  let _ := ((ch.ψ R hg) ≫ redMap I R).hom.toAlgebra
  have : Algebra.FormallySmooth Γ(S, ch.V) Γ(X, ch.U) := hθ.formallySmooth
  have hc := ch.θ_φ₀ R h₀ hg
  let F : Γ(X, ch.U) →ₐ[Γ(S, ch.V)] R ⧸ redIdeal I R :=
    { (ch.φ₀ R hg).hom with
      commutes' := fun a => congrArg (fun F : Γ(S, ch.V) ⟶ _ => F.hom a) hc }
  let G : R →ₐ[Γ(S, ch.V)] R ⧸ redIdeal I R :=
    { (redMap I R).hom with commutes' := fun a => rfl }
  have hG : Function.Surjective G := redMap_surjective R
  have hnil : IsNilpotent (RingHom.ker (G : R →+* R ⧸ redIdeal I R)) := by
    have : RingHom.ker (G : R →+* R ⧸ redIdeal I R) = redIdeal I R := Ideal.mk_ker
    rw [this]; exact (hI.map _).isNilpotent
  let L := Algebra.FormallySmooth.liftOfSurjective F G hG hnil
  refine ⟨CommRingCat.ofHom L.toRingHom, ?_, ?_⟩
  · ext a; exact L.commutes a
  · ext b; exact Algebra.FormallySmooth.liftOfSurjective_apply F G hG hnil b

/-- Lifts restrict along `C`-algebra maps. -/
theorem IsLift.restrict {R R' : Type u} [CommRing R] [Algebra C R] [CommRing R'] [Algebra C R']
    (ρ : R →ₐ[C] R') {y : Spec (CommRingCat.of R) ⟶ X} (hy : IsLift f I x₀ s R y) :
    IsLift f I x₀ s R' (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ y) := by
  have hmap : (redIdeal I R).map ρ = redIdeal I R' := by
    rw [show Ideal.map ρ (Ideal.map (algebraMap C R) I) =
      Ideal.map (ρ : R →+* R') (Ideal.map (algebraMap C R) I) from rfl, Ideal.map_map,
      ρ.comp_algebraMap]
  have hle : redIdeal I R ≤ (redIdeal I R').comap (ρ : R →+* R') :=
    Ideal.map_le_iff_le_comap.mp (le_of_eq hmap)
  let ρb : CommRingCat.of (R ⧸ redIdeal I R) ⟶ CommRingCat.of (R' ⧸ redIdeal I R') :=
    CommRingCat.ofHom (Ideal.quotientMap _ (ρ : R →+* R') hle)
  have e1 : CommRingCat.ofHom ρ.toRingHom ≫ redMap I R' = redMap I R ≫ ρb := by
    ext r; rfl
  have e2 : redStruct I R ≫ ρb = redStruct I R' := by
    ext c
    change Ideal.Quotient.mk _ (ρ (algebraMap C R c)) = Ideal.Quotient.mk _ (algebraMap C R' c)
    rw [ρ.commutes]
  have e3 : strMap (C := C) R ≫ CommRingCat.ofHom ρ.toRingHom = strMap (C := C) R' := by
    ext c
    change ρ (algebraMap C R c) = algebraMap C R' c
    exact ρ.commutes c
  constructor
  · rw [← Category.assoc, ← Spec.map_comp, e1, Spec.map_comp, Category.assoc, hy.1,
      ← Category.assoc, ← Spec.map_comp, e2]
  · rw [Category.assoc, hy.2, ← Category.assoc, ← Spec.map_comp, e3]

theorem Chart.rep_restrict (hI : SqZero I) (ch : Chart f I x₀ s) {R R' : Type u} [CommRing R] [Algebra C R]
    [CommRing R'] [Algebra C R'] (ρ : R →ₐ[C] R') (hg : IsUnit (algebraMap C R ch.g))
    (hg' : IsUnit (algebraMap C R' ch.g)) {y : Spec (CommRingCat.of R) ⟶ X}
    (hy : IsLift f I x₀ s R y) :
    ch.rep R' hI hg' _ (hy.restrict ρ) = ch.rep R hI hg y hy ≫ CommRingCat.ofHom ρ.toRingHom :=
  chartRep_comp ch.hU y _ _ _

section Comb

variable {ι : Type} [Fintype ι]

/-- The affine combination `y₀ + ∑ cₖ (yₖ - y₀)` of lifts, computed in a chart. -/
def Chart.comb (hI : SqZero I) (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g))
    (y₀ : Spec (CommRingCat.of R) ⟶ X) (hy₀ : IsLift f I x₀ s R y₀)
    (y : ι → (Spec (CommRingCat.of R) ⟶ X)) (hy : ∀ k, IsLift f I x₀ s R (y k)) (c : ι → R) :
    Spec (CommRingCat.of R) ⟶ X :=
  Spec.map (CommRingCat.ofHom (affComb (redIdeal I R) (hI.map _) (ch.rep R hI hg y₀ hy₀).hom
    (fun k => (ch.rep R hI hg (y k) (hy k)).hom)
    (fun k b => ch.rep_sub_mem R hI hg _ _ hy₀ (hy k) b) c)) ≫ ch.hU.fromSpec

theorem Chart.comb_isLift (hI : SqZero I) (ch : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g))
    (y₀ : Spec (CommRingCat.of R) ⟶ X) (hy₀ : IsLift f I x₀ s R y₀)
    (y : ι → (Spec (CommRingCat.of R) ⟶ X)) (hy : ∀ k, IsLift f I x₀ s R (y k)) (c : ι → R) :
    IsLift f I x₀ s R (ch.comb R hI hg y₀ hy₀ y hy c) := by
  refine ch.isLift_of_hom R hg _ ?_ ?_
  · ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, affComb_apply]
    have h0 := congrArg (fun F : Γ(S, ch.V) ⟶ CommRingCat.of R => F.hom a)
      (ch.rep_θ R hI hg y₀ hy₀)
    have hk : ∀ k, (ch.rep R hI hg (y k) (hy k)).hom (ch.θ.hom a) = (ch.ψ R hg).hom a :=
      fun k => congrArg (fun F : Γ(S, ch.V) ⟶ CommRingCat.of R => F.hom a)
        (ch.rep_θ R hI hg (y k) (hy k))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h0
    simp only [hk, h0, sub_self, mul_zero, Finset.sum_const_zero, add_zero]
  · ext b
    have h := affComb_sub_mem (redIdeal I R) (hI.map _) (ch.rep R hI hg y₀ hy₀).hom
      (fun k => (ch.rep R hI hg (y k) (hy k)).hom)
      (fun k b => ch.rep_sub_mem R hI hg _ _ hy₀ (hy k) b) c b
    rw [← Ideal.Quotient.eq] at h
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [← ch.rep_red R hI hg y₀ hy₀]
    exact h

/-- **Chart independence of affine combinations.** -/
theorem Chart.comb_eq (hI : SqZero I) (ch ch' : Chart f I x₀ s) (hg : IsUnit (algebraMap C R ch.g))
    (hg' : IsUnit (algebraMap C R ch'.g))
    (y₀ : Spec (CommRingCat.of R) ⟶ X) (hy₀ : IsLift f I x₀ s R y₀)
    (y : ι → (Spec (CommRingCat.of R) ⟶ X)) (hy : ∀ k, IsLift f I x₀ s R (y k)) (c : ι → R) :
    ch.comb R hI hg y₀ hy₀ y hy c = ch'.comb R hI hg' y₀ hy₀ y hy c := by
  set J := redIdeal I R
  have hJ : SqZero J := hI.map _
  let Φ := fibreLift J (ch.rep R hI hg y₀ hy₀).hom (fun k => (ch.rep R hI hg (y k) (hy k)).hom)
    (fun k b => ch.rep_sub_mem R hI hg _ _ hy₀ (hy k) b)
  let Φ' := fibreLift J (ch'.rep R hI hg' y₀ hy₀).hom
    (fun k => (ch'.rep R hI hg' (y k) (hy k)).hom)
    (fun k b => ch'.rep_sub_mem R hI hg' _ _ hy₀ (hy k) b)
  let Y' : Spec (CommRingCat.of (fibreRing ι J)) ⟶ X :=
    Spec.map (CommRingCat.ofHom Φ') ≫ ch'.hU.fromSpec
  let ε : CommRingCat.of (fibreRing ι J) ⟶ CommRingCat.of (R ⧸ J) :=
    CommRingCat.ofHom ((Ideal.Quotient.mk J).comp (fibreFst J))
  have hε : Function.Surjective ε.hom := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨⟨(r, fun _ => r), fun k => by simp⟩, rfl⟩
  have hker : RingHom.ker ε.hom ≤ nilradical _ := by
    intro a ha
    have ha1 : (a : R × (ι → R)).1 ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp ha
    have ha2 : ∀ k, (a : R × (ι → R)).2 k ∈ J := fun k => by
      have := J.add_mem (a.2 k) ha1
      rwa [sub_add_cancel] at this
    refine ⟨2, Subtype.ext (Prod.ext ?_ (funext fun k => ?_))⟩
    · simp only [pow_two, Subring.coe_mul, Prod.fst_mul, ZeroMemClass.coe_zero, Prod.fst_zero]
      exact hJ _ ha1 _ ha1
    · simp only [pow_two, Subring.coe_mul, Prod.snd_mul, Pi.mul_apply, ZeroMemClass.coe_zero,
        Prod.snd_zero, Pi.zero_apply]
      exact hJ _ (ha2 k) _ (ha2 k)
  have hY'ε : Spec.map ε ≫ Y' = Spec.map (redStruct I R) ≫ x₀ := by
    have : CommRingCat.ofHom Φ' ≫ ε = ch'.rep R hI hg' y₀ hy₀ ≫ redMap I R := by ext b; rfl
    rw [← Category.assoc, ← Spec.map_comp, this, Spec.map_comp, Category.assoc,
      Chart.rep_spec, hy₀.1]
  have land : ∀ p, Y' p ∈ ch.U := by
    intro p
    obtain ⟨q, rfl⟩ := specMap_surjective ε hε hker p
    rw [← Scheme.Hom.comp_apply, hY'ε]
    exact chart_x₀_mem R ch hg q
  let Θ := chartRep ch.hU Y' land
  have key : ∀ (κ : fibreRing ι J →+* R) (z : Spec (CommRingCat.of R) ⟶ X)
      (hz : IsLift f I x₀ s R z), κ.comp Φ' = (ch'.rep R hI hg' z hz).hom →
      κ.comp Θ.hom = (ch.rep R hI hg z hz).hom := by
    intro κ z hz h
    have h' : CommRingCat.ofHom Φ' ≫ CommRingCat.ofHom κ = ch'.rep R hI hg' z hz :=
      CommRingCat.hom_ext h
    have : Θ ≫ CommRingCat.ofHom κ = ch.rep R hI hg z hz := by
      refine fromSpec_cancel ch.hU ?_
      rw [Spec.map_comp, Category.assoc, chartRep_spec, ← Category.assoc, ← Spec.map_comp, h',
        Chart.rep_spec, Chart.rep_spec]
    exact congrArg CommRingCat.Hom.hom this
  have hΘ : Θ = CommRingCat.ofHom Φ := by
    refine CommRingCat.hom_ext (fibreRing_hom_ext J ?_ fun k => ?_)
    · exact key (fibreFst J) y₀ hy₀ rfl
    · exact key (fibreEval J k) (y k) (hy k) rfl
  have hY : Y' = Spec.map (CommRingCat.ofHom Φ) ≫ ch.hU.fromSpec := by
    rw [← hΘ, chartRep_spec]
  change Spec.map (CommRingCat.ofHom ((fibreComb J hJ c).comp Φ)) ≫ ch.hU.fromSpec =
    Spec.map (CommRingCat.ofHom ((fibreComb J hJ c).comp Φ')) ≫ ch'.hU.fromSpec
  rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc, ← hY]

end Comb

end Setup

end Langlands.AlgebraicGeometry.SmoothLifting
