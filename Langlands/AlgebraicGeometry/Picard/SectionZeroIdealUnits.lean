import Langlands.AlgebraicGeometry.Picard.SectionZeroIdealFrames

/-! # Regular sections with the same zero ideal differ by a unit -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.SectionZeroIdeal

variable {X : Scheme.{u}} (L : LineBundle X)

/-- A global section is regular if multiplication by it is injective over every open. -/
def IsRegularSection (σ : Γ(L.obj, ⊤)) : Prop :=
  ∀ (W : X.Opens) (c : Γ(X, W)), c • res L σ W = 0 → c = 0

variable {L}

/-- A section is regular as soon as, around every point, it is a regular multiple of a frame on an
affine open. -/
theorem isRegularSection_of_local (σ : Γ(L.obj, ⊤))
    (h : ∀ x : X, ∃ (U : X.affineOpens) (t : Γ(L.obj, U.1)) (a : Γ(X, U.1)), x ∈ U.1 ∧
      Scheme.Modules.IsFrameOn t U.1 ∧ res L σ U.1 = a • t ∧ IsSMulRegular Γ(X, U.1) a) :
    IsRegularSection L σ := by
  intro W c hc
  -- `c` vanishes on a basic open around each point of `W`
  have hloc : ∀ y : W, ∃ (V : X.Opens) (hVW : V ≤ W), y.1 ∈ V ∧
      X.presheaf.map (homOfLE hVW).op c = 0 := by
    rintro ⟨y, hyW⟩
    obtain ⟨U, t, a, hyU, ht, hσ, ha⟩ := h y
    obtain ⟨f, hfWU, hyf⟩ := U.2.exists_basicOpen_le ⟨y, hyW⟩ hyU
    have hfU : X.basicOpen f ≤ U.1 := X.basicOpen_le f
    refine ⟨X.basicOpen f, hfWU, hyf, ?_⟩
    let _ := (X.presheaf.map (homOfLE hfU).op).hom.toAlgebra
    have := U.2.isLocalization_basicOpen f
    have hreg : IsSMulRegular Γ(X, X.basicOpen f)
        (X.presheaf.map (homOfLE hfU).op a) :=
      ha.of_isLocalization (S := Γ(X, X.basicOpen f)) (Submonoid.powers f)
    apply hreg
    -- multiply out using the frame
    have hframe := (ht.bijective hfU hfU).1
    apply hframe
    simp only [smul_zero, zero_smul]
    have h1 : res L σ (X.basicOpen f) = X.presheaf.map (homOfLE hfU).op a •
        L.obj.presheaf.map (homOfLE hfU).op t := by
      have : res L σ (X.basicOpen f) = L.obj.presheaf.map (homOfLE hfU).op (res L σ U.1) := by
        change _ = L.obj.presheaf.map _ (L.obj.presheaf.map _ σ)
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
      rw [this, hσ, Scheme.Modules.map_smul]
    have h2 : res L σ (X.basicOpen f) = L.obj.presheaf.map (homOfLE hfWU).op (res L σ W) := by
      change _ = L.obj.presheaf.map _ (L.obj.presheaf.map _ σ)
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    have h3 := congrArg (L.obj.presheaf.map (homOfLE hfWU).op) hc
    rw [Scheme.Modules.map_smul, ← h2, h1, smul_smul, map_zero] at h3
    change (X.presheaf.map (homOfLE hfU).op a * X.presheaf.map (homOfLE hfWU).op c) •
      L.obj.presheaf.map (homOfLE hfU).op t = 0
    rw [mul_comm]
    exact h3
  choose V hVW hyV hV using hloc
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf V W (fun y => homOfLE (hVW y))
    (fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩) c 0 fun y => ?_
  change X.presheaf.map (homOfLE (hVW y)).op c = X.presheaf.map (homOfLE (hVW y)).op 0
  rw [hV y, map_zero]

/-- **Regular sections with the same zero ideal differ by a unit** of the global functions. -/
theorem exists_isUnit_eq_smul_of_zeroIdeal_eq {σ σ' : Γ(L.obj, ⊤)} (hσ : IsRegularSection L σ)
    (h : zeroIdeal L σ' = zeroIdeal L σ) : ∃ c : Γ(X, ⊤), IsUnit c ∧ σ' = c • σ := by
  have hx := fun x => exists_affine_frame L x
  choose U hxU t ht using hx
  -- coordinates of the two sections in the frames
  have hcoord : ∀ (x : X) (s : Γ(L.obj, ⊤)), ∃ a : Γ(X, (U x).1), res L s (U x).1 = a • t x :=
    fun x s => by
      obtain ⟨a, ha⟩ := ((ht x).bijective (le_refl _) (le_refl _)).2 (res L s (U x).1)
      simp only [map_id_apply] at ha
      exact ⟨a, ha.symm⟩
  choose a ha using fun x => hcoord x σ
  choose a' ha' using fun x => hcoord x σ'
  -- the coordinates of `σ` are regular
  have hreg : ∀ x, IsSMulRegular Γ(X, (U x).1) (a x) := fun x c d hcd => by
    change a x • c = a x • d at hcd
    rw [← sub_eq_zero]
    apply hσ (U x).1
    rw [ha x, smul_smul, sub_mul, sub_smul, mul_comm c, mul_comm d]
    change (a x • c) • t x - (a x • d) • t x = 0
    rw [hcd, sub_self]
  -- the ideals agree, so the coordinates differ by units
  have hspan : ∀ x, Ideal.span {a' x} = Ideal.span {a x} := fun x => by
    rw [← zeroIdeal_ideal_of_frame L σ' (U x) (ht x) (a' x) (ha' x),
      ← zeroIdeal_ideal_of_frame L σ (U x) (ht x) (a x) (ha x), h]
  have hd : ∀ x, ∃ d : Γ(X, (U x).1), IsUnit d ∧ a' x = d * a x := fun x => by
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 ((hspan x).le (Ideal.mem_span_singleton_self _))
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 ((hspan x).ge (Ideal.mem_span_singleton_self _))
    refine ⟨d, isUnit_iff_exists_inv.mpr ⟨e, ?_⟩, hd.symm⟩
    have h1 : a x • (d * e) = a x • 1 := by
      simp only [smul_eq_mul]
      calc a x * (d * e) = e * (d * a x) := by ring
        _ = e * a' x := by rw [hd]
        _ = a x := he
        _ = a x * 1 := (mul_one _).symm
    exact hreg x h1
  choose d hdu hd using hd
  have hσ'loc : ∀ x, res L σ' (U x).1 = d x • res L σ (U x).1 := fun x => by
    rw [ha' x, ha x, smul_smul, hd x]
  -- restriction of `res` along inclusions
  have hres : ∀ (s : Γ(L.obj, ⊤)) {V W : X.Opens} (hVW : V ≤ W),
      L.obj.presheaf.map (homOfLE hVW).op (res L s W) = res L s V := fun s V W hVW => by
    change L.obj.presheaf.map _ (L.obj.presheaf.map _ s) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  -- the local units are compatible
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun x => (U x).1) d := by
    intro x y
    change X.presheaf.map (homOfLE inf_le_left).op (d x) =
      X.presheaf.map (homOfLE inf_le_right).op (d y)
    rw [← sub_eq_zero]
    apply hσ ((U x).1 ⊓ (U y).1)
    rw [sub_smul]
    have h1 := congrArg (L.obj.presheaf.map (homOfLE (inf_le_left : (U x).1 ⊓ (U y).1 ≤ _)).op)
      (hσ'loc x)
    have h2 := congrArg (L.obj.presheaf.map (homOfLE (inf_le_right : (U x).1 ⊓ (U y).1 ≤ _)).op)
      (hσ'loc y)
    rw [hres, Scheme.Modules.map_smul, hres] at h1 h2
    change X.presheaf.map (homOfLE inf_le_left).op (d x) • res L σ _ -
      X.presheaf.map (homOfLE inf_le_right).op (d y) • res L σ _ = 0
    rw [← h1, ← h2, sub_self]
  obtain ⟨c₀, hc, -⟩ := X.sheaf.existsUnique_gluing' (fun x => (U x).1) ⊤ (fun _ => homOfLE le_top)
    (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) d hcomp
  let c : Γ(X, ⊤) := c₀
  have hc' : ∀ x, X.presheaf.map (homOfLE le_top).op c = d x := hc
  refine ⟨c, ?_, ?_⟩
  · apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ c
    intro x _
    rw [← X.presheaf.germ_res_apply (homOfLE (le_top : (U x).1 ≤ ⊤)) x (hxU x) c]
    change IsUnit (X.presheaf.germ (U x).1 x (hxU x) (X.presheaf.map (homOfLE le_top).op c))
    rw [hc' x]
    exact (hdu x).map _
  · refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨L.obj.presheaf, L.obj.isSheaf⟩)
      (fun x => (U x).1) ⊤ (fun _ => homOfLE le_top)
      (fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) _ _ fun x => ?_
    change res L σ' (U x).1 = res L (c • σ) (U x).1
    rw [hσ'loc x, ← hc' x]
    exact (Scheme.Modules.map_smul _ _ _ _).symm

end Langlands.AlgebraicGeometry.Picard.SectionZeroIdeal
