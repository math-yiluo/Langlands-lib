import Langlands.Correspondence.Laumon.EndRingStages

/-!
# Maps of the end ring to henselian local rings

Let `φ : k[x] → B` be a ring map to a henselian local ring with `φ⁻¹(𝔪_B) = (x)`. For a simple
point `b` of `endRing k`, the stage ring of `b` has exactly one ring map to `B` extending `φ` and
sending `b` to an element with the residue of `b` (`exists_stageHom`, `stageHom_ext`). Gluing these
maps along the stage rings gives the unique local map `endRing k → B` extending `φ`
(`existsUnique_endRing_hom`).
-/

noncomputable section

universe u

open Polynomial IsLocalRing

namespace Langlands.Henniart.Laumon

variable (k : Type u) [Field k]

local notation "ι" => endChartCoordinate k FourierEnd.zero
local notation "τ" => endUniformizer k FourierEnd.zero

/-- **The polynomials vanishing at a simple point.** For a simple point `b` there is a polynomial
`μ` over `k[x]`, the primitive part of a multiple of the minimal polynomial of `b` over `k(t)`, with
`μ(b) = 0`, `μ'(b)` a unit, and dividing every polynomial over `k[x]` that vanishes at `b`. -/
theorem exists_dvd_of_isSimplePoint {b : endRing k} (hb : IsSimplePoint k b) :
    ∃ μ : k[X][X], eval₂ ι b μ = 0 ∧ IsUnit (eval₂ ι b (derivative μ)) ∧
      ∀ p : k[X][X], eval₂ ι b p = 0 → μ ∣ p := by
  classical
  obtain ⟨G, hG0, hG1⟩ := hb
  have hG : G ≠ 0 := by
    rintro rfl
    simp at hG1
  have halg : IsAlgebraic (RatFunc k) (b : endField k) := by
    refine ⟨G.map (algebraMap k[X] (RatFunc k)),
      (Polynomial.map_ne_zero_iff (IsFractionRing.injective k[X] (RatFunc k))).2 hG, ?_⟩
    rw [← coe_eval₂_endChartCoordinate, hG0]
    rfl
  have hint : IsIntegral (RatFunc k) (b : endField k) := halg.isIntegral
  obtain ⟨d, hd, hdm⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors k[X])
    (minpoly (RatFunc k) (b : endField k))
  obtain ⟨N, hN⟩ : ∃ N, N = IsLocalization.integerNormalization (nonZeroDivisors k[X])
    (minpoly (RatFunc k) (b : endField k)) := ⟨_, rfl⟩
  rw [← hN] at hdm
  have hd0 : algebraMap k[X] (RatFunc k) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).2 (nonZeroDivisors.ne_zero hd)
  rw [Algebra.smul_def, Polynomial.algebraMap_apply] at hdm
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero, eq_comm, mul_eq_zero, C_eq_zero] at hdm
    exact hdm.elim hd0 (minpoly.ne_zero hint)
  have hc0 : algebraMap k[X] (RatFunc k) N.content ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).2
      (content_eq_zero_iff.not.2 hN0)
  have h1 : C (algebraMap k[X] (RatFunc k) d) * minpoly (RatFunc k) (b : endField k) =
      C (algebraMap k[X] (RatFunc k) N.content) * N.primPart.map (algebraMap k[X] (RatFunc k)) := by
    rw [← hdm]
    conv_lhs => rw [eq_C_content_mul_primPart N]
    rw [Polynomial.map_mul, map_C]
  have hdvd : N.primPart.map (algebraMap k[X] (RatFunc k)) ∣
      minpoly (RatFunc k) (b : endField k) := by
    refine ⟨C ((algebraMap k[X] (RatFunc k) d)⁻¹ * algebraMap k[X] (RatFunc k) N.content), ?_⟩
    calc minpoly (RatFunc k) (b : endField k)
        = C (algebraMap k[X] (RatFunc k) d)⁻¹ *
            (C (algebraMap k[X] (RatFunc k) d) * minpoly (RatFunc k) (b : endField k)) := by
          rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hd0, C_1, one_mul]
      _ = _ := by rw [h1, C_mul]; ring
  have hμ0 : eval₂ ι b N.primPart = 0 := by
    apply Subtype.ext
    rw [coe_eval₂_endChartCoordinate]
    have h2 := congrArg (aeval (b : endField k)) h1
    rw [map_mul, map_mul, minpoly.aeval, mul_zero, aeval_C, eq_comm, mul_eq_zero] at h2
    exact h2.resolve_left ((_root_.map_ne_zero _).2 hc0)
  have hμdvd : ∀ p : k[X][X], eval₂ ι b p = 0 → N.primPart ∣ p := by
    intro p hp
    refine (isPrimitive_primPart N).dvd_of_fraction_map_dvd_fraction_map (hdvd.trans
      (minpoly.dvd _ _ ?_))
    rw [← coe_eval₂_endChartCoordinate, hp]
    rfl
  refine ⟨N.primPart, hμ0, ?_, hμdvd⟩
  obtain ⟨H, hH⟩ := hμdvd G hG0
  rw [hH, derivative_mul, eval₂_add, eval₂_mul, eval₂_mul, hμ0, zero_mul, add_zero] at hG1
  exact isUnit_of_mul_isUnit_left hG1

/-- A ring map out of `A` whose kernel contains that of a surjection `f : A → S` factors through
`f`. -/
theorem exists_ringHom_comp_eq {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
    (f : A →+* S) (hf : Function.Surjective f) (g : A →+* T) (h : ∀ a, f a = 0 → g a = 0) :
    ∃ ψ : S →+* T, ∀ a, ψ (f a) = g a :=
  ⟨f.liftOfSurjective hf ⟨g, fun a ha => h a ha⟩,
    fun a => RingHom.liftOfSurjective_comp_apply f hf ⟨g, fun a ha => h a ha⟩ a⟩

variable {B : Type*} [CommRing B] [HenselianLocalRing B] (φ : k[X] →+* B)

/-- The map of constants `k → κ_B` induced by `φ`. -/
def constantResidue : k →+* ResidueField B :=
  (residue B).comp (φ.comp C)

variable {φ}

theorem residue_comp_eq (hφ : Ideal.comap φ (maximalIdeal B) = Ideal.span {X}) :
    (residue B).comp φ = (constantResidue k φ).comp Polynomial.constantCoeff := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp [constantResidue]
  · have hX : (X : k[X]) ∈ Ideal.comap φ (maximalIdeal B) := by
      rw [hφ]
      exact Ideal.subset_span rfl
    rw [RingHom.comp_apply, RingHom.comp_apply, (residue_eq_zero_iff _).2 hX, constantCoeff_apply,
      coeff_X_zero, map_zero]

/-- The residue of `p(y)` for an element `y ∈ B` with the residue of `b`. -/
theorem residue_eval₂ (hφ : Ideal.comap φ (maximalIdeal B) = Ideal.span {X}) (b : endRing k)
    (y : B) (hy : residue B y = constantResidue k φ (endResidue k b)) (p : k[X][X]) :
    residue B (eval₂ φ y p) = constantResidue k φ (stageResidue k b p) := by
  have h : (residue B).comp (eval₂RingHom φ y) =
      (constantResidue k φ).comp (stageResidue k b) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, ← RingHom.comp_apply,
        residue_comp_eq k hφ, RingHom.comp_apply, RingHom.comp_apply, constantCoeff_apply]
      simp only [stageResidue, RingHom.comp_apply, coe_eval₂RingHom, eval₂_C,
        endResidue_endChartCoordinate]
    · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, hy, stageResidue]
  exact RingHom.congr_fun h p

/-- **Maps out of a stage ring: existence.** For a simple point `b`, the stage ring of `b` has a
ring map to `B` extending `φ` and compatible with the residue maps. -/
theorem exists_stageHom (hφ : Ideal.comap φ (maximalIdeal B) = Ideal.span {X}) {b : endRing k}
    (hb : IsSimplePoint k b) :
    ∃ ψ : stage k b →+* B,
      (∀ a : k[X], ψ ⟨ι a, endChartCoordinate_mem_stage k b a⟩ = φ a) ∧
      ∀ s : stage k b, residue B (ψ s) = constantResidue k φ (endResidue k s) := by
  obtain ⟨μ, hμ0, hμ1, hμdvd⟩ := exists_dvd_of_isSimplePoint k hb
  have hy₀ : residue B (φ (C (endResidue k b))) = constantResidue k φ (endResidue k b) := rfl
  obtain ⟨β, hβ, hβ'⟩ := Langlands.CommutativeAlgebra.exists_isRoot_sub_mem_maximalIdeal
    (μ.map φ) (φ (C (endResidue k b)))
    (by
      rw [eval_map, ← residue_eq_zero_iff, residue_eval₂ k hφ b _ hy₀, stageResidue,
        RingHom.comp_apply, coe_eval₂RingHom, hμ0, RingHom.map_zero, map_zero])
    (by
      rw [derivative_map, eval_map, ← residue_ne_zero_iff_isUnit, residue_eval₂ k hφ b _ hy₀,
        stageResidue, RingHom.comp_apply, coe_eval₂RingHom]
      exact (_root_.map_ne_zero _).2 ((isUnit_iff_endResidue_ne_zero k _).1 hμ1))
  have hβres : residue B β = constantResidue k φ (endResidue k b) := by
    have h := (residue_eq_zero_iff _).2 hβ'
    rw [map_sub, sub_eq_zero] at h
    rw [h, hy₀]
  have hunit : ∀ q : (stagePrime k b).primeCompl, IsUnit (eval₂RingHom φ β (q : k[X][X])) := by
    intro q
    rw [← residue_ne_zero_iff_isUnit, coe_eval₂RingHom, residue_eval₂ k hφ b β hβres]
    exact (_root_.map_ne_zero _).2 q.2
  let g : StageLocalization k b →+* B := IsLocalization.lift hunit
  have hker : ∀ z, stageProj k b z = 0 → g z = 0 := by
    intro z hz
    have hz' : stageMap k b z = 0 := by
      rw [← coe_stageProj, hz]
      rfl
    obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (stagePrime k b).primeCompl z
    have h1 := (IsLocalization.lift_mk'_spec (isUnit_eval₂_of_mem_primeCompl k b) p 0 q).1 hz'
    rw [mul_zero, coe_eval₂RingHom] at h1
    obtain ⟨r, hr⟩ := hμdvd p h1
    refine (IsLocalization.lift_mk'_spec hunit p 0 q).2 ?_
    rw [mul_zero, coe_eval₂RingHom, hr, eval₂_mul, ← eval_map, hβ.eq_zero, zero_mul]
  obtain ⟨ψ, hψ⟩ := exists_ringHom_comp_eq (A := StageLocalization k b) (S := stage k b) (T := B)
    (stageProj k b) (stageProj_surjective k b) g hker
  refine ⟨ψ, fun a => ?_, fun s => ?_⟩
  · have h := hψ (algebraMap k[X][X] (StageLocalization k b) (C a))
    rw [stageProj_algebraMap] at h
    simp only [eval₂_C] at h
    rw [h, IsLocalization.lift_eq, coe_eval₂RingHom, eval₂_C]
  · have hres : (residue B).comp g =
        (constantResidue k φ).comp ((endResidue k).comp (stageMap k b)) := by
      refine IsLocalization.ringHom_ext (stagePrime k b).primeCompl ?_
      refine RingHom.ext fun p => ?_
      simp only [RingHom.comp_apply]
      rw [IsLocalization.lift_eq, coe_eval₂RingHom, residue_eval₂ k hφ b β hβres,
        stageMap_algebraMap]
      rfl
    obtain ⟨z, rfl⟩ := stageProj_surjective k b s
    rw [hψ, coe_stageProj]
    exact RingHom.congr_fun hres z

/-- **Maps out of a stage ring: uniqueness.** Two ring maps from the stage ring of a simple point
`b` to `B` that extend `φ` and send `b` to elements with the residue of `b` are equal. -/
theorem stageHom_ext (hφ : Ideal.comap φ (maximalIdeal B) = Ideal.span {X}) {b : endRing k}
    (hb : IsSimplePoint k b) (χ₁ χ₂ : stage k b →+* B)
    (h₁ : ∀ a : k[X], χ₁ ⟨ι a, endChartCoordinate_mem_stage k b a⟩ = φ a)
    (h₂ : ∀ a : k[X], χ₂ ⟨ι a, endChartCoordinate_mem_stage k b a⟩ = φ a)
    (r₁ : residue B (χ₁ ⟨b, self_mem_stage k b⟩) = constantResidue k φ (endResidue k b))
    (r₂ : residue B (χ₂ ⟨b, self_mem_stage k b⟩) = constantResidue k φ (endResidue k b)) :
    χ₁ = χ₂ := by
  obtain ⟨G, hG0, hG1⟩ := hb
  have hev (χ : stage k b →+* B) (hχ : ∀ a : k[X], χ ⟨ι a, endChartCoordinate_mem_stage k b a⟩ = φ a) :
      (χ.comp (stageProj k b)).comp (algebraMap k[X][X] (StageLocalization k b)) =
        eval₂RingHom φ (χ ⟨b, self_mem_stage k b⟩) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.comp_apply, stageProj_algebraMap, coe_eval₂RingHom, eval₂_C]
      exact hχ a
    · simp only [RingHom.comp_apply, stageProj_algebraMap, coe_eval₂RingHom, eval₂_X]
  have hroot (χ : stage k b →+* B)
      (hχ : ∀ a : k[X], χ ⟨ι a, endChartCoordinate_mem_stage k b a⟩ = φ a) :
      (G.map φ).IsRoot (χ ⟨b, self_mem_stage k b⟩) := by
    show eval _ (G.map φ) = 0
    rw [eval_map, ← coe_eval₂RingHom, ← hev χ hχ]
    simp only [RingHom.comp_apply, stageProj_algebraMap]
    have h0 : (⟨eval₂ ι b G, eval₂_mem_stage k b G⟩ : stage k b) = 0 := Subtype.ext hG0
    rw [h0, map_zero]
  have heq : χ₁ ⟨b, self_mem_stage k b⟩ = χ₂ ⟨b, self_mem_stage k b⟩ := by
    refine Langlands.CommutativeAlgebra.eq_of_isRoot_of_sub_mem_maximalIdeal (hroot χ₁ h₁)
      (hroot χ₂ h₂) ((residue_eq_zero_iff _).1 (by rw [map_sub, r₁, r₂, sub_self])) ?_
    rw [derivative_map, eval_map, ← residue_ne_zero_iff_isUnit, residue_eval₂ k hφ b _ r₁,
      stageResidue, RingHom.comp_apply, coe_eval₂RingHom]
    exact (_root_.map_ne_zero _).2 ((isUnit_iff_endResidue_ne_zero k _).1 hG1)
  have hcomp : χ₁.comp (stageProj k b) = χ₂.comp (stageProj k b) :=
    IsLocalization.ringHom_ext (stagePrime k b).primeCompl
      (by rw [hev χ₁ h₁, hev χ₂ h₂, heq])
  refine RingHom.ext fun s => ?_
  obtain ⟨z, rfl⟩ := stageProj_surjective k b s
  exact RingHom.congr_fun hcomp z

/-- A local map `endRing k → B` extending `φ` sends every element to an element with the image of
its residue. -/
theorem residue_apply_of_isLocalHom (ψ : endRing k →+* B) [IsLocalHom ψ]
    (hψ : ψ.comp ι = φ) (x : endRing k) :
    residue B (ψ x) = constantResidue k φ (endResidue k x) := by
  have hn : ψ (x - ι (C (endResidue k x))) ∈ maximalIdeal B := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := (isUnit_iff_endResidue_ne_zero k _).1 (IsLocalHom.map_nonunit _ hu)
    exact this (endResidue_sub_endChartCoordinate_C k x)
  have h := (residue_eq_zero_iff _).2 hn
  rw [RingHom.map_sub, map_sub, sub_eq_zero, ← RingHom.comp_apply ψ, hψ] at h
  rw [h]
  rfl

/-- **The universal property of the end ring.** Every ring map `φ : k[x] → B` to a henselian local
ring with `φ⁻¹(𝔪_B) = (x)` extends along `x ↦ t` to a unique local ring map `endRing k → B`. -/
theorem existsUnique_endRing_hom (hφ : Ideal.comap φ (maximalIdeal B) = Ideal.span {X}) :
    ∃! ψ : endRing k →+* B, IsLocalHom ψ ∧ ψ.comp ι = φ := by
  classical
  choose b₀ hb₀ hx₀ _ using fun x : endRing k => exists_isSimplePoint_mem_stage k x x
  choose ψs hψι hψres using fun (b : endRing k) (hb : IsSimplePoint k b) =>
    exists_stageHom k hφ hb
  have hrestr : ∀ {b b' : endRing k} (hb : IsSimplePoint k b) (hb' : IsSimplePoint k b')
      (h : b ∈ stage k b'), ψs b hb = (ψs b' hb').comp (Subring.inclusion (stage_le_stage k h)) := by
    intro b b' hb hb' h
    exact stageHom_ext k hφ hb _ _ (hψι b hb) (fun a => hψι b' hb' a) (hψres b hb _)
      (hψres b' hb' _)
  have key : ∀ (x b : endRing k) (hb : IsSimplePoint k b) (hx : x ∈ stage k b),
      ψs (b₀ x) (hb₀ x) ⟨x, hx₀ x⟩ = ψs b hb ⟨x, hx⟩ := by
    intro x b hb hx
    obtain ⟨b'', hb'', h1, h2⟩ := exists_isSimplePoint_mem_stage k (b₀ x) b
    rw [hrestr (hb₀ x) hb'' h1, hrestr hb hb'' h2]
    rfl
  obtain ⟨f, hf⟩ : ∃ f : endRing k → B, ∀ x, f x = ψs (b₀ x) (hb₀ x) ⟨x, hx₀ x⟩ :=
    ⟨_, fun _ => rfl⟩
  have hfb (x b : endRing k) (hb : IsSimplePoint k b) (hx : x ∈ stage k b) :
      f x = ψs b hb ⟨x, hx⟩ := by
    rw [hf, key x b hb hx]
  have h1 : f 1 = 1 := by
    rw [hfb 1 (b₀ 1) (hb₀ 1) (one_mem _),
      show (⟨1, one_mem _⟩ : stage k (b₀ 1)) = 1 from Subtype.ext (OneMemClass.coe_one _).symm,
      map_one]
  have h0 : f 0 = 0 := by
    rw [hfb 0 (b₀ 0) (hb₀ 0) (zero_mem _),
      show (⟨0, zero_mem _⟩ : stage k (b₀ 0)) = 0 from Subtype.ext (ZeroMemClass.coe_zero _).symm,
      map_zero]
  have hmul (x y : endRing k) : f (x * y) = f x * f y := by
    obtain ⟨b, hb, hx, hy⟩ := exists_isSimplePoint_mem_stage k x y
    rw [hfb x b hb hx, hfb y b hb hy, hfb (x * y) b hb (mul_mem hx hy), ← map_mul]
    rfl
  have hadd (x y : endRing k) : f (x + y) = f x + f y := by
    obtain ⟨b, hb, hx, hy⟩ := exists_isSimplePoint_mem_stage k x y
    rw [hfb x b hb hx, hfb y b hb hy, hfb (x + y) b hb (add_mem hx hy), ← (ψs b hb).map_add]
    rfl
  obtain ⟨ψ, hψ⟩ : ∃ ψ : endRing k →+* B, ∀ x, ψ x = f x :=
    ⟨{ toFun := f, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd },
      fun _ => rfl⟩
  refine ⟨ψ, ⟨⟨fun x hx => ?_⟩, ?_⟩, ?_⟩
  · rw [isUnit_iff_endResidue_ne_zero]
    intro h0
    have h := hψres (b₀ x) (hb₀ x) ⟨x, hx₀ x⟩
    rw [← hf, ← hψ] at h
    change residue B (ψ x) = constantResidue k φ (endResidue k x) at h
    rw [h0, map_zero] at h
    exact (residue_ne_zero_iff_isUnit _).2 hx h
  · refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, hψ, hfb _ _ (hb₀ (ι a)) (endChartCoordinate_mem_stage k _ a)]
    exact hψι (b₀ (ι a)) (hb₀ _) a
  · rintro ψ' ⟨hloc, hcomp⟩
    refine RingHom.ext fun x => ?_
    have h := stageHom_ext k hφ (hb₀ x) (ψ'.comp (stage k (b₀ x)).subtype) (ψs (b₀ x) (hb₀ x))
      (fun a => RingHom.congr_fun hcomp a) (hψι _ _)
      (residue_apply_of_isLocalHom k ψ' hcomp (b₀ x)) (hψres _ _ _)
    rw [hψ, hf]
    exact RingHom.congr_fun h ⟨x, hx₀ x⟩

end Langlands.Henniart.Laumon
