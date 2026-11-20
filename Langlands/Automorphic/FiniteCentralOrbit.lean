import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Character vectors retaining a simple subquotient

The algebra in Langlands (1979), Lemma 6, for a locally finite commuting
central action on a module. The orbit-span argument treats the kernel and
image of a shifted central operator using the same dimension comparison.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Automorphic

universe uR uA uV uW

variable {R : Type uR} [Ring R]
variable {A : Type uA} [CommGroup A]
variable {V : Type uV} [AddCommGroup V] [Module R V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module R W]

/-- The complex span of the orbit of a vector under the auxiliary central action. -/
def centralOrbitSpan (z : A →* Module.End R V) (x : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range fun a => z a x)

private theorem mem_centralOrbitSpan (z : A →* Module.End R V) (x : V) :
    x ∈ centralOrbitSpan z x :=
  Submodule.subset_span ⟨1, by simp⟩

private theorem map_centralOrbitSpan (z : A →* Module.End R V) (x : V)
    (L : V →ₗ[ℂ] V) (hL : ∀ a y, L (z a y) = z a (L y)) :
    (centralOrbitSpan z x).map L = centralOrbitSpan z (L x) := by
  unfold centralOrbitSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
  exact congrArg Set.range (funext fun a => hL a x)

private theorem finrank_centralOrbitSpan_lt (z : A →* Module.End R V) (x : V)
    [Module.Finite ℂ (centralOrbitSpan z x)]
    (L : V →ₗ[ℂ] V) (hL : ∀ a y, L (z a y) = z a (L y))
    {w : V} (hw : w ∈ centralOrbitSpan z x) (hn : w ≠ 0) (hzero : L w = 0) :
    Module.finrank ℂ (centralOrbitSpan z (L x)) < Module.finrank ℂ (centralOrbitSpan z x) := by
  let f := L.domRestrict (centralOrbitSpan z x)
  have hk : Nontrivial (LinearMap.ker f) :=
    ⟨⟨⟨⟨w, hw⟩, hzero⟩, 0, fun h => hn (congrArg (fun v => v.val.val) h)⟩⟩
  have hdim := LinearMap.finrank_range_add_finrank_ker f
  have hpos := Module.finrank_pos (R := ℂ) (M := LinearMap.ker f)
  rw [LinearMap.range_domRestrict, map_centralOrbitSpan z x L hL] at hdim
  omega

variable [Algebra ℂ R] [IsScalarTower ℂ R V]

private theorem exists_character_of_eigenvector (z : A →* Module.End R V) {x : V} (hx : x ≠ 0)
    (heig : ∀ a : A, ∃ c : ℂ, z a x = c • x) :
    ∃ χ : A →* ℂˣ, ∀ a : A, z a x = (χ a : ℂ) • x := by
  choose c hc using heig
  have hone : c 1 = 1 := smul_left_injective ℂ hx (by simpa using (hc 1).symm)
  have hmul (a b : A) : c (a * b) = c a * c b := by
    apply smul_left_injective ℂ hx
    change c (a * b) • x = (c a * c b) • x
    calc
      c (a * b) • x = z a (z b x) := by
        rw [← hc, map_mul, Module.End.mul_apply]
      _ = c b • z a x := by
        rw [hc b]
        exact ((z a).restrictScalars ℂ).map_smul (c b) x
      _ = (c a * c b) • x := by rw [hc a, smul_smul, mul_comm (c b)]
  have hne (a : A) : c a ≠ 0 := by
    intro h
    have hh := hmul a a⁻¹
    rw [mul_inv_cancel, hone, h, zero_mul] at hh
    exact one_ne_zero hh
  let χ : A →* ℂˣ :=
    { toFun := fun a => Units.mk0 (c a) (hne a)
      map_one' := Units.ext hone
      map_mul' := fun a b => Units.ext (hmul a b) }
  exact ⟨χ, hc⟩

/-- A nonzero quotient map from a cyclic module can be moved to a cyclic module
whose generator is an eigenvector of the auxiliary central action. The target
and the central action are kept fixed. -/
theorem exists_centralCharacter_cyclic_of_nonzero (z : A →* Module.End R V)
    (hfinite : ∀ x : V, Module.Finite ℂ (centralOrbitSpan z x)) {x₀ : V}
    (q₀ : (R ∙ x₀) →ₗ[R] W) (hq₀ : q₀ ⟨x₀, Submodule.mem_span_singleton_self x₀⟩ ≠ 0) :
    ∃ (x : V) (χ : A →* ℂˣ) (q : (R ∙ x) →ₗ[R] W),
      q ⟨x, Submodule.mem_span_singleton_self x⟩ ≠ 0 ∧
      ∀ a : A, z a x = (χ a : ℂ) • x := by
  classical
  let good (d : ℕ) := ∃ (x : V) (q : (R ∙ x) →ₗ[R] W),
    q ⟨x, Submodule.mem_span_singleton_self x⟩ ≠ 0 ∧ Module.finrank ℂ (centralOrbitSpan z x) = d
  have hex : ∃ d : ℕ, good d := ⟨_, x₀, q₀, hq₀, rfl⟩
  obtain ⟨x, q, hq, hdim⟩ := Nat.find_spec hex
  have hx : x ≠ 0 := by
    intro h
    have hz : (⟨x, Submodule.mem_span_singleton_self x⟩ : (R ∙ x)) = 0 := Subtype.ext h
    exact hq (by rw [hz, map_zero])
  by_cases heig : ∀ a : A, ∃ c : ℂ, z a x = c • x
  · obtain ⟨χ, hχ⟩ := exists_character_of_eigenvector z hx heig
    exact ⟨x, χ, q, hq, hχ⟩
  push Not at heig
  obtain ⟨a, ha⟩ := heig
  let Y := centralOrbitSpan z x
  let : Module.Finite ℂ Y := hfinite x
  let : Nontrivial Y :=
    ⟨⟨⟨x, mem_centralOrbitSpan z x⟩, 0, fun h => hx (congrArg Subtype.val h)⟩⟩
  have hstable : ∀ y ∈ Y, (z a).restrictScalars ℂ y ∈ Y := by
    intro y hy
    have hmap := map_centralOrbitSpan z x ((z a).restrictScalars ℂ) (by
      intro b v
      change (z a * z b) v = (z b * z a) v
      rw [← map_mul, ← map_mul, mul_comm a b])
    have hle : Y.map ((z a).restrictScalars ℂ) ≤ Y := by
      change (centralOrbitSpan z x).map _ ≤ _
      rw [hmap]
      apply Submodule.span_le.mpr
      rintro _ ⟨b, rfl⟩
      exact Submodule.subset_span ⟨b * a, by simp [Module.End.mul_apply]⟩
    exact hle (Submodule.mem_map_of_mem hy)
  let Z : Module.End ℂ Y := ((z a).restrictScalars ℂ).restrict hstable
  obtain ⟨c, hc⟩ := Z.exists_eigenvalue
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  let D : Module.End R V := z a - c • LinearMap.id
  have hDx : D x ≠ 0 := fun h => ha c (sub_eq_zero.mp h)
  have hwzero : D w.val = 0 := sub_eq_zero.mpr (congrArg Subtype.val hw.apply_eq_smul)
  let S := R ∙ x
  let f := D.domRestrict S
  by_cases hker : LinearMap.ker f ≤ LinearMap.ker q
  · have hcomm : ∀ b y, D.restrictScalars ℂ (z b y) = z b (D.restrictScalars ℂ y) := by
      intro b y
      have hmul : z a * z b = z b * z a := by rw [← map_mul, ← map_mul, mul_comm a b]
      have h := congrArg (fun L : Module.End R V => L y) hmul
      change z a (z b y) = z b (z a y) at h
      change z a (z b y) - c • z b y = z b (z a y - c • y)
      rw [map_sub, h]
      exact congrArg (z b (z a y) - ·) (((z b).restrictScalars ℂ).map_smul c y).symm
    have hlt := finrank_centralOrbitSpan_lt z x (D.restrictScalars ℂ) hcomm
      w.property (fun h => hw.2 (Subtype.ext h)) hwzero
    have hrange : LinearMap.range f = R ∙ D x := by
      dsimp [f, S]
      rw [LinearMap.range_domRestrict, Submodule.map_span, Set.image_singleton]
    let q' : (R ∙ D x) →ₗ[R] W := (LinearMap.ker f).liftQ q hker ∘ₗ
      f.quotKerEquivRange.symm.toLinearMap ∘ₗ (LinearEquiv.ofEq _ _ hrange.symm).toLinearMap
    have hq' : q' ⟨D x, Submodule.mem_span_singleton_self (D x)⟩ ≠ 0 := by
      have he : (LinearEquiv.ofEq _ _ hrange.symm) ⟨D x, Submodule.mem_span_singleton_self (D x)⟩ =
          ⟨f ⟨x, Submodule.mem_span_singleton_self x⟩, LinearMap.mem_range_self _ _⟩ := Subtype.ext rfl
      unfold q'
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he,
        LinearMap.quotKerEquivRange_symm_apply_image]
      exact hq
    exfalso
    exact (Nat.not_lt_of_ge (Nat.find_min' hex ⟨D x, q', hq', rfl⟩)) (hlt.trans_eq hdim)
  · obtain ⟨y, hy, hyq⟩ := SetLike.not_le_iff_exists.mp hker
    have hy0 : D y.val = 0 := hy
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp y.property
    let L : V →ₗ[ℂ] V :=
      { toFun := fun v => s • v
        map_add' := smul_add s
        map_smul' := fun d v => smul_comm s d v }
    have hcomm (b : A) (v : V) : L (z b v) = z b (L v) := ((z b).map_smul s v).symm
    have hDy : L (D x) = 0 := by
      change s • D x = 0
      rw [← D.map_smul, hs, hy0]
    have hDxY : D x ∈ Y := by
      change z a x - c • x ∈ Y
      exact Y.sub_mem (Submodule.subset_span ⟨a, rfl⟩)
        (Y.smul_mem c (mem_centralOrbitSpan z x))
    have hlt := finrank_centralOrbitSpan_lt z x L hcomm hDxY hDx hDy
    have hincl : (R ∙ y.val) ≤ S := (Submodule.span_singleton_le_iff_mem _ _).mpr y.property
    let q' := q.comp (Submodule.inclusion hincl)
    have hq' : q' ⟨y.val, Submodule.mem_span_singleton_self y.val⟩ ≠ 0 := hyq
    change Module.finrank ℂ (centralOrbitSpan z (s • x)) < Module.finrank ℂ Y at hlt
    rw [hs] at hlt
    exfalso
    exact (Nat.not_lt_of_ge (Nat.find_min' hex ⟨y.val, q', hq', rfl⟩)) (hlt.trans_eq hdim)

/-- Langlands's algebraic central-character step for a simple subquotient. -/
theorem exists_centralCharacter_cyclic_subquotient (z : A →* Module.End R V)
    (hfinite : ∀ x : V, Module.Finite ℂ (centralOrbitSpan z x)) [IsSimpleModule R W]
    {S : Submodule R V} (q : S →ₗ[R] W) (hq : Function.Surjective q) :
    ∃ (x : V) (χ : A →* ℂˣ) (q' : (R ∙ x) →ₗ[R] W),
      Function.Surjective q' ∧ ∀ a : A, z a x = (χ a : ℂ) • x := by
  have := IsSimpleModule.nontrivial R W
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨x, hqx⟩ := hq w
  let i : (R ∙ (x : V)) →ₗ[R] S :=
    Submodule.inclusion ((Submodule.span_singleton_le_iff_mem _ _).mpr x.property)
  have h : (q.comp i) ⟨x.val, Submodule.mem_span_singleton_self x.val⟩ ≠ 0 := hqx ▸ hw
  obtain ⟨y, χ, p, hp, hχ⟩ := exists_centralCharacter_cyclic_of_nonzero z hfinite (q.comp i) h
  exact ⟨y, χ, p, p.surjective_or_eq_zero.resolve_right (fun he => hp (by simp [he])), hχ⟩

end Langlands.Automorphic
