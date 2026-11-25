import Langlands.Group.Classical.Bruhat
import Langlands.LinearAlgebra.EpsilonHermitian.Determinant
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Tactic.LinearCombination

/-!
# The Rao function

GKT §4.5 (and Lemma 4.29 of §4.4.1), for a commutative `D = E`: a field `K` with an involution `τ`
(`τ = id`: `D = F`; `τ ≠ id`: `E/F` quadratic), `r = 1`.

Let `h` be a non-degenerate `-ε`-Hermitian form on a finite-dimensional `K`-space `V` (the book's
`W`, a left space as in `Basic.lean`), `X` a Lagrangian, `P = P(X)`, and `e` a standard basis with
`X = span {eᵢ}`.

* `siegelDet h X : P(X) →* Kˣ`, `p ↦ det(p|_X)`;
* `siegelDet_mul_conj_siegelDet` (Lemma 4.29): `det(g|_Y) · det(g|_X)^τ = 1` on the Levi factor;
* `exists_siegelDet_mul_siegelDet_eq` (Lemma 4.35): if `p₁ g p₂ = g`, then
  `det(p₁ p₂|_X) = det(q) det(q)^τ` for `q` the map induced by `p₁` on `X/(X ∩ gX)`;
  `mk_siegelDet_mul_siegelDet_eq` (Corollary 4.36);
* `StandardBasis.raoFunction e : G → Kˣ ⧸ 𝒩(Kˣ)` (Definition 4.37), `raoFunction_eq`
  (any decomposition `g = p₁ w_S p₂` computes it), Lemma 4.38
  (`raoFunction_eq_of_lagrangianFst_eq`),
  Lemma 4.40 (`raoFunction_inv`, `raoFunction_mul_mul`), Lemma 4.44 (`raoFunction_conj`),
  Proposition 4.41 (`raoFunction_mul`) and Corollary 4.42 (`raoFunction_mul_of_det_eq_one`);
* `scale h a s ha` (the book's `W^a`, `a^τ = ±a`), `StandardBasis.scale`, and Lemma 4.45
  (`raoFunction_scale`).

The determinant is Mathlib's on the left space `V`, which is `τ` of the book's determinant on the
right space `W` (Proposition B.6); with this convention Proposition 4.41 holds as printed.
-/
noncomputable section

open Matrix

namespace Langlands

namespace EpsilonHermitianForm

open Module
open Langlands.RingInvo (conj conjRingHom conjRingHom_apply normHom normSubgroup)

variable {K : Type*} [Field K] {τ : _root_.RingInvo K} {V : Type*} [AddCommGroup V] [Module K V]

section SiegelDet

variable {ε' : ℤˣ} {h : EpsilonHermitianForm τ ε' V}

variable (h) in
/-- The restriction `P(X) → GL(X)`, `p ↦ p|_X`, as a homomorphism (GKT §4.4.1). -/
def siegelRestrict (X : Submodule K V) : h.siegelParabolic X →* (X ≃ₗ[K] X) where
  toFun p := restrictOfMemSiegelParabolic p.2
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

@[simp] theorem siegelRestrict_apply (X : Submodule K V) (p : h.siegelParabolic X) (x : X) :
    ((h.siegelRestrict X p x : X) : V) = ((p : h.isometryGroup) : V ≃ₗ[K] V) x := rfl

variable (h) in
/-- `p ↦ det(p|_X)` on the Siegel parabolic (GKT (4.15)). -/
def siegelDet (X : Submodule K V) : h.siegelParabolic X →* Kˣ :=
  LinearEquiv.det.comp (h.siegelRestrict X)

theorem coe_siegelDet (X : Submodule K V) (p : h.siegelParabolic X) :
    (h.siegelDet X p : K) = LinearMap.det (h.siegelRestrict X p : X →ₗ[K] X) :=
  LinearEquiv.coe_det _

variable (h) in
/-- The `τ`-sesquilinear pairing `A × B → K`, `(a, b) ↦ h a b`, of two subspaces. -/
def pairing (A B : Submodule K V) : A →ₗ[K] B →ₛₗ[conjRingHom τ] K :=
  LinearMap.mk₂'ₛₗ (RingHom.id K) (conjRingHom τ) (fun a b => h a b)
    (fun a a' b => by simp only [Submodule.coe_add, h.map_add_left])
    (fun c a b => by simp only [Submodule.coe_smul, h.map_smul_left, RingHom.id_apply, smul_eq_mul])
    (fun a b b' => by simp only [Submodule.coe_add, h.map_add_right])
    (fun c a b => by
      simp only [Submodule.coe_smul, h.map_smul_right, conjRingHom_apply, smul_eq_mul]
      ring)

@[simp] theorem pairing_apply (A B : Submodule K V) (a : A) (b : B) :
    h.pairing A B a b = h a b := rfl

/-- GKT Lemma 4.29: for `g` in the Levi factor `P(X) ∩ P(Y)` of a polarization `V = X ⊕ Y`,
`det(g|_Y) = (det(g|_X))^{-τ}`. -/
theorem siegelDet_mul_conj_siegelDet [FiniteDimensional K V] (hh : h.Nondegenerate)
    {X Y : Submodule K V} (hX : h.IsLagrangian X) (hY : h.IsLagrangian Y) (hXY : Disjoint X Y)
    {g : h.isometryGroup} (hgX : g ∈ h.siegelParabolic X) (hgY : g ∈ h.siegelParabolic Y) :
    (h.siegelDet Y ⟨g, hgY⟩ : K) * conj τ (h.siegelDet X ⟨g, hgX⟩ : K) = 1 := by
  rw [coe_siegelDet, coe_siegelDet]
  have hd : finrank K X = finrank K Y := by
    have := hX.two_mul_finrank hh; have := hY.two_mul_finrank hh; omega
  refine det_mul_conj_det_eq_one (h.pairing X Y) ?_ hd _ _ ?_
  · intro x hx
    have : (x : V) ∈ h.orthogonal Y := fun y hy => hx ⟨y, hy⟩
    rw [hY] at this
    exact Subtype.ext (Submodule.disjoint_def.1 hXY _ x.2 this)
  · intro x y
    exact isometryGroup_apply g x y

/-- GKT Lemma 4.35 (Rao's consistency lemma): if `p₁ g p₂ = g` with `p₁, p₂ ∈ P(X)`, then `p₁`
preserves `X ∩ g X`, and `det(p₁ p₂|_X) = det(q) det(q)^τ` for the map `q` induced by `p₁` on
`X/(X ∩ g X)`. -/
theorem exists_siegelDet_mul_siegelDet_eq [FiniteDimensional K V] (hh : h.Nondegenerate)
    {X : Submodule K V} (hX : h.IsLagrangian X) {g : h.isometryGroup}
    (p₁ p₂ : h.siegelParabolic X) (H : (p₁ : h.isometryGroup) * g * p₂ = g) :
    ∃ q : (X ⧸ (X ⊓ X.map (g : V ≃ₗ[K] V).toLinearMap).comap X.subtype) →ₗ[K]
        (X ⧸ (X ⊓ X.map (g : V ≃ₗ[K] V).toLinearMap).comap X.subtype),
      (∀ x : X, q (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk (h.siegelRestrict X p₁ x)) ∧
      ((h.siegelDet X p₁ * h.siegelDet X p₂ : Kˣ) : K) =
        LinearMap.det q * conj τ (LinearMap.det q) := by
  set G' := X.map (g : V ≃ₗ[K] V).toLinearMap with hG'
  set K₀ := X ⊓ G' with hK₀
  have hG'L : h.IsLagrangian G' := hX.map g
  have hpg : (p₁ : h.isometryGroup) * g = g * (p₂ : h.isometryGroup)⁻¹ := eq_mul_inv_of_mul_eq H
  have hp₁G : (p₁ : h.isometryGroup) ∈ h.siegelParabolic G' := by
    change G'.map _ = G'
    rw [hG', ← map_isometryGroup_mul, hpg, map_isometryGroup_mul,
      show X.map (((p₂ : h.isometryGroup)⁻¹ : h.isometryGroup) : V ≃ₗ[K] V).toLinearMap = X from
        (h.siegelParabolic X).inv_mem p₂.2]
  set f₁ : X →ₗ[K] X := (h.siegelRestrict X p₁ : X →ₗ[K] X)
  set f₂ : G' →ₗ[K] G' := (restrictOfMemSiegelParabolic hp₁G : G' →ₗ[K] G')
  set W₁ := K₀.comap X.subtype
  set W₂ := K₀.comap G'.subtype
  have hK₀p : ∀ v ∈ K₀, ((p₁ : h.isometryGroup) : V ≃ₗ[K] V) v ∈ K₀ := fun v hv =>
    ⟨apply_mem_of_mem_siegelParabolic p₁.2 hv.1, apply_mem_of_mem_siegelParabolic hp₁G hv.2⟩
  have hW₁ : W₁ ≤ W₁.comap f₁ := fun x hx => hK₀p x hx
  have hW₂ : W₂ ≤ W₂.comap f₂ := fun x hx => hK₀p x hx
  -- the parts on `K₀` agree
  have hres : LinearMap.det (f₁.restrict hW₁) = LinearMap.det (f₂.restrict hW₂) := by
    let e : W₁ ≃ₗ[K] W₂ := (Submodule.comapSubtypeEquivOfLe (inf_le_left : K₀ ≤ X)).trans
      (Submodule.comapSubtypeEquivOfLe (inf_le_right : K₀ ≤ G')).symm
    rw [← LinearMap.det_conj (f₁.restrict hW₁) e]
    congr 1
  -- `det(p₂|_X) = det(p₁|_{gX})⁻¹`
  have hp₂ : (h.siegelDet X p₂ : K) * LinearMap.det f₂ = 1 := by
    let eg : X ≃ₗ[K] G' := (g : V ≃ₗ[K] V).submoduleMap X
    have hconj : (eg.symm.trans (h.siegelRestrict X p₂)).trans eg =
        (restrictOfMemSiegelParabolic hp₁G).symm := by
      apply LinearEquiv.ext
      intro y
      apply (restrictOfMemSiegelParabolic hp₁G).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      change ((p₁ : h.isometryGroup) : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V)
        (((p₂ : h.isometryGroup) : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V).symm y))) = y
      rw [← isometryGroup_coe_mul_apply, ← isometryGroup_coe_mul_apply]
      rw [H]
      exact (g : V ≃ₗ[K] V).apply_symm_apply y
    have := LinearEquiv.det_conj (h.siegelRestrict X p₂) eg
    rw [hconj, LinearEquiv.det_symm, map_inv] at this
    rw [show (h.siegelDet X p₂ : K) = (LinearEquiv.det (h.siegelRestrict X p₂) : K) from rfl,
      ← this, Units.val_inv_eq_inv_val, LinearEquiv.coe_det]
    have hne := (LinearEquiv.det (restrictOfMemSiegelParabolic hp₁G)).ne_zero
    rw [LinearEquiv.coe_det] at hne
    exact inv_mul_cancel₀ hne
  -- the quotient maps and the induced pairing
  set q₁ := W₁.mapQ W₁ f₁ hW₁
  set q₂ := W₂.mapQ W₂ f₂ hW₂
  have hβ₁ : W₁ ≤ LinearMap.ker (h.pairing X G') := by
    intro x hx
    rw [LinearMap.mem_ker]
    ext y
    exact hG'L.apply_eq_zero hx.2 y.2
  have hβ₂ : W₂ ≤ LinearMap.ker (h.pairing X G').flip := by
    intro y hy
    rw [LinearMap.mem_ker]
    ext x
    exact hX.apply_eq_zero x.2 hy.1
  set β := (h.pairing X G').liftQ₂ W₁ W₂ hβ₁ hβ₂
  have hdual : LinearMap.det q₂ * conj τ (LinearMap.det q₁) = 1 := by
    refine det_mul_conj_det_eq_one β ?_ ?_ q₁ q₂ ?_
    · intro a ha
      induction a using Submodule.Quotient.induction_on with
      | H x =>
        rw [Submodule.Quotient.mk_eq_zero]
        have hx : (x : V) ∈ h.orthogonal G' := fun y hy => by
          have := ha (Submodule.Quotient.mk ⟨y, hy⟩)
          rwa [LinearMap.liftQ₂_mk, pairing_apply] at this
        rw [hG'L] at hx
        exact ⟨x.2, hx⟩
    · have e1 := Submodule.finrank_quotient_add_finrank W₁
      have e2 := Submodule.finrank_quotient_add_finrank W₂
      have e3 : finrank K W₁ = finrank K W₂ := by
        rw [finrank_comap_subtype, finrank_comap_subtype, inf_eq_left.2 inf_le_left,
          inf_eq_left.2 inf_le_right]
      have e4 := hX.two_mul_finrank hh
      have e5 := hG'L.two_mul_finrank hh
      omega
    · intro a b
      induction a using Submodule.Quotient.induction_on with
      | H x =>
        induction b using Submodule.Quotient.induction_on with
        | H y =>
          rw [Submodule.mapQ_apply, Submodule.mapQ_apply, LinearMap.liftQ₂_mk,
            LinearMap.liftQ₂_mk, pairing_apply, pairing_apply]
          exact isometryGroup_apply _ (x : V) (y : V)
  refine ⟨q₁, fun x => Submodule.mapQ_apply _ _ _ _, ?_⟩
  have d₁ := LinearMap.det_eq_det_mul_det W₁ f₁ hW₁
  have d₂ := LinearMap.det_eq_det_mul_det W₂ f₂ hW₂
  rw [Units.val_mul, coe_siegelDet]
  have hq₂ : LinearMap.det q₂ ≠ 0 := left_ne_zero_of_mul_eq_one hdual
  have hr : LinearMap.det (f₂.restrict hW₂) ≠ 0 := by
    intro h0; rw [d₂, h0, zero_mul, mul_zero] at hp₂; exact zero_ne_one hp₂
  -- `det f₁ · det(p₂|_X) = det q₁ / det q₂ = det q₁ · det q₁^τ`
  have key : LinearMap.det f₁ * (h.siegelDet X p₂ : K) * LinearMap.det q₂ =
      LinearMap.det q₁ := by
    have : (h.siegelDet X p₂ : K) * (LinearMap.det (f₂.restrict hW₂) * LinearMap.det q₂) = 1 := by
      rw [← d₂]; exact hp₂
    calc LinearMap.det f₁ * (h.siegelDet X p₂ : K) * LinearMap.det q₂
        = LinearMap.det q₁ * ((h.siegelDet X p₂ : K) *
            (LinearMap.det (f₂.restrict hW₂) * LinearMap.det q₂)) := by
          rw [d₁, hres]; ring
      _ = LinearMap.det q₁ := by rw [this, mul_one]
  have : LinearMap.det q₁ * conj τ (LinearMap.det q₁) * LinearMap.det q₂ = LinearMap.det q₁ := by
    calc LinearMap.det q₁ * conj τ (LinearMap.det q₁) * LinearMap.det q₂
        = LinearMap.det q₁ * (LinearMap.det q₂ * conj τ (LinearMap.det q₁)) := by ring
      _ = LinearMap.det q₁ := by rw [hdual, mul_one]
  exact mul_right_cancel₀ hq₂ (key.trans this.symm)

/-- GKT Corollary 4.36: `det(p₁ p₂|_X)` modulo norms does not depend on the decomposition
`g = p₁ w p₂` for a fixed `w` (any element of `G`). -/
theorem mk_siegelDet_mul_siegelDet_eq [FiniteDimensional K V] (hh : h.Nondegenerate)
    {X : Submodule K V} (hX : h.IsLagrangian X) {w : h.isometryGroup}
    (p₁ p₂ p₁' p₂' : h.siegelParabolic X)
    (H : (p₁ : h.isometryGroup) * w * p₂ = (p₁' : h.isometryGroup) * w * p₂') :
    (QuotientGroup.mk (h.siegelDet X p₁ * h.siegelDet X p₂) : Kˣ ⧸ normSubgroup τ) =
      QuotientGroup.mk (h.siegelDet X p₁' * h.siegelDet X p₂') := by
  obtain ⟨q, -, hq⟩ := h.exists_siegelDet_mul_siegelDet_eq hh hX (p₁'⁻¹ * p₁) (p₂ * p₂'⁻¹)
    (g := w) (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (p₁' : h.isometryGroup)⁻¹ * p₁ * w * (p₂ * (p₂' : h.isometryGroup)⁻¹)
          = (p₁' : h.isometryGroup)⁻¹ * ((p₁ : h.isometryGroup) * w * p₂) *
              (p₂' : h.isometryGroup)⁻¹ := by group
        _ = w := by rw [H]; group)
  have hq0 : LinearMap.det q ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hq
    exact (Units.ne_zero _) hq
  apply RingInvo.mk_eq_mk_of_coe_eq_mul_norm τ (c := Units.mk0 _ hq0)
  rw [Units.val_mk0, ← hq, map_mul, map_mul, map_inv, map_inv]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

end SiegelDet

/-- An isometry of `h` as an element of the isometry group. -/
def IsometryEquiv.toIsometryGroup {ε' : ℤˣ} {h : EpsilonHermitianForm τ ε' V}
    (φ : IsometryEquiv h h) : h.isometryGroup :=
  ⟨φ.toLinearEquiv, fun x y => φ.map_app x y⟩

@[simp] theorem IsometryEquiv.toIsometryGroup_apply {ε' : ℤˣ} {h : EpsilonHermitianForm τ ε' V}
    (φ : IsometryEquiv h h) (v : V) :
    ((φ.toIsometryGroup : h.isometryGroup) : V ≃ₗ[K] V) v = φ v := rfl

private theorem exists_equiv_map_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {S S' : Finset ι}
    (hc : S.card = S'.card) : ∃ σ : ι ≃ ι, S.map σ.toEmbedding = S' := by
  have h₁ : Fintype.card {x // x ∈ S} = Fintype.card {x // x ∈ S'} := by
    rw [Fintype.card_coe, Fintype.card_coe, hc]
  have h₂ : Fintype.card {x // x ∉ S} = Fintype.card {x // x ∉ S'} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_coe, hc]
  let σ := Equiv.subtypeCongr (Fintype.equivOfCardEq h₁) (Fintype.equivOfCardEq h₂)
  refine ⟨σ, Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_map, hc])⟩
  have hmem : ∀ a ∈ S, σ a ∈ S' := by
    intro a ha
    simp only [σ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos ha,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact Subtype.mem _
  intro x hx
  rw [Finset.mem_map_equiv] at hx
  have := hmem _ hx
  rwa [Equiv.apply_symm_apply] at this

variable (K) in
/-- A sign `±1 ∈ ℤˣ` as a unit of `K`. -/
def signUnit (u : ℤˣ) : Kˣ := Units.map (Int.castRingHom K).toMonoidHom u

@[simp] theorem coe_signUnit (u : ℤˣ) : (signUnit K u : K) = ((u : ℤ) : K) := rfl

@[simp] theorem signUnit_one : signUnit K 1 = 1 := map_one _

theorem signUnit_inv (u : ℤˣ) : (signUnit K u)⁻¹ = signUnit K u := by
  rw [signUnit, ← map_inv, Int.units_inv_eq_self]

section Rao

variable {ε : ℤˣ} {h : EpsilonHermitianForm τ (-ε) V} [FiniteDimensional K V]

namespace StandardBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : h.StandardBasis ι)

/-- `w^f_S = π w^e_S π⁻¹` for the isometry `π : eₖ ↦ fₖ` (GKT proofs of Lemmas 4.38, 4.44). -/
theorem weylElement_eq_conj (f : h.StandardBasis ι) (S : Finset ι) :
    f.weylElement S = (e.isometryEquiv f).toIsometryGroup * e.weylElement S *
      ((e.isometryEquiv f).toIsometryGroup)⁻¹ := by
  apply f.isometryGroup_ext
  intro k
  have hπ : ∀ k, (((e.isometryEquiv f).toIsometryGroup : h.isometryGroup) : V ≃ₗ[K] V)
      (e.basis k) = f.basis k := e.isometryEquiv_apply_basis f
  rw [isometryGroup_coe_mul_apply, isometryGroup_coe_mul_apply, ← hπ k,
    isometryGroup_coe_inv_apply', hπ k, weylElement_basis, weylElement_basis]
  rcases k with i | i <;> by_cases hi : i ∈ S <;>
    simp only [weylImage, hi, ite_true, ite_false, map_smul, fst, snd, hπ]

omit [FiniteDimensional K V] in
/-- The isometry `eₖ ↦ fₖ` carries `X_e` onto `X_f`. -/
theorem map_isometryEquiv_lagrangianFst (f : h.StandardBasis ι) :
    e.lagrangianFst.map (((e.isometryEquiv f).toIsometryGroup : h.isometryGroup) :
      V ≃ₗ[K] V).toLinearMap = f.lagrangianFst :=
  e.map_lagrangianFst_eq _ f.isLagrangian_lagrangianFst fun i =>
    (e.isometryEquiv_apply_basis f (.inl i)).symm ▸ f.fst_mem_lagrangianFst i

omit [Fintype ι] [FiniteDimensional K V] in
theorem reindex_fst (σ : ι ≃ ι) (i : ι) : (e.reindex σ).fst i = e.fst (σ.symm i) := by
  simp [reindex, fst, Module.Basis.reindex_apply]

omit [Fintype ι] [FiniteDimensional K V] in
theorem reindex_snd (σ : ι ≃ ι) (i : ι) : (e.reindex σ).snd i = e.snd (σ.symm i) := by
  simp [reindex, snd, Module.Basis.reindex_apply]

omit [Fintype ι] [FiniteDimensional K V] in
theorem lagrangianFst_reindex (σ : ι ≃ ι) : (e.reindex σ).lagrangianFst = e.lagrangianFst := by
  rw [lagrangianFst, lagrangianFst, show Set.range (e.reindex σ).fst = Set.range e.fst by
    ext v; simp only [Set.mem_range, reindex_fst]
    exact ⟨fun ⟨i, hi⟩ => ⟨σ.symm i, hi⟩, fun ⟨i, hi⟩ => ⟨σ i, by simpa using hi⟩⟩]

theorem weylElement_reindex (σ : ι ≃ ι) (S : Finset ι) :
    (e.reindex σ).weylElement (S.map σ.toEmbedding) = e.weylElement S := by
  apply e.isometryGroup_ext
  rintro (i | i)
  · have hf : e.basis (.inl i) = (e.reindex σ).fst (σ i) := by
      rw [reindex_fst, Equiv.symm_apply_apply]; rfl
    have hs : e.snd i = (e.reindex σ).snd (σ i) := by rw [reindex_snd, Equiv.symm_apply_apply]
    rw [hf]
    by_cases hi : i ∈ S
    · rw [(e.reindex σ).weylElement_fst_of_mem (by simpa using hi), ← hf,
        show e.basis (.inl i) = e.fst i from rfl, e.weylElement_fst_of_mem hi, hs]
    · rw [(e.reindex σ).weylElement_fst_of_not_mem (by simpa using hi), ← hf,
        show e.basis (.inl i) = e.fst i from rfl, e.weylElement_fst_of_not_mem hi]
  · have hs : e.basis (.inr i) = (e.reindex σ).snd (σ i) := by
      rw [reindex_snd, Equiv.symm_apply_apply]; rfl
    have hf : e.fst i = (e.reindex σ).fst (σ i) := by rw [reindex_fst, Equiv.symm_apply_apply]
    rw [hs]
    by_cases hi : i ∈ S
    · rw [(e.reindex σ).weylElement_snd_of_mem (by simpa using hi), ← hs,
        show e.basis (.inr i) = e.snd i from rfl, e.weylElement_snd_of_mem hi, hf]
    · rw [(e.reindex σ).weylElement_snd_of_not_mem (by simpa using hi), ← hs,
        show e.basis (.inr i) = e.snd i from rfl, e.weylElement_snd_of_not_mem hi]

/-- Weyl elements of subsets of the same size are conjugate under `P(X)`. -/
theorem exists_weylElement_eq_conj {S S' : Finset ι} (hc : S.card = S'.card) :
    ∃ π ∈ h.siegelParabolic e.lagrangianFst, e.weylElement S' = π * e.weylElement S * π⁻¹ := by
  obtain ⟨σ, hσ⟩ := exists_equiv_map_eq hc
  have hπ : (e.isometryEquiv (e.reindex σ)).toIsometryGroup ∈
      h.siegelParabolic e.lagrangianFst := by
    change e.lagrangianFst.map _ = _
    rw [e.map_isometryEquiv_lagrangianFst, e.lagrangianFst_reindex σ]
  have h1 := e.weylElement_eq_conj (e.reindex σ) S'
  rw [← hσ, e.weylElement_reindex σ S, hσ] at h1
  refine ⟨((e.isometryEquiv (e.reindex σ)).toIsometryGroup)⁻¹,
    (h.siegelParabolic _).inv_mem hπ, ?_⟩
  rw [h1, inv_inv]; group


/-- The basis `(eᵢ)` of `X = span {eᵢ}`. -/
def basisFst : Basis ι K e.lagrangianFst :=
  Basis.span (show LinearIndependent K e.fst from
    e.basis.linearIndependent.comp _ Sum.inl_injective)

omit [Fintype ι] [FiniteDimensional K V] in
@[simp] theorem basisFst_apply (i : ι) : (e.basisFst i : V) = e.fst i :=
  congrArg Subtype.val (Basis.span_apply (show LinearIndependent K e.fst from
    e.basis.linearIndependent.comp _ Sum.inl_injective) i)

omit [Fintype ι] [FiniteDimensional K V] in
/-- The basis `(eᵢ)_{i ∈ A}` of `X_A`. -/
def blockFstBasis (A : Set ι) : Basis A K (e.blockFst A) :=
  (Basis.span (show LinearIndependent K (fun i : A => e.fst i) from
    e.basis.linearIndependent.comp _ (Sum.inl_injective.comp Subtype.val_injective))).map
    (LinearEquiv.ofEq _ _ (by rw [blockFst, Set.image_eq_range]))

omit [Fintype ι] [FiniteDimensional K V] in
@[simp] theorem blockFstBasis_apply (A : Set ι) (i : A) : (e.blockFstBasis A i : V) = e.fst i := by
  simp only [blockFstBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply]
  exact congrArg Subtype.val (Basis.span_apply (show LinearIndependent K (fun i : A => e.fst i)
    from e.basis.linearIndependent.comp _ (Sum.inl_injective.comp Subtype.val_injective)) i)

omit [Fintype ι] [FiniteDimensional K V] in
/-- The basis `(eᵢ*)_{i ∈ A}` of `Y_A`. -/
def blockSndBasis (A : Set ι) : Basis A K (e.blockSnd A) :=
  (Basis.span (show LinearIndependent K (fun i : A => e.snd i) from
    e.basis.linearIndependent.comp _ (Sum.inr_injective.comp Subtype.val_injective))).map
    (LinearEquiv.ofEq _ _ (by rw [blockSnd, Set.image_eq_range]))

omit [Fintype ι] [FiniteDimensional K V] in
@[simp] theorem blockSndBasis_apply (A : Set ι) (i : A) : (e.blockSndBasis A i : V) = e.snd i := by
  simp only [blockSndBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply]
  exact congrArg Subtype.val (Basis.span_apply (show LinearIndependent K (fun i : A => e.snd i)
    from e.basis.linearIndependent.comp _ (Sum.inr_injective.comp Subtype.val_injective)) i)

omit [FiniteDimensional K V] in
/-- The coordinates in `(eᵢ)` are read off with the `eᵢ*`. -/
theorem basisFst_repr (x : e.lagrangianFst) (i : ι) : e.basisFst.repr x i = h x (e.snd i) := by
  conv_rhs => rw [← e.basisFst.sum_repr x]
  rw [Submodule.coe_sum, h.map_sum_left, Finset.sum_eq_single i]
  · rw [Submodule.coe_smul, h.map_smul_left, basisFst_apply, fst, snd, e.apply_inl_inr,
      ite_eq_left (rfl : i = i), mul_one]
  · intro j _ hj
    rw [Submodule.coe_smul, h.map_smul_left, basisFst_apply, fst, snd, e.apply_inl_inr,
      ite_eq_right_iff.2 (fun H => absurd H hj), mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [Fintype ι] [FiniteDimensional K V] in
theorem blockFstBasis_repr (A : Set ι) [Fintype A] (x : e.blockFst A) (i : A) :
    (e.blockFstBasis A).repr x i = h x (e.snd i) := by
  conv_rhs => rw [← (e.blockFstBasis A).sum_repr x]
  rw [Submodule.coe_sum, h.map_sum_left, Finset.sum_eq_single i]
  · rw [Submodule.coe_smul, h.map_smul_left, blockFstBasis_apply, fst, snd, e.apply_inl_inr,
      ite_eq_left (rfl : (i : ι) = i), mul_one]
  · intro j _ hj
    rw [Submodule.coe_smul, h.map_smul_left, blockFstBasis_apply, fst, snd, e.apply_inl_inr,
      ite_eq_right_iff.2 (fun H => absurd (Subtype.ext H) hj), mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [FiniteDimensional K V] in
/-- A map acting diagonally on `(eᵢ)` has determinant `∏ cᵢ`. -/
theorem det_eq_prod_of_apply_basisFst (f : e.lagrangianFst →ₗ[K] e.lagrangianFst) (c : ι → K)
    (hf : ∀ i, (f (e.basisFst i) : V) = c i • e.fst i) : LinearMap.det f = ∏ i, c i := by
  rw [← LinearMap.det_toMatrix e.basisFst, ← Matrix.det_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply, e.basisFst_repr, hf, h.map_smul_left, fst,
    snd, e.apply_inl_inr]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem weylElement_mul_self_fst (S : Finset ι) (i : ι) :
    ((e.weylElement S * e.weylElement S : h.isometryGroup) : V ≃ₗ[K] V) (e.fst i) =
      (if i ∈ S then (((-ε : ℤˣ) : ℤ) : K) else 1) • e.fst i := by
  rw [isometryGroup_coe_mul_apply]
  by_cases hi : i ∈ S
  · rw [e.weylElement_fst_of_mem hi, map_smul, e.weylElement_snd_of_mem hi]
    simp only [hi, ite_true]
  · rw [e.weylElement_fst_of_not_mem hi, e.weylElement_fst_of_not_mem hi]
    simp only [hi, ite_false, one_smul]

theorem weylElement_mul_self_mem (S : Finset ι) :
    e.weylElement S * e.weylElement S ∈ h.siegelParabolic e.lagrangianFst :=
  e.map_lagrangianFst_eq _ e.isLagrangian_lagrangianFst fun i => by
    rw [weylElement_mul_self_fst]; exact Submodule.smul_mem _ _ (e.fst_mem_lagrangianFst i)

/-- `w_S² = -ε` on `W_S`, so `det(w_S²|_X) = (-ε)^{|S|}`. -/
theorem coe_siegelDet_weylElement_mul_self (S : Finset ι) :
    (h.siegelDet e.lagrangianFst ⟨_, e.weylElement_mul_self_mem S⟩ : K) =
      (((-ε : ℤˣ) : ℤ) : K) ^ S.card := by
  rw [coe_siegelDet, e.det_eq_prod_of_apply_basisFst _ (fun i => if i ∈ S then
    (((-ε : ℤˣ) : ℤ) : K) else 1) (fun i => by
      change ((e.weylElement S * e.weylElement S : h.isometryGroup) : V ≃ₗ[K] V)
        (e.basisFst i) = _
      rw [basisFst_apply, weylElement_mul_self_fst]),
    Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]


omit [FiniteDimensional K V] in
/-- Elements of `N(X)` have `det(n|_X) = 1`. -/
theorem siegelDet_eq_one_of_mem_siegelUnipotent {g : h.isometryGroup}
    (hg : g ∈ h.siegelUnipotent e.lagrangianFst) (hgP : g ∈ h.siegelParabolic e.lagrangianFst) :
    h.siegelDet e.lagrangianFst ⟨g, hgP⟩ = 1 := by
  rw [siegelDet, MonoidHom.comp_apply]
  convert LinearEquiv.det.map_one
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  exact apply_eq_of_mem_siegelUnipotent e.nondegenerate e.isLagrangian_lagrangianFst hg x.2

variable [NeZero (2 : K)]

/-- GKT (4.15), Definition 4.37: the Rao function `x(g) = det(p₁ p₂|_X)` modulo `𝒩(E^×)`, computed
in the decomposition `g = p₁ w_S p₂` given by the Bruhat decomposition; every decomposition gives
the same value (`raoFunction_eq`, Corollary 4.36). -/
def raoFunction (g : h.isometryGroup) : Kˣ ⧸ normSubgroup τ :=
  QuotientGroup.mk
    (h.siegelDet e.lagrangianFst ⟨_, (e.exists_mem_doubleCoset g).choose_spec.choose_spec.1⟩ *
      h.siegelDet e.lagrangianFst
        ⟨_, (e.exists_mem_doubleCoset g).choose_spec.choose_spec.2.choose_spec.1⟩)

private theorem exists_raoFunction_eq (g : h.isometryGroup) :
    ∃ (S : Finset ι) (p₁ p₂ : h.siegelParabolic e.lagrangianFst),
      g = p₁ * e.weylElement S * p₂ ∧
        e.raoFunction g = QuotientGroup.mk (h.siegelDet _ p₁ * h.siegelDet _ p₂) :=
  ⟨_, ⟨_, (e.exists_mem_doubleCoset g).choose_spec.choose_spec.1⟩,
    ⟨_, (e.exists_mem_doubleCoset g).choose_spec.choose_spec.2.choose_spec.1⟩,
    (e.exists_mem_doubleCoset g).choose_spec.choose_spec.2.choose_spec.2, rfl⟩

/-- GKT Corollary 4.36: for every decomposition `g = p₁ w_S p₂`,
`x(g) = det(p₁ p₂|_X)` modulo `𝒩(E^×)`. -/
theorem raoFunction_eq {g : h.isometryGroup} (S : Finset ι)
    (p₁ p₂ : h.siegelParabolic e.lagrangianFst) (hg : g = p₁ * e.weylElement S * p₂) :
    e.raoFunction g = QuotientGroup.mk (h.siegelDet _ p₁ * h.siegelDet _ p₂) := by
  obtain ⟨S₀, q₁, q₂, hq, hx⟩ := e.exists_raoFunction_eq g
  have hc : S₀.card = S.card := by
    have h1 := (e.mem_doubleCoset_weylElement_iff S g).1 ⟨p₁, p₁.2, p₂, p₂.2, hg⟩
    have h2 := (e.mem_doubleCoset_weylElement_iff S₀ g).1 ⟨q₁, q₁.2, q₂, q₂.2, hq⟩
    omega
  obtain ⟨π, hπ, hw⟩ := e.exists_weylElement_eq_conj hc
  set π' : h.siegelParabolic e.lagrangianFst := ⟨π, hπ⟩
  rw [hx]
  refine (h.mk_siegelDet_mul_siegelDet_eq e.nondegenerate e.isLagrangian_lagrangianFst
    q₁ q₂ (p₁ * π') (π'⁻¹ * p₂) (w := e.weylElement S₀) ?_).trans ?_
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, π']
    rw [← hq]
    calc g = p₁ * e.weylElement S * p₂ := hg
      _ = (p₁ : h.isometryGroup) * π * e.weylElement S₀ * (π⁻¹ * p₂) := by rw [hw]; group
  · rw [map_mul, map_mul, map_inv]
    congr 1
    group

/-- GKT Lemma 4.40 (b): `x(p₁ g p₂) = x(p₁) x(g) x(p₂)`. -/
theorem raoFunction_mul_mul (p₁ p₂ : h.siegelParabolic e.lagrangianFst) (g : h.isometryGroup) :
    e.raoFunction (p₁ * g * p₂) = QuotientGroup.mk (h.siegelDet _ p₁) * e.raoFunction g *
      QuotientGroup.mk (h.siegelDet _ p₂) := by
  obtain ⟨S, q₁, q₂, hq, hx⟩ := e.exists_raoFunction_eq g
  rw [hx, e.raoFunction_eq S (p₁ * q₁) (q₂ * p₂) (by rw [hq]; simp only [Subgroup.coe_mul]; group),
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, map_mul, map_mul]
  congr 1
  ac_rfl

/-- `x(p) = det(p|_X)` on the Siegel parabolic. -/
theorem raoFunction_of_mem (p : h.siegelParabolic e.lagrangianFst) :
    e.raoFunction p = QuotientGroup.mk (h.siegelDet _ p) := by
  rw [e.raoFunction_eq ∅ p 1 (by rw [weylElement_empty]; simp), map_one, mul_one]

theorem raoFunction_weylElement (S : Finset ι) : e.raoFunction (e.weylElement S) = 1 := by
  rw [e.raoFunction_eq S 1 1 (by simp), map_one, mul_one, QuotientGroup.mk_one]

/-- GKT Lemma 4.40 (a): for `g ∈ P w_S P`, `x(g⁻¹) = x(g)⁻¹ (-ε)^{|S|}`. -/
theorem raoFunction_inv {g : h.isometryGroup} (S : Finset ι)
    (hg : ∃ p₁ ∈ h.siegelParabolic e.lagrangianFst, ∃ p₂ ∈ h.siegelParabolic e.lagrangianFst,
      g = p₁ * e.weylElement S * p₂) :
    e.raoFunction g⁻¹ =
      (e.raoFunction g)⁻¹ * QuotientGroup.mk (signUnit K (-ε) ^ S.card) := by
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := hg
  set a : h.siegelParabolic e.lagrangianFst := ⟨_, e.weylElement_mul_self_mem S⟩
  have hdet : h.siegelDet _ a = signUnit K (-ε) ^ S.card :=
    Units.ext (by rw [e.coe_siegelDet_weylElement_mul_self, Units.val_pow_eq_pow_val,
      coe_signUnit])
  rw [e.raoFunction_eq S ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ rfl,
    e.raoFunction_eq S (⟨p₂, hp₂⟩⁻¹ * a⁻¹) ⟨p₁, hp₁⟩⁻¹ (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, a]; group),
    map_mul, map_inv, map_inv, map_inv, hdet, ← inv_pow, signUnit_inv,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  congr 1
  rw [mul_inv]
  ac_rfl

/-- GKT Lemma 4.44 (and its use in Lemma 4.38): for two standard bases `e, f` and the isometry
`π : eₖ ↦ fₖ`, `x_e(g) = x_f(π g π⁻¹)`. -/
theorem raoFunction_conj (f : h.StandardBasis ι) (g : h.isometryGroup) :
    f.raoFunction ((e.isometryEquiv f).toIsometryGroup * g *
      ((e.isometryEquiv f).toIsometryGroup)⁻¹) = e.raoFunction g := by
  have hπX := e.map_isometryEquiv_lagrangianFst f
  have hw : ∀ S, f.weylElement S = (e.isometryEquiv f).toIsometryGroup * e.weylElement S *
      ((e.isometryEquiv f).toIsometryGroup)⁻¹ := fun S => e.weylElement_eq_conj f S
  generalize (e.isometryEquiv f).toIsometryGroup = π at hπX hw ⊢
  have hconjP : ∀ p : h.siegelParabolic e.lagrangianFst,
      π * (p : h.isometryGroup) * π⁻¹ ∈ h.siegelParabolic f.lagrangianFst := fun p => by
    change f.lagrangianFst.map _ = _
    rw [← hπX, ← map_isometryGroup_mul,
      show π * (p : h.isometryGroup) * π⁻¹ * π = π * p by group, map_isometryGroup_mul,
      show e.lagrangianFst.map ((p : h.isometryGroup) : V ≃ₗ[K] V).toLinearMap = e.lagrangianFst
        from p.2]
  have hdet : ∀ p : h.siegelParabolic e.lagrangianFst,
      h.siegelDet f.lagrangianFst ⟨_, hconjP p⟩ = h.siegelDet e.lagrangianFst p := fun p => by
    let eπ : e.lagrangianFst ≃ₗ[K] f.lagrangianFst :=
      ((π : V ≃ₗ[K] V).submoduleMap e.lagrangianFst).trans (LinearEquiv.ofEq _ _ hπX)
    change LinearEquiv.det (h.siegelRestrict f.lagrangianFst ⟨_, hconjP p⟩) =
      LinearEquiv.det (h.siegelRestrict e.lagrangianFst p)
    rw [← LinearEquiv.det_conj (h.siegelRestrict e.lagrangianFst p) eπ]
    congr 1
  obtain ⟨S, q₁, q₂, hq, hx⟩ := e.exists_raoFunction_eq g
  rw [hx, f.raoFunction_eq S ⟨_, hconjP q₁⟩ ⟨_, hconjP q₂⟩ (by
    rw [hw S, hq]; group), hdet, hdet]

/-- GKT Lemma 4.38: the Rao function depends only on `X`, not on the standard basis. -/
theorem raoFunction_eq_of_lagrangianFst_eq (f : h.StandardBasis ι)
    (hf : f.lagrangianFst = e.lagrangianFst) (g : h.isometryGroup) :
    f.raoFunction g = e.raoFunction g := by
  have hπ : (e.isometryEquiv f).toIsometryGroup ∈ h.siegelParabolic e.lagrangianFst := by
    change e.lagrangianFst.map _ = _
    rw [e.map_isometryEquiv_lagrangianFst f, hf]
  have := e.raoFunction_conj f (((e.isometryEquiv f).toIsometryGroup)⁻¹ * g *
    (e.isometryEquiv f).toIsometryGroup)
  rw [show (e.isometryEquiv f).toIsometryGroup * (((e.isometryEquiv f).toIsometryGroup)⁻¹ * g *
    (e.isometryEquiv f).toIsometryGroup) * ((e.isometryEquiv f).toIsometryGroup)⁻¹ = g by group]
    at this
  rw [this, show ((e.isometryEquiv f).toIsometryGroup)⁻¹ * g * (e.isometryEquiv f).toIsometryGroup
      = ((⟨_, hπ⟩ : h.siegelParabolic _)⁻¹ : h.siegelParabolic _) * g *
        (⟨_, hπ⟩ : h.siegelParabolic _) from rfl, e.raoFunction_mul_mul, map_inv,
    QuotientGroup.mk_inv]
  exact inv_mul_cancel_comm (G := Kˣ ⧸ normSubgroup τ) _ _

end StandardBasis

end Rao

section Multiplicativity

variable {ε : ℤˣ} {h : EpsilonHermitianForm τ (-ε) V} [FiniteDimensional K V]

namespace StandardBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : h.StandardBasis ι) (σ : ι → Fin 5)
  {b : e.lagrangianSnd →ₗ[K] e.lagrangianFst}
  (hb : b ∈ h.siegelHerm e.lagrangianFst e.lagrangianSnd)

/-- The element `κ₁ κ₂ = w_{T₁ ∪ T₂ ∪ T₄} n(b) w_{T₁ ∪ T₃ ∪ T₄}` of the proof of GKT
Proposition 4.41. -/
private abbrev kappa : h.isometryGroup :=
  e.weylElement (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 2 ∨ σ i = 4) *
    (h.siegelUnipotentOf e.nondegenerate e.isLagrangian_lagrangianFst
      e.isCompl_lagrangianFst_lagrangianSnd b hb *
      e.weylElement (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 3 ∨ σ i = 4))

omit [FiniteDimensional K V] [DecidableEq ι] in
private theorem mem_filter_iff {p : ι → Prop} [DecidablePred p] {k : ι} :
    k ∈ Finset.univ.filter p ↔ p k := by simp

private theorem nb_snd (k : ι) :
    ((h.siegelUnipotentOf e.nondegenerate e.isLagrangian_lagrangianFst
      e.isCompl_lagrangianFst_lagrangianSnd b hb : h.isometryGroup) : V ≃ₗ[K] V) (e.snd k) =
        e.snd k + b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩ :=
  siegelUnipotentOf_apply_right _ _ _ hb ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩

private theorem nb_fst (k : ι) :
    ((h.siegelUnipotentOf e.nondegenerate e.isLagrangian_lagrangianFst
      e.isCompl_lagrangianFst_lagrangianSnd b hb : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) =
        e.fst k :=
  apply_eq_of_mem_siegelUnipotent e.nondegenerate e.isLagrangian_lagrangianFst
    (siegelUnipotentOf_mem _ _ _ hb) (e.fst_mem_lagrangianFst k)

variable {σ}

private theorem kappa_fst_zero {k : ι} (hk : σ k = 0) :
    ((e.kappa σ hb : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) = e.fst k := by
  rw [kappa, isometryGroup_coe_mul_apply, isometryGroup_coe_mul_apply,
    e.weylElement_fst_of_not_mem (by rw [mem_filter_iff]; simp [hk]), nb_fst,
    e.weylElement_fst_of_not_mem (by rw [mem_filter_iff]; simp [hk])]

private theorem kappa_fst_one (hb0 : ∀ k, σ k ≠ 4 → b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩ = 0)
    {k : ι} (hk : σ k = 1) : ((e.kappa σ hb : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) =
      (((-ε : ℤˣ) : ℤ) : K) • e.fst k := by
  rw [kappa, isometryGroup_coe_mul_apply, isometryGroup_coe_mul_apply,
    e.weylElement_fst_of_mem (by rw [mem_filter_iff]; simp [hk]), map_smul, nb_snd,
    hb0 k (by rw [hk]; decide), Submodule.coe_zero, add_zero, map_smul,
    e.weylElement_snd_of_mem (by rw [mem_filter_iff]; simp [hk])]

private theorem kappa_fst_two {k : ι} (hk : σ k = 2) :
    ((e.kappa σ hb : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) =
      (((-ε : ℤˣ) : ℤ) : K) • e.snd k := by
  rw [kappa, isometryGroup_coe_mul_apply, isometryGroup_coe_mul_apply,
    e.weylElement_fst_of_not_mem (by rw [mem_filter_iff]; simp [hk]), nb_fst,
    e.weylElement_fst_of_mem (by rw [mem_filter_iff]; simp [hk])]

private theorem kappa_fst_three (hb0 : ∀ k, σ k ≠ 4 → b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩ = 0)
    {k : ι} (hk : σ k = 3) : ((e.kappa σ hb : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) =
      (((-ε : ℤˣ) : ℤ) : K) • e.snd k := by
  rw [kappa, isometryGroup_coe_mul_apply, isometryGroup_coe_mul_apply,
    e.weylElement_fst_of_mem (by rw [mem_filter_iff]; simp [hk]), map_smul, nb_snd,
    hb0 k (by rw [hk]; decide), Submodule.coe_zero, add_zero, map_smul,
    e.weylElement_snd_of_not_mem (by rw [mem_filter_iff]; simp [hk])]

private theorem kappa_fst_four {k : ι} (hk : σ k = 4) :
    ((e.kappa σ hb : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) =
      (((-ε : ℤˣ) : ℤ) : K) • (e.fst k +
        ((e.weylElement (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 2 ∨ σ i = 4) :
          h.isometryGroup) : V ≃ₗ[K] V) (b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩)) := by
  rw [kappa, isometryGroup_coe_mul_apply, isometryGroup_coe_mul_apply,
    e.weylElement_fst_of_mem (by rw [mem_filter_iff]; simp [hk]), map_smul, nb_snd, map_smul,
    map_add, e.weylElement_snd_of_mem (by rw [mem_filter_iff]; simp [hk])]

private theorem kappa_snd_zero (hb0 : ∀ k, σ k ≠ 4 → b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩ = 0)
    {k : ι} (hk : σ k = 0) :
    ((e.kappa σ hb : h.isometryGroup) : V ≃ₗ[K] V) (e.snd k) = e.snd k := by
  rw [kappa, isometryGroup_coe_mul_apply, isometryGroup_coe_mul_apply,
    e.weylElement_snd_of_not_mem (by rw [mem_filter_iff]; simp [hk]), nb_snd,
    hb0 k (by rw [hk]; decide), Submodule.coe_zero, add_zero,
    e.weylElement_snd_of_not_mem (by rw [mem_filter_iff]; simp [hk])]

private theorem kappa_snd_one {k : ι} (hk : σ k = 1) :
    ((e.kappa σ hb : h.isometryGroup) : V ≃ₗ[K] V) (e.snd k) =
      (((-ε : ℤˣ) : ℤ) : K) • e.snd k := by
  rw [kappa, isometryGroup_coe_mul_apply, isometryGroup_coe_mul_apply,
    e.weylElement_snd_of_mem (by rw [mem_filter_iff]; simp [hk]), nb_fst,
    e.weylElement_fst_of_mem (by rw [mem_filter_iff]; simp [hk])]

omit [FiniteDimensional K V] in
private theorem fin_five_cases' (j : Fin 5) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
  fin_cases j <;> simp

/-- The decomposition `κ₁ κ₂ = n(c) w_{T₂ ∪ T₃ ∪ T₄} q` of the proof of GKT Proposition 4.41, with
`q ∈ P` equal to `-ε` on `X_{T₁}`, to `x ↦ -ε b (x*)` on `X_{T₄}` and to the identity on the other
`eₖ`. -/
private theorem exists_kappa_eq
    (hb0 : ∀ k, σ k ≠ 4 → b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩ = 0)
    (hb4 : ∀ y : e.lagrangianSnd, (b y : V) ∈ e.blockFst {i | σ i = 4})
    (hinj : ∀ y : e.lagrangianSnd, (y : V) ∈ e.blockSnd {i | σ i = 4} → b y = 0 → y = 0) :
    ∃ (c : e.lagrangianSnd →ₗ[K] e.lagrangianFst) (hc : c ∈ h.siegelHerm _ _)
      (q : h.siegelParabolic e.lagrangianFst),
      e.kappa σ hb = h.siegelUnipotentOf e.nondegenerate e.isLagrangian_lagrangianFst
          e.isCompl_lagrangianFst_lagrangianSnd c hc *
        e.weylElement (Finset.univ.filter fun i => σ i = 2 ∨ σ i = 3 ∨ σ i = 4) * q ∧
      (∀ k, σ k ≠ 1 → σ k ≠ 4 → ((q : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) = e.fst k) ∧
      (∀ k, σ k = 1 → ((q : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) =
        (((-ε : ℤˣ) : ℤ) : K) • e.fst k) ∧
      (∀ k, σ k = 4 → ((q : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) =
        (((-ε : ℤˣ) : ℤ) : K) • (b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩ : V)) := by
  set c₀ : K := (((-ε : ℤˣ) : ℤ) : K) with hc₀
  have hcc : c₀ * c₀ = 1 := units_int_cast_mul_self' _
  have hh := e.nondegenerate
  have hX := e.isLagrangian_lagrangianFst
  have hY := e.isLagrangian_lagrangianSnd
  set wA := e.weylElement (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 2 ∨ σ i = 4) with hwA
  set w' := e.weylElement (Finset.univ.filter fun i => σ i = 2 ∨ σ i = 3 ∨ σ i = 4) with hw'
  set κ := e.kappa σ hb with hκ
  -- `w_A = w'` on `X_{T₄}`, with values in `Y_{T₄}`
  have hAS : ∀ x ∈ e.blockFst {i | σ i = 4},
      (wA : V ≃ₗ[K] V) x = (w' : V ≃ₗ[K] V) x ∧ (wA : V ≃ₗ[K] V) x ∈ e.blockSnd {i | σ i = 4} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      have hi' : σ i = 4 := hi
      rw [hwA, hw', e.weylElement_fst_of_mem (by rw [mem_filter_iff]; simp [hi']),
        e.weylElement_fst_of_mem (by rw [mem_filter_iff]; simp [hi'])]
      exact ⟨rfl, Submodule.smul_mem _ _ (e.snd_mem_blockSnd hi)⟩
    | zero => simp
    | add x y _ _ hx hy =>
      exact ⟨by rw [map_add, map_add, hx.1, hy.1], by rw [map_add]; exact add_mem hx.2 hy.2⟩
    | smul a x _ hx =>
      exact ⟨by rw [map_smul, map_smul, hx.1], by rw [map_smul]; exact Submodule.smul_mem _ _ hx.2⟩
  set y : ι → V := fun k => (wA : V ≃ₗ[K] V) (b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩) with hy
  have hyY : ∀ k, y k ∈ e.lagrangianSnd := fun k =>
    e.blockSnd_le_lagrangianSnd _ (hAS _ (hb4 _)).2
  -- the Lagrangian `Ẑ = κ w' Y`
  set Z := e.lagrangianSnd.map ((κ * w' : h.isometryGroup) : V ≃ₗ[K] V).toLinearMap with hZdef
  have hZ : h.IsLagrangian Z := hY.map _
  have hκw' : ∀ v ∈ e.lagrangianSnd, (κ : V ≃ₗ[K] V) ((w' : V ≃ₗ[K] V) v) ∈ Z :=
    fun v hv => ⟨v, hv, rfl⟩
  have hsmul : ∀ v, c₀ • v ∈ Z → v ∈ Z := fun v hv => by
    have := Z.smul_mem c₀ hv; rwa [smul_smul, hcc, one_smul] at this
  have hZs : ∀ k, σ k ≠ 4 → e.snd k ∈ Z := by
    intro k hk
    have := hκw' _ (e.snd_mem_lagrangianSnd k)
    rcases fin_five_cases' (σ k) with h0 | h1 | h2 | h3 | h4
    · rwa [hw', e.weylElement_snd_of_not_mem (by rw [mem_filter_iff]; simp [h0]),
        e.kappa_snd_zero hb hb0 h0] at this
    · rw [hw', e.weylElement_snd_of_not_mem (by rw [mem_filter_iff]; simp [h1]),
        e.kappa_snd_one hb h1] at this
      exact hsmul _ this
    · rw [hw', e.weylElement_snd_of_mem (by rw [mem_filter_iff]; simp [h2]),
        e.kappa_fst_two hb h2] at this
      exact hsmul _ this
    · rw [hw', e.weylElement_snd_of_mem (by rw [mem_filter_iff]; simp [h3]),
        e.kappa_fst_three hb hb0 h3] at this
      exact hsmul _ this
    · exact absurd h4 hk
  have hZ4 : ∀ k, σ k = 4 → e.fst k + y k ∈ Z := by
    intro k hk
    have := hκw' _ (e.snd_mem_lagrangianSnd k)
    rw [hw', e.weylElement_snd_of_mem (by rw [mem_filter_iff]; simp [hk]),
      e.kappa_fst_four hb hk] at this
    exact hsmul _ this
  -- `Ẑ` is a complement of `X`
  have hsupY4 : ∀ v ∈ e.blockSnd {i | σ i = 4}, ∀ hv : v ∈ e.lagrangianSnd,
      (wA : V ≃ₗ[K] V) (b ⟨v, hv⟩) ∈ Z ⊔ e.lagrangianFst := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      intro _
      have := Submodule.sub_mem _ (Submodule.mem_sup_left (hZ4 k hk))
        (Submodule.mem_sup_right (e.fst_mem_lagrangianFst k))
      rwa [add_sub_cancel_left] at this
    | zero =>
      intro hv
      rw [show (⟨0, hv⟩ : e.lagrangianSnd) = 0 from rfl, map_zero, Submodule.coe_zero, map_zero]
      exact zero_mem _
    | add x x' hx hx' ihx ihx' =>
      intro hv
      rw [show (⟨x + x', hv⟩ : e.lagrangianSnd) = ⟨x, e.blockSnd_le_lagrangianSnd _ hx⟩ +
        ⟨x', e.blockSnd_le_lagrangianSnd _ hx'⟩ from rfl, map_add, Submodule.coe_add, map_add]
      exact add_mem (ihx _) (ihx' _)
    | smul a x hx ihx =>
      intro hv
      rw [show (⟨a • x, hv⟩ : e.lagrangianSnd) = a • ⟨x, e.blockSnd_le_lagrangianSnd _ hx⟩
        from rfl, map_smul, Submodule.coe_smul, map_smul]
      exact Submodule.smul_mem _ _ (ihx _)
  have hsurj : ∀ k, σ k = 4 → ∃ v, ∃ hv4 : v ∈ e.blockSnd {i | σ i = 4},
      (b ⟨v, e.blockSnd_le_lagrangianSnd _ hv4⟩ : V) = e.fst k := by
    let b₄ : e.blockSnd {i | σ i = 4} →ₗ[K] e.blockFst {i | σ i = 4} :=
      LinearMap.codRestrict _ (e.lagrangianFst.subtype ∘ₗ b ∘ₗ
        Submodule.inclusion (e.blockSnd_le_lagrangianSnd _)) (fun v => hb4 _)
    have hinj₄ : Function.Injective b₄ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro v hv
      have hv' : b₄ v = 0 := LinearMap.mem_ker.1 hv
      have h0' : ((b₄ v : e.blockFst {i | σ i = 4}) : V) = 0 := by rw [hv']; rfl
      have h0 : b (Submodule.inclusion (e.blockSnd_le_lagrangianSnd _) v) = 0 := Subtype.ext h0'
      have h1 := hinj _ v.2 h0
      have h2 : ((Submodule.inclusion (e.blockSnd_le_lagrangianSnd _) v : e.lagrangianSnd) :
          V) = 0 := by rw [h1]; rfl
      rw [Submodule.mem_bot]
      exact Subtype.ext h2
    have hd : finrank K (e.blockSnd {i | σ i = 4}) = finrank K (e.blockFst {i | σ i = 4}) := by
      rw [← Finset.coe_filter_univ, e.finrank_blockSnd, e.finrank_blockFst]
    have hsurj₄ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 hinj₄
    intro k hk
    obtain ⟨v, hv⟩ := hsurj₄ ⟨e.fst k, e.fst_mem_blockFst hk⟩
    exact ⟨v, v.2, congrArg Subtype.val hv⟩
  have hsup : Z ⊔ e.lagrangianFst = ⊤ := by
    rw [eq_top_iff, ← e.basis.span_eq, Submodule.span_le]
    rintro _ ⟨k | k, rfl⟩
    · exact Submodule.mem_sup_right (e.fst_mem_lagrangianFst k)
    · by_cases hk : σ k = 4
      · obtain ⟨v, hv4, hv⟩ := hsurj k hk
        have hk' : k ∈ Finset.univ.filter fun i => σ i = 1 ∨ σ i = 2 ∨ σ i = 4 := by
          rw [mem_filter_iff]; simp [hk]
        have := Submodule.smul_mem _ c₀ (hsupY4 v hv4 (e.blockSnd_le_lagrangianSnd _ hv4))
        rw [hv, e.weylElement_fst_of_mem hk', smul_smul, hcc, one_smul] at this
        exact this
      · exact Submodule.mem_sup_left (hZs k hk)
  have hZX : IsCompl Z e.lagrangianFst := by
    refine (hZ.isCompl_iff_disjoint hh hX).2 ?_
    have : Z ⊓ e.lagrangianFst = h.orthogonal (Z ⊔ e.lagrangianFst) := by
      rw [orthogonal_sup, hZ, hX]
    rw [disjoint_iff, this, hsup, orthogonal_top hh]
  -- the map `c`
  obtain ⟨c, hc, hcZ⟩ := exists_siegelHerm_add_mem hX hY hZ hZX
  have huniq : ∀ (v : e.lagrangianSnd) (x : V), x ∈ e.lagrangianFst → (v : V) + x ∈ Z →
      (c v : V) = x := by
    intro v x hx hvx
    have h1 := Z.sub_mem (hcZ v) hvx
    rw [add_sub_add_left_eq_sub] at h1
    exact sub_eq_zero.1 (Submodule.disjoint_def.1 hZX.disjoint _ h1
      (e.lagrangianFst.sub_mem (c v).2 hx))
  have hc0 : ∀ k, σ k ≠ 4 → c ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩ = 0 := fun k hk =>
    Subtype.ext (huniq _ 0 (zero_mem _) (by rw [add_zero]; exact hZs k hk))
  have hc4 : ∀ k, σ k = 4 → (c ⟨y k, hyY k⟩ : V) = e.fst k := fun k hk =>
    huniq _ _ (e.fst_mem_lagrangianFst k) (by rw [add_comm]; exact hZ4 k hk)
  set n' := h.siegelUnipotentOf hh hX e.isCompl_lagrangianFst_lagrangianSnd c hc with hn'
  have hn'X : ∀ x ∈ e.lagrangianFst, ((n'⁻¹ : h.isometryGroup) : V ≃ₗ[K] V) x = x :=
    fun x hx => apply_eq_of_mem_siegelUnipotent hh hX
      ((h.siegelUnipotent _).inv_mem
        (siegelUnipotentOf_mem hh hX e.isCompl_lagrangianFst_lagrangianSnd hc)) hx
  have hn'Y : ∀ v (hv : v ∈ e.lagrangianSnd),
      ((n'⁻¹ : h.isometryGroup) : V ≃ₗ[K] V) (v + c ⟨v, hv⟩) = v := fun v hv => by
    rw [← siegelUnipotentOf_apply_right hh hX e.isCompl_lagrangianFst_lagrangianSnd hc ⟨v, hv⟩,
      isometryGroup_coe_inv_apply']
  -- the element `q = w'⁻¹ n'⁻¹ κ` and its values on `X`
  set q := w'⁻¹ * n'⁻¹ * κ with hq
  have hq0 : ∀ k, σ k ≠ 1 → σ k ≠ 4 → ((q : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) = e.fst k := by
    intro k hk1 hk4
    rw [hq, isometryGroup_coe_mul_apply, isometryGroup_coe_mul_apply]
    rcases fin_five_cases' (σ k) with h0 | h1 | h2 | h3 | h4
    · rw [e.kappa_fst_zero hb h0, hn'X _ (e.fst_mem_lagrangianFst k), hw',
        e.weylElement_inv_fst_of_not_mem (by rw [mem_filter_iff]; simp [h0])]
    · exact absurd h1 hk1
    · rw [e.kappa_fst_two hb h2, map_smul, show e.snd k = e.snd k + c ⟨e.snd k,
        e.snd_mem_lagrangianSnd k⟩ by rw [hc0 k hk4, Submodule.coe_zero, add_zero], hn'Y,
        hw', ← e.weylElement_fst_of_mem
          (S := Finset.univ.filter fun i => σ i = 2 ∨ σ i = 3 ∨ σ i = 4)
          (by rw [mem_filter_iff]; simp [h2]),
        isometryGroup_coe_inv_apply']
    · rw [e.kappa_fst_three hb hb0 h3, map_smul, show e.snd k = e.snd k + c ⟨e.snd k,
        e.snd_mem_lagrangianSnd k⟩ by rw [hc0 k hk4, Submodule.coe_zero, add_zero], hn'Y,
        hw', ← e.weylElement_fst_of_mem
          (S := Finset.univ.filter fun i => σ i = 2 ∨ σ i = 3 ∨ σ i = 4)
          (by rw [mem_filter_iff]; simp [h3]),
        isometryGroup_coe_inv_apply']
    · exact absurd h4 hk4
  have hq1 : ∀ k, σ k = 1 → ((q : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) = c₀ • e.fst k := by
    intro k hk
    rw [hq, isometryGroup_coe_mul_apply, isometryGroup_coe_mul_apply, e.kappa_fst_one hb hb0 hk,
      hn'X _ (Submodule.smul_mem _ _ (e.fst_mem_lagrangianFst k)), map_smul, hw',
      e.weylElement_inv_fst_of_not_mem (by rw [mem_filter_iff]; simp [hk])]
  have hq4 : ∀ k, σ k = 4 → ((q : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) =
      c₀ • (b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩ : V) := by
    intro k hk
    rw [hq, isometryGroup_coe_mul_apply, isometryGroup_coe_mul_apply, e.kappa_fst_four hb hk,
      ← hwA, show e.fst k + (wA : V ≃ₗ[K] V) (b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩) =
        y k + c ⟨y k, hyY k⟩ by rw [hc4 k hk, add_comm], map_smul, hn'Y, map_smul, hy]
    simp only
    rw [(hAS _ (hb4 _)).1, isometryGroup_coe_inv_apply']
  have hqP : q ∈ h.siegelParabolic e.lagrangianFst :=
    e.map_lagrangianFst_eq q hX fun k => by
      by_cases hk1 : σ k = 1
      · rw [hq1 k hk1]; exact Submodule.smul_mem _ _ (e.fst_mem_lagrangianFst k)
      by_cases hk4 : σ k = 4
      · rw [hq4 k hk4]; exact Submodule.smul_mem _ _ (b _).2
      · rw [hq0 k hk1 hk4]; exact e.fst_mem_lagrangianFst k
  refine ⟨c, hc, ⟨q, hqP⟩, ?_, hq0, hq1, hq4⟩
  change κ = n' * w' * (w'⁻¹ * n'⁻¹ * κ)
  group

omit [FiniteDimensional K V] in
/-- `det f = det (f|_W)` when `f` is the identity modulo `W`. -/
private theorem det_eq_det_restrict_of_sub_mem {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (W : Submodule K M) (f : M →ₗ[K] M) (hf : ∀ x, f x - x ∈ W)
    (hW : W ≤ W.comap f) : LinearMap.det f = LinearMap.det (f.restrict hW) := by
  rw [LinearMap.det_eq_det_mul_det W f hW]
  have : W.mapQ W f hW = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_comp]
    exact (Submodule.Quotient.eq W).2 (hf x)
  rw [this, LinearMap.det_id, mul_one]

/-- The determinant of the element `q` of `exists_kappa_eq`: `(-ε)^{|T₁| + |T₄|}` times the
determinant of the Gram matrix of `(y, y') ↦ h(b y, y')` on `Y_{T₄}`. -/
private theorem coe_siegelDet_of_apply
    (hb4 : ∀ y : e.lagrangianSnd, (b y : V) ∈ e.blockFst {i | σ i = 4})
    (q : h.siegelParabolic e.lagrangianFst)
    (hq0 : ∀ k, σ k ≠ 1 → σ k ≠ 4 → ((q : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) = e.fst k)
    (hq1 : ∀ k, σ k = 1 → ((q : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) =
      (((-ε : ℤˣ) : ℤ) : K) • e.fst k)
    (hq4 : ∀ k, σ k = 4 → ((q : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) =
      (((-ε : ℤˣ) : ℤ) : K) • (b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩ : V)) :
    (h.siegelDet _ q : K) = (((-ε : ℤˣ) : ℤ) : K) ^ ((Finset.univ.filter fun i => σ i = 1).card +
      (Finset.univ.filter fun i => σ i = 4).card) *
      ((h.siegelHermForm hb (e.blockSnd {i | σ i = 4}) (e.blockSnd_le_lagrangianSnd _)).gramMatrix
        (e.blockSndBasis {i | σ i = 4})).det := by
  set c₀ : K := (((-ε : ℤˣ) : ℤ) : K) with hc₀
  have hcc : c₀ * c₀ = 1 := units_int_cast_mul_self' _
  set T₁ := Finset.univ.filter fun i => σ i = 1 with hT₁
  set m₁ : h.siegelParabolic e.lagrangianFst := ⟨_, e.weylElement_mul_self_mem T₁⟩ with hm₁
  set m₄ := m₁⁻¹ * q with hm₄
  have hq : q = m₁ * m₄ := by rw [hm₄, mul_inv_cancel_left]
  rw [hq, map_mul, Units.val_mul, e.coe_siegelDet_weylElement_mul_self, pow_add, mul_assoc]
  congr 1
  -- `m₁⁻¹` on the basis vectors and on `X_{T₄}`
  have hm₁k : ∀ k, (((m₁⁻¹ : h.siegelParabolic _) : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) =
      (if k ∈ T₁ then c₀ else 1) • e.fst k := by
    intro k
    have h1 := e.weylElement_mul_self_fst T₁ k
    have hd : (if k ∈ T₁ then c₀ else 1) * (if k ∈ T₁ then c₀ else 1) = 1 := by
      split_ifs <;> simp [hcc]
    rw [Subgroup.coe_inv]
    conv_lhs => rw [← one_smul K (e.fst k), ← hd, ← smul_smul, ← h1]
    rw [map_smul, hm₁, isometryGroup_coe_inv_apply']
  have hm₁4 : ∀ x ∈ e.blockFst {i | σ i = 4},
      (((m₁⁻¹ : h.siegelParabolic _) : h.isometryGroup) : V ≃ₗ[K] V) x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      have hk' : σ k = 4 := hk
      rw [hm₁k, ite_eq_right (by rw [hT₁, mem_filter_iff, hk']; decide), one_smul]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  have hm4 : ∀ k, (((m₄ : h.siegelParabolic _) : h.isometryGroup) : V ≃ₗ[K] V) (e.fst k) =
      if σ k = 4 then c₀ • (b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩ : V) else e.fst k := by
    intro k
    rw [hm₄, Subgroup.coe_mul, isometryGroup_coe_mul_apply]
    by_cases hk4 : σ k = 4
    · rw [hq4 k hk4, hm₁4 _ (Submodule.smul_mem _ _ (hb4 _)), ite_eq_left hk4]
    · rw [ite_eq_right hk4]
      by_cases hk1 : σ k = 1
      · rw [hq1 k hk1, map_smul, hm₁k, ite_eq_left (by rw [hT₁, mem_filter_iff]; exact hk1),
          smul_smul, hcc, one_smul]
      · rw [hq0 k hk1 hk4, hm₁k, ite_eq_right (by rw [hT₁, mem_filter_iff]; exact hk1), one_smul]
  -- restriction to `X_{T₄}`
  set f := (h.siegelRestrict _ m₄ : e.lagrangianFst →ₗ[K] e.lagrangianFst) with hf
  set W := (e.blockFst {i | σ i = 4}).comap e.lagrangianFst.subtype with hW
  have hfW : ∀ x, f x - x ∈ W := by
    have key : ∀ k, f (e.basisFst k) - e.basisFst k ∈ W := by
      intro k
      change ((m₄ : h.isometryGroup) : V ≃ₗ[K] V) (e.basisFst k) - e.basisFst k ∈
        e.blockFst {i | σ i = 4}
      rw [basisFst_apply, hm4]
      split_ifs with hk4
      · exact sub_mem (Submodule.smul_mem _ _ (hb4 _)) (e.fst_mem_blockFst hk4)
      · rw [sub_self]; exact zero_mem _
    have : (⊤ : Submodule K e.lagrangianFst) ≤ W.comap (f - LinearMap.id) := by
      rw [← e.basisFst.span_eq, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact key k
    exact fun x => this Submodule.mem_top
  have hWf : W ≤ W.comap f := fun x hx => by
    have := add_mem (hfW x) hx; rwa [sub_add_cancel] at this
  rw [coe_siegelDet, ← hf, det_eq_det_restrict_of_sub_mem W f hfW hWf]
  set bW : Basis {i | σ i = 4} K W := (e.blockFstBasis {i | σ i = 4}).map
    (Submodule.comapSubtypeEquivOfLe (e.blockFst_le_lagrangianFst _)).symm with hbW
  rw [← LinearMap.det_toMatrix bW]
  have hM : LinearMap.toMatrix bW bW (f.restrict hWf) =
      c₀ • ((h.siegelHermForm hb (e.blockSnd {i | σ i = 4})
        (e.blockSnd_le_lagrangianSnd _)).gramMatrix (e.blockSndBasis {i | σ i = 4}))ᵀ := by
    ext j k
    have hk4 : σ k = 4 := k.2
    have hincl : Submodule.inclusion (e.blockSnd_le_lagrangianSnd _)
        (e.blockSndBasis {i | σ i = 4} k) = ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩ :=
      Subtype.ext (e.blockSndBasis_apply _ k)
    rw [LinearMap.toMatrix_apply, Matrix.smul_apply, Matrix.transpose_apply, gramMatrix_apply,
      siegelHermForm_apply, hincl, smul_eq_mul]
    change (e.blockFstBasis {i | σ i = 4}).repr
      (Submodule.comapSubtypeEquivOfLe (e.blockFst_le_lagrangianFst _)
        (f.restrict hWf (bW k))) j = _
    rw [blockFstBasis_repr]
    change h (((m₄ : h.isometryGroup) : V ≃ₗ[K] V) (e.blockFstBasis _ k)) (e.snd j) =
      c₀ * h _ (e.blockSndBasis _ j)
    rw [blockFstBasis_apply, blockSndBasis_apply, hm4, ite_eq_left hk4, h.map_smul_left]
  rw [hM, Matrix.det_smul, Matrix.det_transpose]
  congr 2
  rw [Fintype.card_subtype]
  rfl

variable [NeZero (2 : K)]

/-- `x(κ₁ κ₂) = (-ε)^{|T₁| + |T₄|} det(Y_{T₄}, (-, -)_b)` and `κ₁ κ₂ ∈ P w_{T₂ ∪ T₃ ∪ T₄} P`
(the computation of GKT Proposition 4.41, (4.17)). -/
private theorem raoFunction_kappa
    (hb0 : ∀ y : e.lagrangianSnd, (y : V) ∈ e.blockSnd {i | σ i ≠ 4} → b y = 0)
    (hb4 : ∀ y : e.lagrangianSnd, (b y : V) ∈ e.blockFst {i | σ i = 4})
    (hnd : (h.siegelHermForm hb (e.blockSnd {i | σ i = 4})
      (e.blockSnd_le_lagrangianSnd _)).Nondegenerate) :
    (∃ p₁ ∈ h.siegelParabolic e.lagrangianFst, ∃ p₂ ∈ h.siegelParabolic e.lagrangianFst,
      e.kappa σ hb = p₁ * e.weylElement (Finset.univ.filter fun i => σ i = 2 ∨ σ i = 3 ∨ σ i = 4) *
        p₂) ∧
    e.raoFunction (e.kappa σ hb) = QuotientGroup.mk (signUnit K (-ε) ^
      ((Finset.univ.filter fun i => σ i = 1).card + (Finset.univ.filter fun i => σ i = 4).card)) *
      (h.siegelHermForm hb (e.blockSnd {i | σ i = 4}) (e.blockSnd_le_lagrangianSnd _)).det hnd := by
  have hb0' : ∀ k, σ k ≠ 4 → b ⟨e.snd k, e.snd_mem_lagrangianSnd k⟩ = 0 := fun k hk =>
    hb0 _ (e.snd_mem_blockSnd hk)
  have hinj : ∀ y : e.lagrangianSnd, (y : V) ∈ e.blockSnd {i | σ i = 4} → b y = 0 → y = 0 := by
    intro y hy hby
    have : (⟨y, hy⟩ : e.blockSnd {i | σ i = 4}) = 0 := hnd _ fun y' => by
      rw [siegelHermForm_apply, show Submodule.inclusion (e.blockSnd_le_lagrangianSnd _)
        (⟨y, hy⟩ : e.blockSnd {i | σ i = 4}) = y from rfl, hby, Submodule.coe_zero,
        h.map_zero_left]
    have h2 : ((⟨y, hy⟩ : e.blockSnd {i | σ i = 4}) : V) = 0 := by rw [this]; rfl
    exact Subtype.ext h2
  obtain ⟨c, hc, q, hκ, hq0, hq1, hq4⟩ := e.exists_kappa_eq hb hb0' hb4 hinj
  have hn'P := siegelUnipotent_le_siegelParabolic e.nondegenerate e.isLagrangian_lagrangianFst
    (siegelUnipotentOf_mem e.nondegenerate e.isLagrangian_lagrangianFst
      e.isCompl_lagrangianFst_lagrangianSnd hc)
  refine ⟨⟨_, hn'P, q, q.2, hκ⟩, ?_⟩
  rw [e.raoFunction_eq _ ⟨_, hn'P⟩ q hκ]
  have hdet1 : h.siegelDet e.lagrangianFst ⟨_, hn'P⟩ = 1 := by
    rw [siegelDet, MonoidHom.comp_apply]
    convert LinearEquiv.det.map_one
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    exact apply_eq_of_mem_siegelUnipotent e.nondegenerate e.isLagrangian_lagrangianFst
      (siegelUnipotentOf_mem e.nondegenerate e.isLagrangian_lagrangianFst
        e.isCompl_lagrangianFst_lagrangianSnd hc) x.2
  rw [hdet1, one_mul, det_eq_mk _ hnd (e.blockSndBasis {i | σ i = 4}), ← QuotientGroup.mk_mul]
  congr 1
  apply Units.ext
  rw [e.coe_siegelDet_of_apply hb hb4 q hq0 hq1 hq4, Units.val_mul, Units.val_pow_eq_pow_val,
    coe_signUnit, coe_detUnit]

omit [FiniteDimensional K V] in
private theorem mul_one_mul {G : Type*} [Group G] (a b : G) : a * 1 * b = a * b := by
  rw [mul_one]

omit [FiniteDimensional K V] in
private theorem comm_aux {G : Type*} [CommGroup G] (a d u D c : G) :
    a * (u * D) * c⁻¹ = a * d⁻¹ * (d * c⁻¹) * u * D := by
  rw [mul_assoc a d⁻¹, inv_mul_cancel_left]
  ac_rfl

omit [NeZero (2 : K)] [FiniteDimensional K V] in
private theorem card_filter_or₃ {a a' a'' : Fin 5} (h₁ : a ≠ a') (h₂ : a ≠ a'') (h₃ : a' ≠ a'') :
    (Finset.univ.filter fun i => σ i = a ∨ σ i = a' ∨ σ i = a'').card =
      (Finset.univ.filter fun i => σ i = a).card + (Finset.univ.filter fun i => σ i = a').card +
        (Finset.univ.filter fun i => σ i = a'').card := by
  have d₁ : Disjoint (Finset.univ.filter fun i => σ i = a')
      (Finset.univ.filter fun i => σ i = a'') :=
    Finset.disjoint_filter.2 fun i _ hi hi' => h₃ (hi.symm.trans hi')
  have d₂ : Disjoint (Finset.univ.filter fun i => σ i = a)
      ((Finset.univ.filter fun i => σ i = a') ∪ (Finset.univ.filter fun i => σ i = a'')) := by
    rw [Finset.disjoint_union_right]
    exact ⟨Finset.disjoint_filter.2 fun i _ hi hi' => h₁ (hi.symm.trans hi'),
      Finset.disjoint_filter.2 fun i _ hi hi' => h₂ (hi.symm.trans hi')⟩
  rw [Finset.filter_or, Finset.filter_or, Finset.card_union_of_disjoint d₂,
    Finset.card_union_of_disjoint d₁, add_assoc]

variable {e} in
/-- GKT Proposition 4.41: if `g₁ ∈ P w_{S₁} P`, `g₂ ∈ P w_{S₂} P`, `g₁ g₂ ∈ P w_S P` and
`ρ = L(X, g₁⁻¹ X, g₂ X)`, then `|S₁| + |S₂| + dim ρ = |S| + 2t` for an integer `t`, and
`x(g₁ g₂) = x(g₁) x(g₂) (-ε)^t det(ρ)` (`r = 1`). -/
theorem raoFunction_mul {g₁ g₂ : h.isometryGroup} {S₁ S₂ S : Finset ι}
    (h₁ : ∃ p₁ ∈ h.siegelParabolic e.lagrangianFst, ∃ p₂ ∈ h.siegelParabolic e.lagrangianFst,
      g₁ = p₁ * e.weylElement S₁ * p₂)
    (h₂ : ∃ p₁ ∈ h.siegelParabolic e.lagrangianFst, ∃ p₂ ∈ h.siegelParabolic e.lagrangianFst,
      g₂ = p₁ * e.weylElement S₂ * p₂)
    (h₃ : ∃ p₁ ∈ h.siegelParabolic e.lagrangianFst, ∃ p₂ ∈ h.siegelParabolic e.lagrangianFst,
      g₁ * g₂ = p₁ * e.weylElement S * p₂) :
    ∃ t : ℕ, S₁.card + S₂.card + finrank K (h.reductionSubmodule (lerayM e.lagrangianFst
        (e.lagrangianFst.map ((g₁⁻¹ : h.isometryGroup) : V ≃ₗ[K] V).toLinearMap)
        (e.lagrangianFst.map (g₂ : V ≃ₗ[K] V).toLinearMap))
        (e.lagrangianFst.map ((g₁⁻¹ : h.isometryGroup) : V ≃ₗ[K] V).toLinearMap)) =
          S.card + 2 * t ∧
      e.raoFunction (g₁ * g₂) = e.raoFunction g₁ * e.raoFunction g₂ *
        QuotientGroup.mk (signUnit K (-ε) ^ t) *
        (h.lerayInvariant e.nondegenerate e.isLagrangian_lagrangianFst
          (e.isLagrangian_lagrangianFst.map g₁⁻¹) (e.isLagrangian_lagrangianFst.map g₂)).det
          (lerayInvariant_nondegenerate _ _ _ _) := by
  obtain ⟨σ, b, hb, hb0, hb4, ⟨p₁, hp₁, p, hp, p₂, hp₂, hg₁, hg₂⟩, hnd, ⟨L⟩⟩ :=
    e.exists_generalizedBruhat g₁ g₂
  obtain ⟨⟨q₁, hq₁, q₂, hq₂, hκ⟩, hx⟩ := e.raoFunction_kappa hb hb0 hb4 hnd
  have hnP := siegelUnipotent_le_siegelParabolic e.nondegenerate e.isLagrangian_lagrangianFst
    (siegelUnipotentOf_mem e.nondegenerate e.isLagrangian_lagrangianFst
      e.isCompl_lagrangianFst_lagrangianSnd hb)
  have hg₁₂ : g₁ * g₂ = p₁ * e.kappa σ hb * p₂⁻¹ := by
    rw [hg₁, hg₂, kappa]; group
  refine ⟨(Finset.univ.filter fun i => σ i = 1).card +
    (Finset.univ.filter fun i => σ i = 4).card, ?_, ?_⟩
  · have hA : S₁.card = (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 2 ∨ σ i = 4).card := by
      have e1 := (e.mem_doubleCoset_weylElement_iff S₁ g₁).1 h₁
      have e2 := (e.mem_doubleCoset_weylElement_iff _ g₁).1
        ⟨p₁, hp₁, p⁻¹, (h.siegelParabolic _).inv_mem hp, hg₁⟩
      omega
    have hB : S₂.card = (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 3 ∨ σ i = 4).card := by
      have e1 := (e.mem_doubleCoset_weylElement_iff S₂ g₂).1 h₂
      have e2 := (e.mem_doubleCoset_weylElement_iff
        (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 3 ∨ σ i = 4) g₂).1
        ⟨p * _, (h.siegelParabolic _).mul_mem hp hnP, p₂⁻¹, (h.siegelParabolic _).inv_mem hp₂,
          by rw [hg₂]; group⟩
      omega
    have hS : S.card = (Finset.univ.filter fun i => σ i = 2 ∨ σ i = 3 ∨ σ i = 4).card := by
      have e1 := (e.mem_doubleCoset_weylElement_iff S (g₁ * g₂)).1 h₃
      have e2 := (e.mem_doubleCoset_weylElement_iff
        (Finset.univ.filter fun i => σ i = 2 ∨ σ i = 3 ∨ σ i = 4) (g₁ * g₂)).1
        ⟨p₁ * q₁, (h.siegelParabolic _).mul_mem hp₁ hq₁, q₂ * p₂⁻¹,
          (h.siegelParabolic _).mul_mem hq₂ ((h.siegelParabolic _).inv_mem hp₂),
          by rw [hg₁₂, hκ]; group⟩
      omega
    have hρ := L.toLinearEquiv.finrank_eq
    rw [← Finset.coe_filter_univ, e.finrank_blockSnd] at hρ
    rw [hρ, hA, hB, hS, card_filter_or₃ (by decide) (by decide) (by decide),
      card_filter_or₃ (by decide) (by decide) (by decide),
      card_filter_or₃ (by decide) (by decide) (by decide)]
    ring
  · have hx₁ : e.raoFunction g₁ = QuotientGroup.mk (h.siegelDet _ ⟨p₁, hp₁⟩) *
        (QuotientGroup.mk (h.siegelDet _ ⟨p, hp⟩))⁻¹ := by
      rw [hg₁, show (p₁ * e.weylElement (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 2 ∨ σ i = 4)
        * p⁻¹ : h.isometryGroup) = ((⟨p₁, hp₁⟩ : h.siegelParabolic _) : h.isometryGroup) *
          e.weylElement _ * ((⟨p, hp⟩⁻¹ : h.siegelParabolic _) : h.isometryGroup) from rfl,
        e.raoFunction_mul_mul, e.raoFunction_weylElement, map_inv, QuotientGroup.mk_inv]
      exact mul_one_mul _ _
    have hx₂ : e.raoFunction g₂ = QuotientGroup.mk (h.siegelDet _ ⟨p, hp⟩) *
        (QuotientGroup.mk (h.siegelDet _ ⟨p₂, hp₂⟩))⁻¹ := by
      have hn1 := e.siegelDet_eq_one_of_mem_siegelUnipotent (siegelUnipotentOf_mem
        e.nondegenerate e.isLagrangian_lagrangianFst e.isCompl_lagrangianFst_lagrangianSnd hb) hnP
      rw [hg₂, show (p * (h.siegelUnipotentOf e.nondegenerate e.isLagrangian_lagrangianFst
          e.isCompl_lagrangianFst_lagrangianSnd b hb *
          e.weylElement (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 3 ∨ σ i = 4)) * p₂⁻¹ :
          h.isometryGroup) = ((⟨p, hp⟩ * ⟨_, hnP⟩ : h.siegelParabolic _) : h.isometryGroup) *
          e.weylElement (Finset.univ.filter fun i => σ i = 1 ∨ σ i = 3 ∨ σ i = 4) *
          ((⟨p₂, hp₂⟩⁻¹ : h.siegelParabolic _) : h.isometryGroup) by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group,
        e.raoFunction_mul_mul, e.raoFunction_weylElement, map_mul, hn1, mul_one, map_inv,
        QuotientGroup.mk_inv]
      exact mul_one_mul _ _
    have hx₁₂ : e.raoFunction (g₁ * g₂) = QuotientGroup.mk (h.siegelDet _ ⟨p₁, hp₁⟩) *
        e.raoFunction (e.kappa σ hb) * (QuotientGroup.mk (h.siegelDet _ ⟨p₂, hp₂⟩))⁻¹ := by
      rw [hg₁₂, show (p₁ * e.kappa σ hb * p₂⁻¹ : h.isometryGroup) =
        ((⟨p₁, hp₁⟩ : h.siegelParabolic _) : h.isometryGroup) * e.kappa σ hb *
          ((⟨p₂, hp₂⟩⁻¹ : h.siegelParabolic _) : h.isometryGroup) from rfl,
        e.raoFunction_mul_mul, map_inv, QuotientGroup.mk_inv]
    rw [hx₁₂, hx, hx₁, hx₂, IsometryEquiv.det_eq L (lerayInvariant_nondegenerate _ _ _ _) hnd]
    exact comm_aux (G := Kˣ ⧸ normSubgroup τ) _ _ _ _ _

omit [FiniteDimensional K V] in
private theorem mul_one_mul_one {G : Type*} [Group G] (a : G) : a * 1 * 1 = a := by
  rw [mul_one, mul_one]

variable {e} in
/-- GKT Corollary 4.42 (`r = 1`): if `-ε = 1` and every Leray invariant `L(X, g₁⁻¹ X, g₂ X)` has
trivial determinant modulo norms, the Rao function is a homomorphism. -/
theorem raoFunction_mul_of_det_eq_one (hε : -ε = 1)
    (hdet : ∀ g₁ g₂ : h.isometryGroup, (h.lerayInvariant e.nondegenerate
      e.isLagrangian_lagrangianFst (e.isLagrangian_lagrangianFst.map g₁⁻¹)
      (e.isLagrangian_lagrangianFst.map g₂)).det (lerayInvariant_nondegenerate _ _ _ _) = 1)
    (g₁ g₂ : h.isometryGroup) :
    e.raoFunction (g₁ * g₂) = e.raoFunction g₁ * e.raoFunction g₂ := by
  obtain ⟨S₁, h₁⟩ := e.exists_mem_doubleCoset g₁
  obtain ⟨S₂, h₂⟩ := e.exists_mem_doubleCoset g₂
  obtain ⟨S, h₃⟩ := e.exists_mem_doubleCoset (g₁ * g₂)
  obtain ⟨t, -, ht⟩ := raoFunction_mul h₁ h₂ h₃
  rw [ht, hdet, hε, signUnit_one, one_pow, QuotientGroup.mk_one]
  exact mul_one_mul_one (G := Kˣ ⧸ normSubgroup τ) _

end StandardBasis

end Multiplicativity

section Scaling

/-! ### Changing `W` by a scalar (GKT §4.5.7) -/

variable {ε : ℤˣ} (h : EpsilonHermitianForm τ (-ε) V)

/-- The form `a h` (the book's `W^a`) for `a` with `a^τ = s a`, `s = ±1`; it is
`-(ε s)`-Hermitian (GKT §4.5.7). -/
def scale (a : K) (s : ℤˣ) (ha : conj τ a = ((s : ℤ) : K) * a) :
    EpsilonHermitianForm τ (-(ε * s)) V where
  toFun x y := a * h x y
  map_add_left' x y z := by rw [h.map_add_left, mul_add]
  map_smul_left' c x y := by rw [h.map_smul_left]; ring
  conj_swap' x y := by
    change a * h y x = (((-(ε * s) : ℤˣ) : ℤ) : K) * conj τ (a * h x y)
    rw [h.conj_swap x y, RingInvo.conj_mul, ha]
    have hs : ((s : ℤ) : K) * ((s : ℤ) : K) = 1 := units_int_cast_mul_self' s
    simp only [Units.val_neg, Units.val_mul, Int.cast_neg, Int.cast_mul]
    linear_combination (((ε : ℤ) : K) * a * conj τ (h x y)) * hs

variable {h}

@[simp] theorem scale_apply (a : K) (s : ℤˣ) (ha : conj τ a = ((s : ℤ) : K) * a) (x y : V) :
    h.scale a s ha x y = a * h x y := rfl

theorem isometryGroup_scale {a : K} {s : ℤˣ} (ha : conj τ a = ((s : ℤ) : K) * a) (ha0 : a ≠ 0) :
    (h.scale a s ha).isometryGroup = h.isometryGroup := by
  ext g
  rw [mem_isometryGroup_iff, mem_isometryGroup_iff]
  exact ⟨fun H x y => mul_left_cancel₀ ha0 (H x y),
    fun H x y => by rw [scale_apply, scale_apply, H]⟩

/-- The identification `G(W) = G(W^a)` of the two isometry groups. -/
def toScaleIsometryGroup {a : K} {s : ℤˣ} (ha : conj τ a = ((s : ℤ) : K) * a) (ha0 : a ≠ 0) :
    h.isometryGroup ≃* (h.scale a s ha).isometryGroup :=
  MulEquiv.subgroupCongr (isometryGroup_scale ha ha0).symm

@[simp] theorem coe_toScaleIsometryGroup {a : K} {s : ℤˣ}
    (ha : conj τ a = ((s : ℤ) : K) * a) (ha0 : a ≠ 0) (g : h.isometryGroup) :
    ((toScaleIsometryGroup ha ha0 g : (h.scale a s ha).isometryGroup) : V ≃ₗ[K] V) =
      (g : V ≃ₗ[K] V) := rfl

namespace StandardBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : h.StandardBasis ι)

/-- The standard basis `{eᵢ} ∪ {eᵢ* (a^τ)⁻¹}` of `W^a` (the book's `{eᵢ} ∪ {eᵢ* (1/a)}`). -/
def scale {a : K} {s : ℤˣ} (ha : conj τ a = ((s : ℤ) : K) * a) (ha0 : a ≠ 0) :
    (h.scale a s ha).StandardBasis ι where
  basis := e.basis.unitsSMul fun k => Sum.elim (fun _ => 1)
    (fun _ => Units.mk0 (conj τ a)⁻¹ (inv_ne_zero ((RingInvo.conj_eq_zero_iff τ).not.2 ha0))) k
  apply_inl_inl i j := by
    simp only [Basis.unitsSMul_apply, Sum.elim_inl, one_smul, scale_apply, e.apply_inl_inl,
      mul_zero]
  apply_inr_inr i j := by
    simp only [Basis.unitsSMul_apply, Sum.elim_inr, Units.smul_mk0, scale_apply, h.map_smul_left,
      h.map_smul_right, e.apply_inr_inr, mul_zero, zero_mul]
  apply_inl_inr i j := by
    simp only [Basis.unitsSMul_apply, Sum.elim_inl, Sum.elim_inr, one_smul, Units.smul_mk0,
      scale_apply, h.map_smul_right, e.apply_inl_inr, RingInvo.conj_inv, RingInvo.conj_conj]
    split_ifs <;> simp [ha0]

omit [Fintype ι] in
@[simp] theorem scale_fst {a : K} {s : ℤˣ} (ha : conj τ a = ((s : ℤ) : K) * a) (ha0 : a ≠ 0)
    (i : ι) : (e.scale ha ha0).fst i = e.fst i := by
  simp [scale, fst, Basis.unitsSMul_apply]

omit [Fintype ι] in
@[simp] theorem scale_snd {a : K} {s : ℤˣ} (ha : conj τ a = ((s : ℤ) : K) * a) (ha0 : a ≠ 0)
    (i : ι) : (e.scale ha ha0).snd i = (conj τ a)⁻¹ • e.snd i := by
  simp [scale, snd, Basis.unitsSMul_apply, Units.smul_mk0]

omit [Fintype ι] in
theorem lagrangianFst_scale {a : K} {s : ℤˣ} (ha : conj τ a = ((s : ℤ) : K) * a) (ha0 : a ≠ 0) :
    (e.scale ha ha0).lagrangianFst = e.lagrangianFst := by
  rw [lagrangianFst, lagrangianFst, show (e.scale ha ha0).fst = e.fst from
    funext (e.scale_fst ha ha0)]

variable [FiniteDimensional K V] [NeZero (2 : K)]

/-- GKT Lemma 4.45: for `a^τ = ±a` and `g ∈ P w_S P`, the Rao functions of `W^a` and `W` satisfy
`x_a(g) = x(g) (a^τ)^{-|S|}` (`≡ x(g) a^{|S|}` modulo norms). -/
theorem raoFunction_scale {a : K} {s : ℤˣ} (ha : conj τ a = ((s : ℤ) : K) * a) (ha0 : a ≠ 0)
    {g : h.isometryGroup} (S : Finset ι)
    (hg : ∃ p₁ ∈ h.siegelParabolic e.lagrangianFst, ∃ p₂ ∈ h.siegelParabolic e.lagrangianFst,
      g = p₁ * e.weylElement S * p₂) :
    (e.scale ha ha0).raoFunction (toScaleIsometryGroup ha ha0 g) = e.raoFunction g *
      (QuotientGroup.mk (Units.mk0 (conj τ a) ((RingInvo.conj_eq_zero_iff τ).not.2 ha0)))⁻¹ ^
        S.card := by
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := hg
  set T := toScaleIsometryGroup (h := h) ha ha0
  have hca0 : conj τ a ≠ 0 := (RingInvo.conj_eq_zero_iff τ).not.2 ha0
  -- `d = w^a_S w_S⁻¹` acts on `X` by `a^τ` on `X_S`
  set d := T.symm ((e.scale ha ha0).weylElement S) * (e.weylElement S)⁻¹ with hd
  have hdX : ∀ i, ((d : h.isometryGroup) : V ≃ₗ[K] V) (e.fst i) =
      (if i ∈ S then conj τ a else 1) • e.fst i := by
    intro i
    rw [hd, isometryGroup_coe_mul_apply]
    by_cases hi : i ∈ S
    · conv_lhs => rw [← e.weylElement_snd_of_mem hi, isometryGroup_coe_inv_apply']
      change (((e.scale ha ha0).weylElement S : (h.scale a s ha).isometryGroup) : V ≃ₗ[K] V)
        (e.snd i) = _
      have h1 := (e.scale ha ha0).weylElement_snd_of_mem hi
      rw [scale_snd, scale_fst, map_smul] at h1
      have h2 := congrArg (conj τ a • ·) h1
      simp only [smul_smul, mul_inv_cancel₀ hca0, one_smul] at h2
      rw [h2]; simp [hi]
    · conv_lhs => rw [← e.weylElement_fst_of_not_mem hi, isometryGroup_coe_inv_apply']
      change (((e.scale ha ha0).weylElement S : (h.scale a s ha).isometryGroup) : V ≃ₗ[K] V)
        (e.fst i) = _
      have h1 := (e.scale ha ha0).weylElement_fst_of_not_mem hi
      rw [scale_fst] at h1
      rw [h1]; simp [hi]
  have hdP : d ∈ h.siegelParabolic e.lagrangianFst :=
    e.map_lagrangianFst_eq d e.isLagrangian_lagrangianFst fun i => by
      rw [hdX]; exact Submodule.smul_mem _ _ (e.fst_mem_lagrangianFst i)
  have hdet : (h.siegelDet e.lagrangianFst ⟨d, hdP⟩ : K) = conj τ a ^ S.card := by
    rw [coe_siegelDet, e.det_eq_prod_of_apply_basisFst _
      (fun i => if i ∈ S then conj τ a else 1)
      (fun i => by
        change ((d : h.isometryGroup) : V ≃ₗ[K] V) (e.basisFst i) = _
        rw [basisFst_apply, hdX]),
      Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  -- transport of `P` and of `det(·|_X)`
  have hP : ∀ q ∈ h.siegelParabolic e.lagrangianFst,
      T q ∈ (h.scale a s ha).siegelParabolic (e.scale ha ha0).lagrangianFst := fun q hq => by
    rw [lagrangianFst_scale]; exact hq
  have hdetT : ∀ q (hq : q ∈ h.siegelParabolic e.lagrangianFst),
      (h.scale a s ha).siegelDet (e.scale ha ha0).lagrangianFst ⟨T q, hP q hq⟩ =
        h.siegelDet e.lagrangianFst ⟨q, hq⟩ := by
    intro q hq
    have hX := e.lagrangianFst_scale ha ha0
    revert hP
    rw [hX]
    intro hP
    rfl
  have hdecomp : T (p₁ * e.weylElement S * p₂) =
      T (p₁ * d⁻¹) * (e.scale ha ha0).weylElement S * T p₂ := by
    rw [hd, _root_.mul_inv_rev, inv_inv]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    group
  have hmem : p₁ * d⁻¹ ∈ h.siegelParabolic e.lagrangianFst :=
    (h.siegelParabolic _).mul_mem hp₁ ((h.siegelParabolic _).inv_mem hdP)
  rw [(e.scale ha ha0).raoFunction_eq S ⟨_, hP _ hmem⟩ ⟨_, hP p₂ hp₂⟩ hdecomp, hdetT _ hmem,
    hdetT p₂ hp₂,
    e.raoFunction_eq S ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ rfl,
    show (⟨p₁ * d⁻¹, (h.siegelParabolic _).mul_mem hp₁ ((h.siegelParabolic _).inv_mem hdP)⟩ :
      h.siegelParabolic e.lagrangianFst) = ⟨p₁, hp₁⟩ * ⟨d, hdP⟩⁻¹ from rfl, map_mul, map_inv]
  have hu : h.siegelDet e.lagrangianFst ⟨d, hdP⟩ = Units.mk0 (conj τ a) hca0 ^ S.card :=
    Units.ext (by rw [hdet, Units.val_pow_eq_pow_val, Units.val_mk0])
  rw [hu, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul]
  congr 1
  rw [inv_pow]
  ac_rfl

end StandardBasis

end Scaling

end EpsilonHermitianForm

end Langlands
