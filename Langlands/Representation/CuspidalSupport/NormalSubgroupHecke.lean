import Langlands.Representation.Induction.OpenAdjunction

/-!
# The Hecke algebra of an open normal subgroup

Let `H` be an open normal subgroup of a topological group `G`, let `ρ` be an
irreducible smooth complex representation of `H` and let `I = ind_H^G ρ` be the
published compact induction. This module identifies `End I` with the space
`heckeSubmodule H ρ` of functions `φ : G → End ρ` with `φ(h g h') = ρ(h) φ(g) ρ(h')`
whose support meets finitely many cosets, carrying composition to the convolution
`heckeConvolution H ρ` (Renard VI.4.2 in this generality).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport.NormalHecke

universe uG uV

open Induction

variable {G : Type uG} [Group G]

section Quotients

variable (H : Subgroup G) [hN : H.Normal]

/-- For a normal subgroup the cosets `H x` and `x H` coincide. -/
def leftQuotientEquiv : LeftQuotient H ≃ G ⧸ H :=
  Quotient.congr (Equiv.refl G) fun a b => by
    change QuotientGroup.rightRel H a b ↔ QuotientGroup.leftRel H a b
    rw [QuotientGroup.rightRel_apply, QuotientGroup.leftRel_apply]
    exact hN.mem_comm_iff

theorem leftQuotientEquiv_quotientMap (x : G) :
    leftQuotientEquiv H (quotientMap H x) = (x : G ⧸ H) :=
  rfl

omit hN in
theorem quotientMap_out (q : LeftQuotient H) : quotientMap H (Quotient.out q) = q :=
  Quotient.out_eq q

theorem leftQuotientEquiv_apply (q : LeftQuotient H) :
    leftQuotientEquiv H q = ((Quotient.out q : G) : G ⧸ H) := by
  conv_lhs => rw [← quotientMap_out H q]
  rfl

/-- The images of a set in `H \ G` and in `G ⧸ H` are simultaneously finite. -/
theorem finite_mk_image_iff (S : Set G) :
    (QuotientGroup.mk '' S : Set (G ⧸ H)).Finite ↔ (quotientMap H '' S).Finite := by
  have h : (QuotientGroup.mk '' S : Set (G ⧸ H)) =
      leftQuotientEquiv H '' (quotientMap H '' S) := by
    rw [Set.image_image]
    rfl
  rw [h, Set.finite_image_iff (leftQuotientEquiv H).injective.injOn]

/-- A sum over `H \ G` of a function of the representatives which is invariant under
right multiplication by `H` equals the corresponding sum over `G ⧸ H`. -/
theorem finsum_leftQuotient_eq {M : Type*} [AddCommMonoid M] (Φ : G → M)
    (hΦ : ∀ (g : G) (h : H), Φ (g * h) = Φ g) :
    ∑ᶠ q : LeftQuotient H, Φ (Quotient.out q) = ∑ᶠ q : G ⧸ H, Φ q.out := by
  rw [← finsum_comp_equiv (leftQuotientEquiv H)]
  refine finsum_congr fun q => ?_
  have hq : (((leftQuotientEquiv H q).out : G) : G ⧸ H) = ((Quotient.out q : G) : G ⧸ H) := by
    rw [QuotientGroup.out_eq', leftQuotientEquiv_apply]
  have hmem := QuotientGroup.eq.mp hq.symm
  have := hΦ (Quotient.out q) ⟨_, hmem⟩
  rw [mul_inv_cancel_left] at this
  exact this.symm

/-- Reindexing a sum over `G ⧸ H` along `q ↦ x q⁻¹`, for a function of the representatives
which is invariant under right multiplication by `H`. -/
theorem finsum_quotient_mul_inv {M : Type*} [AddCommMonoid M] (Ψ : G → M)
    (hΨ : ∀ (g : G) (h : H), Ψ (g * h) = Ψ g) (x : G) :
    ∑ᶠ q : G ⧸ H, Ψ (x * q.out⁻¹) = ∑ᶠ q : G ⧸ H, Ψ q.out := by
  let E : G ⧸ H ≃ G ⧸ H := (Equiv.inv (G ⧸ H)).trans (Equiv.mulLeft (x : G ⧸ H))
  refine Eq.trans ?_ (finsum_comp_equiv E (f := fun q : G ⧸ H => Ψ q.out))
  refine finsum_congr fun q => ?_
  have hq : ((E q).out : G ⧸ H) = ((x * q.out⁻¹ : G) : G ⧸ H) := by
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq']
    rfl
  have hmem := QuotientGroup.eq.mp hq.symm
  have := hΨ (x * q.out⁻¹) ⟨_, hmem⟩
  rw [mul_inv_cancel_left] at this
  exact this.symm

/-- A sum over `H \ G` along `q ↦ x q⁻¹`, for a function which is invariant under left and
right multiplication by `H`, equals the sum over the representatives. -/
theorem finsum_leftQuotient_mul_inv {M : Type*} [AddCommMonoid M] (Ψ : G → M)
    (hl : ∀ (h : H) (g : G), Ψ (h * g) = Ψ g) (hr : ∀ (g : G) (h : H), Ψ (g * h) = Ψ g)
    (x : G) :
    ∑ᶠ q : LeftQuotient H, Ψ (x * (Quotient.out q)⁻¹) =
      ∑ᶠ q : LeftQuotient H, Ψ (Quotient.out q) := by
  have hr' : ∀ (g : G) (h : H), Ψ (x * (g * h)⁻¹) = Ψ (x * g⁻¹) := by
    intro g h
    have hmem : x * (h : G)⁻¹ * x⁻¹ ∈ H := hN.conj_mem _ (H.inv_mem h.2) x
    rw [mul_inv_rev, ← mul_assoc, show x * (h : G)⁻¹ = (x * (h : G)⁻¹ * x⁻¹) * x by group,
      mul_assoc]
    exact hl ⟨_, hmem⟩ _
  rw [finsum_leftQuotient_eq H (fun g => Ψ (x * g⁻¹)) hr', finsum_leftQuotient_eq H Ψ hr]
  exact finsum_quotient_mul_inv H Ψ hr x

end Quotients

section Irreducible

variable {K : Type*} [Group K] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ K V)

/-- In an irreducible representation, a stable subspace containing a nonzero vector is
everything. -/
theorem mem_of_isIrreducible [σ.IsIrreducible] (W : Submodule ℂ V)
    (hW : ∀ (k : K) (v : V), v ∈ W → σ k v ∈ W) {w₀ : V} (hw₀ : w₀ ∈ W) (hne : w₀ ≠ 0)
    (v : V) : v ∈ W := by
  let S : Subrepresentation σ := ⟨W, fun k v hv => hW k v hv⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top S with hS | hS
  · have h0 : w₀ ∈ (⊥ : Subrepresentation σ).toSubmodule := by
      rw [← hS]
      exact hw₀
    exact absurd ((Submodule.mem_bot ℂ).mp h0) hne
  · have h1 : v ∈ (⊤ : Subrepresentation σ).toSubmodule := Submodule.mem_top
    rw [← hS] at h1
    exact h1

/-- An irreducible representation has a nonzero vector. -/
theorem exists_ne_zero_of_isIrreducible [σ.IsIrreducible] : ∃ v : V, v ≠ 0 := by
  by_contra h
  push Not at h
  apply (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  change (⊥ : Submodule ℂ V) = ⊤
  refine eq_top_iff.mpr fun v _ => ?_
  rw [h v]
  exact Submodule.zero_mem _

/-- A nonzero endomorphism of an irreducible representation which is twisted-equivariant,
`T σ(k) = σ(c k) T`, is injective. -/
theorem injective_of_twisted [σ.IsIrreducible] (T : Module.End ℂ V) (c : K → K)
    (hT : ∀ (k : K) (v : V), T (σ k v) = σ (c k) (T v)) (hT0 : T ≠ 0) :
    Function.Injective T := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro w hw
  by_contra hne
  apply hT0
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply]
  refine LinearMap.mem_ker.mp (mem_of_isIrreducible σ (LinearMap.ker T) (fun k v hv => ?_) hw hne v)
  rw [LinearMap.mem_ker] at hv ⊢
  rw [hT, hv, map_zero]

end Irreducible

section Hecke

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) (ρ : SmoothRep.{0, uG, uV} ℂ H)

/-- Renard's `H(G,ρ)` (VI.4.2.1) for a subgroup `H`: the functions `φ : G → End ρ` with
`φ(h g h') = ρ(h) φ(g) ρ(h')` for `h, h' ∈ H`, whose support meets only finitely many
cosets `g H`. -/
def heckeSubmodule : Submodule ℂ (G → Module.End ℂ ρ) where
  carrier := {φ |
    (∀ (h h' : H) (g : G),
      φ ((h : G) * g * h') = ρ.representation h * φ g * ρ.representation h') ∧
    (QuotientGroup.mk '' Function.support φ : Set (G ⧸ H)).Finite}
  zero_mem' := by
    refine ⟨fun h h' g => ?_, ?_⟩
    · simp
    · simp
  add_mem' := by
    rintro φ ψ ⟨hφ, sφ⟩ ⟨hψ, sψ⟩
    refine ⟨fun h h' g => ?_, ?_⟩
    · simp only [Pi.add_apply, hφ, hψ, mul_add, add_mul]
    · refine (sφ.union sψ).subset ?_
      rintro _ ⟨x, hx, rfl⟩
      by_cases h0 : φ x = 0
      · refine Or.inr ⟨x, fun h1 => hx ?_, rfl⟩
        simp [h0, h1]
      · exact Or.inl ⟨x, h0, rfl⟩
  smul_mem' := by
    rintro c φ ⟨hφ, sφ⟩
    refine ⟨fun h h' g => ?_, ?_⟩
    · simp only [Pi.smul_apply, hφ, mul_smul_comm, smul_mul_assoc]
    · refine sφ.subset ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x, fun h0 => hx ?_, rfl⟩
      simp [h0]

/-- Renard's convolution `(φ ∗ ψ)(x) = ∑_{g ∈ G/H} φ(g) ψ(g⁻¹ x)` over the chosen
representatives of the cosets `g H`. -/
def heckeConvolution (φ ψ : G → Module.End ℂ ρ) : G → Module.End ℂ ρ :=
  fun x => ∑ᶠ q : G ⧸ H, φ q.out * ψ (q.out⁻¹ * x)

/-- The compact induction `ind_H^G ρ`. -/
abbrev inducedRep : SmoothRep.{0, uG, max uG uV} ℂ G :=
  (compactInductionFunctor H).obj (SmoothRep.toRep.obj ρ)

/-- Evaluation at `g`, as a linear map on compactly induced functions. -/
def evalLinear (g : G) : CompactFunctions H ρ.representation →ₗ[ℂ] ρ where
  toFun f := eval H ρ.representation f.1 g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem eval_mul_left (f : CompactFunctions H ρ.representation) (p : H) (x : G) :
    eval H ρ.representation f.1 ((p : G) * x) = ρ.representation p (eval H ρ.representation f.1 x) :=
  f.1.1.2 p x

omit [IsTopologicalGroup G] in
theorem representation_mul_inv (k : H) (u : ρ) :
    ρ.representation k (ρ.representation k⁻¹ u) = u := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]


omit [IsTopologicalGroup G] in
theorem hecke_mul_right {φ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ) (g : G) (h : H) :
    φ (g * h) = φ g * ρ.representation h := by
  have := hφ.1 1 h g
  rwa [OneMemClass.coe_one, one_mul, map_one, one_mul] at this

omit [IsTopologicalGroup G] in
theorem hecke_mul_left {φ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ) (h : H) (g : G) :
    φ (h * g) = ρ.representation h * φ g := by
  have := hφ.1 h 1 g
  rwa [OneMemClass.coe_one, mul_one, map_one, mul_one] at this

omit [IsTopologicalGroup G] in
theorem hecke_finite {φ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ) [H.Normal] :
    (quotientMap H '' Function.support φ).Finite :=
  (finite_mk_image_iff H _).mp hφ.2

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- For a normal subgroup, `H (g k) = H g` when `k ∈ H`. -/
theorem quotientMap_mul_mem [hN : H.Normal] (g : G) (k : H) :
    quotientMap H (g * k) = quotientMap H g := by
  rw [quotientMap_eq_iff]
  have := hN.conj_mem _ (H.inv_mem k.2) g
  rw [mul_inv_rev, ← mul_assoc]
  exact this

variable (hH : IsOpen (H : Set G))

/-- The value `φ_α(g) : w ↦ α(f_w)(g)` of the function attached to an endomorphism `α` of
`ind_H^G ρ`, where `f_w` is the function supported on `H` with `f_w(1) = w`. -/
def endValue (α : End (inducedRep H ρ)) (g : G) : Module.End ℂ ρ :=
  (evalLinear H ρ g).comp ((SmoothRep.hom α).toLinearMap.comp
    (unitMap H hH ρ.representation ρ.isSmooth).toLinearMap)

theorem endValue_apply (α : End (inducedRep H ρ)) (g : G) (w : ρ) :
    endValue H ρ hH α g w = eval H ρ.representation
      (SmoothRep.hom α (unitFunction H hH ρ.representation ρ.isSmooth w)).1 g :=
  rfl

/-- `α(f_{ρ(h) w})(g) = α(f_w)(g h)`. -/
theorem endValue_mul_right (α : End (inducedRep H ρ)) (g : G) (h : H) (w : ρ) :
    endValue H ρ hH α (g * h) w = endValue H ρ hH α g (ρ.representation h w) := by
  have h1 := Representation.IntertwiningMap.isIntertwining _ _
    (unitMap H hH ρ.representation ρ.isSmooth) h w
  have h2 := Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom α) (h : G)
    (unitMap H hH ρ.representation ρ.isSmooth w)
  rw [endValue_apply, endValue_apply, ← unitMap_apply, ← unitMap_apply, h1]
  change _ = eval H ρ.representation ((SmoothRep.hom α)
    ((inducedRep H ρ).representation (h : G) (unitMap H hH ρ.representation ρ.isSmooth w))).1 g
  rw [h2]
  rfl

theorem endValue_mul_left (α : End (inducedRep H ρ)) (h : H) (g : G) (w : ρ) :
    endValue H ρ hH α ((h : G) * g) w = ρ.representation h (endValue H ρ hH α g w) :=
  eval_mul_left H ρ _ h g

theorem endValue_bi (α : End (inducedRep H ρ)) (h h' : H) (g : G) :
    endValue H ρ hH α ((h : G) * g * h') =
      ρ.representation h * endValue H ρ hH α g * ρ.representation h' := by
  refine LinearMap.ext fun w => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, mul_assoc, endValue_mul_left,
    endValue_mul_right]

theorem endValue_mul_right' (α : End (inducedRep H ρ)) (g : G) (h : H) :
    endValue H ρ hH α (g * h) = endValue H ρ hH α g * ρ.representation h :=
  LinearMap.ext fun w => endValue_mul_right H ρ hH α g h w

variable [hN : H.Normal]

/-- The support of `φ_α` meets only finitely many cosets: the vectors `w` with
`α(f_w)` supported in the finitely many cosets meeting the support of `α(f_{w₀})` form a
subrepresentation containing `w₀ ≠ 0`, hence everything. -/
theorem endValue_finite [ρ.representation.IsIrreducible] (α : End (inducedRep H ρ)) :
    (QuotientGroup.mk '' Function.support (endValue H ρ hH α) : Set (G ⧸ H)).Finite := by
  obtain ⟨w₀, hw₀⟩ := exists_ne_zero_of_isIrreducible ρ.representation
  let X : Set (LeftQuotient H) := quotientSupport H (eval H ρ.representation
    (SmoothRep.hom α (unitFunction H hH ρ.representation ρ.isSmooth w₀)).1)
  have hX : X.Finite := quotientSupport_finite H ρ.representation hH _
  let W : Submodule ℂ ρ :=
    { carrier := {w | ∀ g, endValue H ρ hH α g w ≠ 0 → quotientMap H g ∈ X}
      add_mem' := by
        intro u v hu hv g hg
        rw [map_add] at hg
        by_cases h0 : endValue H ρ hH α g u = 0
        · rw [h0, zero_add] at hg
          exact hv g hg
        · exact hu g h0
      zero_mem' := by
        intro g hg
        exact absurd (map_zero _) hg
      smul_mem' := by
        intro c u hu g hg
        rw [map_smul] at hg
        exact hu g (right_ne_zero_of_smul hg) }
  have hW : ∀ w, w ∈ W := by
    refine mem_of_isIrreducible ρ.representation W (fun k w hw g hg => ?_) (fun g hg => ?_) hw₀
    · rw [← endValue_mul_right] at hg
      have := hw (g * k) hg
      rwa [quotientMap_mul_mem] at this
    · exact ⟨g, hg, rfl⟩
  rw [finite_mk_image_iff]
  refine hX.subset ?_
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, endValue H ρ hH α g w ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (LinearMap.ext h)
  exact hW w g hw

/-- For `φ` in the Hecke space and `w ∈ ρ`, the compactly induced function `x ↦ φ(x) w`. -/
def heckeFunction (φ : heckeSubmodule H ρ) (w : ρ) : CompactFunctions H ρ.representation :=
  compactFunctionOf H ρ.representation (fun x => (φ : G → Module.End ℂ ρ) x w)
    (fun p x => by
      rw [hecke_mul_left H ρ φ.2, Module.End.mul_apply])
    (openSubgroupMap H hH (Classical.choose (ρ.isSmooth w)))
    (fun k x => by
      obtain ⟨k₀, hk₀, hk⟩ := Subgroup.mem_map.mp k.2
      have hfix : ρ.representation k₀ w = w := Classical.choose_spec (ρ.isSmooth w) ⟨k₀, hk₀⟩
      change (φ : G → Module.End ℂ ρ) (x * (k : G)) w = (φ : G → Module.End ℂ ρ) x w
      rw [← hk]
      change (φ : G → Module.End ℂ ρ) (x * (k₀ : G)) w = _
      rw [hecke_mul_right H ρ φ.2, Module.End.mul_apply, hfix])
    (by
      refine ((hecke_finite H ρ φ.2).subset ?_).isCompact
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x, fun h0 => hx ?_, rfl⟩
      change (φ : G → Module.End ℂ ρ) x w = 0
      rw [h0]
      rfl)

theorem eval_heckeFunction (φ : heckeSubmodule H ρ) (w : ρ) (x : G) :
    eval H ρ.representation (heckeFunction H ρ hH φ w).1 x = (φ : G → Module.End ℂ ρ) x w :=
  rfl

/-- `w ↦ (x ↦ φ(x) w)`, an `H`-equivariant map `ρ → Res ind_H^G ρ`. -/
def heckeMap (φ : heckeSubmodule H ρ) :
    ρ.representation.IntertwiningMap ((compactInduced H ρ.representation).comp H.subtype) where
  toFun := heckeFunction H ρ hH φ
  map_add' v w := compactFunctions_ext H _ fun x => map_add ((φ : G → Module.End ℂ ρ) x) v w
  map_smul' c v := compactFunctions_ext H _ fun x => map_smul ((φ : G → Module.End ℂ ρ) x) c v
  isIntertwining' h := LinearMap.ext fun v => compactFunctions_ext H _ fun x => by
    change (φ : G → Module.End ℂ ρ) x (ρ.representation h v) =
      (φ : G → Module.End ℂ ρ) (x * (h : G)) v
    rw [hecke_mul_right H ρ φ.2, Module.End.mul_apply]

/-- The endomorphism `α_φ = ∑_{H x} r(x⁻¹) φ(·)(f(x))` of `ind_H^G ρ` attached to `φ`. -/
def endOfHecke (φ : heckeSubmodule H ρ) : End (inducedRep H ρ) :=
  SmoothRep.ofHom (cosetSum H hH (compactInduced H ρ.representation) ρ.representation
    (heckeMap H ρ hH φ))

theorem endValue_endOfHecke (φ : heckeSubmodule H ρ) (g : G) (w : ρ) :
    endValue H ρ hH (endOfHecke H ρ hH φ) g w = (φ : G → Module.End ℂ ρ) g w := by
  rw [endValue_apply, ← unitMap_apply]
  change eval H ρ.representation (cosetSum H hH (compactInduced H ρ.representation)
    ρ.representation (heckeMap H ρ hH φ) (unitMap H hH ρ.representation ρ.isSmooth w)).1 g = _
  rw [cosetSum_comp_unitMap]
  rfl

omit hN in
/-- Every endomorphism is the coset sum of its restriction to the unit functions. -/
theorem hom_eq_cosetSum (α : End (inducedRep H ρ)) (f : CompactFunctions H ρ.representation) :
    SmoothRep.hom α f = cosetSum H hH (compactInduced H ρ.representation) ρ.representation
      ((resIntertwining H _ (SmoothRep.hom α)).comp
        (unitMap H hH ρ.representation ρ.isSmooth)) f :=
  (congrArg (SmoothRep.hom α) (cosetSum_unitMap H hH ρ.representation ρ.isSmooth f)).symm.trans
    (cosetSum_resIntertwining_comp H hH _ ρ.representation (SmoothRep.hom α)
      (unitMap H hH ρ.representation ρ.isSmooth) f).symm

omit hN in
/-- Endomorphisms agreeing on all unit functions `f_w` are equal. -/
theorem end_ext {α β : End (inducedRep H ρ)}
    (h : ∀ g w, endValue H ρ hH α g w = endValue H ρ hH β g w) : α = β := by
  have hu : (resIntertwining H _ (SmoothRep.hom α)).comp
      (unitMap H hH ρ.representation ρ.isSmooth) =
      (resIntertwining H _ (SmoothRep.hom β)).comp (unitMap H hH ρ.representation ρ.isSmooth) := by
    ext w
    exact compactFunctions_ext H _ fun x => h x w
  rw [← SmoothRep.ofHom_hom α, ← SmoothRep.ofHom_hom β]
  congr 1
  ext f
  have e := congrArg (fun T => cosetSum H hH (compactInduced H ρ.representation)
    ρ.representation T f) hu
  exact (hom_eq_cosetSum H ρ hH α f).trans (e.trans (hom_eq_cosetSum H ρ hH β f).symm)

/-- The linear map `α ↦ φ_α` into the Hecke space. -/
def toHecke [ρ.representation.IsIrreducible] :
    End (inducedRep H ρ) →ₗ[ℂ] heckeSubmodule H ρ where
  toFun α := ⟨endValue H ρ hH α, endValue_bi H ρ hH α, endValue_finite H ρ hH α⟩
  map_add' _ _ := Subtype.ext (funext fun _ => LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => LinearMap.ext fun _ => rfl)

/-- Renard VI.4.2: `α ↦ φ_α` is a linear isomorphism `End (ind_H^G ρ) ≃ H(G,ρ)`. -/
def heckeEquiv [ρ.representation.IsIrreducible] :
    End (inducedRep H ρ) ≃ₗ[ℂ] heckeSubmodule H ρ :=
  { toHecke H ρ hH with
    invFun := endOfHecke H ρ hH
    left_inv := fun _ => end_ext H ρ hH fun g w => endValue_endOfHecke H ρ hH _ g w
    right_inv := fun φ => Subtype.ext (funext fun g => LinearMap.ext fun w =>
      endValue_endOfHecke H ρ hH φ g w) }

theorem heckeEquiv_apply [ρ.representation.IsIrreducible] (α : End (inducedRep H ρ)) (g : G)
    (w : ρ) : (heckeEquiv H ρ hH α : G → Module.End ℂ ρ) g w =
      eval H ρ.representation
        (SmoothRep.hom α (unitFunction H hH ρ.representation ρ.isSmooth w)).1 g :=
  rfl

theorem heckeEquiv_symm [ρ.representation.IsIrreducible] (φ : heckeSubmodule H ρ) :
    (heckeEquiv H ρ hH).symm φ = endOfHecke H ρ hH φ :=
  rfl

/-- The inverse formula `α_φ(v)(x) = ∑_{H g} φ(g)(v(g⁻¹ x))`. -/
theorem eval_endOfHecke (φ : heckeSubmodule H ρ) (v : CompactFunctions H ρ.representation)
    (x : G) :
    eval H ρ.representation (SmoothRep.hom (endOfHecke H ρ hH φ) v).1 x =
      ∑ᶠ q : LeftQuotient H, (φ : G → Module.End ℂ ρ) (Quotient.out q)
        (eval H ρ.representation v.1 ((Quotient.out q)⁻¹ * x)) := by
  let Ψ : G → ρ := fun g => (φ : G → Module.End ℂ ρ) g (eval H ρ.representation v.1 (g⁻¹ * x))
  have hl : ∀ (h : H) (g : G), Ψ (h * g) = Ψ g := by
    intro h g
    let k : H := ⟨g⁻¹ * h * g, by simpa using hN.conj_mem _ h.2 g⁻¹⟩
    have h1 : (h : G) * g = g * (k : G) := by
      change (h : G) * g = g * (g⁻¹ * h * g)
      group
    have h2 : ((h : G) * g)⁻¹ * x = ((k⁻¹ : H) : G) * (g⁻¹ * x) := by
      change ((h : G) * g)⁻¹ * x = (g⁻¹ * (h : G) * g)⁻¹ * (g⁻¹ * x)
      group
    simp only [Ψ]
    rw [h2, h1, hecke_mul_right H ρ φ.2, Module.End.mul_apply, eval_mul_left,
      representation_mul_inv]
  have hr : ∀ (g : G) (h : H), Ψ (g * h) = Ψ g := by
    intro g h
    have h2 : (g * (h : G))⁻¹ * x = ((h⁻¹ : H) : G) * (g⁻¹ * x) := by
      change (g * (h : G))⁻¹ * x = (h : G)⁻¹ * (g⁻¹ * x)
      group
    simp only [Ψ]
    rw [h2, hecke_mul_right H ρ φ.2, Module.End.mul_apply, eval_mul_left, representation_mul_inv]
  change evalAddHom H ρ.representation x (cosetSum H hH (compactInduced H ρ.representation)
    ρ.representation (heckeMap H ρ hH φ) v) = ∑ᶠ q : LeftQuotient H, Ψ (Quotient.out q)
  rw [cosetSum_apply, map_finsum (evalAddHom H ρ.representation x)
    (hasFiniteSupport_cosetTerm H hH _ _ (heckeMap H ρ hH φ) v),
    ← finsum_leftQuotient_mul_inv H Ψ hl hr x]
  refine finsum_congr fun q => ?_
  conv_lhs => rw [← quotientMap_out H q]
  rw [cosetTerm_quotientMap]
  change (φ : G → Module.End ℂ ρ) (x * (Quotient.out q)⁻¹) (eval H ρ.representation v.1
    (Quotient.out q)) = (φ : G → Module.End ℂ ρ) (x * (Quotient.out q)⁻¹)
      (eval H ρ.representation v.1 ((x * (Quotient.out q)⁻¹)⁻¹ * x))
  rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]

/-- Every endomorphism is given by the inverse formula applied to its Hecke function. -/
theorem eval_hom_eq [ρ.representation.IsIrreducible] (α : End (inducedRep H ρ))
    (v : CompactFunctions H ρ.representation) (x : G) :
    eval H ρ.representation (SmoothRep.hom α v).1 x =
      ∑ᶠ q : LeftQuotient H, endValue H ρ hH α (Quotient.out q)
        (eval H ρ.representation v.1 ((Quotient.out q)⁻¹ * x)) := by
  conv_lhs => rw [← (heckeEquiv H ρ hH).symm_apply_apply α]
  exact eval_endOfHecke H ρ hH _ v x

/-- Renard VI.4.2: composition corresponds to convolution. -/
theorem heckeEquiv_mul [ρ.representation.IsIrreducible] (α β : End (inducedRep H ρ)) :
    (heckeEquiv H ρ hH (α * β) : G → Module.End ℂ ρ) =
      heckeConvolution H ρ (heckeEquiv H ρ hH α) (heckeEquiv H ρ hH β) := by
  funext x
  refine LinearMap.ext fun w => ?_
  let Φ : G → ρ := fun g => endValue H ρ hH α g (endValue H ρ hH β (g⁻¹ * x) w)
  have hΦ : ∀ (g : G) (h : H), Φ (g * h) = Φ g := by
    intro g h
    have h2 : (g * (h : G))⁻¹ * x = ((h⁻¹ : H) : G) * (g⁻¹ * x) := by
      change (g * (h : G))⁻¹ * x = (h : G)⁻¹ * (g⁻¹ * x)
      group
    simp only [Φ]
    rw [h2, endValue_mul_right', Module.End.mul_apply, endValue_mul_left, representation_mul_inv]
  let ev : Module.End ℂ ρ →+ ρ :=
    { toFun := fun T => T w, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hfin : Function.HasFiniteSupport (fun q : G ⧸ H =>
      endValue H ρ hH α q.out * endValue H ρ hH β (q.out⁻¹ * x)) := by
    refine (endValue_finite H ρ hH α).subset fun q hq => ⟨q.out, fun h0 => hq ?_, ?_⟩
    · change endValue H ρ hH α q.out * _ = 0
      rw [h0, zero_mul]
    · exact QuotientGroup.out_eq' q
  change eval H ρ.representation ((SmoothRep.hom α) ((SmoothRep.hom β)
      (unitFunction H hH ρ.representation ρ.isSmooth w))).1 x =
    ev (∑ᶠ q : G ⧸ H, endValue H ρ hH α q.out * endValue H ρ hH β (q.out⁻¹ * x))
  rw [eval_hom_eq H ρ hH α, map_finsum ev hfin]
  exact finsum_leftQuotient_eq H Φ hΦ

end Hecke

end Langlands.CuspidalSupport.NormalHecke
