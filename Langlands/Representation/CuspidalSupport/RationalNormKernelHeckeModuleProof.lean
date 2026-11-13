import Langlands.Representation.CuspidalSupport.RationalNormKernelHeckeModuleStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelHeckeProof

/-! Renard VI.4.2, after the Proposition: the right `H(G, ρ)`-module structures on
`Hom_{⁰G}(ρ, Res τ)` and `Hom_G(Π, τ)` and the compatibility of the adjunction with them.
The general part is written for an open normal subgroup `H` of a topological group, in the
setting of `NormalSubgroupHecke`; the final theorem specializes it to `⁰G`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport.NormalHecke

universe uG uV

open Induction

section RightModule

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) (hH : IsOpen (H : Set G))
variable (ρ : SmoothRep.{0, uG, uV} ℂ H) (τ : SmoothRep.{0, uG, max uG uV} ℂ G)

/-- Renard's right action of `H(G, ρ)` on `H`-maps `ψ : ρ → Res τ`:
`(ψ · φ)(w) = ∑_{g ∈ G/H} τ(g) ψ(φ(g⁻¹) w)`, summed over the chosen representatives. -/
def heckeRightAction
    (ψ : ρ.representation.IntertwiningMap (SmoothRep.restrictSubgroup H τ).representation)
    (φ : G → Module.End ℂ ρ) (w : ρ) : τ :=
  ∑ᶠ q : G ⧸ H, τ.representation q.out (ψ (φ q.out⁻¹ w))

/-- Every `G`-map out of `ind_H^G ρ` is the coset sum of its restriction to the unit
functions `f_w`. -/
theorem hom_eq_cosetSum_restrict (s : inducedRep H ρ ⟶ τ)
    (v : CompactFunctions H ρ.representation) :
    SmoothRep.hom s v = cosetSum H hH τ.representation ρ.representation
      ((resIntertwining H τ.representation (SmoothRep.hom s)).comp
        (unitMap H hH ρ.representation ρ.isSmooth)) v :=
  (congrArg (SmoothRep.hom s) (cosetSum_unitMap H hH ρ.representation ρ.isSmooth v)).symm.trans
    (cosetSum_resIntertwining_comp H hH _ ρ.representation (SmoothRep.hom s)
      (unitMap H hH ρ.representation ρ.isSmooth) v).symm

variable [hN : H.Normal]

/-- The coset sum of `OpenAdjunction` is the formula (VI.4.2.6):
`∑_{H x} τ(x⁻¹) ψ(v(x)) = ∑_{H g} τ(g) ψ(v(g⁻¹))`. -/
theorem cosetSum_eq_finsum_inv
    (ψ : ρ.representation.IntertwiningMap (SmoothRep.restrictSubgroup H τ).representation)
    (v : CompactFunctions H ρ.representation) :
    cosetSum H hH τ.representation ρ.representation ψ v =
      ∑ᶠ q : LeftQuotient H, τ.representation (Quotient.out q)
        (ψ (eval H ρ.representation v.1 (Quotient.out q)⁻¹)) := by
  let Ψ : G → τ := fun x => τ.representation x⁻¹ (ψ (eval H ρ.representation v.1 x))
  have hl : ∀ (h : H) (x : G), Ψ (h * x) = Ψ x := by
    intro h x
    change τ.representation ((h : G) * x)⁻¹ (ψ (eval H ρ.representation v.1 ((h : G) * x))) =
      τ.representation x⁻¹ (ψ (eval H ρ.representation v.1 x))
    rw [eval_mul_left H ρ v h x, ψ.isIntertwining]
    change τ.representation ((h : G) * x)⁻¹ (τ.representation (h : G) _) = _
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
  have hr : ∀ (x : G) (h : H), Ψ (x * h) = Ψ x := by
    intro x h
    let k : H := ⟨x * h * x⁻¹, hN.conj_mem _ h.2 x⟩
    have hk : x * (h : G) = (k : G) * x := by
      change x * (h : G) = x * h * x⁻¹ * x
      group
    change τ.representation (x * (h : G))⁻¹ (ψ (eval H ρ.representation v.1 (x * (h : G)))) =
      τ.representation x⁻¹ (ψ (eval H ρ.representation v.1 x))
    rw [hk, eval_mul_left H ρ v k x, ψ.isIntertwining]
    change τ.representation ((k : G) * x)⁻¹ (τ.representation (k : G) _) = _
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
  have h1 : ∀ q : LeftQuotient H, cosetTerm H τ.representation ρ.representation ψ v q =
      Ψ (Quotient.out q) := by
    intro q
    conv_lhs => rw [← quotientMap_out H q]
    rfl
  rw [cosetSum_apply, finsum_congr h1, ← finsum_leftQuotient_mul_inv H Ψ hl hr 1]
  refine finsum_congr fun q => ?_
  change τ.representation (1 * (Quotient.out q)⁻¹)⁻¹
      (ψ (eval H ρ.representation v.1 (1 * (Quotient.out q)⁻¹))) = _
  rw [one_mul, inv_inv]

/-- A `G`-map `s` out of `ind_H^G ρ` is given by (VI.4.2.6) in terms of `ψ_s : w ↦ s(f_w)`. -/
theorem hom_apply_eq_finsum (s : inducedRep H ρ ⟶ τ)
    (ψ : ρ.representation.IntertwiningMap (SmoothRep.restrictSubgroup H τ).representation)
    (hψ : ∀ w, ψ w = SmoothRep.hom s (unitFunction H hH ρ.representation ρ.isSmooth w))
    (v : CompactFunctions H ρ.representation) :
    SmoothRep.hom s v = ∑ᶠ q : LeftQuotient H, τ.representation (Quotient.out q)
        (ψ (eval H ρ.representation v.1 (Quotient.out q)⁻¹)) := by
  have hres : (resIntertwining H τ.representation (SmoothRep.hom s)).comp
      (unitMap H hH ρ.representation ρ.isSmooth) = ψ :=
    Representation.IntertwiningMap.ext (LinearMap.ext fun w => (hψ w).symm)
  rw [hom_eq_cosetSum_restrict H hH ρ τ s v, hres, cosetSum_eq_finsum_inv H hH ρ τ ψ v]

/-- The transported action `s ↦ α ≫ s` corresponds to the right action on `ψ_s`: if
`α(f_w)(g) = φ(g)(w)` for all `g, w`, then `(α ≫ s)(f_w) = (ψ_s · φ)(w)`. -/
theorem hom_comp_unitFunction (α : End (inducedRep H ρ)) (s : inducedRep H ρ ⟶ τ)
    (ψ : ρ.representation.IntertwiningMap (SmoothRep.restrictSubgroup H τ).representation)
    (hψ : ∀ w, ψ w = SmoothRep.hom s (unitFunction H hH ρ.representation ρ.isSmooth w))
    (φ : G → Module.End ℂ ρ)
    (hα : ∀ g w, eval H ρ.representation
      (SmoothRep.hom α (unitFunction H hH ρ.representation ρ.isSmooth w)).1 g = φ g w)
    (w : ρ) :
    SmoothRep.hom (α ≫ s) (unitFunction H hH ρ.representation ρ.isSmooth w) =
      heckeRightAction H ρ τ ψ φ w := by
  have hφ : ∀ (h : H) (g : G) (u : ρ), φ ((h : G) * g) u = ρ.representation h (φ g u) := by
    intro h g u
    rw [← hα, ← hα]
    exact eval_mul_left H ρ _ h g
  let Φ : G → τ := fun g => τ.representation g (ψ (φ g⁻¹ w))
  have hΦ : ∀ (g : G) (h : H), Φ (g * h) = Φ g := by
    intro g h
    change τ.representation (g * (h : G)) (ψ (φ (g * (h : G))⁻¹ w)) =
      τ.representation g (ψ (φ g⁻¹ w))
    rw [mul_inv_rev, show ((h : G))⁻¹ = ((h⁻¹ : H) : G) from rfl, hφ, ψ.isIntertwining]
    change τ.representation (g * (h : G)) (τ.representation ((h⁻¹ : H) : G) _) = _
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel_right]
  change SmoothRep.hom s (SmoothRep.hom α (unitFunction H hH ρ.representation ρ.isSmooth w)) =
    ∑ᶠ q : G ⧸ H, Φ q.out
  rw [hom_apply_eq_finsum H hH ρ τ s ψ hψ, ← finsum_leftQuotient_eq H Φ hΦ]
  refine finsum_congr fun q => ?_
  rw [hα]

include hH in
/-- Item 1: `ψ · φ` is again an `H`-map. -/
theorem exists_heckeRightAction
    (ψ : ρ.representation.IntertwiningMap (SmoothRep.restrictSubgroup H τ).representation)
    (φ : heckeSubmodule H ρ) :
    ∃ ψ' : ρ.representation.IntertwiningMap (SmoothRep.restrictSubgroup H τ).representation,
      ∀ w, ψ' w = heckeRightAction H ρ τ ψ φ w := by
  let s₀ : inducedRep H ρ ⟶ τ :=
    SmoothRep.ofHom (cosetSum H hH τ.representation ρ.representation ψ)
  have hψ : ∀ w, ψ w = SmoothRep.hom s₀ (unitFunction H hH ρ.representation ρ.isSmooth w) :=
    fun w => (cosetSum_comp_unitMap H hH τ.representation ρ.representation ρ.isSmooth ψ w).symm
  refine ⟨(resIntertwining H τ.representation
    (SmoothRep.hom (endOfHecke H ρ hH φ ≫ s₀))).comp (unitMap H hH ρ.representation ρ.isSmooth),
    fun w => ?_⟩
  exact hom_comp_unitFunction H hH ρ τ (endOfHecke H ρ hH φ) s₀ ψ hψ φ
    (fun g u => endValue_endOfHecke H ρ hH φ g u) w

include hH in
/-- Item 2: associativity, `(ψ · φ) · φ' = ψ · (φ ∗ φ')`. -/
theorem heckeRightAction_heckeRightAction [ρ.representation.IsIrreducible]
    (ψ ψ' : ρ.representation.IntertwiningMap (SmoothRep.restrictSubgroup H τ).representation)
    (φ φ' : heckeSubmodule H ρ) (hψ' : ∀ w, ψ' w = heckeRightAction H ρ τ ψ φ w) (w : ρ) :
    heckeRightAction H ρ τ ψ' φ' w =
      heckeRightAction H ρ τ ψ (heckeConvolution H ρ φ φ') w := by
  let s₀ : inducedRep H ρ ⟶ τ :=
    SmoothRep.ofHom (cosetSum H hH τ.representation ρ.representation ψ)
  have hψ : ∀ w, ψ w = SmoothRep.hom s₀ (unitFunction H hH ρ.representation ρ.isSmooth w) :=
    fun w => (cosetSum_comp_unitMap H hH τ.representation ρ.representation ρ.isSmooth ψ w).symm
  obtain ⟨α, rfl⟩ := (heckeEquiv H ρ hH).surjective φ
  obtain ⟨β, rfl⟩ := (heckeEquiv H ρ hH).surjective φ'
  have hψ₁ : ∀ u, ψ' u = SmoothRep.hom (α ≫ s₀)
      (unitFunction H hH ρ.representation ρ.isSmooth u) := fun u =>
    (hψ' u).trans (hom_comp_unitFunction H hH ρ τ α s₀ ψ hψ
      (heckeEquiv H ρ hH α : G → Module.End ℂ ρ)
      (fun g u => (heckeEquiv_apply H ρ hH α g u).symm) u).symm
  rw [← heckeEquiv_mul H ρ hH α β,
    ← hom_comp_unitFunction H hH ρ τ β (α ≫ s₀) ψ' hψ₁
      (heckeEquiv H ρ hH β : G → Module.End ℂ ρ)
      (fun g u => (heckeEquiv_apply H ρ hH β g u).symm) w,
    ← hom_comp_unitFunction H hH ρ τ (α * β) s₀ ψ hψ
      (heckeEquiv H ρ hH (α * β) : G → Module.End ℂ ρ)
      (fun g u => (heckeEquiv_apply H ρ hH (α * β) g u).symm) w,
    End.mul_def, Category.assoc]

omit [IsTopologicalGroup G] in
/-- Item 2, unit: the unit `φ_e` of `H(G, ρ)` acts trivially. -/
theorem heckeRightAction_unit
    (ψ : ρ.representation.IntertwiningMap (SmoothRep.restrictSubgroup H τ).representation)
    (φe : G → Module.End ℂ ρ) (h1 : ∀ h : H, φe h = ρ.representation h)
    (h0 : ∀ g : G, g ∉ H → φe g = 0) (w : ρ) :
    heckeRightAction H ρ τ ψ φe w = ψ w := by
  unfold heckeRightAction
  rw [finsum_eq_single _ (1 : G ⧸ H)]
  · have hmem : ((1 : G ⧸ H).out : G) ∈ H :=
      (QuotientGroup.eq_one_iff _).mp (QuotientGroup.out_eq' 1)
    have hinv : ((1 : G ⧸ H).out)⁻¹ ∈ H := H.inv_mem hmem
    rw [show ((1 : G ⧸ H).out)⁻¹ = ((⟨_, hinv⟩ : H) : G) from rfl, h1, ψ.isIntertwining]
    change τ.representation (1 : G ⧸ H).out (τ.representation ((1 : G ⧸ H).out)⁻¹ (ψ w)) = ψ w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · intro q hq
    have hq' : (q.out)⁻¹ ∉ H := by
      intro hm
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact (QuotientGroup.eq_one_iff _).mpr (by simpa using H.inv_mem hm)
    rw [h0 _ hq', LinearMap.zero_apply, map_zero]
    exact map_zero (τ.representation q.out)

/-- Items 3–4: the adjunction map `s ↦ ψ_s` is bijective, with inverse (VI.4.2.6). -/
theorem existsUnique_hom_unitFunction
    (ψ : ρ.representation.IntertwiningMap (SmoothRep.restrictSubgroup H τ).representation) :
    ∃! s : inducedRep H ρ ⟶ τ,
      (∀ w, SmoothRep.hom s (unitFunction H hH ρ.representation ρ.isSmooth w) = ψ w) ∧
      ∀ v : inducedRep H ρ, SmoothRep.hom s v =
        ∑ᶠ q : LeftQuotient H, τ.representation q.out
          (ψ (eval H ρ.representation v.1 q.out⁻¹)) := by
  refine ⟨SmoothRep.ofHom (cosetSum H hH τ.representation ρ.representation ψ),
    ⟨fun w => cosetSum_comp_unitMap H hH τ.representation ρ.representation ρ.isSmooth ψ w,
      fun v => cosetSum_eq_finsum_inv H hH ρ τ ψ v⟩, ?_⟩
  rintro s ⟨hs, -⟩
  rw [← SmoothRep.ofHom_hom s]
  congr 1
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => ?_)
  exact (hom_apply_eq_finsum H hH ρ τ s ψ (fun w => (hs w).symm) v).trans
    (cosetSum_eq_finsum_inv H hH ρ τ ψ v).symm

end RightModule

end Langlands.CuspidalSupport.NormalHecke

open AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open GroupScheme Induction

/-- Renard VI.4.2, the paragraphs after the Proposition: the right `H(G, ρ)`-module
structures and the `H(G, ρ)`-linearity of the adjunction (VI.4.2.5)–(VI.4.2.6). -/
theorem rationalNormKernelHeckeModule : RationalNormKernelHeckeModuleStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  intro ρ hρ I f τ Rτ act
  have : ρ.representation.IsIrreducible := hρ
  have hH := isOpen_rationalCommonNormKernel G
  refine ⟨fun ψ φ => NormalHecke.exists_heckeRightAction _ hH ρ τ ψ φ,
    fun ψ ψ' φ φ' hψ' w =>
      NormalHecke.heckeRightAction_heckeRightAction _ hH ρ τ ψ ψ' φ φ' hψ' w,
    fun ψ φe h1 h0 w => NormalHecke.heckeRightAction_unit _ ρ τ ψ φe h1 h0 w,
    fun e he s φ ψ hψ w => ?_,
    fun ψ => NormalHecke.existsUnique_hom_unitFunction _ hH ρ τ ψ⟩
  exact NormalHecke.hom_comp_unitFunction _ hH ρ τ (e.symm φ) s ψ hψ
    (φ : GroupScheme.rationalPoints G → Module.End ℂ ρ)
    (fun g u => (he (e.symm φ) g u).symm.trans
      (congrArg (fun T : rationalNormKernelHecke G ρ =>
        (T : GroupScheme.rationalPoints G → Module.End ℂ ρ) g u) (e.apply_symm_apply φ))) w

end Langlands.CuspidalSupport
