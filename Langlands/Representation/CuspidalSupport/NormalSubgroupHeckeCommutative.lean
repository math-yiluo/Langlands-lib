import Langlands.Representation.CuspidalSupport.NormalSubgroupHeckeSeparation
import Langlands.Algebra.SchurProof

/-!
# Commutativity of the Hecke algebra of an open normal subgroup

Let `H` be an open normal subgroup of a topological group `G`, `ρ` an irreducible smooth complex
representation of `H`, `I = ind_H^G ρ` and `R = End I`. Let `π` be a complex representation
of `G` and `j : ρ → Res_H π` a nonzero `H`-equivariant map.

* If `R` is commutative, `π` is irreducible, `G ⧸ H` is countable and `ρ` has countable
  dimension, then `Hom_H(σ, Res_H π)` has dimension at most one for every irreducible `σ`
  (`rank_le_one_of_commute`).
* If `Hom_H(ρ, Res_H π)` has dimension at most one, `j` is injective and the characters of
  `G ⧸ H` separate its points, then `R` is commutative (`commute_of_rank_le_one`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped MonoidAlgebra

namespace Langlands.CuspidalSupport.NormalHecke

universe uG uV uW uX uK

open Induction

section Irreducible

variable {K : Type uK} [Group K] {K' : Type*} [Group K'] {X : Type uX} [AddCommGroup X]
  [Module ℂ X]

/-- Precomposition with a surjective homomorphism preserves irreducibility. -/
theorem isIrreducible_comp (σ : Representation ℂ K' X) [σ.IsIrreducible] (c : K →* K')
    (hc : Function.Surjective c) : Representation.IsIrreducible (σ.comp c) := by
  let e : Subrepresentation (σ.comp c) ≃o Subrepresentation σ :=
    { toFun := fun W => ⟨W.toSubmodule, fun k v hv => by
        obtain ⟨k', rfl⟩ := hc k
        exact W.apply_mem_toSubmodule k' hv⟩
      invFun := fun W => ⟨W.toSubmodule, fun k v hv => W.apply_mem_toSubmodule (c k) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder_iff.mpr inferInstance

end Irreducible

section Characters

variable {V : Type uW} [AddCommGroup V] [Module ℂ V]

/-- Dedekind's independence of characters, with vector coefficients: if the characters of `Q`
separate its points and `∑ᶠ i, ω (e i) • t i = 0` for every character `ω`, where `e` is
injective and `t` has finite support, then `t = 0`. -/
theorem eq_zero_of_forall_character {Q : Type*} [Group Q]
    (hsep : ∀ q : Q, q ≠ 1 → ∃ ω : Q →* ℂˣ, ω q ≠ 1) {ι : Type*} (e : ι → Q)
    (he : Function.Injective e) (t : ι → V) (ht : (Function.support t).Finite)
    (h : ∀ ω : Q →* ℂˣ, ∑ᶠ i, ((ω (e i) : ℂˣ) : ℂ) • t i = 0) : t = 0 := by
  let ev : ι → ((Q →* ℂˣ) →* ℂ) := fun i =>
    { toFun := fun ω => ((ω (e i) : ℂˣ) : ℂ)
      map_one' := by simp
      map_mul' := fun a b => by simp }
  have hev : Function.Injective ev := by
    intro i i' hii'
    by_contra hne
    obtain ⟨ω, hω⟩ := hsep (e i * (e i')⁻¹) fun h1 => hne (he (mul_inv_eq_one.mp h1))
    apply hω
    have h2 : ω (e i) = ω (e i') := Units.ext (DFunLike.congr_fun hii' ω)
    rw [map_mul, map_inv, h2, mul_inv_cancel]
  have hli : LinearIndependent ℂ (fun i => (ev i : (Q →* ℂˣ) → ℂ)) :=
    (linearIndependent_monoidHom (Q →* ℂˣ) ℂ).comp ev hev
  funext i
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (t i)).mp fun l => ?_
  let s := ht.toFinset
  have key : ∑ k ∈ s, l (t k) • (ev k : (Q →* ℂˣ) → ℂ) = 0 := by
    funext ω
    have h1 := congrArg l (h ω)
    rw [map_zero, finsum_eq_sum_of_support_subset _ (s := s), map_sum] at h1
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h1
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl
    · intro k hk
      rw [Set.Finite.coe_toFinset]
      exact Function.support_smul_subset_right _ _ hk
  by_cases his : i ∈ s
  · exact linearIndependent_iff'.mp hli s (fun k => l (t k)) key i his
  · have : t i = 0 := by simpa [s] using his
    rw [this, map_zero]

/-- The twist `g ↦ ω(g) π(g)` of a representation by a character. -/
def twist {G : Type uG} [Group G] (ω : G →* ℂˣ) (π : Representation ℂ G V) :
    Representation ℂ G V where
  toFun g := ((ω g : ℂˣ) : ℂ) • π g
  map_one' := by simp
  map_mul' g g' := by rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

theorem twist_apply {G : Type uG} [Group G] (ω : G →* ℂˣ) (π : Representation ℂ G V) (g : G)
    (v : V) : twist ω π g v = ((ω g : ℂˣ) : ℂ) • π g v :=
  rfl

/-- For a character trivial on `H`, the restrictions of `π` and its twist have the same
equivariant maps. -/
def twistRes {G : Type uG} [Group G] {H : Subgroup G} (ω : G →* ℂˣ) (hω : ∀ h : H, ω h = 1)
    (π : Representation ℂ G V) {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ H X) :
    σ.IntertwiningMap ((twist ω π).comp H.subtype) ≃ₗ[ℂ]
      σ.IntertwiningMap (π.comp H.subtype) where
  toFun S := ⟨S.toLinearMap, fun h => LinearMap.ext fun v => by
    change S (σ h v) = π h (S v)
    rw [S.isIntertwining _ _ h v]
    change ((ω h : ℂˣ) : ℂ) • π h (S v) = π h (S v)
    rw [hω h, Units.val_one, one_smul]⟩
  invFun S := ⟨S.toLinearMap, fun h => LinearMap.ext fun v => by
    change S (σ h v) = ((ω h : ℂˣ) : ℂ) • π h (S v)
    rw [S.isIntertwining _ _ h v, hω h, Units.val_one, one_smul]
    rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end Characters

section Rank

/-- Linearly equivalent spaces have dimension at most one simultaneously. -/
theorem rank_le_one_iff_of_equiv {M : Type uV} {M' : Type uW} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup M'] [Module ℂ M'] (e : M ≃ₗ[ℂ] M') :
    Module.rank ℂ M ≤ 1 ↔ Module.rank ℂ M' ≤ 1 := by
  have h := e.lift_rank_eq
  constructor <;> intro h'
  · apply Cardinal.lift_le_one_iff.{uW, uV}.mp
    rw [← h]
    exact Cardinal.lift_le_one_iff.mpr h'
  · apply Cardinal.lift_le_one_iff.{uV, uW}.mp
    rw [h]
    exact Cardinal.lift_le_one_iff.mpr h'

/-- Morphisms of smooth representations are the same as equivariant linear maps, linearly. -/
def homLinearEquiv {K : Type uK} [Group K] [TopologicalSpace K]
    (A B : SmoothRep.{0, uK, uV} ℂ K) :
    (A ⟶ B) ≃ₗ[ℂ] A.representation.IntertwiningMap B.representation where
  toFun := SmoothRep.hom
  invFun := SmoothRep.ofHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end Rank

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) (ρ : SmoothRep.{0, uG, uV} ℂ H)
variable {V : Type uW} [AddCommGroup V] [Module ℂ V]

section Frobenius

variable (hH : IsOpen (H : Set G))

/-- Frobenius reciprocity for compact induction from the open subgroup `H`, as a linear
equivalence `Hom_G(ind_H^G ρ, τ) ≃ Hom_H(ρ, Res_H τ)`: `T ↦ T ∘ (w ↦ f_w)`, with inverse
the coset sum `f ↦ ∑_{H x} τ(x⁻¹) φ(f(x))`. -/
def frobenius (τ : Representation ℂ G V) :
    (inducedRep H ρ).representation.IntertwiningMap τ ≃ₗ[ℂ]
      ρ.representation.IntertwiningMap (τ.comp H.subtype) where
  toFun T := (resIntertwining H τ T).comp (unitMap H hH ρ.representation ρ.isSmooth)
  invFun φ := cosetSum H hH τ ρ.representation φ
  map_add' _ _ := Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  left_inv T := Representation.IntertwiningMap.ext (LinearMap.ext fun f =>
    (cosetSum_resIntertwining_comp H hH τ ρ.representation T
      (unitMap H hH ρ.representation ρ.isSmooth) f).trans
      (congrArg T (cosetSum_unitMap H hH ρ.representation ρ.isSmooth f)))
  right_inv φ := Representation.IntertwiningMap.ext (LinearMap.ext fun w =>
    cosetSum_comp_unitMap H hH τ ρ.representation ρ.isSmooth φ w)

end Frobenius

section RightModule

variable (τ : Representation ℂ G V)

/-- The right action of `End (ind_H^G ρ)` on `Hom_G(ind_H^G ρ, τ)` by precomposition. -/
def rightAction :
    (End (inducedRep H ρ))ᵐᵒᵖ →+*
      Module.End ℂ ((inducedRep H ρ).representation.IntertwiningMap τ) where
  toFun β :=
    { toFun := fun T => T.comp (SmoothRep.hom β.unop)
      map_add' := fun _ _ => Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
      map_smul' := fun _ _ => Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl) }
  map_one' := LinearMap.ext fun _ => Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ :=
    LinearMap.ext fun _ => Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  map_zero' := LinearMap.ext fun T => Representation.IntertwiningMap.ext (LinearMap.ext fun _ =>
    map_zero T)
  map_add' _ _ := LinearMap.ext fun T => Representation.IntertwiningMap.ext (LinearMap.ext fun _ =>
    map_add T _ _)

/-- `Hom_G(ind_H^G ρ, τ)` as a module over `End (ind_H^G ρ)ᵐᵒᵖ`. -/
abbrev rightModule : Module (End (inducedRep H ρ))ᵐᵒᵖ
    ((inducedRep H ρ).representation.IntertwiningMap τ) :=
  Module.compHom _ (rightAction H ρ τ)

attribute [local instance] rightModule

theorem op_smul_eq_comp (β : End (inducedRep H ρ))
    (T : (inducedRep H ρ).representation.IntertwiningMap τ) :
    MulOpposite.op β • T = T.comp (SmoothRep.hom β) :=
  rfl

instance rightModule_isScalarTower :
    IsScalarTower ℂ (End (inducedRep H ρ))ᵐᵒᵖ
      ((inducedRep H ρ).representation.IntertwiningMap τ) :=
  ⟨fun c _ T => Representation.IntertwiningMap.ext (LinearMap.ext fun _ => map_smul T c _)⟩

end RightModule

section Semisimple

variable [hN : H.Normal]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Conjugation `h ↦ x h x⁻¹` of the normal subgroup `H`. -/
def conjHom (x : G) : H →* H where
  toFun h := ⟨x * h * x⁻¹, hN.conj_mem _ h.2 x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change x * ((a * b : H) : G) * x⁻¹ = x * (a : G) * x⁻¹ * (x * (b : G) * x⁻¹)
    rw [Subgroup.coe_mul]
    group)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem conjHom_apply (x : G) (h : H) : (conjHom H x h : G) = x * h * x⁻¹ :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem conjHom_surjective (x : G) : Function.Surjective (conjHom H x) := fun h =>
  ⟨conjHom H x⁻¹ h, Subtype.ext (by
    change x * (x⁻¹ * (h : G) * x⁻¹⁻¹) * x⁻¹ = h
    group)⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A nonzero equivariant map to an irreducible representation is surjective. -/
theorem surjective_of_ne_zero {X : Type uX} [AddCommGroup X] [Module ℂ X]
    {σ : Representation ℂ G X} (π : Representation ℂ G V) [π.IsIrreducible]
    (T : σ.IntertwiningMap π) (hT : T ≠ 0) : Function.Surjective T :=
  (Representation.IsIrreducible.surjective_or_eq_zero T).resolve_right hT

variable (hH : IsOpen (H : Set G))

theorem translate_unitFunction (x : G) (h : H) (w : ρ) :
    compactInduced H ρ.representation x⁻¹
        (unitFunction H hH ρ.representation ρ.isSmooth (ρ.representation (conjHom H x h) w)) =
      compactInduced H ρ.representation h (compactInduced H ρ.representation x⁻¹
        (unitFunction H hH ρ.representation ρ.isSmooth w)) := by
  have hu : unitFunction H hH ρ.representation ρ.isSmooth (ρ.representation (conjHom H x h) w) =
      compactInduced H ρ.representation (x * h * x⁻¹)
        (unitFunction H hH ρ.representation ρ.isSmooth w) :=
    (unitMap H hH ρ.representation ρ.isSmooth).isIntertwining _ _ (conjHom H x h) w
  have hmul : ∀ (a b : G) (f : CompactFunctions H ρ.representation),
      compactInduced H ρ.representation a (compactInduced H ρ.representation b f) =
        compactInduced H ρ.representation (a * b) f := fun a b f => by
    rw [map_mul, Module.End.mul_apply]
  rw [hu, hmul, hmul, show x⁻¹ * (x * (h : G) * x⁻¹) = h * x⁻¹ by group]

/-- `w ↦ x⁻¹ · f_w`, the function supported on `H x` with value `w` at `x`: an `H`-equivariant
map from the conjugate `ρ ∘ conjHom x` to the restriction of `ind_H^G ρ`. -/
def translateMap (x : G) :
    Representation.IntertwiningMap (ρ.representation.comp (conjHom H x))
      ((inducedRep H ρ).representation.comp H.subtype) where
  toLinearMap := (compactInduced H ρ.representation x⁻¹) ∘ₗ
    (unitMap H hH ρ.representation ρ.isSmooth).toLinearMap
  isIntertwining' h := LinearMap.ext fun w => translate_unitFunction H ρ hH x h w

theorem eval_translateMap_self (x : G) (w : ρ) :
    eval H ρ.representation (translateMap H ρ hH x w).1 x = w := by
  change eval H ρ.representation (unitFunction H hH ρ.representation ρ.isSmooth w).1
    (x * x⁻¹) = w
  rw [mul_inv_cancel, eval_unitFunction_one]

theorem translateMap_injective (x : G) : Function.Injective (translateMap H ρ hH x) :=
  fun a b hab => by
    rw [← eval_translateMap_self H ρ hH x a, hab, eval_translateMap_self]

include hH

/-- The restriction of `ind_H^G ρ` to `H` is a semisimple `ℂ[H]`-module: it is the sum of the
simple submodules of functions supported on single cosets. -/
theorem isSemisimpleModule_res [ρ.representation.IsIrreducible] :
    IsSemisimpleModule ℂ[H]
      (Representation.asModule ((inducedRep H ρ).representation.comp H.subtype)) := by
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun x => LinearMap.range
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (translateMap H ρ hH x)))
    (fun x => ?_) ?_
  · have : Representation.IsIrreducible (ρ.representation.comp (conjHom H x)) :=
      isIrreducible_comp _ _ (conjHom_surjective H x)
    have : IsSimpleModule ℂ[H]
        (Representation.asModule (ρ.representation.comp (conjHom H x))) :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).mp inferInstance
    have := IsSimpleModule.congr (LinearEquiv.ofInjective
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (translateMap H ρ hH x))
      (translateMap_injective H ρ hH x)).symm
    infer_instance
  · refine eq_top_iff.mpr fun F _ => ?_
    let F' : CompactFunctions H ρ.representation := F
    have hF : cosetSum H hH (compactInduced H ρ.representation) ρ.representation
        (unitMap H hH ρ.representation ρ.isSmooth) F' = F' :=
      cosetSum_unitMap H hH ρ.representation ρ.isSmooth F'
    change F' ∈ ⨆ x, LinearMap.range
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (translateMap H ρ hH x))
    rw [← hF, cosetSum_apply]
    refine finsum_induction (fun y => y ∈ ⨆ x, LinearMap.range
        (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (translateMap H ρ hH x)))
      (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) fun q => ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    exact Submodule.mem_iSup_of_mem x
      (LinearMap.mem_range.mpr ⟨eval H ρ.representation F'.1 x, rfl⟩)

/-- Equivariant maps into `Res_H π` lift through a surjective `G`-map `ind_H^G ρ → π`. -/
theorem exists_lift [ρ.representation.IsIrreducible] (π : Representation ℂ G V)
    {X : Type uX} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ H X)
    (T : (inducedRep H ρ).representation.IntertwiningMap π) (hT : Function.Surjective T)
    (S : σ.IntertwiningMap (π.comp H.subtype)) :
    ∃ ψ : σ.IntertwiningMap ((inducedRep H ρ).representation.comp H.subtype),
      (resIntertwining H π T).comp ψ = S := by
  have := isSemisimpleModule_res H ρ hH
  obtain ⟨h, hh⟩ := IsSemisimpleModule.lifting_property
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (resIntertwining H π T)) hT
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ S)
  refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm h, ?_⟩
  exact Representation.IntertwiningMap.ext (LinearMap.ext fun v => LinearMap.congr_fun hh v)

/-- For a surjective `T : ind_H^G ρ → π`, every `T'` is `T ∘ β` for some `β ∈ End (ind_H^G ρ)`. -/
theorem exists_end_comp_eq [ρ.representation.IsIrreducible] (π : Representation ℂ G V)
    (T T' : (inducedRep H ρ).representation.IntertwiningMap π)
    (hT : Function.Surjective T) :
    ∃ β : End (inducedRep H ρ), T.comp (SmoothRep.hom β) = T' := by
  obtain ⟨ψ, hψ⟩ := exists_lift H ρ hH π ρ.representation T hT (frobenius H ρ hH π T')
  refine ⟨SmoothRep.ofHom ((frobenius H ρ hH (inducedRep H ρ).representation).symm ψ), ?_⟩
  apply (frobenius H ρ hH π).injective
  rw [← hψ]
  refine Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)
  change T (cosetSum H hH (inducedRep H ρ).representation ρ.representation ψ
    (unitMap H hH ρ.representation ρ.isSmooth w)) = T (ψ w)
  rw [cosetSum_comp_unitMap]

end Semisimple

section Forward

variable [hN : H.Normal] (hH : IsOpen (H : Set G))
include hH

attribute [local instance] rightModule

/-- If `End (ind_H^G ρ)` is commutative, `Hom_H(ρ, Res_H π)` has dimension at most one. -/
theorem rank_le_one_of_commute' [ρ.representation.IsIrreducible] [Countable (G ⧸ H)]
    (hρ : Module.rank ℂ ρ ≤ Cardinal.aleph0) (π : Representation ℂ G V) [π.IsIrreducible]
    (hcomm : ∀ α β : End (inducedRep H ρ), α * β = β * α)
    (j : ρ.representation.IntertwiningMap (π.comp H.subtype)) (hj : j ≠ 0) :
    Module.rank ℂ (ρ.representation.IntertwiningMap (π.comp H.subtype)) ≤ 1 := by
  rw [← rank_le_one_iff_of_equiv (frobenius H ρ hH π)]
  set T₀ := (frobenius H ρ hH π).symm j with hT₀def
  have hT₀ : T₀ ≠ 0 := fun h0 => hj (by rwa [LinearEquiv.map_eq_zero_iff] at h0)
  have htrans : ∀ T T' : (inducedRep H ρ).representation.IntertwiningMap π, T ≠ 0 →
      ∃ a : (End (inducedRep H ρ))ᵐᵒᵖ, a • T = T' := fun T T' hT => by
    obtain ⟨β, hβ⟩ := exists_end_comp_eq H ρ hH π T T' (surjective_of_ne_zero π T hT)
    exact ⟨MulOpposite.op β, hβ⟩
  have hsimple : IsSimpleModule (End (inducedRep H ρ))ᵐᵒᵖ
      ((inducedRep H ρ).representation.IntertwiningMap π) :=
    isSimpleModule_iff_toSpanSingleton_surjective.mpr
      ⟨⟨T₀, 0, hT₀⟩, fun T hT T' => htrans T T' hT⟩
  have hrank : Module.rank ℂ (End (inducedRep H ρ))ᵐᵒᵖ ≤ Cardinal.aleph0 := by
    rw [← (MulOpposite.opLinearEquiv ℂ).rank_eq]
    exact rank_end_le H ρ hH hρ
  have hbij := Langlands.Renard.schurScalarOfAlgebraRankCountable _
    ((inducedRep H ρ).representation.IntertwiningMap π) hsimple hrank
  have hcomm' : ∀ a b : (End (inducedRep H ρ))ᵐᵒᵖ, a * b = b * a := fun a b =>
    MulOpposite.unop_injective (by
      rw [MulOpposite.unop_mul, MulOpposite.unop_mul]
      exact hcomm _ _)
  have hscalar : ∀ a : (End (inducedRep H ρ))ᵐᵒᵖ, ∃ c : ℂ,
      ∀ T : (inducedRep H ρ).representation.IntertwiningMap π, a • T = c • T := by
    intro a
    let φ : Module.End (End (inducedRep H ρ))ᵐᵒᵖ
        ((inducedRep H ρ).representation.IntertwiningMap π) :=
      { toFun := fun T => a • T
        map_add' := smul_add a
        map_smul' := fun b T => by
          rw [RingHom.id_apply, ← mul_smul, ← mul_smul, hcomm' a b] }
    obtain ⟨c, hc⟩ := hbij.2 φ
    exact ⟨c, fun T => (LinearMap.congr_fun hc T).symm⟩
  rw [rank_le_one_iff]
  refine ⟨T₀, fun T => ?_⟩
  obtain ⟨a, ha⟩ := htrans T₀ T hT₀
  obtain ⟨c, hc⟩ := hscalar a
  exact ⟨c, by rw [← hc, ha]⟩

/-- Given a nonzero `j : ρ → Res_H π`, if `Hom_H(ρ, Res_H π)` has dimension at most one then
so has `Hom_H(σ, Res_H π)` for every irreducible `σ`: a nonzero `S : σ → Res_H π` lifts to
`ind_H^G ρ`, and evaluating the lift at a suitable point identifies `σ` with a conjugate of `ρ`. -/
theorem rank_le_one_of_ne_zero [ρ.representation.IsIrreducible] (π : Representation ℂ G V)
    [π.IsIrreducible] (j : ρ.representation.IntertwiningMap (π.comp H.subtype)) (hj : j ≠ 0)
    (hρπ : Module.rank ℂ (ρ.representation.IntertwiningMap (π.comp H.subtype)) ≤ 1)
    {X : Type uX} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ H X) [σ.IsIrreducible] :
    Module.rank ℂ (σ.IntertwiningMap (π.comp H.subtype)) ≤ 1 := by
  by_cases hS : ∀ S : σ.IntertwiningMap (π.comp H.subtype), S = 0
  · have : Subsingleton (σ.IntertwiningMap (π.comp H.subtype)) :=
      ⟨fun a b => (hS a).trans (hS b).symm⟩
    rw [rank_subsingleton']
    exact zero_le_one
  push Not at hS
  obtain ⟨S, hS0⟩ := hS
  set T := (frobenius H ρ hH π).symm j
  have hT : T ≠ 0 := fun h0 => hj (by rwa [LinearEquiv.map_eq_zero_iff] at h0)
  obtain ⟨ψ, hψ⟩ := exists_lift H ρ hH π σ T (surjective_of_ne_zero π T hT) S
  obtain ⟨v, hv⟩ : ∃ v, ψ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hS0
    rw [← hψ]
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun u => ?_)
    change T (ψ u) = 0
    rw [h u, map_zero]
  obtain ⟨x, hx⟩ : ∃ x, eval H ρ.representation (ψ v).1 x ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (compactFunctions_ext H _ h)
  let ε : σ.IntertwiningMap (ρ.representation.comp (conjHom H x)) :=
    { toLinearMap := (evalLinear H ρ x) ∘ₗ ψ.toLinearMap
      isIntertwining' := fun h => LinearMap.ext fun u => by
        change eval H ρ.representation (ψ (σ h u)).1 x =
          ρ.representation (conjHom H x h) (eval H ρ.representation (ψ u).1 x)
        rw [ψ.isIntertwining _ _ h u]
        change eval H ρ.representation (ψ u).1 (x * h) = _
        rw [← eval_mul_left]
        congr 1
        change x * (h : G) = x * h * x⁻¹ * x
        group }
  have : Representation.IsIrreducible (ρ.representation.comp (conjHom H x)) :=
    isIrreducible_comp _ _ (conjHom_surjective H x)
  have hε : Function.Bijective ε :=
    (Representation.IsIrreducible.bijective_or_eq_zero ε).resolve_right fun h0 => hx (by
      change ε v = 0
      rw [h0]
      rfl)
  let e := LinearEquiv.ofBijective ε.toLinearMap hε
  have he : ∀ (h : H) (w : ρ), e.symm (ρ.representation (conjHom H x h) w) =
      σ h (e.symm w) := by
    intro h w
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    change _ = ε (σ h (e.symm w))
    rw [ε.isIntertwining _ _ h (e.symm w)]
    change _ = ρ.representation (conjHom H x h) (e (e.symm w))
    rw [LinearEquiv.apply_symm_apply]
  let Φ : σ.IntertwiningMap (π.comp H.subtype) →ₗ[ℂ]
      ρ.representation.IntertwiningMap (π.comp H.subtype) :=
    { toFun := fun S' =>
        { toLinearMap := π x ∘ₗ S'.toLinearMap ∘ₗ e.symm.toLinearMap
          isIntertwining' := fun m => LinearMap.ext fun w => by
            have h1 : conjHom H x (conjHom H x⁻¹ m) = m := Subtype.ext (by
              change x * (x⁻¹ * (m : G) * x⁻¹⁻¹) * x⁻¹ = m
              group)
            change π x (S' (e.symm (ρ.representation m w))) = π m (π x (S' (e.symm w)))
            conv_lhs => rw [← h1]
            rw [he, S'.isIntertwining _ _ _ (e.symm w)]
            change π x (π ((conjHom H x⁻¹ m : H) : G) _) = _
            rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
            congr 2
            change x * (x⁻¹ * (m : G) * x⁻¹⁻¹) = m * x
            group }
      map_add' := fun S₁ S₂ => Representation.IntertwiningMap.ext (LinearMap.ext fun w =>
        show π x ((S₁ + S₂) (e.symm w)) = π x (S₁ (e.symm w)) + π x (S₂ (e.symm w)) from
          map_add (π x) _ _)
      map_smul' := fun c S₁ => Representation.IntertwiningMap.ext (LinearMap.ext fun w =>
        show π x ((c • S₁) (e.symm w)) = c • π x (S₁ (e.symm w)) from map_smul (π x) _ _) }
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro S' hS'
    refine Representation.IntertwiningMap.ext (LinearMap.ext fun u => ?_)
    have h1 := LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap hS') (e u)
    change π x (S' (e.symm (e u))) = 0 at h1
    rw [LinearEquiv.symm_apply_apply] at h1
    change S' u = 0
    rw [← Representation.inv_self_apply π x (S' u), h1, map_zero]
  have h2 := LinearMap.lift_rank_le_of_injective Φ hΦ
  exact Cardinal.lift_le_one_iff.mp (h2.trans (Cardinal.lift_le_one_iff.mpr hρπ))

/-- If `End (ind_H^G ρ)` is commutative, then `Hom_H(σ, Res_H π)` has dimension at most one
for every irreducible `σ`. -/
theorem rank_le_one_of_commute [ρ.representation.IsIrreducible] [Countable (G ⧸ H)]
    (hρ : Module.rank ℂ ρ ≤ Cardinal.aleph0) (π : Representation ℂ G V) [π.IsIrreducible]
    (hcomm : ∀ α β : End (inducedRep H ρ), α * β = β * α)
    (j : ρ.representation.IntertwiningMap (π.comp H.subtype)) (hj : j ≠ 0)
    {X : Type uX} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ H X) [σ.IsIrreducible] :
    Module.rank ℂ (σ.IntertwiningMap (π.comp H.subtype)) ≤ 1 :=
  rank_le_one_of_ne_zero H ρ hH π j hj (rank_le_one_of_commute' H ρ hH hρ π hcomm j hj) σ

end Forward

section Backward

theorem cosetTerm_twist (ω : G →* ℂˣ) (hω : ∀ h : H, ω h = 1) (π : Representation ℂ G V)
    (φ : ρ.representation.IntertwiningMap (π.comp H.subtype))
    (f : CompactFunctions H ρ.representation) (x : G) :
    cosetTerm H (twist ω π) ρ.representation ((twistRes ω hω π ρ.representation).symm φ) f
        (quotientMap H x) =
      (((ω x)⁻¹ : ℂˣ) : ℂ) • cosetTerm H π ρ.representation φ f (quotientMap H x) := by
  change twist ω π x⁻¹ (φ (eval H ρ.representation f.1 x)) = _
  rw [twist_apply, map_inv]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem comp_mk'_eq_one [H.Normal] (ω₀ : G ⧸ H →* ℂˣ) (h : H) :
    ω₀.comp (QuotientGroup.mk' H) h = 1 := by
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff (h : G)).mpr h.2,
    map_one]

variable [hN : H.Normal] (hH : IsOpen (H : Set G))
include hH

/-- If `Hom_H(ρ, Res_H π)` has dimension at most one, `j : ρ → Res_H π` is injective and the
characters of `G ⧸ H` separate points, then `End (ind_H^G ρ)` is commutative. -/
theorem commute_of_rank_le_one [ρ.representation.IsIrreducible] (π : Representation ℂ G V)
    (hsep : ∀ q : G ⧸ H, q ≠ 1 → ∃ ω : G ⧸ H →* ℂˣ, ω q ≠ 1)
    (j : ρ.representation.IntertwiningMap (π.comp H.subtype)) (hj : Function.Injective j)
    (hrank : Module.rank ℂ (ρ.representation.IntertwiningMap (π.comp H.subtype)) ≤ 1)
    (α β : End (inducedRep H ρ)) : α * β = β * α := by
  have hj0 : j ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_ne_zero_of_isIrreducible ρ.representation
    intro h0
    apply hw
    apply hj
    rw [h0, map_zero]
    rfl
  rw [← sub_eq_zero]
  set γ := α * β - β * α with hγ
  have hJ : ∀ ω₀ : G ⧸ H →* ℂˣ,
      ((frobenius H ρ hH (twist (ω₀.comp (QuotientGroup.mk' H)) π)).symm
        ((twistRes (ω₀.comp (QuotientGroup.mk' H)) (comp_mk'_eq_one H ω₀) π
          ρ.representation).symm j)).comp (SmoothRep.hom γ) = 0 := by
    intro ω₀
    set ω := ω₀.comp (QuotientGroup.mk' H)
    have hω : ∀ h : H, ω h = 1 := comp_mk'_eq_one H ω₀
    set J := (frobenius H ρ hH (twist ω π)).symm ((twistRes ω hω π ρ.representation).symm j)
    have hr : Module.rank ℂ ((inducedRep H ρ).representation.IntertwiningMap
        (twist ω π)) ≤ 1 := by
      rw [rank_le_one_iff_of_equiv (frobenius H ρ hH _),
        rank_le_one_iff_of_equiv (twistRes ω hω π ρ.representation)]
      exact hrank
    have hJ0 : J ≠ 0 := by
      intro h0
      apply hj0
      rwa [LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff] at h0
    obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hr
    have hscal : ∀ δ : End (inducedRep H ρ), ∃ c : ℂ, J.comp (SmoothRep.hom δ) = c • J := by
      intro δ
      obtain ⟨a, ha⟩ := hv₀ J
      obtain ⟨b, hb⟩ := hv₀ (J.comp (SmoothRep.hom δ))
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ha
        exact hJ0 ha.symm
      exact ⟨b / a, by rw [← hb, ← ha, smul_smul, div_mul_cancel₀ _ ha0]⟩
    obtain ⟨cα, hcα⟩ := hscal α
    obtain ⟨cβ, hcβ⟩ := hscal β
    have e1 : J.comp (SmoothRep.hom γ) =
        (J.comp (SmoothRep.hom α)).comp (SmoothRep.hom β) -
          (J.comp (SmoothRep.hom β)).comp (SmoothRep.hom α) :=
      Representation.IntertwiningMap.ext (LinearMap.ext fun f =>
        map_sub J ((SmoothRep.hom α) ((SmoothRep.hom β) f))
          ((SmoothRep.hom β) ((SmoothRep.hom α) f)))
    rw [e1, hcα, hcβ, Representation.IntertwiningMap.smul_comp,
      Representation.IntertwiningMap.smul_comp, hcα, hcβ, smul_smul, smul_smul, mul_comm,
      sub_self]
  have hF : ∀ w : ρ, SmoothRep.hom γ (unitFunction H hH ρ.representation ρ.isSmooth w) = 0 := by
    intro w
    set F : CompactFunctions H ρ.representation :=
      SmoothRep.hom γ (unitFunction H hH ρ.representation ρ.isSmooth w)
    let t : LeftQuotient H → V := cosetTerm H π ρ.representation j F
    have ht : t = 0 := by
      refine eq_zero_of_forall_character hsep (leftQuotientEquiv H)
        (leftQuotientEquiv H).injective t (hasFiniteSupport_cosetTerm H hH π _ j F) fun ω₀ => ?_
      have h1 := DFunLike.congr_fun (hJ ω₀⁻¹) (unitFunction H hH ρ.representation ρ.isSmooth w)
      change cosetSum H hH _ _ _ F = 0 at h1
      rw [cosetSum_apply] at h1
      refine Eq.trans (finsum_congr fun q => ?_) h1
      obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      refine Eq.trans ?_ (cosetTerm_twist H ρ _ (comp_mk'_eq_one H ω₀⁻¹) π j F x).symm
      simp only [t, MonoidHom.comp_apply, QuotientGroup.mk'_apply, MonoidHom.inv_apply, inv_inv]
      rfl
    refine compactFunctions_ext H _ fun x => ?_
    have h1 := congrFun ht (quotientMap H x)
    change π x⁻¹ (j (eval H ρ.representation F.1 x)) = 0 at h1
    have h2 : j (eval H ρ.representation F.1 x) = 0 := by
      rw [← Representation.self_inv_apply π x (j _), h1, map_zero]
    apply hj
    exact h2.trans (map_zero j).symm
  refine end_ext H ρ hH fun g w => ?_
  rw [endValue_apply, endValue_apply, hF w]
  rfl

end Backward

end Langlands.CuspidalSupport.NormalHecke
