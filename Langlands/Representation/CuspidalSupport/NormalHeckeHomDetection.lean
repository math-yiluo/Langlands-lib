import Langlands.Representation.CuspidalSupport.RationalSummandEndCenterReduction

/-!
# Detecting kernels and twists through `End(ind_H^G ρ)`

Let `H` be an open normal subgroup of a topological group `G`, `ρ` an irreducible smooth complex
representation of `H` and `I = ind_H^G ρ`.

* `eq_zero_of_comp_eq_zero`: if two `G`-maps `T₁, T₂` out of `I` satisfy `T₁ ∘ β = 0 → T₂ ∘ β = 0`
  for every `β ∈ End I`, then `ker T₁ ⊆ ker T₂`.
* `exists_comp_eq_of_ne_zero`: for an irreducible `B`, every map `I → B` is `α ≫ φ` for any
  nonzero `φ : I → B` and some `α ∈ End I`.
* `nonempty_twist_iso_of_linearEquiv`: for an irreducible `B` with `Hom(I, B) ≠ 0` and a character
  `ω` with open kernel, an `End I`-equivariant linear bijection `Hom(I, B ⊗ ω) ≃ Hom(I, B)` forces
  `B ⊗ ω ≅ B`.

For `G = G(F)`, `H = ⁰G` and `B` the carrier lift of an irreducible `π`, the last two results are
the hypotheses `hcyc` and `hiso` of `NormalHeckeCenter`. With them, Renard VI.4.4 (Theorem,
Corollary and Proposition) follows from the finite-length clause of VI.3.2(ii) alone
(`rationalSummandEndCenter_of_finiteRestriction` and its two companions), without VI.4.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped MonoidAlgebra CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uG uV uW uX

namespace NormalHecke

open Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) [hN : H.Normal] (ρ : SmoothRep.{0, uG, uV} ℂ H)

/-- Evaluation at `x`, an `H`-equivariant map from the restriction of `ind_H^G ρ` to the
conjugate `ρ ∘ conjHom x`. -/
def evalAt (x : G) :
    Representation.IntertwiningMap ((inducedRep H ρ).representation.comp H.subtype)
      (ρ.representation.comp (conjHom H x)) where
  toLinearMap := evalLinear H ρ x
  isIntertwining' h := LinearMap.ext fun F => by
    change eval H ρ.representation F.1 (x * (h : G)) =
      ρ.representation (conjHom H x h) (eval H ρ.representation F.1 x)
    rw [← eval_mul_left, conjHom_apply, inv_mul_cancel_right]

theorem evalAt_apply (x : G) (F : CompactFunctions H ρ.representation) :
    evalAt H ρ x F = eval H ρ.representation F.1 x :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem conjHom_conjHom_inv (x : G) (k : H) : conjHom H x (conjHom H x⁻¹ k) = k :=
  Subtype.ext (by rw [conjHom_apply, conjHom_apply]; group)

variable (hH : IsOpen (H : Set G))

/-- An `H`-map from the conjugate `ρ ∘ conjHom x` to the restriction of `ind_H^G ρ`, translated
by `x`, is an `H`-map from `ρ`. -/
def translateBack (x : G)
    (S : Representation.IntertwiningMap (ρ.representation.comp (conjHom H x))
      ((inducedRep H ρ).representation.comp H.subtype)) :
    ρ.representation.IntertwiningMap ((inducedRep H ρ).representation.comp H.subtype) where
  toLinearMap := (inducedRep H ρ).representation x ∘ₗ S.toLinearMap
  isIntertwining' k := LinearMap.ext fun w => by
    change (inducedRep H ρ).representation x (S (ρ.representation k w)) =
      (inducedRep H ρ).representation k ((inducedRep H ρ).representation x (S w))
    have hk : ρ.representation k w =
        (ρ.representation.comp (conjHom H x)) (conjHom H x⁻¹ k) w := by
      change _ = ρ.representation (conjHom H x (conjHom H x⁻¹ k)) w
      rw [conjHom_conjHom_inv]
    rw [hk, S.isIntertwining]
    change (inducedRep H ρ).representation x
        ((inducedRep H ρ).representation (conjHom H x⁻¹ k : G) (S w)) = _
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, conjHom_apply]
    congr 2
    group

include hH

/-- **Kernel detection.** If `T₁ ∘ β = 0` implies `T₂ ∘ β = 0` for every endomorphism `β` of
`ind_H^G ρ`, then the kernel of `T₁` lies in the kernel of `T₂`. -/
theorem eq_zero_of_comp_eq_zero [ρ.representation.IsIrreducible]
    {V₁ : Type uW} [AddCommGroup V₁] [Module ℂ V₁] {V₂ : Type uX} [AddCommGroup V₂] [Module ℂ V₂]
    (τ₁ : Representation ℂ G V₁) (τ₂ : Representation ℂ G V₂)
    (T₁ : (inducedRep H ρ).representation.IntertwiningMap τ₁)
    (T₂ : (inducedRep H ρ).representation.IntertwiningMap τ₂)
    (h : ∀ β : End (inducedRep H ρ),
      T₁.comp (SmoothRep.hom β) = 0 → T₂.comp (SmoothRep.hom β) = 0)
    (F : CompactFunctions H ρ.representation) (hF : T₁ F = 0) : T₂ F = 0 := by
  have hsemi := isSemisimpleModule_res H ρ hH
  let A₁ := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (resIntertwining H τ₁ T₁)
  have key : ∀ U : Submodule ℂ[H]
      (Representation.asModule ((inducedRep H ρ).representation.comp H.subtype)),
      IsSimpleModule ℂ[H] U → U ≤ LinearMap.ker A₁ → ∀ u ∈ U, T₂ u = 0 := by
    intro U hU hUK u hu
    by_cases hu0 : ∀ x, eval H ρ.representation (u : CompactFunctions H ρ.representation).1 x = 0
    · rw [show u = (0 : CompactFunctions H ρ.representation) from
        compactFunctions_ext H _ fun x => hu0 x]
      exact map_zero T₂
    push Not at hu0
    obtain ⟨x, hx⟩ := hu0
    have : Representation.IsIrreducible (ρ.representation.comp (conjHom H x)) :=
      isIrreducible_comp _ _ (conjHom_surjective H x)
    have : IsSimpleModule ℂ[H] (Representation.asModule (ρ.representation.comp (conjHom H x))) :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).mp inferInstance
    let E := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (evalAt H ρ x)
    let EU := E ∘ₗ U.subtype
    have hEU : EU ≠ 0 := fun h0 => hx (LinearMap.congr_fun h0 ⟨u, hu⟩)
    let e := LinearEquiv.ofBijective EU (LinearMap.bijective_of_ne_zero hEU)
    let S := (Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm
      (U.subtype ∘ₗ e.symm.toLinearMap)
    have hSK : ∀ w, T₁ (S w) = 0 := fun w => hUK (e.symm w).2
    have hSu : S (E u) = u := congrArg Subtype.val (e.symm_apply_apply ⟨u, hu⟩)
    let σ := translateBack H ρ x S
    let β : End (inducedRep H ρ) :=
      SmoothRep.ofHom ((frobenius H ρ hH (inducedRep H ρ).representation).symm σ)
    have hβ : ∀ w, SmoothRep.hom β (unitFunction H hH ρ.representation ρ.isSmooth w) = σ w :=
      fun w => congrArg (fun T => T w)
        ((frobenius H ρ hH (inducedRep H ρ).representation).apply_symm_apply σ)
    have h1 : T₁.comp (SmoothRep.hom β) = 0 := by
      apply (frobenius H ρ hH τ₁).injective
      rw [map_zero]
      refine Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)
      change T₁ (SmoothRep.hom β (unitFunction H hH ρ.representation ρ.isSmooth w)) = 0
      rw [hβ]
      change T₁ ((inducedRep H ρ).representation x (S w)) = 0
      rw [T₁.isIntertwining, hSK, map_zero]
    have h2 := congrArg (fun T => T (unitFunction H hH ρ.representation ρ.isSmooth (E u))) (h β h1)
    change T₂ (SmoothRep.hom β (unitFunction H hH ρ.representation ρ.isSmooth (E u))) = 0 at h2
    rw [hβ] at h2
    change T₂ ((inducedRep H ρ).representation x (S (E u))) = 0 at h2
    rw [T₂.isIntertwining, hSu] at h2
    have h3 := congrArg (τ₂ x⁻¹) h2
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at h3
  have hFK : F ∈ LinearMap.ker A₁ := hF
  rw [← IsSemisimpleModule.sSup_simples_le (LinearMap.ker A₁), sSup_eq_iSup'] at hFK
  exact Submodule.iSup_induction _
    (motive := fun v : Representation.asModule
      ((inducedRep H ρ).representation.comp H.subtype) => T₂ v = 0) hFK
    (fun U v hv => key U.1 U.2.1 U.2.2 v hv) (map_zero T₂)
    (fun a b ha hb => (map_add T₂ a b).trans ((congrArg₂ (· + ·) ha hb).trans (add_zero 0)))

/-- For an irreducible `B`, the maps `ind_H^G ρ → B` are generated by any nonzero one under
`End(ind_H^G ρ)`. -/
theorem exists_comp_eq_of_ne_zero [ρ.representation.IsIrreducible]
    (B : SmoothRep.{0, uG, max uG uV} ℂ G) [B.representation.IsIrreducible]
    (φ : inducedRep H ρ ⟶ B) (hφ : φ ≠ 0) (ψ : inducedRep H ρ ⟶ B) :
    ∃ α : End (inducedRep H ρ), α ≫ φ = ψ := by
  have hφ' : SmoothRep.hom φ ≠ 0 := fun h0 => hφ (by rw [← SmoothRep.ofHom_hom φ, h0]; rfl)
  obtain ⟨β, hβ⟩ := exists_end_comp_eq H ρ hH B.representation (SmoothRep.hom φ)
    (SmoothRep.hom ψ) (surjective_of_ne_zero B.representation _ hφ')
  exact ⟨β, by rw [← SmoothRep.ofHom_hom (β ≫ φ), SmoothRep.hom_comp, hβ]; rfl⟩

/-- For an irreducible `B` with `Hom(ind_H^G ρ, B) ≠ 0` and a character `ω` with open kernel, an
`End(ind_H^G ρ)`-equivariant linear bijection `Hom(ind ρ, B ⊗ ω) ≃ Hom(ind ρ, B)` forces
`B ⊗ ω ≅ B`. -/
theorem nonempty_twist_iso_of_linearEquiv [ρ.representation.IsIrreducible]
    (B : SmoothRep.{0, uG, max uG uV} ℂ G) (hB : B.IsIrreducible) [Nontrivial (inducedRep H ρ ⟶ B)]
    (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G))
    (Ψ : (inducedRep H ρ ⟶ B.twist ω hω) ≃ₗ[ℂ] (inducedRep H ρ ⟶ B))
    (hΨ : ∀ (α : End (inducedRep H ρ)) φ, Ψ (α ≫ φ) = α ≫ Ψ φ) :
    Nonempty (B.twist ω hω ≅ B) := by
  obtain ⟨φ', hφ'⟩ := exists_ne (0 : inducedRep H ρ ⟶ B)
  let φ := Ψ.symm φ'
  have hΨs : ∀ (α : End (inducedRep H ρ)) φ₁, Ψ.symm (α ≫ φ₁) = α ≫ Ψ.symm φ₁ :=
    fun α φ₁ => Ψ.injective (by rw [hΨ, Ψ.apply_symm_apply, Ψ.apply_symm_apply])
  have hhom : ∀ {X : SmoothRep.{0, uG, max uG uV} ℂ G} (f : inducedRep H ρ ⟶ X),
      SmoothRep.hom f = 0 ↔ f = 0 := fun f =>
    ⟨fun h0 => by rw [← SmoothRep.ofHom_hom f, h0]; rfl, fun h0 => by rw [h0]; rfl⟩
  have h1 : ∀ β : End (inducedRep H ρ), (SmoothRep.hom φ).comp (SmoothRep.hom β) = 0 →
      (SmoothRep.hom φ').comp (SmoothRep.hom β) = 0 := fun β hβ => by
    rw [← SmoothRep.hom_comp, hhom] at hβ ⊢
    rw [← Ψ.apply_symm_apply φ', ← hΨ, hβ, map_zero]
  have h2 : ∀ β : End (inducedRep H ρ), (SmoothRep.hom φ').comp (SmoothRep.hom β) = 0 →
      (SmoothRep.hom φ).comp (SmoothRep.hom β) = 0 := fun β hβ => by
    rw [← SmoothRep.hom_comp, hhom] at hβ ⊢
    change β ≫ Ψ.symm φ' = 0
    rw [← hΨs, hβ, map_zero]
  have : B.representation.IsIrreducible := hB
  have : (B.twist ω hω).representation.IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff ω hω B).mpr hB
  have hφ0 : SmoothRep.hom φ ≠ 0 := fun h0 => hφ' (by
    rw [← Ψ.apply_symm_apply φ']
    change Ψ φ = 0
    rw [(hhom φ).mp h0, map_zero])
  have hφ'0 : SmoothRep.hom φ' ≠ 0 := fun h0 => hφ' ((hhom φ').mp h0)
  have hs := surjective_of_ne_zero _ _ hφ0
  have hs' := surjective_of_ne_zero _ _ hφ'0
  have hker : LinearMap.ker (SmoothRep.hom φ).toLinearMap ≤
      LinearMap.ker (SmoothRep.hom φ').toLinearMap := fun F hF =>
    eq_zero_of_comp_eq_zero H ρ hH _ _ _ _ h1 F hF
  have hker' : LinearMap.ker (SmoothRep.hom φ').toLinearMap ≤
      LinearMap.ker (SmoothRep.hom φ).toLinearMap := fun F hF =>
    eq_zero_of_comp_eq_zero H ρ hH _ _ _ _ h2 F hF
  let f : B.twist ω hω →ₗ[ℂ] B :=
    (LinearMap.ker (SmoothRep.hom φ).toLinearMap).liftQ (SmoothRep.hom φ').toLinearMap hker ∘ₗ
      ((SmoothRep.hom φ).toLinearMap.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hf : ∀ F, f (SmoothRep.hom φ F) = SmoothRep.hom φ' F := fun F => by
    have : ((SmoothRep.hom φ).toLinearMap.quotKerEquivOfSurjective hs).symm
        (SmoothRep.hom φ F) = Submodule.Quotient.mk F :=
      (LinearEquiv.symm_apply_eq _).mpr (LinearMap.quotKerEquivOfSurjective_apply_mk _ hs F).symm
    change (LinearMap.ker (SmoothRep.hom φ).toLinearMap).liftQ _ hker
      (((SmoothRep.hom φ).toLinearMap.quotKerEquivOfSurjective hs).symm (SmoothRep.hom φ F)) = _
    rw [this, Submodule.liftQ_apply]
    rfl
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun b hb => ?_
    obtain ⟨F, rfl⟩ := hs b
    rw [hf] at hb
    exact hker' hb
  have hsurj : Function.Surjective f := fun b => by
    obtain ⟨F, rfl⟩ := hs' b
    exact ⟨SmoothRep.hom φ F, hf F⟩
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨SmoothRep.mkIso (Representation.Equiv.mk e fun g => LinearMap.ext fun b => ?_)⟩
  obtain ⟨F, rfl⟩ := hs b
  change f ((B.twist ω hω).representation g (SmoothRep.hom φ F)) =
    B.representation g (f (SmoothRep.hom φ F))
  rw [← (SmoothRep.hom φ).isIntertwining, hf, hf, (SmoothRep.hom φ').isIntertwining]

end NormalHecke

section Rational

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalSummandHomDetectionTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance rationalSummandHomDetectionTopologicalGroup :
    IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable {π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)}
variable {ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G)}

/-- Every map `ind ρ → π` is a multiple of any nonzero one under `End(ind ρ)`, without
VI.4.1. -/
theorem rationalSummand_cyclic_of_isIrreducible (hπ : π.IsIrreducible) (hρ : ρ.IsIrreducible)
    (φ : NormalHecke.inducedRep (rationalCommonNormKernel G) ρ ⟶ rationalInertiaBaseLift G π)
    (hφ : φ ≠ 0)
    (ψ : NormalHecke.inducedRep (rationalCommonNormKernel G) ρ ⟶ rationalInertiaBaseLift G π) :
    ∃ α : End (NormalHecke.inducedRep (rationalCommonNormKernel G) ρ), α ≫ φ = ψ := by
  have : ρ.representation.IsIrreducible := hρ
  have : (rationalInertiaBaseLift G π).representation.IsIrreducible :=
    isIrreducible_rationalInertiaBaseLift hπ
  exact NormalHecke.exists_comp_eq_of_ne_zero _ ρ (isOpen_rationalCommonNormKernel G) _ φ hφ ψ

/-- An `End(ind ρ)`-equivariant identification of the maps into a twist with the maps into `π`
gives an isomorphism of the twist with `π`, without VI.4.1. -/
theorem rationalSummand_twistIso_of_isIrreducible (hπ : π.IsIrreducible) (hρ : ρ.IsIrreducible)
    [Nontrivial
      (NormalHecke.inducedRep (rationalCommonNormKernel G) ρ ⟶ rationalInertiaBaseLift G π)]
    (ω : GroupScheme.rationalPoints G →* ℂˣ)
    (hω : IsOpen (ω.ker : Set (GroupScheme.rationalPoints G)))
    (_hωH : rationalCommonNormKernel G ≤ ω.ker)
    (Ψ : (NormalHecke.inducedRep (rationalCommonNormKernel G) ρ ⟶
        (rationalInertiaBaseLift G π).twist ω hω) ≃ₗ[ℂ]
      (NormalHecke.inducedRep (rationalCommonNormKernel G) ρ ⟶ rationalInertiaBaseLift G π))
    (hΨ : ∀ (α : End (NormalHecke.inducedRep (rationalCommonNormKernel G) ρ)) φ,
      Ψ (α ≫ φ) = α ≫ Ψ φ) :
    Nonempty ((rationalInertiaBaseLift G π).twist ω hω ≅ rationalInertiaBaseLift G π) := by
  have : ρ.representation.IsIrreducible := hρ
  exact NormalHecke.nonempty_twist_iso_of_linearEquiv _ ρ (isOpen_rationalCommonNormKernel G) _
    (isIrreducible_rationalInertiaBaseLift hπ) ω hω Ψ hΨ

end Rational

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- Renard VI.4.4, Theorem, from the finite-length clause of VI.3.2(ii) alone, with the same
quantifiers, premises and universes. -/
theorem rationalSummandEndCenter_of_finiteRestriction
    (hFin : RationalNormKernelFiniteRestrictionStatement.{uF, uV}) :
    RationalSummandEndCenterStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ j hj T I f
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have hlen := (hFin F G hG π hπ).2.1
  classical
  have : ρ.representation.IsIrreducible := hρ
  have := finiteDimensional_rationalSummandHom hρ hlen
  have := nontrivial_rationalSummandHom hρ j hj
  have hH := isOpen_rationalCommonNormKernel G
  have hrank := rank_le_aleph0_of_rationalCommonNormKernel G ρ hρ
  have hcyc := rationalSummand_cyclic_of_isIrreducible hπ hρ
  refine ⟨fun α => (NormalHecke.mem_center_iff_endValue ρ hH (isDegree_rationalValuation G)
    hrank _ hcyc (rationalSummand_twistIso_of_isIrreducible hπ hρ)
    (fun g => mem_rationalTwistGroup_iff g) α).trans
      ⟨fun h w g hg => LinearMap.congr_fun (h g hg) w,
        fun h g hg => LinearMap.ext fun w => h w g hg⟩, ?_⟩
  let e := NormalHecke.inducedLiftHomEquiv (rationalCommonNormKernel G) ρ hH π
  have : FiniteDimensional ℂ (ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π) :=
    Module.Finite.equiv e
  refine ⟨Module.finrank ℂ (ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π),
    (Module.finrank_eq_rank ℂ _).symm, ?_⟩
  rw [← e.finrank_eq]
  exact NormalHecke.exists_basis_center ρ hH (isDegree_rationalValuation G) hrank _ hcyc

/-- Renard VI.4.4, Corollary, from the finite-length clause of VI.3.2(ii) alone, with the same
quantifiers, premises and universes. -/
theorem rationalSummandEndNoetherian_of_finiteRestriction
    (hFin : RationalNormKernelFiniteRestrictionStatement.{uF, uV}) :
    RationalSummandEndNoetherianStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ j hj I
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have hlen := (hFin F G hG π hπ).2.1
  classical
  have : ρ.representation.IsIrreducible := hρ
  have := finiteDimensional_rationalSummandHom hρ hlen
  have := nontrivial_rationalSummandHom hρ j hj
  have : Module.Finite ℤ (Additive (rationalDiscreteValuationImage G)) :=
    Module.Finite.of_basis (rationalReductiveValuationBasis G hG)
  exact NormalHecke.isNoetherianRing_end ρ (isOpen_rationalCommonNormKernel G)
    (isDegree_rationalValuation G) (rank_le_aleph0_of_rationalCommonNormKernel G ρ hρ) _
    (rationalSummand_cyclic_of_isIrreducible hπ hρ)

/-- Renard VI.4.4, Proposition, from the finite-length clause of VI.3.2(ii) alone, with the
same quantifiers, premises and universes. -/
theorem rationalSummandCenterGroupAlgebra_of_finiteRestriction
    (hFin : RationalNormKernelFiniteRestrictionStatement.{uF, uV}) :
    RationalSummandCenterGroupAlgebraStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ j hj T I f
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have hlen := (hFin F G hG π hπ).2.1
  classical
  have : ρ.representation.IsIrreducible := hρ
  have := finiteDimensional_rationalSummandHom hρ hlen
  have := nontrivial_rationalSummandHom hρ j hj
  obtain ⟨e, he⟩ := NormalHecke.exists_algEquiv_center_quotient ρ
    (isOpen_rationalCommonNormKernel G) (isDegree_rationalValuation G)
    (rank_le_aleph0_of_rationalCommonNormKernel G ρ hρ) _
    (rationalSummand_cyclic_of_isIrreducible hπ hρ)
    (rationalSummand_twistIso_of_isIrreducible hπ hρ) (fun g => mem_rationalTwistGroup_iff g)
  refine ⟨e, fun t => ?_⟩
  intro ψ
  exact ⟨fun w g hg => LinearMap.congr_fun ((he t).1 g hg) w,
    fun ω φ => (he t).2 ω.val.toMonoidHom (isOpen_rationalUnramifiedCharacter_ker G ω)
      ω.property φ⟩

end Langlands.CuspidalSupport
