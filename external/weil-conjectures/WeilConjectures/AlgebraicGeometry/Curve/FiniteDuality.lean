/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.TraceSections
public import WeilConjectures.AlgebraicGeometry.Modules.HomOfBasis
public import WeilConjectures.AlgebraicGeometry.Modules.PushforwardHomAffine

/-!
# The trace identification along a finite flat morphism to the projective line

Let `X` be a smooth curve over a field `k` and `f : X ⟶ ℙ¹_k` a finite flat morphism over `k`
which is unramified at the generic points of `X`. The traces of differentials
`Γ(Ω¹_{X/k}, f⁻¹V) → Γ(Ω¹_{ℙ¹/k}, V)`, `c da ↦ Tr(C · dA)`, over the basic opens `V` of the
standard charts of `ℙ¹_k` glue to a morphism `τ : f_* Ω¹_{X/k} ⟶ Ω¹_{ℙ¹/k}`
(`AlgebraicGeometry.Scheme.Modules.homOfBasis`), and the comparison
`f_* Ω¹_{X/k} ⟶ Hom(f_* 𝒪_X, Ω¹_{ℙ¹/k})`, `ω ↦ (a ↦ τ(a ω))`, is an isomorphism, since it is
bijective on the sections over these opens by the local duality for the trace of differentials
(`AlgebraicGeometry.Scheme.Hom.traceSections_smul_eq_zero`,
`AlgebraicGeometry.Scheme.Hom.exists_traceSections_smul_eq`).

## Main results

- `AlgebraicGeometry.Scheme.Hom.traceSections_restrict_of_le`: the trace of differentials on
  sections is compatible with restriction between affine opens.
- `AlgebraicGeometry.Scheme.exists_isIso_pushforwardHomObjComparison_unit`: the trace
  identification `f_* Ω¹_{X/k} ≅ Hom(f_* 𝒪_X, Ω¹_{ℙ¹/k})`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace Polynomial

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of k))]

/-- `traceSections_restrict` for an open `W` which is equal to a basic open of `V`. -/
lemma traceSections_restrict_of_eq {V W : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V)) (hfree) (hfin) (r : Γ(Y, V)) (hr : W = Y.basicOpen r)
    (hW : IsAffineOpen (f ⁻¹ᵁ W)) (hfree') (hfin') (hWV : W ≤ V)
    (ω : Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ V)) :
    f.traceSections W hW hfree' hfin'
        ((X ↘ Spec (.of k)).relativeDifferentials.presheaf.map
          (homOfLE (f.preimage_mono hWV)).op ω) =
      (Y ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE hWV).op
        (f.traceSections V hV' hfree hfin ω) := by
  subst hr
  exact traceSections_restrict hV hV' hfree hfin r hW hfree' hfin' ω

/-- **The trace of differentials on sections is compatible with restriction** between affine
opens `V₂ ⊆ V₁`: both sides agree on the opens which are basic in both `V₁` and `V₂`, and these
cover `V₂`. -/
lemma traceSections_restrict_of_le [IsAffineHom f] {V₁ V₂ : Y.Opens} (h₁ : IsAffineOpen V₁)
    (h₂ : IsAffineOpen V₂) (hle : V₂ ≤ V₁) (h₁' : IsAffineOpen (f ⁻¹ᵁ V₁))
    (h₂' : IsAffineOpen (f ⁻¹ᵁ V₂)) (hfree₁) (hfin₁) (hfree₂) (hfin₂)
    (ω : Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ V₁)) :
    f.traceSections V₂ h₂' hfree₂ hfin₂
        ((X ↘ Spec (.of k)).relativeDifferentials.presheaf.map
          (homOfLE (f.preimage_mono hle)).op ω) =
      (Y ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE hle).op
        (f.traceSections V₁ h₁' hfree₁ hfin₁ ω) := by
  choose r₁ r₂ hr hx using fun x : V₂ ↦ exists_basicOpen_le_affine_inter h₁ h₂ x.1
    ⟨hle x.2, x.2⟩
  have hW₂ (x : V₂) : Y.basicOpen (r₁ x) ≤ V₂ := (hr x).symm ▸ Y.basicOpen_le (r₂ x)
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, (Y ↘ Spec (.of k)).relativeDifferentials.isSheaf⟩
    (fun x : V₂ ↦ Y.basicOpen (r₁ x)) V₂ (fun x ↦ homOfLE (hW₂ x))
    (fun x hx' ↦ Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx ⟨x, hx'⟩⟩) _ _ fun x ↦ ?_
  have hW (x : V₂) : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen (r₁ x)) := (h₁.basicOpen (r₁ x)).preimage f
  have hff (x : V₂) := free_finite_basicOpen h₁ h₁' hfree₁ hfin₁ (r₁ x)
  change (Y ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE (hW₂ x)).op _ =
    (Y ↘ Spec (.of k)).relativeDifferentials.presheaf.map (homOfLE (hW₂ x)).op _
  rw [← traceSections_restrict_of_eq h₂ h₂' hfree₂ hfin₂ (r₂ x) (hr x) (hW x) (hff x).1
      (hff x).2 (hW₂ x), Modules.presheaf_map_homOfLE_map_homOfLE,
    Modules.presheaf_map_homOfLE_map_homOfLE,
    ← traceSections_restrict_of_eq h₁ h₁' hfree₁ hfin₁ (r₁ x) rfl (hW x) (hff x).1 (hff x).2]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

open ProjectiveLine Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]

/-- **Trace identification along a finite flat morphism to `ℙ¹`.** Let `X` be a smooth curve
over `k` and `f : X ⟶ ℙ¹_k` a finite flat morphism over `k`, unramified at the generic points of
`X`. There is a trace map `τ : f_* Ω¹_{X/k} ⟶ Ω¹_{ℙ¹_k/k}` such that
`f_* Ω¹_{X/k} ⟶ Hom(f_* 𝒪_X, Ω¹_{ℙ¹_k/k})`, `ω ↦ (a ↦ τ(a ω))`, is an isomorphism: the comparison
`φ ↦ τ ∘ f_* φ` for `ℳ = 𝒪_X`. Locally over `V = Spec R ⊆ ℙ¹_k` with `f⁻¹V = Spec B` this is
`Ω¹_{B/k} ≅ Hom_R(B, Ω¹_{R/k})`, the codifferent of the finite flat extension `R ⊆ B`, i.e.
Grothendieck duality `f^! Ω¹_{ℙ¹} ≅ Ω¹_{X/k}` for `f`; `τ` is glued from the traces of
differentials `c da ↦ Tr(C · dA)` over the basic opens of the standard charts of `ℙ¹_k`.

The hypothesis `hf` (`f` unramified at the generic points, i.e. `k(X)/k(t)` separable) is not
in the blueprint statement, but the blueprint's own proof uses it: the generic-point step is the
perfect trace pairing of the separable extension `k(X) ⊇ k(t)` together with left exactness of
the Kähler sequence. It cannot be dropped: the isomorphism is induced by the trace of
differentials, which vanishes identically when `f` is inseparable (e.g. a Frobenius-type map),
so for such `f` the comparison is the zero map. Downstream (`nonempty_dual_H_one_iso`) `f` is
chosen by `exists_isFinite_flat_hom_projectiveLine`, which provides a separable `f` and `hf`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`, the trace identification) -/
theorem exists_isIso_pushforwardHomObjComparison_unit (f : X ⟶ ProjectiveLine (Spec (.of k)))
    [f.IsOver (Spec (.of k))] [IsFinite f] [Flat f]
    (hf : ∀ x : X, IsField (X.presheaf.stalk x) → (f.stalkMap x).hom.FormallyUnramified) :
    ∃ τ : (Modules.pushforward f).obj (X ↘ Spec (.of k)).relativeDifferentials ⟶
        (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials,
      IsIso (Modules.pushforwardHomObjComparison f τ (SheafOfModules.unit X.ringCatSheaf)) := by
  let O : (Σ _ : ULift.{u} (Fin 2), {g : k[X] // g ≠ 0}) → (ProjectiveLine (Spec (.of k))).Opens :=
    fun a ↦ chartBasicOpen k a.1 a.2.1
  have hO : Opens.IsBasis (Set.range O) := isBasis_chartBasicOpen k
  have hcov (W : (ProjectiveLine (Spec (.of k))).Opens) (x) (hx : x ∈ W) :
      ∃ a, x ∈ O a ∧ O a ≤ W := by
    obtain ⟨_, ⟨a, rfl⟩, hxa, haW⟩ := (Opens.isBasis_iff_nbhd.1 hO) hx
    exact ⟨a, hxa, haW⟩
  have hA (a : Σ _ : ULift.{u} (Fin 2), {g : k[X] // g ≠ 0}) : IsAffineOpen (O a) :=
    isAffineOpen_chartBasicOpen k a.1 a.2.1
  have hA' (a : Σ _ : ULift.{u} (Fin 2), {g : k[X] // g ≠ 0}) : IsAffineOpen (f ⁻¹ᵁ O a) :=
    (hA a).preimage f
  have hff (a : Σ _ : ULift.{u} (Fin 2), {g : k[X] // g ≠ 0}) :=
    Hom.free_finite_chartBasicOpen (f := f) a.1 (g := a.2.1)
  let φ (a) : Γ((Modules.pushforward f).obj (X ↘ Spec (.of k)).relativeDifferentials, O a) →+
      Γ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials, O a) :=
    f.traceSections (O a) (hA' a) (hff a).1 (hff a).2
  have hcomp (a b) (h : O b ≤ O a) (m) :
      φ b (((Modules.pushforward f).obj (X ↘ Spec (.of k)).relativeDifferentials).presheaf.map
        (homOfLE h).op m) =
        (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials.presheaf.map
          (homOfLE h).op (φ a m) :=
    Hom.traceSections_restrict_of_le (hA a) (hA b) h (hA' a) (hA' b) _ _ _ _ m
  have hsmul (a) (r : Γ(ProjectiveLine (Spec (.of k)), O a)) (m) : φ a (r • m) = r • φ a m :=
    (congrArg (φ a) (pushforward_smul_def f _ _ r m)).trans
      (Hom.traceSections_smul (O a) (hA' a) (hff a).1 (hff a).2 r m)
  let τ := homOfBasis hcov hcomp hsmul
  refine ⟨τ, isIso_of_bijective_app_of_basis hO _ fun a ↦ ?_⟩
  have hτ (m) : τ.app (O a) m = φ a m := homOfBasis_app_basis hcov hcomp hsmul a m
  have key (ω : Γ((X ↘ Spec (.of k)).relativeDifferentials, f ⁻¹ᵁ O a))
      (b : Γ(X, f ⁻¹ᵁ O a)) :
      ((pushforwardHomObjComparison f τ (SheafOfModules.unit X.ringCatSheaf)).app (O a)
        (PresheafOfModules.homObjUnitInvApp _ ω)).app (op (Over.mk (𝟙 (O a)))) b =
        φ a (b • ω) := by
    refine (hτ _).trans (congrArg (φ a) ?_)
    change ((PresheafOfModules.homObjUnitInvApp _ ω).app
      (op (Over.mk (𝟙 (f ⁻¹ᵁ O a))))).hom b = _
    rw [PresheafOfModules.homObjUnitInvApp_app_apply]
    exact congrArg (fun m ↦ b • m) (PresheafOfModules.map_id_apply' _ ω)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ψ hψ
    have e := ConcreteCategory.congr_hom (PresheafOfModules.homObjUnitIsoApp
      (X ↘ Spec (.of k)).relativeDifferentials.val (op (f ⁻¹ᵁ O a))).hom_inv_id ψ
    set ω := ConcreteCategory.hom (PresheafOfModules.homObjUnitIsoApp
      (X ↘ Spec (.of k)).relativeDifferentials.val (op (f ⁻¹ᵁ O a))).hom ψ
    have hψω : ψ = PresheafOfModules.homObjUnitInvApp _ ω := e.symm
    have hω : ω = 0 := by
      refine Hom.traceSections_smul_eq_zero hf a.1 a.2.2 ω fun b ↦ ?_
      refine (key ω b).symm.trans ?_
      rw [← hψω, hψ]
      rfl
    rw [hψω, hω]
    exact map_zero (ConcreteCategory.hom (PresheafOfModules.homObjUnitIsoApp
      (X ↘ Spec (.of k)).relativeDifferentials.val (op (f ⁻¹ᵁ O a))).inv)
  · intro χ
    let φ₀ : Γ(X, f ⁻¹ᵁ O a) →+
        Γ((ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials, O a) :=
      (χ.app (op (Over.mk (𝟙 (O a))))).hom.toAddMonoidHom
    have hφ₀ (r : Γ(ProjectiveLine (Spec (.of k)), O a)) (b : Γ(X, f ⁻¹ᵁ O a)) :
        φ₀ (f.app _ r * b) = r • φ₀ b :=
      (χ.app (op (Over.mk (𝟙 (O a))))).hom.map_smul r b
    obtain ⟨ω, hω⟩ := Hom.exists_traceSections_smul_eq hf a.1 a.2.2 φ₀ hφ₀
    refine ⟨PresheafOfModules.homObjUnitInvApp _ ω, ?_⟩
    refine restrictOver_pushforward_unit_hom_ext f (hA a) (hA' a) ?_
    ext b
    exact (key ω b).trans (hω b)

end AlgebraicGeometry.Scheme
