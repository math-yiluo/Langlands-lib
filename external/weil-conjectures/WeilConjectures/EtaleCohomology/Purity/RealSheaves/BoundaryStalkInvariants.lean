/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericRep
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodData
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary
public import WeilConjectures.WeilSheaf.BoundaryStalkSpecialization

/-!
# Boundary stalks of direct images as inertia invariants

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite
field `k₀`, `U₀` geometrically connected, `F` a lisse Weil sheaf on `U₀` with Weil fundamental
representation `(V, ρ)` and `z ∈ C₀ ∖ U₀` a boundary point with closed point `x`. Given a strictly
henselian neighbourhood of the boundary point
(`AlgebraicGeometry.WeilGroup.BoundaryNeighbourhood`), the boundary stalk `(j_* F)_x̄` is the
module of inertia invariants `V ^ (I_z)`, the Frobenius of the stalk corresponding to the residue
Frobenius lift `ρ(Frob_z)`
(`AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_stalk_directImage_boundaryStalk`).
This is blueprint `lemma-boundary-stalk--1`.

The proof identifies, Frobenius-equivariantly, the stalk with the `Gal(Ω / K')`-invariant
sections over the geometric generic point `Spec Ω`
(`AlgebraicGeometry.WeilSheaf.exists_stalk_directImage_linearMap_invariants`), and these sections
with the Weil fundamental representation, on which the inertia group acts through `Gal(Ω / K')`
and the residue Frobenius lift through the Weil structure
(`AlgebraicGeometry.WeilGroup.genericStalkEquiv_fundamentalRep`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

open scoped Pointwise

/-- An element lies in the inertia group of a translate `τ • P` iff its conjugate by `τ` lies in the
inertia group of `P`. -/
lemma Ideal.mem_inertia_pointwise_smul_iff {G R : Type*} [Group G] [CommRing R]
    [MulSemiringAction G R] (P : Ideal R) (τ σ : G) :
    σ ∈ (τ • P).inertia G ↔ τ⁻¹ * σ * τ ∈ P.inertia G := by
  change (∀ x, σ • x - x ∈ τ • P) ↔ ∀ x, (τ⁻¹ * σ * τ) • x - x ∈ P
  constructor
  · intro h x
    have := h (τ • x)
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul] at this
    simpa [mul_smul] using this
  · intro h x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub]
    simpa [mul_smul] using h (τ⁻¹ • x)

/-- An element lies in the range of `e⁻¹ ∘ S`, `e` a linear equivalence, iff its image under `e`
lies in the range of `S`. -/
lemma LinearMap.mem_range_linearEquiv_symm_comp_iff {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
    (e : P ≃ₗ[R] N) (S : M →ₗ[R] N) (w : P) :
    w ∈ LinearMap.range (e.symm.toLinearMap ∘ₗ S) ↔ e w ∈ LinearMap.range S := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, by simp⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by simp [hv]⟩

/-- If `S` intertwines `f` with `T` and `e` intertwines `R` with `T`, then `e⁻¹ ∘ S` intertwines `f`
with `R`. -/
lemma LinearMap.linearEquiv_symm_comp_apply_of_intertwine {R M N P : Type*} {_ : Semiring R}
    {_ : AddCommMonoid M} {_ : AddCommMonoid N} {_ : AddCommMonoid P} {_ : Module R M}
    {_ : Module R N} {_ : Module R P}
    (e : P ≃ₗ[R] N) (S : M →ₗ[R] N) (f : M → M) (T : N → N) (Q : P → P)
    (hS : ∀ v, S (f v) = T (S v)) (hQ : ∀ w, e (Q w) = T (e w)) (v : M) :
    (e.symm.toLinearMap ∘ₗ S) (f v) = Q ((e.symm.toLinearMap ∘ₗ S) v) := by
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hS]
  rw [LinearEquiv.symm_apply_eq, hQ, LinearEquiv.apply_symm_apply]


/-- **Transport of invariants along a conjugation.** Let `f : V ≃ S` intertwine representations
`ρ` and `ρ'` of `G`, `H ≤ G`, `T, Φ ∈ G`, and `L : M → S` an injective linear map whose image is
the subspace of vectors fixed by `T H T⁻¹`, intertwining `φ` with `ρ' (T Φ T⁻¹)`. Then `M` is
isomorphic to the `H`-invariants of `V`, intertwining `φ` with `ρ Φ`. -/
lemma Representation.exists_linearEquiv_invariants_of_conj {k G V S M : Type*} [Field k]
    [Group G] [AddCommGroup V] [Module k V] [AddCommGroup S] [Module k S] [AddCommGroup M]
    [Module k M] (ρ : Representation k G V) (ρ' : Representation k G S) (f : V ≃ₗ[k] S)
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (H : Subgroup G) (T Φ : G) (L : M →ₗ[k] S)
    (hL : Function.Injective L)
    (hLr : ∀ w, w ∈ LinearMap.range L ↔ ∀ g ∈ H, ρ' (T * g * T⁻¹) w = w) (φ : M → M)
    (hLf : ∀ v, L (φ v) = ρ' (T * Φ * T⁻¹) (L v)) :
    ∃ e : M ≃ₗ[k] Representation.invariants (ρ.comp H.subtype),
      ∀ v, (e (φ v) : V) = ρ Φ (e v) := by
  have hfs (g : G) (s : S) : f.symm (ρ' g s) = ρ g (f.symm s) :=
    f.symm_apply_eq.2 (by rw [hf, f.apply_symm_apply])
  have hmul (a b : G) (v : V) : ρ (a * b) v = ρ a (ρ b v) := by
    rw [map_mul, Module.End.mul_apply]
  have hcancel (a : G) (v : V) : ρ a (ρ a⁻¹ v) = v := by
    rw [← hmul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hcancel' (a : G) (v : V) : ρ a⁻¹ (ρ a v) = v := by
    rw [← hmul, inv_mul_cancel, map_one, Module.End.one_apply]
  set L' : M →ₗ[k] V := ρ T⁻¹ ∘ₗ f.symm.toLinearMap ∘ₗ L with hL'def
  have hL'apply (m : M) : L' m = ρ T⁻¹ (f.symm (L m)) := rfl
  have hinj : Function.Injective L' := by
    intro a b h
    rw [hL'apply, hL'apply] at h
    have h' := congrArg (ρ T) h
    rw [hcancel, hcancel] at h'
    exact hL (f.symm.injective h')
  have hr : LinearMap.range L' = Representation.invariants (ρ.comp H.subtype) := by
    ext v
    rw [Representation.mem_invariants]
    constructor
    · rintro ⟨m, rfl⟩ ⟨g, hg⟩
      have hm := (hLr (L m)).1 ⟨m, rfl⟩ g hg
      have hm' : ρ (T * g * T⁻¹) (f.symm (L m)) = f.symm (L m) := by
        rw [← hfs, hm]
      change ρ g (L' m) = L' m
      rw [hL'apply, ← hmul, show g * T⁻¹ = T⁻¹ * (T * g * T⁻¹) by group, hmul, hm']
    · intro hv
      obtain ⟨m, hm⟩ := (hLr (f (ρ T v))).2 fun g hg ↦ by
        rw [← hf, ← hmul, show T * g * T⁻¹ * T = T * g by group, hmul]
        exact congrArg (fun u ↦ f (ρ T u)) (hv ⟨g, hg⟩)
      refine ⟨m, ?_⟩
      rw [hL'apply, hm, f.symm_apply_apply, hcancel']
  refine ⟨(LinearEquiv.ofInjective L' hinj).trans (LinearEquiv.ofEq _ _ hr), fun v ↦ ?_⟩
  change L' (φ v) = ρ Φ (L' v)
  rw [hL'apply, hL'apply, hLf, hfs, ← hmul, ← hmul, show T⁻¹ * (T * Φ * T⁻¹) = Φ * T⁻¹ by group]
namespace AlgebraicGeometry.WeilGroup

section Generic

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  [GeometricallyConnected p] [ConnectedSpace C] [Smooth p] {pU : U ⟶ Spec (.of K)} [IsCurve pU]
  [GeometricallyConnected pU] [ConnectedSpace U] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
  [IsIntegral C] [SmoothOfRelativeDimension 1 p] (sU : Spec (.of (AlgebraicClosure K)) ⟶ U)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]

omit [GeometricallyConnected p] [IsCurve pU] in
/-- The image in the Weil group of an element of the inertia group of the chosen point over a
boundary point `z`, of degree zero, lies in the inertia group `I_z`. -/
lemma mk_mem_boundaryInertia (z : ↥((Set.range j.base)ᶜ))
    {σ : Gal(SeparableClosure (Scheme.functionField C)/C.functionField)}
    (hσ : σ ∈ (boundaryChart (p := p) j z).point.inertia
      Gal(SeparableClosure (Scheme.functionField C)/C.functionField))
    (hw : (genericGaloisMap j sU GU σ, Multiplicative.ofAdd (0 : ℤ)) ∈ weilGroup pU sU GU) :
    (⟨_, hw⟩ : weilGroup pU sU GU) ∈ boundaryInertia (p := p) (pU := pU) j sU GU z :=
  ⟨⟨σ, hσ, rfl⟩, rfl⟩

omit [ConnectedSpace C] [IsCurve pU] in
/-- Conjugation of elements of the Weil group in the image of `Gal(Ω / k(C))`. -/
lemma coe_mk_mul_mk_mul_inv {τ σ : Gal(SeparableClosure (Scheme.functionField C)/C.functionField)}
    {n m : ℤ} (hτ : (genericGaloisMap j sU GU τ, Multiplicative.ofAdd n) ∈ weilGroup pU sU GU)
    (hσ : (genericGaloisMap j sU GU σ, Multiplicative.ofAdd m) ∈ weilGroup pU sU GU) :
    (((⟨_, hτ⟩ : weilGroup pU sU GU) * ⟨_, hσ⟩ * (⟨_, hτ⟩ : weilGroup pU sU GU)⁻¹ :
        weilGroup pU sU GU) : GU × Multiplicative ℤ) =
      (genericGaloisMap j sU GU (τ * σ * τ⁻¹), Multiplicative.ofAdd m) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  simp only [Prod.mk_mul_mk, Prod.inv_mk, map_mul, map_inv]
  congr 1
  rw [mul_comm, inv_mul_cancel_left]

omit [IsCurve pU] in
/-- The residue Frobenius lift at `z` as an explicit element of the Weil group. -/
lemma boundaryResidueFrobenius_eq (hj : j ≫ p = pU) {sC : Spec (.of (AlgebraicClosure K)) ⟶ C}
    (τ : fiber (sU ≫ j) ≅ fiber sC) (GC : Type u) [Group GC] [TopologicalSpace GC]
    [IsTopologicalGroup GC] [CompactSpace GC] [∀ P, MulAction GC ((fiber sC).obj P)]
    [IsFundamentalGroup (fiber sC) GC] (z : ↥((Set.range j.base)ᶜ)) :
    boundaryResidueFrobenius j sU GU hj τ GC z =
      ⟨_, mem_weilGroup_boundaryFrobeniusLift j sU GU hj τ GC z⟩ :=
  rfl

end Generic

end AlgebraicGeometry.WeilGroup

namespace AlgebraicGeometry.WeilGroup

open Scheme Scheme.FiniteEtale ProEtale WeilSheaf

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} [C.Over (Spec (.of K))]
  [U.Over (Spec (.of K))] [IsCurve (C ↘ Spec (.of K))] [GeometricallyConnected (C ↘ Spec (.of K))]
  [ConnectedSpace C] [IsIntegral C] [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))]
  [Smooth (C ↘ Spec (.of K))]
  [IsCurve (U ↘ Spec (.of K))] [GeometricallyConnected (U ↘ Spec (.of K))] [ConnectedSpace U]
  (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [Nonempty U] [j.IsOver (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  (sU : Spec (.of (AlgebraicClosure K)) ⟶ U)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]
  {sC : Spec (.of (AlgebraicClosure K)) ⟶ C} (τ : fiber (sU ≫ j) ≅ fiber sC)
  (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC] [CompactSpace GC]
  [∀ P, MulAction GC ((fiber sC).obj P)] [IsFundamentalGroup (fiber sC) GC]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

local notation "M" =>
  universalLisseMonodromy l (Scheme.Hom.geometricFiber (U ↘ Spec (CommRingCat.of K))) K

/-- A strictly henselian neighbourhood of the boundary point `z` with closed point `x`, for the
inertia group of the chosen point over `z` and the residue Frobenius lift at `z`. -/
abbrev BoundaryNeighbourhoodAt (z : ↥((Set.range j.base)ᶜ)) (x : C.finitePoints) : Type (u + 1) :=
  BoundaryNeighbourhood (K := K) j
    ((boundaryChart (p := C ↘ Spec (.of K)) j z).point.inertia Gal(Ω/C.functionField))
    (boundaryFrobeniusLift (p := C ↘ Spec (.of K)) j sU GU τ GC z) x

omit [IsCurve (U ↘ Spec (.of K))] [QuasiCompact j] in
include τ GC in
/-- An element of the inertia group at the chosen point over `z` maps to an element of degree
zero of the Weil group. -/
lemma genericGaloisMap_mem_weilGroup_of_mem_inertia (z : ↥((Set.range j.base)ᶜ))
    {σ : Gal(Ω/C.functionField)}
    (hσ : σ ∈ (boundaryChart (p := C ↘ Spec (.of K)) j z).point.inertia Gal(Ω/C.functionField)) :
    (genericGaloisMap j sU GU σ, Multiplicative.ofAdd (0 : ℤ)) ∈
      weilGroup (U ↘ Spec (.of K)) sU GU := by
  have : Finite (C.residueField z.1) :=
    boundary_subset_finitePoints (p := C ↘ Spec (.of K)) j z.2
  have hk : genericGaloisMap j sU GU σ ∈ inertiaGroup sU GU
      (boundaryChart (p := C ↘ Spec (.of K)) j z)
      (boundaryChart (p := C ↘ Spec (.of K)) j z).point :=
    ⟨σ, hσ, rfl⟩
  have hkL := inertiaGroup_le_localKernel (p := C ↘ Spec (.of K)) sU GU _ _ hk
  rw [mem_weilGroup_fundamentalGroupMap_iff j (comp_over j _) sU τ GU GC,
    MonoidHom.mem_ker.1 (localKernel_le_ker_restrictionMap j τ GU GC z.1 hkL)]
  exact (weilGroup (C ↘ Spec (.of K)) sC GC).one_mem

section Rep

variable [IsLocallyNoetherian (U ↘ Spec (.of K)).geometricFiber]
  [CompactSpace (U ↘ Spec (.of K)).geometricFiber] [IsRegular (U ↘ Spec (.of K)).geometricFiber]
  [ConnectedSpace (U ↘ Spec (.of K)).geometricFiber]
  [QuasiSeparatedSpace (U ↘ Spec (.of K)).geometricFiber]

omit [GeometricallyConnected (C ↘ Spec (.of K))] [ConnectedSpace C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (.of K))] [Smooth (C ↘ Spec (.of K))] in
/-- **The boundary stalk in the Weil fundamental representation, for a neighbourhood.** Given a
strictly henselian neighbourhood of the boundary point `z` with closed point `x`, for a subgroup
`I` of `Gal(Ω / k(C))` (the Galois group of the punctured neighbourhood) mapping to elements of
degree zero of the Weil group and a Frobenius lift `σ_F` mapping to an element of degree `deg x`,
there is an injective linear map from the boundary stalk `(j_* F)_x̄` to the Weil fundamental
representation `F_t`, with image the invariants of the image of `I`, intertwining the Frobenius of
the stalk with the image of `σ_F`.
(blueprint: `lemma-boundary-stalk--1`) -/
theorem exists_linearMap_stalk_directImage_fundamentalRep_of_neighbourhood
    (B₀ : BasePointData (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU))
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint (U ↘ Spec (.of K)) j)
    (F : WeilSheaf K l U) (hF : F.IsLisse) (x : C.finitePoints)
    {I : Subgroup Gal(Ω/C.functionField)} {σF : Gal(Ω/C.functionField)}
    (N : BoundaryNeighbourhood (K := K) j I σF x)
    (hIw : ∀ σ ∈ I, (genericGaloisMap j sU GU σ, Multiplicative.ofAdd (0 : ℤ)) ∈
      weilGroup (U ↘ Spec (.of K)) sU GU)
    (hwF : (genericGaloisMap j sU GU σF,
      Multiplicative.ofAdd ((C ↘ Spec (.of K)).degreeOver x.1 : ℤ)) ∈
        weilGroup (U ↘ Spec (.of K)) sU GU) :
    ∃ L : (((lowerStar j).obj F).stalk x).carrier →ₗ[PadicAlgCl l]
        LisseMonodromy.StalkSpace (BasePointData.ofLift j sU GU B₀ ξ hξ).t (F.toLisse hF),
      Function.Injective L ∧
      (∀ w, w ∈ LinearMap.range L ↔ ∀ σ (hσ : σ ∈ I),
        fundamentalRep M (BasePointData.ofLift j sU GU B₀ ξ hξ).weilMonodromyData F hF
          (⟨_, hIw σ hσ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) w = w) ∧
      ∀ v, L ((((lowerStar j).obj F).stalk x).frobenius v) =
        fundamentalRep M (BasePointData.ofLift j sU GU B₀ ξ hξ).weilMonodromyData F hF
          (⟨_, hwF⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) (L v) := by
  let _ := N.commRing
  let _ := N.isStrictlyHenselianLocalRing
  let _ := N.weaklyEtale
  let _ := N.field
  let _ := N.algebra
  let _ := N.isSeparable
  let _ := N.normal
  let _ := N.weaklyEtale_k
  have ha := specMap_comp_genericGeomPoint j sU GU _ _ hwF
  obtain ⟨Sp, hSp, hSpr, hSpf⟩ := WeilSheaf.exists_stalk_directImage_linearMap_invariants j F
    N.h N.k N.e x N.t hF N.ht N.α N.hα N.hcα (genericGeomPoint (U ↘ Spec (.of K)) j)
    N.specFieldMap_comp _ ha N.hεα
  set Ψ := genericStalkEquiv B₀ ξ hξ F hF
  -- the Galois groups `Gal(Ω / K')` and `I`
  have hfix (σ : Ω ≃ₐ[N.K'] Ω) (a : C.functionField) :
      σ (algebraMap C.functionField Ω a) = algebraMap C.functionField Ω a := by
    obtain ⟨b, hb⟩ := N.exists_algebraMap_eq a
    rw [← hb, σ.commutes]
  let toGal (σ : Ω ≃ₐ[N.K'] Ω) : Gal(Ω/C.functionField) :=
    AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (hfix σ)
  have hσI (σ : Ω ≃ₐ[N.K'] Ω) : toGal σ ∈ I := (N.mem_iff _).2 fun b ↦ σ.commutes b
  let ofGal (σ : Gal(Ω/C.functionField)) (hσ : σ ∈ I) : Ω ≃ₐ[N.K'] Ω :=
    AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) ((N.mem_iff σ).1 hσ)
  -- `I` acts through restrictions along `Spec σ`
  have hres (ε₁ ε₂ : Spec (.of Ω) ⟶ Spec (.of Ω)) (hε : ε₁ = ε₂)
      (h₁ : ε₁ ≫ genericGeomPoint (U ↘ Spec (.of K)) j = genericGeomPoint (U ↘ Spec (.of K)) j)
      (h₂ : ε₂ ≫ genericGeomPoint (U ↘ Spec (.of K)) j = genericGeomPoint (U ↘ Spec (.of K)) j) :
      (resOver (WeilCoefficients.{u} l) ε₁ h₁).app F.obj.carrier.X =
        (resOver (WeilCoefficients.{u} l) ε₂ h₂).app F.obj.carrier.X := by
    subst hε
    rfl
  have hI (σ' : Ω ≃ₐ[N.K'] Ω) (σ : Gal(Ω/C.functionField)) (hσ : σ ∈ I)
      (hσσ' : (σ : Ω →+* Ω) = σ'.toRingHom) (w) :
      Ψ (fundamentalRep M (BasePointData.ofLift j sU GU B₀ ξ hξ).weilMonodromyData F hF
        (⟨_, hIw σ hσ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) w) =
      ((WeilCoefficients.toModuleCat l).map ((resOver _ _
          (show Spec.map (CommRingCat.ofHom σ'.toRingHom) ≫
              genericGeomPoint (U ↘ Spec (.of K)) j = genericGeomPoint (U ↘ Spec (.of K)) j by
            rw [← N.specFieldMap_comp, ← Category.assoc,
              specMap_algEquiv_comp_specFieldMap])).app
            F.obj.carrier.X)).hom (Ψ w) := by
    have h0 := specMap_comp_genericGeomPoint j sU GU σ 0 (hIw σ hσ)
    rw [pow_zero] at h0
    exact (genericStalkEquiv_fundamentalRep_of_deg_zero B₀ ξ hξ F hF σ _
      (h0.trans (Category.comp_id _)) w).trans
      (congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom (Ψ w))
        (hres _ _ (congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hσσ') _ _))
  refine ⟨Ψ.symm.toLinearMap ∘ₗ Sp, Ψ.symm.injective.comp hSp, fun w ↦ ?_, fun v ↦ ?_⟩
  · have hr := LinearMap.mem_range_linearEquiv_symm_comp_iff Ψ Sp w
    rw [hr, hSpr]
    constructor
    · intro h σ hσ
      apply Ψ.injective
      exact (hI (ofGal σ hσ) σ hσ rfl w).trans (h (ofGal σ hσ))
    · intro h σ
      exact (hI σ _ (hσI σ) rfl w).symm.trans (congrArg Ψ (h _ (hσI σ)))
  · have hQ (w) := genericStalkEquiv_fundamentalRep B₀ ξ hξ F hF _ _ hwF ha w
    exact LinearMap.linearEquiv_symm_comp_apply_of_intertwine Ψ Sp _ _ _ hSpf hQ v

/-- **The boundary stalk in the Weil fundamental representation.** Given a strictly henselian
neighbourhood of the boundary point `z` with closed point `x`, there is an injective linear map
from the boundary stalk `(j_* F)_x̄` to the Weil fundamental representation `F_t` (at the base
point data adapted to the geometric generic point), with image the invariants of the inertia
group `I_z`, intertwining the Frobenius of the stalk with the residue Frobenius lift at `z`.
(blueprint: `lemma-boundary-stalk--1`) -/
theorem exists_linearMap_stalk_directImage_fundamentalRep
    (B₀ : BasePointData (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU))
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint (U ↘ Spec (.of K)) j)
    (F : WeilSheaf K l U) (hF : F.IsLisse) (z : ↥((Set.range j.base)ᶜ)) (x : C.finitePoints)
    (hx : x.1 = z.1) (N : BoundaryNeighbourhoodAt j sU GU τ GC z x) :
    ∃ L : (((lowerStar j).obj F).stalk x).carrier →ₗ[PadicAlgCl l]
        LisseMonodromy.StalkSpace (BasePointData.ofLift j sU GU B₀ ξ hξ).t (F.toLisse hF),
      Function.Injective L ∧
      (∀ w, w ∈ LinearMap.range L ↔ ∀ g ∈ boundaryInertia (p := C ↘ Spec (.of K))
          (pU := U ↘ Spec (.of K)) j sU GU z,
        fundamentalRep M (BasePointData.ofLift j sU GU B₀ ξ hξ).weilMonodromyData F hF g w = w) ∧
      ∀ v, L ((((lowerStar j).obj F).stalk x).frobenius v) =
        fundamentalRep M (BasePointData.ofLift j sU GU B₀ ξ hξ).weilMonodromyData F hF
          (boundaryResidueFrobenius j sU GU (comp_over j _) τ GC z) (L v) := by
  have hwF : (genericGaloisMap j sU GU
      (boundaryFrobeniusLift (p := C ↘ Spec (.of K)) j sU GU τ GC z),
      Multiplicative.ofAdd ((C ↘ Spec (.of K)).degreeOver x.1 : ℤ)) ∈
        weilGroup (U ↘ Spec (.of K)) sU GU := by
    rw [hx]
    exact mem_weilGroup_boundaryFrobeniusLift j sU GU (comp_over j _) τ GC z
  obtain ⟨L, hL, hLr, hLf⟩ := exists_linearMap_stalk_directImage_fundamentalRep_of_neighbourhood
    j sU GU B₀ ξ hξ F hF x N
    (fun σ hσ ↦ genericGaloisMap_mem_weilGroup_of_mem_inertia j sU GU τ GC z hσ) hwF
  have hmemI (g : weilGroup (U ↘ Spec (.of K)) sU GU)
      (hg : g ∈ boundaryInertia (p := C ↘ Spec (.of K)) (pU := U ↘ Spec (.of K)) j sU GU z) :
      ∃ σ, ∃ hσ : σ ∈ (boundaryChart (p := C ↘ Spec (.of K)) j z).point.inertia
          Gal(Ω/C.functionField),
        g = ⟨_, genericGaloisMap_mem_weilGroup_of_mem_inertia j sU GU τ GC z hσ⟩ := by
    rw [boundaryInertia, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_ker] at hg
    obtain ⟨⟨σ, hσ, hσg⟩, hdeg⟩ := hg
    refine ⟨σ, hσ, Subtype.ext (Prod.ext ?_ ?_)⟩
    · exact hσg.symm
    · exact hdeg
  refine ⟨L, hL, fun w ↦ ?_, fun v ↦ ?_⟩
  · rw [hLr]
    constructor
    · intro h g hg
      obtain ⟨σ, hσ, rfl⟩ := hmemI g hg
      exact h σ hσ
    · intro h σ hσ
      exact h _ (mk_mem_boundaryInertia j sU GU z hσ _)
  · have hel : boundaryResidueFrobenius j sU GU (comp_over j _) τ GC z = ⟨_, hwF⟩ := by
      rw [boundaryResidueFrobenius_eq j sU GU (comp_over j _) τ GC z]
      exact Subtype.ext (Prod.ext rfl (congrArg (fun d : ℕ ↦ Multiplicative.ofAdd (d : ℤ))
        (congrArg (C ↘ Spec (.of K)).degreeOver hx.symm)))
    rw [hel]
    exact hLf v


/-- **The boundary stalk in the Weil fundamental representation, for a conjugated
neighbourhood.** Given a strictly henselian neighbourhood of the boundary point `z` with closed
point `x` for the inertia group of a translate `γ • Q` of the chosen point `Q` over `z` and the
conjugate `γ σ_F γ⁻¹` of the residue Frobenius lift, `γ` mapping to `T` in the Weil group, there
is an injective linear map from the boundary stalk `(j_* F)_x̄` to the Weil fundamental
representation `F_t`, with image the vectors fixed by `T I_z T⁻¹`, intertwining the Frobenius of
the stalk with `T Frob_z T⁻¹`.
(blueprint: `lemma-boundary-stalk--1`) -/
theorem exists_linearMap_stalk_directImage_fundamentalRep_conj
    (B₀ : BasePointData (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU))
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint (U ↘ Spec (.of K)) j)
    (F : WeilSheaf K l U) (hF : F.IsLisse) (z : ↥((Set.range j.base)ᶜ)) (x : C.finitePoints)
    (hx : x.1 = z.1) {γ : Gal(Ω/C.functionField)} {n : ℤ}
    (hγ : (genericGaloisMap j sU GU γ, Multiplicative.ofAdd n) ∈ weilGroup (U ↘ Spec (.of K)) sU GU)
    (N : BoundaryNeighbourhood (K := K) j
      ((γ • (boundaryChart (p := C ↘ Spec (.of K)) j z).point).inertia Gal(Ω/C.functionField))
      (γ * boundaryFrobeniusLift (p := C ↘ Spec (.of K)) j sU GU τ GC z * γ⁻¹) x) :
    ∃ L : (((lowerStar j).obj F).stalk x).carrier →ₗ[PadicAlgCl l]
        LisseMonodromy.StalkSpace (BasePointData.ofLift j sU GU B₀ ξ hξ).t (F.toLisse hF),
      Function.Injective L ∧
      (∀ w, w ∈ LinearMap.range L ↔ ∀ g ∈ boundaryInertia (p := C ↘ Spec (.of K))
          (pU := U ↘ Spec (.of K)) j sU GU z,
        fundamentalRep M (BasePointData.ofLift j sU GU B₀ ξ hξ).weilMonodromyData F hF
          ((⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) * g *
            (⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU)⁻¹) w = w) ∧
      ∀ v, L ((((lowerStar j).obj F).stalk x).frobenius v) =
        fundamentalRep M (BasePointData.ofLift j sU GU B₀ ξ hξ).weilMonodromyData F hF
          ((⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) *
            boundaryResidueFrobenius j sU GU (comp_over j _) τ GC z *
            (⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU)⁻¹) (L v) := by
  have hwF0 : (genericGaloisMap j sU GU
      (boundaryFrobeniusLift (p := C ↘ Spec (.of K)) j sU GU τ GC z),
      Multiplicative.ofAdd ((C ↘ Spec (.of K)).degreeOver x.1 : ℤ)) ∈
        weilGroup (U ↘ Spec (.of K)) sU GU := by
    rw [hx]
    exact mem_weilGroup_boundaryFrobeniusLift j sU GU (comp_over j _) τ GC z
  have hIw (σ : Gal(Ω/C.functionField))
      (hσ : σ ∈ (γ • (boundaryChart (p := C ↘ Spec (.of K)) j z).point).inertia
        Gal(Ω/C.functionField)) :
      (genericGaloisMap j sU GU σ, Multiplicative.ofAdd (0 : ℤ)) ∈
        weilGroup (U ↘ Spec (.of K)) sU GU := by
    have h0 := genericGaloisMap_mem_weilGroup_of_mem_inertia j sU GU τ GC z
      ((Ideal.mem_inertia_pointwise_smul_iff _ γ σ).1 hσ)
    have := ((⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) * ⟨_, h0⟩ *
      (⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU)⁻¹).2
    rwa [coe_mk_mul_mk_mul_inv j sU GU hγ h0, show γ * (γ⁻¹ * σ * γ) * γ⁻¹ = σ by group] at this
  have hwF : (genericGaloisMap j sU GU
      (γ * boundaryFrobeniusLift (p := C ↘ Spec (.of K)) j sU GU τ GC z * γ⁻¹),
      Multiplicative.ofAdd ((C ↘ Spec (.of K)).degreeOver x.1 : ℤ)) ∈
        weilGroup (U ↘ Spec (.of K)) sU GU := by
    have := ((⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) * ⟨_, hwF0⟩ *
      (⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU)⁻¹).2
    rwa [coe_mk_mul_mk_mul_inv j sU GU hγ hwF0] at this
  obtain ⟨L, hL, hLr, hLf⟩ := exists_linearMap_stalk_directImage_fundamentalRep_of_neighbourhood
    j sU GU B₀ ξ hξ F hF x N hIw hwF
  have hmemI (g : weilGroup (U ↘ Spec (.of K)) sU GU)
      (hg : g ∈ boundaryInertia (p := C ↘ Spec (.of K)) (pU := U ↘ Spec (.of K)) j sU GU z) :
      ∃ σ, ∃ hσ : σ ∈ (boundaryChart (p := C ↘ Spec (.of K)) j z).point.inertia
          Gal(Ω/C.functionField),
        g = ⟨_, genericGaloisMap_mem_weilGroup_of_mem_inertia j sU GU τ GC z hσ⟩ := by
    rw [boundaryInertia, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_ker] at hg
    obtain ⟨⟨σ, hσ, hσg⟩, hdeg⟩ := hg
    refine ⟨σ, hσ, Subtype.ext (Prod.ext ?_ ?_)⟩
    · exact hσg.symm
    · exact hdeg
  refine ⟨L, hL, fun w ↦ ?_, fun v ↦ ?_⟩
  · rw [hLr]
    constructor
    · intro h g hg
      obtain ⟨σ, hσ, rfl⟩ := hmemI g hg
      have hσ' : γ * σ * γ⁻¹ ∈ (γ • (boundaryChart (p := C ↘ Spec (.of K)) j z).point).inertia
          Gal(Ω/C.functionField) := by
        rw [Ideal.mem_inertia_pointwise_smul_iff, show γ⁻¹ * (γ * σ * γ⁻¹) * γ = σ by group]
        exact hσ
      have heq : (⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) *
          ⟨_, genericGaloisMap_mem_weilGroup_of_mem_inertia j sU GU τ GC z hσ⟩ *
          (⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU)⁻¹ = ⟨_, hIw _ hσ'⟩ :=
        Subtype.ext (coe_mk_mul_mk_mul_inv j sU GU hγ _)
      rw [heq]
      exact h _ hσ'
    · intro h σ hσ
      have hσ0 := (Ideal.mem_inertia_pointwise_smul_iff _ γ σ).1 hσ
      have heq : (⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) *
          ⟨_, genericGaloisMap_mem_weilGroup_of_mem_inertia j sU GU τ GC z hσ0⟩ *
          (⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU)⁻¹ = ⟨_, hIw σ hσ⟩ :=
        Subtype.ext ((coe_mk_mul_mk_mul_inv j sU GU hγ _).trans
          (by rw [show γ * (γ⁻¹ * σ * γ) * γ⁻¹ = σ by group]))
      rw [← heq]
      exact h _ (mk_mem_boundaryInertia j sU GU z hσ0 _)
  · have hel : (⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) *
        boundaryResidueFrobenius j sU GU (comp_over j _) τ GC z *
        (⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU)⁻¹ = ⟨_, hwF⟩ := by
      rw [boundaryResidueFrobenius_eq j sU GU (comp_over j _) τ GC z]
      exact Subtype.ext ((coe_mk_mul_mk_mul_inv j sU GU hγ _).trans
        (Prod.ext rfl (congrArg (fun d : ℕ ↦ Multiplicative.ofAdd (d : ℤ))
          (congrArg (C ↘ Spec (.of K)).degreeOver hx.symm))))
    rw [hel]
    exact hLf v
end Rep

include τ GC in
/-- Blueprint `lemma-boundary-stalk--1`, together with
`definition-weil-representation--1`.

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over `𝔽_q`, `U₀`
geometrically connected, with the boundary datum of actual inertia groups and residue Frobenius
lifts (`AlgebraicGeometry.WeilGroup.boundaryDatum`). Assume that every boundary point `z` has a
strictly henselian neighbourhood (`AlgebraicGeometry.WeilGroup.BoundaryNeighbourhood`). There is
a lisse sheaf–representation equivalence `ℱ ↦ (V, ρ)` for `W(U₀)`, identifying the stalk `ℱ_x̄`
with its local Frobenius with `V` with `ρ (Frob_x)` at the closed points of `U₀`, such that at
every boundary point `z` with closed point `x`, the boundary stalk `(j_* ℱ)_x̄` is isomorphic to
the inertia invariants `V ^ (I_z)`, the Frobenius of the stalk corresponding to the residue
Frobenius lift `ρ (Frob_z)`. -/
theorem exists_equivalence_isLisse_stalk_directImage_boundaryStalk
    (hN : ∀ (z : ↥((Set.range j.base)ᶜ)) (x : C.finitePoints), x.1 = z.1 →
      Nonempty (BoundaryNeighbourhoodAt j sU GU τ GC z x)) :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory ((ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse))
          (x : U.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) = (e.functor.obj F).obj.ρ
            ((ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).frobenius x) (f v)) ∧
      ∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse))
        (z : ↥((Set.range j.base)ᶜ)) (x : C.finitePoints), x.1 = z.1 →
        ∃ f : (((directImage j).obj F.obj).stalk x).carrier ≃ₗ[PadicAlgCl l]
            (boundaryDatum (p := C ↘ Spec (.of K)) j sU GU (comp_over j _) τ GC).boundaryStalk l
              (e.functor.obj F).obj.ρ z,
          ∀ v, (f ((((directImage j).obj F.obj).stalk x).frobenius v) :
              (e.functor.obj F).obj.V) =
            (e.functor.obj F).obj.ρ ((boundaryDatum (p := C ↘ Spec (.of K)) j sU GU
              (comp_over j _) τ GC).residueFrobenius z) (f v) := by
  have hjU : j ≫ C ↘ Spec (.of K) = U ↘ Spec (.of K) := comp_over j _
  have : SmoothOfRelativeDimension 1 (U ↘ Spec (.of K)) :=
    hjU ▸ (zero_add 1) ▸ (inferInstance : SmoothOfRelativeDimension (0 + 1) (j ≫ C ↘ Spec (.of K)))
  have : Smooth (U ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth 1 _
  have : ConnectedSpace (U ↘ Spec (.of K)).geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := U ↘ Spec (.of K))
      (Scheme.specAlgebraicClosure K).hom (U ↘ Spec (.of K)).geometricFiberProj
      (U ↘ Spec (.of K)).geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : Smooth (U ↘ Spec (.of K)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (U ↘ Spec (.of K)).geometricFiberToAlgebraicClosure
  set W := ofFundamentalGroup (U ↘ Spec (.of K)) sU GU
  obtain ⟨B₀⟩ := nonempty_basePointData W
  obtain ⟨ξ, hξ⟩ := exists_comp_eq_of_weaklyEtale_of_surjective (UniversalCover.proj B₀.t)
    (UniversalCover.surjective_proj B₀.t) (genericGeomPoint (U ↘ Spec (.of K)) j)
  set B := BasePointData.ofLift j sU GU B₀ ξ hξ
  obtain ⟨e, h₁, -, -, -, hf⟩ := exists_equivalence_isLisse_of_lisseMonodromy W l M B
    (universalLisseMonodromy_isEquivalenceAt l _ K B.t)
  refine ⟨e, h₁, fun F z x hx ↦ ?_⟩
  rw [show (directImage j : WeilSheaf K l U ⥤ WeilSheaf K l C) = lowerStar j from rfl]
  obtain ⟨f, hf⟩ := hf F
  obtain ⟨L, hL, hLr, hLf⟩ := exists_linearMap_stalk_directImage_fundamentalRep j sU GU τ GC
    B₀ ξ hξ F.obj F.property z x hx (hN z x hx).some
  set L' := f.symm.toLinearMap ∘ₗ L
  have hL' : Function.Injective L' := f.symm.injective.comp hL
  have hr : LinearMap.range L' =
      (boundaryDatum (p := C ↘ Spec (.of K)) j sU GU (comp_over j _) τ GC).boundaryStalk l
        (e.functor.obj F).obj.ρ z := by
    ext v
    rw [BoundaryDatum.boundaryStalk, Representation.mem_invariants]
    constructor
    · rintro ⟨w, rfl⟩ ⟨g, hg⟩
      apply f.injective
      simp only [L', LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.coe_comp,
        Function.comp_apply, Subgroup.coe_subtype]
      rw [hf, f.apply_symm_apply]
      exact (hLr _).1 ⟨w, rfl⟩ g hg
    · intro h
      obtain ⟨w, hw⟩ := (hLr (f v)).2 fun g hg ↦ by
        rw [← hf]
        exact congrArg f (h ⟨g, hg⟩)
      refine ⟨w, ?_⟩
      change f.symm (L w) = v
      rw [hw, LinearEquiv.symm_apply_apply]
  refine ⟨(LinearEquiv.ofInjective L' hL').trans (LinearEquiv.ofEq _ _ hr), fun v ↦ ?_⟩
  change L' _ = (e.functor.obj F).obj.ρ _ (L' v)
  change f.symm (L _) = (e.functor.obj F).obj.ρ _ (f.symm (L v))
  apply f.injective
  rw [hf, f.apply_symm_apply, f.apply_symm_apply]
  exact hLf v


include τ GC in
/-- Blueprint `lemma-boundary-stalk--1`, together with
`definition-weil-representation--1`, for conjugated neighbourhoods.

As `AlgebraicGeometry.WeilGroup.exists_equivalence_isLisse_stalk_directImage_boundaryStalk`, but
assuming at every boundary point `z` a strictly henselian neighbourhood for the inertia group of
a Galois translate `γ • Q` of the chosen point `Q` over `z` and the conjugate `γ σ_F γ⁻¹` of the
residue Frobenius lift, `γ` mapping into the Weil group: the boundary stalk `(j_* ℱ)_x̄` is
isomorphic to `V ^ (I_z)`, the Frobenius corresponding to `ρ (Frob_z)`. -/
theorem exists_equivalence_isLisse_stalk_directImage_boundaryStalk_of_conj
    (hN : ∀ (z : ↥((Set.range j.base)ᶜ)) (x : C.finitePoints), x.1 = z.1 →
      ∃ (γ : Gal(Ω/C.functionField)) (n : ℤ),
        (genericGaloisMap j sU GU γ, Multiplicative.ofAdd n) ∈
          weilGroup (U ↘ Spec (.of K)) sU GU ∧
        Nonempty (BoundaryNeighbourhood (K := K) j
          ((γ • (boundaryChart (p := C ↘ Spec (.of K)) j z).point).inertia
            Gal(Ω/C.functionField))
          (γ * boundaryFrobeniusLift (p := C ↘ Spec (.of K)) j sU GU τ GC z * γ⁻¹) x)) :
    ∃ e : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse) ≌
        ObjectProperty.FullSubcategory ((ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).isLisseRep l),
      (∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse))
          (x : U.finitePoints),
        ∃ f : (F.obj.stalk x).carrier ≃ₗ[PadicAlgCl l] (e.functor.obj F).obj.V,
          ∀ v, f ((F.obj.stalk x).frobenius v) = (e.functor.obj F).obj.ρ
            ((ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).frobenius x) (f v)) ∧
      ∀ (F : ObjectProperty.FullSubcategory (fun F : WeilSheaf K l U ↦ F.IsLisse))
        (z : ↥((Set.range j.base)ᶜ)) (x : C.finitePoints), x.1 = z.1 →
        ∃ f : (((directImage j).obj F.obj).stalk x).carrier ≃ₗ[PadicAlgCl l]
            (boundaryDatum (p := C ↘ Spec (.of K)) j sU GU (comp_over j _) τ GC).boundaryStalk l
              (e.functor.obj F).obj.ρ z,
          ∀ v, (f ((((directImage j).obj F.obj).stalk x).frobenius v) :
              (e.functor.obj F).obj.V) =
            (e.functor.obj F).obj.ρ ((boundaryDatum (p := C ↘ Spec (.of K)) j sU GU
              (comp_over j _) τ GC).residueFrobenius z) (f v) := by
  have hjU : j ≫ C ↘ Spec (.of K) = U ↘ Spec (.of K) := comp_over j _
  have : SmoothOfRelativeDimension 1 (U ↘ Spec (.of K)) :=
    hjU ▸ (zero_add 1) ▸ (inferInstance : SmoothOfRelativeDimension (0 + 1) (j ≫ C ↘ Spec (.of K)))
  have : Smooth (U ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth 1 _
  have : ConnectedSpace (U ↘ Spec (.of K)).geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := U ↘ Spec (.of K))
      (Scheme.specAlgebraicClosure K).hom (U ↘ Spec (.of K)).geometricFiberProj
      (U ↘ Spec (.of K)).geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : Smooth (U ↘ Spec (.of K)).geometricFiberToAlgebraicClosure :=
    inferInstanceAs (Smooth (Limits.pullback.snd _ _))
  have := IsRegular.of_smooth (U ↘ Spec (.of K)).geometricFiberToAlgebraicClosure
  set W := ofFundamentalGroup (U ↘ Spec (.of K)) sU GU
  obtain ⟨B₀⟩ := nonempty_basePointData W
  obtain ⟨ξ, hξ⟩ := exists_comp_eq_of_weaklyEtale_of_surjective (UniversalCover.proj B₀.t)
    (UniversalCover.surjective_proj B₀.t) (genericGeomPoint (U ↘ Spec (.of K)) j)
  set B := BasePointData.ofLift j sU GU B₀ ξ hξ
  obtain ⟨e, h₁, -, -, -, hf⟩ := exists_equivalence_isLisse_of_lisseMonodromy W l M B
    (universalLisseMonodromy_isEquivalenceAt l _ K B.t)
  refine ⟨e, h₁, fun F z x hx ↦ ?_⟩
  rw [show (directImage j : WeilSheaf K l U ⥤ WeilSheaf K l C) = lowerStar j from rfl]
  obtain ⟨f, hf⟩ := hf F
  obtain ⟨γ, n, hγ, ⟨N⟩⟩ := hN z x hx
  obtain ⟨L, hL, hLr, hLf⟩ := exists_linearMap_stalk_directImage_fundamentalRep_conj j sU GU τ GC
    B₀ ξ hξ F.obj F.property z x hx hγ N
  exact Representation.exists_linearEquiv_invariants_of_conj (e.functor.obj F).obj.ρ _ f hf
    (boundaryInertia (p := C ↘ Spec (.of K)) (pU := U ↘ Spec (.of K)) j sU GU z)
    (⟨_, hγ⟩ : weilGroup (U ↘ Spec (.of K)) sU GU)
    (boundaryResidueFrobenius j sU GU (comp_over j _) τ GC z) L hL hLr _ hLf
end AlgebraicGeometry.WeilGroup
