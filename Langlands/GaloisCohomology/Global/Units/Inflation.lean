import Langlands.GaloisCohomology.Global.Units.Capitulation
import Langlands.Cohomology.Profinite.InflationRestriction.Higher
import Langlands.Cohomology.Profinite.Dimension.Subgroup
import Langlands.GaloisCohomology.Local.Invariant

/-!
# Inflation from `G_S` to the absolute Galois group

For a continuous surjective homomorphism `f : G → P` of profinite groups which is a quotient map,
and a morphism `φ : B → A` identifying the `P`-module `B` with the invariants of `ker f` in `A`,
inflation-restriction holds for the map `map f φ` along `f` (`map_injective_of_isQuotientMap`,
`range_map_eq_ker_res_of_isQuotientMap`), provided the cohomology of `ker f` with coefficients `A`
vanishes in degrees `1, …, q - 1`.

Applied to the restriction `Gal(Ω/K) → G_S = Gal(K_S/K)` and the inclusion `K_Sˣ → Ωˣ` this gives
the inflation `maximalUnitsInflation n : Hⁿ(G_S, K_Sˣ) → Hⁿ(Gal(Ω/K), Ωˣ)`; in degree `2` it is
injective (Hilbert 90 for `Ω/K_S`) and its image is the kernel of the restriction to
`Gal(Ω/K_S)` (`maximalUnitsInflation_two_injective`, `mem_range_maximalUnitsInflation_two_iff`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory CategoryTheory.Limits Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain

universe u

noncomputable section

section Quotient

variable {k G P : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [T2Space P] (f : G →ₜ* P) (hf : Function.Surjective f) (hq : Topology.IsQuotientMap f)
  {B : Rep.{u} k P} [IsSmoothRep B] {A : Rep.{u} k G} [IsSmoothRep A] (φ : Rep.res (f : G →* P) B ⟶ A)
  (hφ : Function.Injective φ.hom)
  (hrange : ∀ a : A, (∀ s ∈ (f : G →* P).ker, A.ρ s a = a) → ∃ b, φ.hom b = a)

omit [CompactSpace G] [TotallyDisconnectedSpace G] [T2Space P] in
include hf hq hφ hrange in
/-- `map f φ` is the composite of an isomorphism and the inflation from `G ⧸ ker f`. -/
theorem exists_map_eq_iso_comp_infl (n : ℕ) :
    ∃ I : cohomology B n ⟶ cohomology (A.quotientToInvariants (f : G →* P).ker) n,
      IsIso I ∧ map f φ n = I ≫ infl A (f : G →* P).ker n := by
  set N := (f : G →* P).ker
  let e : G ⧸ N ≃* P := QuotientGroup.quotientKerEquivOfSurjective (f : G →* P) hf
  have he : Continuous e.toMonoidHom := by
    rw [(QuotientGroup.isQuotientMap_mk N).continuous_iff]
    exact f.continuous
  have he' : Continuous e.symm.toMonoidHom := by
    rw [hq.continuous_iff]
    have : (e.symm.toMonoidHom : P → G ⧸ N) ∘ f = QuotientGroup.mk := by
      funext g
      exact (MulEquiv.symm_apply_eq e).2 rfl
    rw [this]
    exact continuous_quot_mk
  have hmem : ∀ b : B, φ.hom b ∈ Representation.invariants (A.ρ.comp N.subtype) := by
    intro b s
    have hc := Rep.hom_comm_apply φ (s : G) b
    have hs : f (s : G) = 1 := s.2
    change φ.hom (B.ρ (f s) b) = A.ρ s (φ.hom b) at hc
    rw [hs, map_one, Module.End.one_apply] at hc
    exact hc.symm
  let ψl : B →ₗ[k] Representation.invariants (A.ρ.comp N.subtype) :=
    LinearMap.codRestrict _ φ.hom.toLinearMap hmem
  have hψ : Function.Bijective ψl := by
    refine ⟨fun b b' hb => hφ (congrArg Subtype.val hb), fun a => ?_⟩
    obtain ⟨b, hb⟩ := hrange a.1 fun s hs => a.2 ⟨s, hs⟩
    exact ⟨b, Subtype.ext hb⟩
  let ψ : Rep.res e.toMonoidHom B ⟶ A.quotientToInvariants N :=
    Rep.ofHom ⟨ψl, fun q => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      refine LinearMap.ext fun b => Subtype.ext ?_
      change φ.hom (B.ρ (f g) b) = A.ρ g (φ.hom b)
      exact Rep.hom_comm_apply φ g b⟩
  refine ⟨map ⟨e.toMonoidHom, he⟩ ψ n, isIso_map_of_mulEquiv e he he' ψ hψ n, ?_⟩
  rw [infl_eq, ← map_comp]
  exact map_congr _ _ (ContinuousMonoidHom.ext fun g => rfl) (fun b => rfl) n

include hf hq hφ hrange in
/-- Inflation along a quotient map is injective in degree `q` when the cohomology of the kernel
vanishes in degrees `1, …, q - 1`. -/
theorem map_injective_of_isQuotientMap {q : ℕ} (hq0 : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (cohomology (Rep.res (f : G →* P).ker.subtype A) i)) :
    Function.Injective (map f φ q).hom := by
  have hN : IsClosed ((f : G →* P).ker : Set G) := by
    have : ((f : G →* P).ker : Set G) = f ⁻¹' {1} := rfl
    rw [this]
    exact isClosed_singleton.preimage f.continuous
  obtain ⟨I, hI, hmap⟩ := exists_map_eq_iso_comp_infl f hf hq φ hφ hrange q
  rw [hmap, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact (infl_injective_of_isZero hN hq0 hA).comp
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

include hf hq hφ hrange in
/-- The image of inflation along a quotient map is the kernel of restriction to the kernel, when the
cohomology of the kernel vanishes in degrees `1, …, q - 1`. -/
theorem range_map_eq_ker_res_of_isQuotientMap {q : ℕ} (hq0 : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (cohomology (Rep.res (f : G →* P).ker.subtype A) i)) :
    LinearMap.range (map f φ q).hom = LinearMap.ker (res A (f : G →* P).ker q).hom := by
  have hN : IsClosed ((f : G →* P).ker : Set G) := by
    have : ((f : G →* P).ker : Set G) = f ⁻¹' {1} := rfl
    rw [this]
    exact isClosed_singleton.preimage f.continuous
  obtain ⟨I, hI, hmap⟩ := exists_map_eq_iso_comp_infl f hf hq φ hφ hrange q
  rw [← range_infl_eq_ker_res hN hq0 hA, hmap, ModuleCat.hom_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.2 ((ModuleCat.epi_iff_surjective _).1 inferInstance), Submodule.map_top]

end Quotient

section Maximal

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K)))

variable (K Ω) in
/-- The inclusion `K_Sˣ → Ωˣ`, a morphism of modules of `Gal(Ω/K)`. -/
abbrev maximalUnitsHom :
    Rep.res (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →* GaloisGroupUnramifiedOutside K Ω S)
      (unitsModule K (maximalUnramifiedOutside K Ω S)) ⟶ unitsModule K Ω :=
  unitsRestrictHom (maximalUnramifiedOutside K Ω S)

variable (K Ω) in
/-- Inflation `Hⁿ(G_S, K_Sˣ) → Hⁿ(Gal(Ω/K), Ωˣ)`. -/
def maximalUnitsInflation (n : ℕ) :
    cohomology (unitsModule K (maximalUnramifiedOutside K Ω S)) n →+ cohomology (unitsModule K Ω) n :=
  (map (GaloisGroupUnramifiedOutside.quotientMap K Ω S) (maximalUnitsHom K Ω S) n).hom.toAddMonoidHom

theorem maximalUnitsInflation_apply (n : ℕ)
    (x : cohomology (unitsModule K (maximalUnramifiedOutside K Ω S)) n) :
    maximalUnitsInflation K Ω S n x = (map (GaloisGroupUnramifiedOutside.quotientMap K Ω S) (maximalUnitsHom K Ω S) n).hom x :=
  rfl

theorem mem_ker_quotientMap_iff (σ : Gal(Ω/K)) :
    σ ∈ (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →* GaloisGroupUnramifiedOutside K Ω S).ker ↔
      ∀ x ∈ maximalUnramifiedOutside K Ω S, σ x = x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x hx
    have h' : GaloisGroupUnramifiedOutside.quotientMap K Ω S σ = 1 := h
    have := GaloisGroupUnramifiedOutside.quotientMap_apply (S := S) σ ⟨x, hx⟩
    rw [h'] at this
    exact this.symm
  · intro h
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change ((GaloisGroupUnramifiedOutside.quotientMap K Ω S σ x : maximalUnramifiedOutside K Ω S) :
      Ω) = x
    rw [GaloisGroupUnramifiedOutside.quotientMap_apply]
    exact h x x.2

theorem maximalUnitsHom_injective : Function.Injective (maximalUnitsHom K Ω S).hom :=
  fun _ _ h => Additive.toMul.injective (Units.ext (Subtype.ext (congrArg (fun y : Additive Ωˣ =>
    ((Additive.toMul y : Ωˣ) : Ω)) h)))

theorem exists_maximalUnitsHom_eq (a : unitsModule K Ω)
    (ha : ∀ s ∈ (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →* GaloisGroupUnramifiedOutside K Ω S).ker,
      (unitsModule K Ω).ρ s a = a) :
    ∃ b, (maximalUnitsHom K Ω S).hom b = a := by
  set y : Ωˣ := Additive.toMul a
  have hfix : ∀ σ ∈ (maximalUnramifiedOutside K Ω S).fixingSubgroup, σ (y : Ω) = (y : Ω) := by
    intro σ hσ
    have hσ' : σ ∈ (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →* GaloisGroupUnramifiedOutside K Ω S).ker :=
      (mem_ker_quotientMap_iff S σ).2 fun x hx =>
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx
    have := congrArg (fun z : Additive Ωˣ => ((Additive.toMul z : Ωˣ) : Ω)) (ha σ hσ')
    exact this
  have hmem : (y : Ω) ∈ maximalUnramifiedOutside K Ω S := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (maximalUnramifiedOutside K Ω S)]
    exact fun σ => hfix σ σ.2
  have hmem' : ((y⁻¹ : Ωˣ) : Ω) ∈ maximalUnramifiedOutside K Ω S := by
    rw [Units.val_inv_eq_inv_val]
    exact inv_mem hmem
  refine ⟨Additive.ofMul ⟨⟨_, hmem⟩, ⟨_, hmem'⟩, Subtype.ext y.mul_inv, Subtype.ext y.inv_mul⟩, ?_⟩
  rfl

/-- Hilbert 90 for the closed subgroup `Gal(Ω/K_S)` of `Gal(Ω/K)`. -/
theorem isZero_cohomology_one_ker_quotientMap :
    IsZero (cohomology (Rep.res (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →*
      GaloisGroupUnramifiedOutside K Ω S).ker.subtype (unitsModule K Ω)) 1) := by
  have hc : CompactSpace Gal(Ω/K) := galois_compactSpace _ _
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y => ?_⟩
  suffices h : ∀ x : cohomology (Rep.res (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →*
      GaloisGroupUnramifiedOutside K Ω S).ker.subtype (unitsModule K Ω)) 1, x = 0 from
    (h x).trans (h y).symm
  intro x
  have hN : IsClosed (((GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →* GaloisGroupUnramifiedOutside K Ω S).ker :
      Subgroup Gal(Ω/K)) : Set Gal(Ω/K)) := by
    have : (((GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →* GaloisGroupUnramifiedOutside K Ω S).ker :
        Subgroup Gal(Ω/K)) : Set Gal(Ω/K)) = GaloisGroupUnramifiedOutside.quotientMap K Ω S ⁻¹' {1} := rfl
    rw [this]
    have : T1Space (GaloisGroupUnramifiedOutside K Ω S) :=
      @T2Space.t1Space _ _ (GaloisGroupUnramifiedOutside.t2Space K Ω S)
    exact isClosed_singleton.preimage (GaloisGroupUnramifiedOutside.quotientMap K Ω S).continuous
  obtain ⟨U, hU, hNU, y, rfl⟩ := exists_resOfLE_eq (unitsModule K Ω) hN 1 x
  have hy : y = 0 := (ModuleCat.subsingleton_of_isZero
    (isZero_cohomology_one_res_unitsModule (⟨U, hU⟩ : OpenSubgroup Gal(Ω/K)))).elim _ _
  rw [hy, map_zero]

/-- Inflation `H²(G_S, K_Sˣ) → H²(Gal(Ω/K), Ωˣ)` is injective. -/
theorem maximalUnitsInflation_two_injective :
    Function.Injective (maximalUnitsInflation K Ω S 2) := by
  have : CompactSpace Gal(Ω/K) := galois_compactSpace _ _
  refine map_injective_of_isQuotientMap (GaloisGroupUnramifiedOutside.quotientMap K Ω S) (GaloisGroupUnramifiedOutside.quotientMap_surjective K Ω S)
    (GaloisGroupUnramifiedOutside.isQuotientMap_quotientMap K Ω S) _ (maximalUnitsHom_injective S) (exists_maximalUnitsHom_eq S)
    (by norm_num) fun i hi hi2 => ?_
  have : i = 1 := by omega
  subst this
  exact isZero_cohomology_one_ker_quotientMap S

/-- A class of `H²(Gal(Ω/K), Ωˣ)` is inflated from `G_S` exactly when its restriction to
`Gal(Ω/K_S)` vanishes. -/
theorem mem_range_maximalUnitsInflation_two_iff (x : cohomology (unitsModule K Ω) 2) :
    x ∈ (maximalUnitsInflation K Ω S 2).range ↔
      (res (unitsModule K Ω) (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →*
        GaloisGroupUnramifiedOutside K Ω S).ker 2).hom x = 0 := by
  have : CompactSpace Gal(Ω/K) := galois_compactSpace _ _
  have h := range_map_eq_ker_res_of_isQuotientMap (GaloisGroupUnramifiedOutside.quotientMap K Ω S)
    (GaloisGroupUnramifiedOutside.quotientMap_surjective K Ω S) (GaloisGroupUnramifiedOutside.isQuotientMap_quotientMap K Ω S) _ (maximalUnitsHom_injective S)
    (exists_maximalUnitsHom_eq S) (q := 2) (by norm_num) fun i hi hi2 => by
      have : i = 1 := by omega
      subst this
      exact isZero_cohomology_one_ker_quotientMap S
  have := SetLike.ext_iff.1 h x
  rw [LinearMap.mem_range, LinearMap.mem_ker] at this
  rw [AddMonoidHom.mem_range, ← this]
  rfl

/-- Restriction to `Gal(Ω/K_S)`, read as a subgroup of `Gal(Ω/K)` or as the Galois group of `Ω` over
`K_S`: a class whose restriction to the Galois group of `Ω / K_S` vanishes restricts to zero on the
kernel of `Gal(Ω/K) → G_S`. -/
theorem res_ker_quotientMap_eq_zero (x : cohomology (unitsModule K Ω) 2)
    (hx : haveI : IsGalois (maximalUnramifiedOutside K Ω S) Ω :=
      IsGalois.tower_top_of_isGalois K (maximalUnramifiedOutside K Ω S) Ω
      (unitsRestriction K (maximalUnramifiedOutside K Ω S) Ω 2).hom x = 0) :
    (res (unitsModule K Ω) (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →*
      GaloisGroupUnramifiedOutside K Ω S).ker 2).hom x = 0 := by
  have : IsGalois (maximalUnramifiedOutside K Ω S) Ω :=
    IsGalois.tower_top_of_isGalois K (maximalUnramifiedOutside K Ω S) Ω
  set N := (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →*
    GaloisGroupUnramifiedOutside K Ω S).ker
  have hmemN : ∀ σ : Gal(Ω/maximalUnramifiedOutside K Ω S),
      (AlgEquiv.restrictScalarsHom K σ : Gal(Ω/K)) ∈ N := fun σ =>
    (mem_ker_quotientMap_iff S _).2 fun y hy => by
      change σ y = y
      exact σ.commutes ⟨y, hy⟩
  let e : Gal(Ω/maximalUnramifiedOutside K Ω S) ≃* N :=
    { toFun := fun σ => ⟨AlgEquiv.restrictScalarsHom K σ, hmemN σ⟩
      invFun := fun τ => { (τ.1 : Ω ≃ₐ[K] Ω) with
        commutes' := fun c => (mem_ker_quotientMap_iff S τ.1).1 τ.2 c c.2 }
      left_inv := fun σ => AlgEquiv.ext fun _ => rfl
      right_inv := fun τ => Subtype.ext (AlgEquiv.ext fun _ => rfl)
      map_mul' := fun _ _ => rfl }
  have he : Continuous e.toMonoidHom :=
    ((BrauerComparison.krullRestrictScalars K (maximalUnramifiedOutside K Ω S) Ω).continuous).subtype_mk _
  have : CompactSpace Gal(Ω/maximalUnramifiedOutside K Ω S) := galois_compactSpace _ _
  have : T2Space Gal(Ω/K) := galois_t2Space _ _
  have he' : Continuous e.symm.toMonoidHom := by
    let h := he.homeoOfEquivCompactToT2 (f := e.toEquiv)
    exact h.symm.continuous
  let f : Rep.res e.toMonoidHom (Rep.res N.subtype (unitsModule K Ω)) ⟶
      unitsModule (maximalUnramifiedOutside K Ω S) Ω :=
    Rep.ofHom ⟨LinearMap.id, fun σ => rfl⟩
  have hiso := isIso_map_of_mulEquiv (A := Rep.res N.subtype (unitsModule K Ω))
    (B := unitsModule (maximalUnramifiedOutside K Ω S) Ω) e he he' f (by exact Function.bijective_id) 2
  have hinj : Function.Injective (map ⟨e.toMonoidHom, he⟩ f 2).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [map_zero, ← hx]
  have h1 := congrArg (fun F => F.hom x) (map_comp (subgroupInclusion N)
    (𝟙 (Rep.res N.subtype (unitsModule K Ω))) ⟨e.toMonoidHom, he⟩ f 2)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h1
  rw [res_eq, ← h1, unitsRestriction]
  have hgrp : (subgroupInclusion N).comp
      (⟨e.toMonoidHom, he⟩ : Gal(Ω/maximalUnramifiedOutside K Ω S) →ₜ* N) =
      BrauerComparison.krullRestriction K (maximalUnramifiedOutside K Ω S) Ω Ω :=
    ContinuousMonoidHom.ext fun σ => AlgEquiv.ext fun y => by
      rw [krullRestriction_self_apply]
      rfl
  refine congrArg (fun F => F.hom x) (map_congr _
    (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients K
      (maximalUnramifiedOutside K Ω S) Ω Ω)) hgrp (fun a => ?_) 2)
  exact Additive.toMul.injective (Units.ext rfl)

/-- If a class dies in a subextension `E ⊆ K_S`, it dies in `K_S`. -/
theorem unitsRestriction_maximal_eq_zero [IsSepClosure K Ω] (E : IntermediateField K Ω)
    (hE : E ≤ maximalUnramifiedOutside K Ω S) (x : cohomology (unitsModule K Ω) 2)
    (hx : brauerRestriction E x = 0) :
    haveI : IsGalois (maximalUnramifiedOutside K Ω S) Ω :=
      IsGalois.tower_top_of_isGalois K (maximalUnramifiedOutside K Ω S) Ω
    (unitsRestriction K (maximalUnramifiedOutside K Ω S) Ω 2).hom x = 0 := by
  have : IsGalois (maximalUnramifiedOutside K Ω S) Ω :=
    IsGalois.tower_top_of_isGalois K (maximalUnramifiedOutside K Ω S) Ω
  have : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  let : Algebra E (maximalUnramifiedOutside K Ω S) := (IntermediateField.inclusion hE).toRingHom.toAlgebra
  have : IsScalarTower E (maximalUnramifiedOutside K Ω S) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 := congrArg (fun F => F.hom x) (map_comp (BrauerComparison.krullRestriction K E Ω Ω)
    (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients K E Ω Ω))
    (BrauerComparison.krullRestriction E (maximalUnramifiedOutside K Ω S) Ω Ω)
    (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients E
      (maximalUnramifiedOutside K Ω S) Ω Ω)) 2)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h1
  have hx' : (unitsRestriction K E Ω 2).hom x = 0 := hx
  change (map _ _ 2).hom x = 0
  have h2 : (map (BrauerComparison.krullRestriction E (maximalUnramifiedOutside K Ω S) Ω Ω)
      (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients E
        (maximalUnramifiedOutside K Ω S) Ω Ω)) 2).hom ((unitsRestriction K E Ω 2).hom x) = 0 := by
    rw [hx']
    exact map_zero _
  have h1' : (map ((BrauerComparison.krullRestriction K E Ω Ω).comp
        (BrauerComparison.krullRestriction E (maximalUnramifiedOutside K Ω S) Ω Ω))
      ((Rep.resFunctor (BrauerComparison.krullRestriction E (maximalUnramifiedOutside K Ω S) Ω Ω :
        Gal(Ω/maximalUnramifiedOutside K Ω S) →* Gal(Ω/E))).map
        (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients K E Ω Ω)) ≫
        underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients E
          (maximalUnramifiedOutside K Ω S) Ω Ω)) 2).hom x =
      (map (BrauerComparison.krullRestriction E (maximalUnramifiedOutside K Ω S) Ω Ω)
        (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients E
          (maximalUnramifiedOutside K Ω S) Ω Ω)) 2).hom ((unitsRestriction K E Ω 2).hom x) := h1
  rw [← h1'] at h2
  refine Eq.trans ?_ h2
  have hgrp : BrauerComparison.krullRestriction K (maximalUnramifiedOutside K Ω S) Ω Ω =
      (BrauerComparison.krullRestriction K E Ω Ω).comp
        (BrauerComparison.krullRestriction E (maximalUnramifiedOutside K Ω S) Ω Ω) :=
    ContinuousMonoidHom.ext fun σ => AlgEquiv.ext fun y => by
      rw [krullRestriction_self_apply]
      change σ y = BrauerComparison.krullRestriction K E Ω Ω
        (BrauerComparison.krullRestriction E (maximalUnramifiedOutside K Ω S) Ω Ω σ) y
      rw [krullRestriction_self_apply, krullRestriction_self_apply]
  refine congrArg (fun F => F.hom x) (map_congr
    (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients K
      (maximalUnramifiedOutside K Ω S) Ω Ω)) _ hgrp (fun a => ?_) 2)
  exact Additive.toMul.injective (Units.ext rfl)

/-- A class of `H²(Gal(Ω/K), Ωˣ)` which dies in a subextension of `K_S` is inflated from `G_S`. -/
theorem exists_maximalUnitsInflation_eq [IsSepClosure K Ω] (E : IntermediateField K Ω)
    (hE : E ≤ maximalUnramifiedOutside K Ω S) (x : cohomology (unitsModule K Ω) 2)
    (hx : brauerRestriction E x = 0) : ∃ z, maximalUnitsInflation K Ω S 2 z = x :=
  (mem_range_maximalUnitsInflation_two_iff S x).2
    (res_ker_quotientMap_eq_zero S x (unitsRestriction_maximal_eq_zero S E hE x hx))

end Maximal

end

end Langlands.GaloisCohomology
