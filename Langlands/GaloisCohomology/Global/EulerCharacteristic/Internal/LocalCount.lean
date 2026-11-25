import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.BaseDegrees
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.PlaceCount
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Corollaries
import Langlands.GaloisCohomology.Local.Duality.Main

/-!
# The dual module and the local terms in Tate's base case

In the situation of Tate's base case (`L ⊆ K_S` Galois over `K` of degree prime to `ℓ`, `μ_ℓ ⊆ L`,
`M` killed by `ℓ` and trivial on `G_S(L)`), with `N = Hom(μ_ℓ, M)` as a representation of
`Γ = Gal(L/K)`:

* `#H⁰(G_S, M') = ℓ^{dim N^Γ}` for `M' = Hom(M, μ_ℓ)` (`card_cohomology_zero_dual`): `H⁰(G_S, M')` is
  `Hom_Γ(M, μ_ℓ)`, which has the dimension of `Hom_Γ(μ_ℓ, M) = N^Γ` because `#Γ` is prime to `ℓ`
  (`finrank_invariants_linHom_comp_line`);
* `#H²(K_v, M) = ℓ^{dim N^{D_v}}` at a finite place `v` (`card_cohomology_two_localModule`), by
  local duality `#H²(K_v, M) = #H⁰(K_v, M^∨)` (Cartier dual) and the same comparison for the
  decomposition group `D_v`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  Langlands.GaloisCohomology.Local Representation Module

universe u

noncomputable section

section Generic

variable {k : Type u} [Field k] {Γ : Type*} [Group Γ] [Finite Γ] {H₀ : Type*} [Group H₀]
  {T A : Type u} [AddCommGroup T] [Module k T] [AddCommGroup A] [Module k A]
  (ρT : Representation k Γ T) (ρA : Representation k Γ A)

omit [Finite Γ] in
theorem linHom_comp (φ : H₀ →* Γ) : linHom (ρA.comp φ) (ρT.comp φ) = (linHom ρA ρT).comp φ := by
  ext g f x
  simp [linHom_apply, map_inv]

variable [FiniteDimensional k T] [FiniteDimensional k A]

/-- **Homomorphisms to and from `T` through a finite quotient.** For `q : H₀ → Γ` with image `D` of
order invertible in `k` and `T` of dimension one: `dim Hom_{H₀}(A, T) = dim Hom_D(T, A)`. -/
theorem finrank_invariants_linHom_comp_line (q : H₀ →* Γ) (hT1 : finrank k T = 1)
    (hD : ((Nat.card q.range : ℕ) : k) ≠ 0) :
    finrank k (linHom (ρA.comp q) (ρT.comp q)).invariants =
      finrank k (Representation.invariants ((linHom ρT ρA).comp q.range.subtype)) := by
  classical
  have := Fintype.ofFinite q.range
  have : Invertible (Fintype.card q.range : k) :=
    invertibleOfNonzero (by rwa [← Nat.card_eq_fintype_card])
  have hq : linHom (ρA.comp q) (ρT.comp q) =
      ((linHom ρA ρT).comp q.range.subtype).comp q.rangeRestrict := by
    rw [linHom_comp]
    rfl
  rw [hq, invariants_comp_of_surjective _ _ q.rangeRestrict_surjective]
  have h1 := finrank_invariants_linHom_line (ρT.comp q.range.subtype) (ρA.comp q.range.subtype) hT1
  rw [linHom_comp, linHom_comp] at h1
  exact h1

end Generic

section Linear

attribute [local instance 2000] Rep.hV2

variable {G : Type u} [Group G] (ℓ : ℕ) (A D : Rep.{u} (ULift.{u} ℤ) G) (hA : ∀ a : A, ℓ • a = 0)
  (hD : ∀ d : D, ℓ • d = 0)

/-- An additive map between modules over `ULift (ZMod ℓ)` is linear. -/
def zmodLinearOfAddHom {X Y : Type*} [AddCommGroup X] [Module (ULift.{u} (ZMod ℓ)) X] [AddCommGroup Y]
    [Module (ULift.{u} (ZMod ℓ)) Y] (φ : X →+ Y) : X →ₗ[ULift.{u} (ZMod ℓ)] Y :=
  { φ with
    map_smul' := fun c x => by
      change φ (c • x) = c • φ x
      rw [ulift_zmod_smul_eq_zsmul, ulift_zmod_smul_eq_zsmul, map_zsmul] }

/-- A `ℤ`-linear map between modules killed by `ℓ` is `𝔽_ℓ`-linear. -/
def zmodLinearOfIntLinear (f : A →ₗ[ULift.{u} ℤ] D) :
    zmodRepOfTorsion ℓ A hA →ₗ[ULift.{u} (ZMod ℓ)] zmodRepOfTorsion ℓ D hD :=
  zmodLinearOfAddHom ℓ (X := zmodRepOfTorsion ℓ A hA) (Y := zmodRepOfTorsion ℓ D hD)
    f.toAddMonoidHom

/-- The morphisms `A → D` of modules killed by `ℓ` are the invariant `𝔽_ℓ`-linear maps. -/
def homEquivInvariants :
    (A ⟶ D) ≃ (linHom (zmodRepOfTorsion ℓ A hA).ρ (zmodRepOfTorsion ℓ D hD).ρ).invariants where
  toFun f := ⟨zmodLinearOfIntLinear ℓ A D hA hD f.hom.toLinearMap, fun g =>
    LinearMap.ext fun a => by
      have h : ∀ x : A, A.ρ g (A.ρ g⁻¹ x) = x := fun x => by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      change D.ρ g (f.hom (A.ρ g⁻¹ a)) = f.hom a
      rw [← Rep.hom_comm_apply]
      exact congrArg f.hom (h a)⟩
  invFun f := Rep.ofHom ⟨(uliftIntLinearEquivAddHom A D).symm f.1.toAddMonoidHom,
    fun g => LinearMap.ext fun a => by
      have h : ∀ x : A, A.ρ g⁻¹ (A.ρ g x) = x := fun x => by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      have := LinearMap.congr_fun (f.2 g) (A.ρ g a)
      change D.ρ g (f.1 (A.ρ g⁻¹ (A.ρ g a))) = f.1 (A.ρ g a) at this
      rw [h] at this
      exact this.symm⟩
  left_inv f := rfl
  right_inv f := rfl

end Linear

section Twist

attribute [local instance 2000] Rep.hV2

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (P : OpenSubgroup G) [(P : Subgroup G).Normal] [CompactSpace (P : Subgroup G)]
  {Γ : Type u} [Group Γ] [Finite Γ] (e : G ⧸ (P : Subgroup G) ≃* Γ) (ℓ : ℕ) [Fact ℓ.Prime]
  (T M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep T] [IsSmoothRep M] [Finite T] [Finite M]
  (hTℓ : ∀ t : T, ℓ • t = 0) (hMℓ : ∀ m : M, ℓ • m = 0)
  (hT : ∀ (g : (P : Subgroup G)) (t : T), T.ρ g t = t)
  (hM : ∀ (g : (P : Subgroup G)) (m : M), M.ρ g m = m)
  (hTr : Module.finrank (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ T hTℓ) = 1)
  (hΓ : Nat.Coprime (Nat.card Γ) ℓ)

/-- A module of `G` trivial on `P`, over `𝔽_ℓ`, as a representation of `Γ ≅ G/P`. -/
def quotRepZMod (A : Rep.{u} (ULift.{u} ℤ) G) (hAℓ : ∀ a : A, ℓ • a = 0)
    (hA : ∀ (g : (P : Subgroup G)) (a : A), A.ρ g a = a) :
    Representation (ULift.{u} (ZMod ℓ)) Γ (zmodRepOfTorsion ℓ A hAℓ) :=
  (quotientRep (P : Subgroup G) (zmodRepOfTorsion ℓ A hAℓ) hA).comp e.symm.toMonoidHom

/-- The surjection `G → G/P ≅ Γ`. -/
def quotHom : G →* Γ := e.toMonoidHom.comp (QuotientGroup.mk' (P : Subgroup G))

omit [IsTopologicalGroup G] [CompactSpace G] [CompactSpace (P : Subgroup G)] [Finite Γ] in
theorem quotRepZMod_comp (A : Rep.{u} (ULift.{u} ℤ) G) (hAℓ : ∀ a : A, ℓ • a = 0)
    (hA : ∀ (g : (P : Subgroup G)) (a : A), A.ρ g a = a) :
    (quotRepZMod P e ℓ A hAℓ hA).comp (quotHom P e) = (zmodRepOfTorsion ℓ A hAℓ).ρ := by
  ext g a
  change quotientRep (P : Subgroup G) (zmodRepOfTorsion ℓ A hAℓ) hA
    (e.symm (e (QuotientGroup.mk g))) a = _
  rw [MulEquiv.symm_apply_apply]
  rfl

omit [IsTopologicalGroup G] [CompactSpace G] [CompactSpace (P : Subgroup G)] [Finite Γ] in
theorem zmodRepOfTorsion_res_eq {H₀ : Type u} [Group H₀] (φ : H₀ →* G) (A : Rep.{u} (ULift.{u} ℤ) G)
    (hAℓ : ∀ a : A, ℓ • a = 0) (hA : ∀ (g : (P : Subgroup G)) (a : A), A.ρ g a = a) :
    (zmodRepOfTorsion ℓ (Rep.res φ A) fun a => hAℓ a).ρ =
      (quotRepZMod P e ℓ A hAℓ hA).comp ((quotHom P e).comp φ) := by
  ext h a
  change A.ρ (φ h) a = quotientRep (P : Subgroup G) (zmodRepOfTorsion ℓ A hAℓ) hA
    (e.symm (e (QuotientGroup.mk (φ h)))) a
  rw [MulEquiv.symm_apply_apply]
  rfl

omit [IsTopologicalGroup G] [CompactSpace G] [CompactSpace (P : Subgroup G)] [Finite Γ]
  [IsSmoothRep T] [IsSmoothRep M] [Finite T] [Finite M] in
theorem linHom_quotRepZMod :
    linHom (quotRepZMod P e ℓ T hTℓ hT) (quotRepZMod P e ℓ M hMℓ hM) =
      twistRep P e ℓ T M hTℓ hMℓ hT hM := by
  ext γ f t
  obtain ⟨q, rfl⟩ := e.surjective γ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [twistRep_apply, linHom_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← map_inv,
    ← QuotientGroup.mk_inv]
  simp only [quotRepZMod, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

include hTr hΓ in
omit [IsTopologicalGroup G] [CompactSpace G] [CompactSpace (P : Subgroup G)] [IsSmoothRep T]
  [IsSmoothRep M] in
/-- **Invariant homomorphisms into `μ_ℓ`.** For a group `H₀` mapping to `G` through `φ` with image
`D` in `Γ`: `#Hom_{H₀}(M, T) = ℓ^{dim Hom(T, M)^D}`. -/
theorem card_hom_res_eq_pow {H₀ : Type u} [Group H₀] (φ : H₀ →* G) :
    Nat.card (Rep.res φ M ⟶ Rep.res φ T) = ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ))
      (Representation.invariants ((twistRep P e ℓ T M hTℓ hMℓ hT hM).comp
        ((quotHom P e).comp φ).range.subtype)) := by
  have hl : ℓ.Prime := Fact.out
  have : Finite (zmodRepOfTorsion ℓ M hMℓ) := inferInstanceAs (Finite M)
  have : Finite (zmodRepOfTorsion ℓ T hTℓ) := inferInstanceAs (Finite T)
  have : FiniteDimensional (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ M hMℓ) := Module.Finite.of_finite
  have : FiniteDimensional (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ T hTℓ) := Module.Finite.of_finite
  rw [Nat.card_congr (homEquivInvariants ℓ (Rep.res φ M) (Rep.res φ T) (fun a => hMℓ a)
    (fun t => hTℓ t))]
  have : Finite ((zmodRepOfTorsion ℓ (Rep.res φ M) fun a => hMℓ a) →ₗ[ULift.{u} (ZMod ℓ)]
      (zmodRepOfTorsion ℓ (Rep.res φ T) fun t => hTℓ t)) := by
    have : Finite (zmodRepOfTorsion ℓ (Rep.res φ M) fun a => hMℓ a) := inferInstanceAs (Finite M)
    have : Finite (zmodRepOfTorsion ℓ (Rep.res φ T) fun t => hTℓ t) := inferInstanceAs (Finite T)
    exact Finite.of_injective _ DFunLike.coe_injective
  have : Finite (linHom (zmodRepOfTorsion ℓ (Rep.res φ M) fun a => hMℓ a).ρ
      (zmodRepOfTorsion ℓ (Rep.res φ T) fun t => hTℓ t).ρ).invariants :=
    Subtype.finite
  rw [natCard_eq_pow_finrank_zmod ℓ]
  congr 1
  have hD : ((Nat.card ((quotHom P e).comp φ).range : ℕ) : ULift.{u} (ZMod ℓ)) ≠ 0 := by
    intro h0
    have h0' : ((Nat.card ((quotHom P e).comp φ).range : ℕ) : ZMod ℓ) = 0 := congrArg ULift.down h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    have hdvd := Subgroup.card_subgroup_dvd_card ((quotHom P e).comp φ).range
    exact (Nat.Prime.coprime_iff_not_dvd hl).1 hΓ.symm (dvd_trans h0' hdvd)
  have h := finrank_invariants_linHom_comp_line (quotRepZMod P e ℓ T hTℓ hT)
    (quotRepZMod P e ℓ M hMℓ hM) ((quotHom P e).comp φ) hTr hD
  rw [linHom_quotRepZMod] at h
  rw [← h, zmodRepOfTorsion_res_eq P e ℓ φ M hMℓ hM, zmodRepOfTorsion_res_eq P e ℓ φ T hTℓ hT]
  rfl

end Twist

end

end Langlands.GaloisCohomology
