import Langlands.AlgebraicGeometry.FiniteEtale.KummerCyclicAlgebra
import Langlands.AlgebraicGeometry.FiniteEtale.KummerCyclicCover
import Langlands.CommutativeAlgebra.KummerEigenvector
import Langlands.CommutativeAlgebra.RegularLocalAwayPicardProof
import Langlands.CommutativeAlgebra.RegularLocalFactorialTools

/-! # Cyclic quotients of order `ℓ` of `π₁(Spec R[1/t])` are Kummer

Let `R` be a strictly Henselian regular local domain, `t` a regular parameter and `ℓ` a prime
invertible in `R`. This module defines the Kummer character of level `m` of `t`, the character
of `π₁(Spec R[1/t], x)` describing the action on the geometric fibre of
`Spec R[1/t][X]/(X^m - t)`. It proves that the kernel of every surjective homomorphism with
open kernel from `π₁(Spec R[1/t], x)` onto the `ℓ`-th roots of unity of `R` is contained in the
kernel of the Kummer character of level `ℓ`, and that this Kummer character is nontrivial.
The proof realizes the homomorphism by a cover with an action of the roots of unity, finds a
unit eigenvector of a generator in the ring of the cover (the Picard group of `R[1/t]` is
trivial), and maps the cover equivariantly to a Kummer cover of parameter `1` or `t`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.AlgebraicGeometry.FiniteEtale

section CoverHom

variable {A : Type u} [CommRing A] {C : Type u} [Group C]
  (D : SingleObj C ⥤ Cover (Spec (.of A)))

/-- The ring map `A → Γ(Y, ⊤)` of the cover `Y` carried by a diagram `D` over `Spec A`. -/
def coverBaseHom : A →+* coverRing D :=
  (algebraMap Γ(Spec (.of A), ⊤) (coverRing D)).comp (Scheme.ΓSpecIso (.of A)).inv.hom

theorem coverBaseHom_ΓSpecIso_hom (r : Γ(Spec (.of A), ⊤)) :
    coverBaseHom D ((Scheme.ΓSpecIso (.of A)).hom.hom r) =
      algebraMap Γ(Spec (.of A), ⊤) (coverRing D) r := by
  change algebraMap Γ(Spec (.of A), ⊤) (coverRing D)
    (((Scheme.ΓSpecIso (.of A)).hom ≫ (Scheme.ΓSpecIso (.of A)).inv).hom r) = _
  rw [Iso.hom_inv_id]
  rfl

theorem coverAction_coverBaseHom (c : C) (r : A) :
    (coverAction D c).hom (coverBaseHom D r) = coverBaseHom D r :=
  congrArg (fun f => f.hom ((Scheme.ΓSpecIso (.of A)).inv.hom r)) (appTop_comp_coverAction D c)

variable (a : A) (m : ℕ) (hm0 : m ≠ 0) (hm : IsUnit (m : A)) (ha : IsUnit a)

/-- The cover map from the cover carried by `D` to the Kummer cover `Spec A[X]/(X^m - a)`
given by an `A`-algebra map `ψ : A[X]/(X^m - a) → Γ(Y, ⊤)`. -/
def kummerCoverHom (ψ : KummerRootAlgebra a m →+* coverRing D)
    (hψ : ψ.comp (algebraMap A (KummerRootAlgebra a m)) = coverBaseHom D) :
    D.obj (SingleObj.star C) ⟶ kummerRootCover a m hm0 hm ha :=
  ObjectProperty.homMk (Over.homMk
    ((coverScheme D).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ)) (by
      change _ ≫ kummerRootMorphism a m = _
      have e : CommRingCat.ofHom (algebraMap A (KummerRootAlgebra a m)) ≫ CommRingCat.ofHom ψ =
          (Scheme.ΓSpecIso (.of A)).inv ≫ (D.obj (SingleObj.star C)).obj.hom.appTop := by
        ext r
        exact RingHom.congr_fun hψ r
      rw [Category.assoc, kummerRootMorphism, ← Spec.map_comp, e, Spec.map_comp,
        ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id,
        Category.comp_id]))

/-- If `ψ` intertwines the action of `c` with `X ↦ η X`, then so does the cover map. -/
theorem kummerCoverHom_comm (ψ : KummerRootAlgebra a m →+* coverRing D)
    (hψ : ψ.comp (algebraMap A (KummerRootAlgebra a m)) = coverBaseHom D) (c : C)
    (R : Type*) [CommRing R] [Algebra R A] (η : rootsOfUnity m R)
    (hc : (coverAction D c).hom.comp ψ = ψ.comp (kummerScale R a m η).toRingHom) :
    (D.map (SingleObj.toEnd C c).asHom).hom ≫ (kummerCoverHom D a m hm0 hm ha ψ hψ).hom =
      (kummerCoverHom D a m hm0 hm ha ψ hψ).hom ≫ (kummerScaleHom a m hm0 hm ha R η).hom := by
  apply Over.OverMorphism.ext
  change (D.map (SingleObj.toEnd C c).asHom).hom.left ≫
      (coverScheme D).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ) =
    ((coverScheme D).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ)) ≫
      Spec.map (CommRingCat.ofHom (kummerScale R a m η).toRingHom)
  rw [← Scheme.isoSpec_hom_naturality_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  exact hc

end CoverHom

section Parameter

theorem isUnit_natCast_away {R : Type u} [CommRing R] (t : R) {m : ℕ} (hmR : IsUnit (m : R)) :
    IsUnit (m : Localization.Away t) := by
  simpa using hmR.map (algebraMap R (Localization.Away t))

variable {R : Type u} [CommRing R] [IsDomain R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)]

theorem card_rootsOfUnity_eq {m : ℕ} (hmR : IsUnit (m : R)) (hm0 : m ≠ 0) :
    Nat.card (rootsOfUnity m R) = m := by
  have : NeZero m := ⟨hm0⟩
  obtain ⟨ζ, hζ⟩ :=
    Langlands.CommutativeAlgebra.StrictlyHenselianKummerUnits.exists_isPrimitiveRoot hmR hm0
  exact hζ.card_rootsOfUnity

variable (t : R) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ Spec (.of (Localization.Away t)))

/-- The Kummer character of level `m` of the parameter `t`: the character of `π₁(U, x)`,
`U = Spec R[1/t]`, with values in the `m`-th roots of unity of `R` describing the action on
the geometric fibre of `Spec R[1/t][X]/(X^m - t)`. -/
def parameterKummerCharacter (m : ℕ) (hm0 : m ≠ 0) (hmR : IsUnit (m : R)) :
    FundamentalGroup x (geometricFiberFinite x) →* rootsOfUnity m R :=
  kummerCharacter (algebraMap R (Localization.Away t) t) m hm0 (isUnit_natCast_away t hmR)
    (IsLocalization.Away.algebraMap_isUnit t) x (geometricFiberFinite x) R hmR
    (card_rootsOfUnity_eq hmR hm0)

end Parameter

section Quotient

variable {R : Type u} [CommRing R] [IsDomain R] [IsRegularLocalRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] {t : R} (ht : t ∈ maximalIdeal R)
  (ht2 : t ∉ maximalIdeal R ^ 2) {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓR : IsUnit (ℓ : R))
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of (Localization.Away t)))

include ht ht2 in
/-- **Cyclic quotients of order `ℓ` are Kummer.** For every surjective homomorphism `χ` with
open kernel from `π₁(Spec R[1/t], x)` onto the `ℓ`-th roots of unity of `R`, the Kummer character
of level `ℓ` of `t` vanishes on the kernel of `χ`, and this Kummer character is nontrivial. -/
theorem ker_le_ker_parameterKummerCharacter
    (χ : FundamentalGroup x (geometricFiberFinite x) →* rootsOfUnity ℓ R)
    (hχ : Function.Surjective χ)
    (hχo : IsOpen (χ.ker : Set (FundamentalGroup x (geometricFiberFinite x)))) :
    χ.ker ≤ (parameterKummerCharacter t x ℓ hℓ.out.ne_zero hℓR).ker ∧
      parameterKummerCharacter t x ℓ hℓ.out.ne_zero hℓR ≠ 1 := by
  have hℓ0 : ℓ ≠ 0 := hℓ.out.ne_zero
  have hℓA : IsUnit (ℓ : Localization.Away t) := isUnit_natCast_away t hℓR
  have htprime : Prime t :=
    Langlands.CommutativeAlgebra.RegularLocalFactorial.prime_of_mem_maximalIdeal_notMem_sq ht ht2
  have : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors htprime.ne_zero)
  have : IsNoetherianRing (Localization.Away t) :=
    IsLocalization.isNoetherianRing (Submonoid.powers t) _ inferInstance
  have hcard : Nat.card (rootsOfUnity ℓ R) = ℓ := card_rootsOfUnity_eq hℓR hℓ0
  obtain ⟨D, φ, hφg, hφc⟩ := exists_torsor_cover x (geometricFiberFinite x) χ hχo
  have hne : Nonempty (Fiber x (D.obj (SingleObj.star _))) := ⟨φ.symm 1⟩
  have htrans : ∀ y z : Fiber x (D.obj (SingleObj.star _)),
      ∃ c : rootsOfUnity ℓ R, z = y ≫ (D.map (SingleObj.toEnd _ c).asHom).hom := by
    intro y z
    refine ⟨φ z * (φ y)⁻¹, φ.injective ?_⟩
    rw [hφc, inv_mul_cancel_right]
  have hfree : ∀ (y : Fiber x (D.obj (SingleObj.star _))) (c : rootsOfUnity ℓ R),
      y ≫ (D.map (SingleObj.toEnd _ c).asHom).hom = y → c = 1 := by
    intro y c h
    have h1 := congrArg φ h
    rw [hφc] at h1
    exact mul_eq_right.mp h1
  -- a generator `ζ` of the group of `ℓ`-th roots of unity
  have : Nontrivial (rootsOfUnity ℓ R) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact hℓ.out.one_lt)
  obtain ⟨ζ, hζ⟩ := exists_ne (1 : rootsOfUnity ℓ R)
  have hζℓ : ζ ^ ℓ = 1 := (congrArg (ζ ^ ·) hcard).symm.trans pow_card_eq_one'
  have hord : orderOf ζ = ℓ := orderOf_eq_prime hζℓ hζ
  have hgen : ∀ c : rootsOfUnity ℓ R, ∃ j : ℕ, ζ ^ j = c := fun c =>
    mem_powers_iff_mem_zpowers.mpr (mem_zpowers_of_prime_card hcard hζ)
  -- the ring of the cover as an `R[1/t]`-algebra with the automorphism `σ` given by `ζ`
  let : Algebra (Localization.Away t) (coverRing D) := (coverBaseHom D).toAlgebra
  let σ : coverRing D →ₐ[Localization.Away t] coverRing D :=
    { toRingHom := (coverAction D ζ).hom
      commutes' := fun r => coverAction_coverBaseHom D ζ r }
  have hσpow : ∀ j : ℕ, ∀ b : coverRing D, (σ ^ j) b = (coverAction D (ζ ^ j)).hom b := by
    intro j
    induction j with
    | zero =>
      intro b
      rw [pow_zero, pow_zero, coverAction_one]
      rfl
    | succ j ih =>
      intro b
      rw [pow_succ', AlgHom.mul_apply, ih, pow_succ, coverAction_mul]
      rfl
  have hσℓ : σ ^ ℓ = 1 := by
    apply AlgHom.ext
    intro b
    rw [hσpow, hζℓ, coverAction_one]
    rfl
  have hfix : ∀ b : coverRing D, σ b = b →
      ∃ r : Localization.Away t, algebraMap (Localization.Away t) (coverRing D) r = b := by
    intro b hb
    have hj : ∀ j : ℕ, (σ ^ j) b = b := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [pow_succ', AlgHom.mul_apply, ih, hb]
    have hall : ∀ c : rootsOfUnity ℓ R, (coverAction D c).hom b = b := by
      intro c
      obtain ⟨j, rfl⟩ := hgen c
      rw [← hσpow j]
      exact hj j
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_forall_coverAction_eq x D hne htrans b hall
    exact ⟨(Scheme.ΓSpecIso (.of (Localization.Away t))).hom.hom r,
      (coverBaseHom_ΓSpecIso_hom D r).trans hr⟩
  have hpts : ∀ 𝔪 : Ideal (Localization.Away t), 𝔪.IsMaximal →
      ∃ (K : Type u) (_ : Field K) (ϕ : coverRing D →+* K),
        (∀ r ∈ 𝔪, ϕ (algebraMap (Localization.Away t) (coverRing D) r) = 0) ∧
          ∀ j, 0 < j → j < ℓ → ϕ.comp (σ ^ j).toRingHom ≠ ϕ := by
    intro 𝔪 h𝔪
    let e := Scheme.ΓSpecIso (.of (Localization.Away t))
    have : (𝔪.comap e.hom.hom).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ (ConcreteCategory.bijective_of_isIso e.hom).2
    obtain ⟨K, hK, ϕ, hϕ0, hϕ1⟩ := exists_free_residue_point x D hne hfree (𝔪.comap e.hom.hom)
    refine ⟨K, hK, ϕ, fun r hr => hϕ0 (e.inv.hom r) ?_, fun j hj0 hjℓ h => ?_⟩
    · rw [Ideal.mem_comap]
      change (e.inv ≫ e.hom).hom r ∈ 𝔪
      rw [Iso.inv_hom_id]
      exact hr
    · refine hϕ1 (ζ ^ j) (pow_ne_one_of_lt_orderOf hj0.ne' (by rw [hord]; exact hjℓ)) ?_
      refine RingHom.ext fun b => ?_
      change ϕ ((coverAction D (ζ ^ j)).hom b) = ϕ b
      rw [← hσpow j b]
      exact RingHom.congr_fun h b
  have hinj : Function.Injective (algebraMap (Localization.Away t) (coverRing D)) := by
    have h1 := (bijective_algebraMap_quotientRing x D hne htrans).1
    have h2 : Function.Injective
        (algebraMap Γ(Spec (.of (Localization.Away t)), ⊤) (coverRing D)) := fun r r' h =>
      h1 (Subtype.ext h)
    exact h2.comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Localization.Away t))).inv).1
  have : FaithfulSMul (Localization.Away t) (coverRing D) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Subsingleton (CommRing.Pic (Localization.Away t)) :=
    Langlands.CommutativeAlgebra.regularLocalAwayPicard R inferInstance t
  have hcℓ : (algebraMap R (Localization.Away t) ((ζ : Rˣ) : R)) ^ ℓ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity ℓ (ζ : Rˣ)).mp ζ.2,
      Units.val_one, map_one]
  obtain ⟨v, hv, w, hw⟩ := Langlands.CommutativeAlgebra.KummerEigenvector.exists_unit_eigenvector
    σ hℓ.out.pos hσℓ hfix hpts hcℓ
  obtain ⟨a, ha', η, ψ, hη, hψ⟩ :=
    exists_kummerLift_of_unit_eigenvector htprime hℓ.out hℓR σ ζ hζ v hv w hw
  have haU : IsUnit a := by
    rcases ha' with rfl | rfl
    · exact isUnit_one
    · exact IsLocalization.Away.algebraMap_isUnit t
  -- the cover map to the Kummer cover
  have hψA : ψ.toRingHom.comp (algebraMap (Localization.Away t) (KummerRootAlgebra a ℓ)) =
      coverBaseHom D := by
    ext r
    exact ψ.commutes r
  have hψc : (coverAction D ζ).hom.comp ψ.toRingHom =
      ψ.toRingHom.comp (kummerScale R a ℓ η).toRingHom :=
    RingHom.ext fun b => AlgHom.congr_fun hψ b
  have hπ := kummerCoverHom_comm D a ℓ hℓ0 hℓA haU ψ.toRingHom hψA ζ R η hψc
  obtain ⟨y⟩ := hne
  have hsmul : ∀ g : FundamentalGroup x (geometricFiberFinite x),
      g • y = y ≫ (D.map (SingleObj.toEnd _ (χ g)).asHom).hom := by
    intro g
    apply φ.injective
    rw [hφg, hφc]
  have hker : ∀ g ∈ χ.ker,
      kummerCharacter a ℓ hℓ0 hℓA haU x (geometricFiberFinite x) R hℓR hcard g = 1 := by
    intro g hg
    rw [← smul_eq_self_iff_kummerCharacter a ℓ hℓ0 hℓA haU x (geometricFiberFinite x) R hℓR
      hcard g (y ≫ (kummerCoverHom D a ℓ hℓ0 hℓA haU ψ.toRingHom hψA).hom), smul_naturality]
    congr 1
    apply φ.injective
    rw [hφg, MonoidHom.mem_ker.mp hg, one_mul]
  obtain ⟨g₀, hg₀⟩ := hχ ζ
  have hκg₀ : kummerCharacter a ℓ hℓ0 hℓA haU x (geometricFiberFinite x) R hℓR hcard g₀ = η := by
    apply kummerScale_injective a ℓ hℓ0 hℓA haU x R hℓR
      (y ≫ (kummerCoverHom D a ℓ hℓ0 hℓA haU ψ.toRingHom hψA).hom)
    dsimp only
    rw [← smul_eq_comp_kummerCharacter a ℓ hℓ0 hℓA haU x (geometricFiberFinite x) R hℓR hcard g₀,
      smul_naturality, hsmul, hg₀, Category.assoc, hπ, ← Category.assoc]
  rcases ha' with rfl | rfl
  · exfalso
    have h1 := kummerCharacter_one_eq_one ℓ hℓ0 hℓA x (geometricFiberFinite x) R hℓR hcard
    apply hη
    rw [← hκg₀]
    exact congrArg (fun f => f g₀) h1
  · refine ⟨fun g hg => hker g hg, fun h => hη ?_⟩
    rw [← hκg₀]
    exact congrArg (fun f => f g₀) h
end Quotient

end Langlands.AlgebraicGeometry.FiniteEtale
