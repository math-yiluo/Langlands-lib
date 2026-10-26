import Langlands.ClassField.Global.CohomologyMaps
import Langlands.ClassField.Global.FundamentalClassStatement
import Langlands.ClassField.Global.IdeleClassGaloisDescentProof
import Langlands.ClassField.Global.CyclicIdeleClassHerbrandAssembly
import Langlands.ClassField.Global.H1VanishingProof
import Langlands.ClassField.Global.IdeleClassH2OrderStatement
import Langlands.Cohomology.H2OrderReduction

/-! # The order bound for second idele-class cohomology -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField CategoryTheory
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

universe u v

namespace IdeleClassH2Order

variable {F : Type u} {E : Type v} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

/-- A subgroup `H ≤ Gal(E/F)` is the Galois group of `E` over the fixed field of `H`. -/
def fixedFieldAutEquiv (H : Subgroup (E ≃ₐ[F] E)) :
    (E ≃ₐ[IntermediateField.fixedField H] E) ≃* H :=
  (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)).symm.trans
    (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H))

omit [IsGalois F E] in
theorem fixedFieldAutEquiv_apply (H : Subgroup (E ≃ₐ[F] E))
    (σ : E ≃ₐ[IntermediateField.fixedField H] E) :
    ((fixedFieldAutEquiv H σ : H) : E ≃ₐ[F] E) = σ.restrictScalars F := rfl

/-- Degree-one vanishing on every subgroup of `Gal(E/F)`, from `H¹(Gal(E/K'), C_E) = 0` for
the fixed field `K'` of the subgroup. -/
theorem h1VanishesOnSubgroups (hH1 : FundamentalClass.IdeleClassH1Vanishing.{v}) :
    Langlands.Cohomology.H1VanishesOnSubgroups (relativeIdeleClassRepresentation F E) := by
  intro H
  have := hH1 (IntermediateField.fixedField H) E
  exact (groupCohomology.mapIso (fixedFieldAutEquiv H) (LinearEquiv.refl _ _)
    (fun _ => rfl) 1).toLinearEquiv.toEquiv.subsingleton_congr.mp this

set_option backward.isDefEq.respectTransparency false in
/-- The prime-index layers: for `N ⊴ H ≤ Gal(E/F)` of prime index, the quotient `H ⧸ N`
acting on the `N`-invariants of `C_E` is `Gal(M/K')` acting on `C_M`, where `K'` and `M`
are the fixed fields of `H` and `N`, so its second cohomology has order `[M : K'] = [H : N]`
by the cyclic Herbrand quotient and degree-one vanishing. -/
theorem h2PrimeLayerBound (hH1 : FundamentalClass.IdeleClassH1Vanishing.{v}) :
    Langlands.Cohomology.H2PrimeLayerBound (relativeIdeleClassRepresentation F E) := by
  intro H N _ hN
  classical
  have hA := ideleClassGaloisDescent.{v, v}
  let A := relativeIdeleClassRepresentation F E
  let X := (Rep.res H.subtype A).quotientToInvariants N
  let K' : IntermediateField F E := IntermediateField.fixedField H
  let e : (E ≃ₐ[K'] E) ≃* H := fixedFieldAutEquiv H
  let N' : Subgroup (E ≃ₐ[K'] E) := N.comap e.toMonoidHom
  have : N'.Normal := Subgroup.Normal.comap inferInstance _
  let M : IntermediateField K' E := IntermediateField.fixedField N'
  have hMfix : M.fixingSubgroup = N' := IntermediateField.fixingSubgroup_fixedField N'
  have hmap : N'.map (e : (E ≃ₐ[K'] E) →* H) = N :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective N
  let φ : (M ≃ₐ[K'] M) ≃* H ⧸ N :=
    (IsGalois.normalAutEquivQuotient N').symm.trans (QuotientGroup.congr N' N e hmap)
  have hφ : ∀ σ : E ≃ₐ[K'] E,
      φ (AlgEquiv.restrictNormalHom M σ) = (QuotientGroup.mk (e σ) : H ⧸ N) := by
    intro σ
    change QuotientGroup.congr N' N e hmap ((IsGalois.normalAutEquivQuotient N').symm
      (IsGalois.normalAutEquivQuotient N' (σ : (E ≃ₐ[K'] E) ⧸ N'))) = _
    rw [MulEquiv.symm_apply_apply, QuotientGroup.congr_mk]
  -- the inclusion `C_M → C_E`, equivariant along `Gal(E/K') → Gal(M/K')`
  let ι := ideleClassInclusionLinear K' M E
  have hι : ∀ (σ : E ≃ₐ[K'] E) (x : (relativeIdeleClassRepresentation K' M).V),
      ι ((relativeIdeleClassRepresentation K' M).ρ (AlgEquiv.restrictNormalHom M σ) x) =
        A.ρ (e σ : E ≃ₐ[F] E) (ι x) :=
    fun σ x => Rep.hom_comm_apply (ideleClassInflationCoefficients K' M E) σ x
  have hinv : ∀ x, ι x ∈ Representation.invariants ((Rep.res H.subtype A).ρ.comp N.subtype) := by
    intro x n
    obtain ⟨n, hn⟩ := n
    obtain ⟨σ, rfl⟩ := e.surjective n
    have hσ : AlgEquiv.restrictNormalHom M σ = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, hMfix]
      exact hn
    have h := hι σ x
    rw [hσ, map_one] at h
    exact h.symm
  let ι' := ι.codRestrict _ hinv
  have hinj : Function.Injective ι' := by
    intro x y h
    exact Additive.toMul.injective ((hA M E).1 (congrArg Additive.toMul (congrArg Subtype.val h)))
  have hsurj : Function.Surjective ι' := by
    rintro ⟨y, hy⟩
    have hfix : ∀ σ : E ≃ₐ[M] E, relativeIdeleClassAut M E σ (Additive.toMul y) =
        Additive.toMul y := by
      intro σ
      have hτ : σ.restrictScalars K' ∈ N' := by
        rw [← hMfix]
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun z hz => σ.commutes ⟨z, hz⟩
      exact congrArg Additive.toMul (hy ⟨e (σ.restrictScalars K'), hτ⟩)
    obtain ⟨a, ha⟩ := ((hA M E).2 (Additive.toMul y)).1 hfix
    refine ⟨Additive.ofMul a, Subtype.ext ?_⟩
    change Additive.ofMul (ideleClassInclusion (K := M) (L := E) a) = y
    rw [ha]
    rfl
  let e' := LinearEquiv.ofBijective ι' ⟨hinj, hsurj⟩
  have he' : ∀ τ : M ≃ₐ[K'] M,
      e'.toLinearMap ∘ₗ (relativeIdeleClassRepresentation K' M).ρ τ =
        X.ρ (φ τ) ∘ₗ e'.toLinearMap := by
    intro τ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K') (K₁ := M) E τ
    rw [hφ σ]
    refine LinearMap.ext fun x => Subtype.ext ?_
    change ι ((relativeIdeleClassRepresentation K' M).ρ (AlgEquiv.restrictNormalHom M σ) x) =
      A.ρ (e σ : E ≃ₐ[F] E) (ι x)
    exact hι σ x
  let iso := (groupCohomology.mapIso (A := X) (B := relativeIdeleClassRepresentation K' M) φ e' he' 2).toLinearEquiv.toEquiv
  have hcardM : Nat.card (M ≃ₐ[K'] M) = N.index := Nat.card_congr φ.toEquiv
  have : Fact (Nat.card (M ≃ₐ[K'] M)).Prime := ⟨hcardM ▸ hN⟩
  have : IsCyclic (M ≃ₐ[K'] M) := isCyclic_of_prime_card rfl
  obtain ⟨-, hfin2, hcard⟩ := cyclicIdeleClassHerbrandQuotient.{v, v} K' M
  have hsub := hH1 K' M
  refine ⟨Finite.of_equiv _ iso, ?_⟩
  rw [← Nat.card_congr iso, hcard, Nat.card_of_subsingleton (0 : relativeIdeleClassCohomology K' M 1),
    mul_one, ← IsGalois.card_aut_eq_finrank, hcardM]

/-- **Conditional order bound.** Degree-one vanishing for idele classes (with the published
cyclic Herbrand quotient and Galois descent) gives `#H²(Gal(E/F), C_E) ∣ [E : F]`. -/
theorem ideleClassH2OrderBound_of (hH1 : FundamentalClass.IdeleClassH1Vanishing.{v}) :
    IdeleClassH2OrderBound.{u, v} := by
  intro F _ _ E _ _ _ _
  obtain ⟨hfin, hdvd⟩ := Langlands.Cohomology.finite_card_dvd_of_primeLayers
    (h1VanishesOnSubgroups (F := F) (E := E) hH1) (h2PrimeLayerBound hH1)
  exact ⟨hfin, IsGalois.card_aut_eq_finrank F E ▸ hdvd⟩

end IdeleClassH2Order

/-- **Order bound for second idele-class cohomology.** For every finite Galois extension
`E/F` of number fields, `H²(Gal(E/F), C_E)` is finite and its order divides `[E : F]`. -/
theorem ideleClassH2OrderBound : IdeleClassH2OrderBound.{u, v} :=
  IdeleClassH2Order.ideleClassH2OrderBound_of ideleClassH1Vanishing.{v}

end Langlands.ClassField.Global
