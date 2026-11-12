import Langlands.ClassField.Global.LocalRelativeWeilUnramified
import Langlands.ClassField.Global.LocalRelativeWeilMap
import Langlands.ClassField.Global.IdeleClassPlaceProduct
import Langlands.ClassField.Global.IdeleLocalInjectivity
import Langlands.ClassField.Global.IdeleCohomology
import Langlands.ClassField.Global.IdeleGaloisDescentProof
import Langlands.GroupTheory.TransferDoubleCoset
import Langlands.GroupTheory.TransferCyclicQuotient
import Langlands.Global.AdelicFunctoriality.CompletedRamification
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.LocalField.Uniformizer

/-! # The transfer at a local relative Weil map of ramification index one

Let `w` be a finite place of `E` above a finite place `z` of `F` with ramification index one,
and let `ι : W_{F_z} → W_{E/F}` be a local relative Weil map for `w`. For every `y ∈ W_{F_z}`
of degree one, the transfer `W_{E/F} → C_F` sends `ι y` to the inverse of the idele class of
an element of `F_zˣ` of normalized order one.
-/

noncomputable section

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

namespace Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Under the geometric normalization, the reciprocity unit of an element of degree one has
order one. -/
theorem ord_reciprocityUnits_of_localDegree_eq_one
    (eF : LocalFactor.RankOne.ReciprocityCandidate F)
    (heF : LocalClassField.GeometricWeilReciprocityRelation F F.canonicalTopologicalData eF)
    (g : localWeilGroup F) (hg : localDegree F g = Multiplicative.ofAdd (1 : ℤ)) :
    F.canonicalTopologicalData.ord (LocalFactor.RankOne.reciprocityUnits F eF g : F.Carrier) =
      1 := by
  have h : F.canonicalTopologicalData.orderHom (LocalFactor.RankOne.reciprocityUnits F eF g) =
      localDegree F g :=
    DFunLike.congr_fun heF.1 (LocalClassField.WeilQuotients.projection (localResidueDegree F) g)
  rw [hg] at h
  exact congrArg Multiplicative.toAdd h

end Langlands.Weil.Local

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

section Places

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (z : Langlands.Global.FinitePlace F)

/-- If `σ` followed by the place embedding at `u` is the place embedding at `u'` followed by
an automorphism of `\bar{F_z}`, then `σ` moves `u'` to `u`: `finitePlaceEquiv σ u = u'`. -/
theorem finitePlaceEquiv_eq_of_placeEmbedding (σ : E ≃ₐ[F] E) (u u' : FinitePlacesAbove E z)
    (ρ : Field.absoluteGaloisGroup (padicField z).Carrier)
    (h : ∀ x : E, placeEmbedding z u (σ x) = AlgEquiv.toAlgHom ρ (placeEmbedding z u' x)) :
    finitePlaceEquiv σ.toRingEquiv u.1 = u'.1 := by
  have hqz := Langlands.ClassField.Global.liesOver_finitePlaceEquiv z u.1 σ
  let q := finitePlaceEquiv σ.toRingEquiv u.1
  let φ := finiteCompletionEquiv σ.toRingEquiv u.1
  let κ : q.adicCompletion E →+* AlgebraicClosure (z.adicCompletion F) :=
    (AlgEquiv.toAlgHom ρ⁻¹).toRingHom.comp ((completionClosureEmbedding z u.1).comp φ.toRingHom)
  have hκ : ∀ a : z.adicCompletion F, κ (algebraMap (z.adicCompletion F) (q.adicCompletion E) a) =
      algebraMap (z.adicCompletion F) (AlgebraicClosure (z.adicCompletion F)) a := by
    intro a
    change AlgEquiv.toAlgHom ρ⁻¹
      (completionClosureEmbedding z u.1 (φ (FiniteExtension.completionMap z q a))) = _
    rw [IdeleGaloisDescentProof.finiteCompletionEquiv_completionMap σ z u.1 a,
      show completionClosureEmbedding z u.1 (FiniteExtension.completionMap z u.1 a) = _ from
        completionClosureEmbedding_algebraMap z u.1 a, AlgHom.commutes]
  obtain ⟨τ, hτ⟩ := exists_eq_comp_completionClosureEmbedding (K := E) z ⟨q, hqz⟩ κ hκ
  have key := eq_of_placeEmbedding_eq (K := E) z ⟨q, hqz⟩ u' τ (fun x => by
    change AlgEquiv.toAlgHom τ
      (completionClosureEmbedding z q (algebraMap E (q.adicCompletion E) x)) =
        placeEmbedding z u' x
    rw [← hτ]
    change AlgEquiv.toAlgHom ρ⁻¹
      (completionClosureEmbedding z u.1 (φ (algebraMap E (q.adicCompletion E) x))) = _
    rw [finiteCompletionEquiv_coe]
    change AlgEquiv.toAlgHom ρ⁻¹ (placeEmbedding z u (σ x)) = _
    rw [h, absoluteGalois_inv_apply_apply])
  exact congrArg Subtype.val key

/-- Under the hypothesis of `finitePlaceEquiv_eq_of_placeEmbedding`, the completed transport
`E_{σ*u} → E_u` followed by the embedding at `u` is the embedding at `σ*u` followed by `ρ`. -/
theorem completionClosureEmbedding_finiteCompletionEquiv (σ : E ≃ₐ[F] E)
    (u : FinitePlacesAbove E z) (ρ : Field.absoluteGaloisGroup (padicField z).Carrier)
    [(finitePlaceEquiv σ.toRingEquiv u.1).asIdeal.LiesOver z.asIdeal]
    (h : ∀ x : E, placeEmbedding z u (σ x) = AlgEquiv.toAlgHom ρ
      (placeEmbedding z ⟨finitePlaceEquiv σ.toRingEquiv u.1, inferInstance⟩ x))
    (t : (finitePlaceEquiv σ.toRingEquiv u.1).adicCompletion E) :
    completionClosureEmbedding z u.1 (finiteCompletionEquiv σ.toRingEquiv u.1 t) =
      AlgEquiv.toAlgHom ρ (completionClosureEmbedding z (finitePlaceEquiv σ.toRingEquiv u.1) t) := by
  let q := finitePlaceEquiv σ.toRingEquiv u.1
  let f₁ : q.adicCompletion E →ₐ[z.adicCompletion F] AlgebraicClosure (z.adicCompletion F) :=
    { toRingHom := (completionClosureEmbedding z u.1).comp
        (finiteCompletionEquiv σ.toRingEquiv u.1).toRingHom
      commutes' := fun a => by
        change completionClosureEmbedding z u.1
          (finiteCompletionEquiv σ.toRingEquiv u.1 (FiniteExtension.completionMap z q a)) = _
        rw [IdeleGaloisDescentProof.finiteCompletionEquiv_completionMap σ z u.1 a]
        exact completionClosureEmbedding_algebraMap z u.1 a }
  let f₂ : q.adicCompletion E →ₐ[z.adicCompletion F] AlgebraicClosure (z.adicCompletion F) :=
    (AlgEquiv.toAlgHom ρ).comp (placeClosureAlgHom z ⟨q, inferInstance⟩)
  have hS := subalgebra_eq_top_of_algebraMap_mem z q (AlgHom.equalizer f₁ f₂) (fun x => by
    change completionClosureEmbedding z u.1
      (finiteCompletionEquiv σ.toRingEquiv u.1 (algebraMap E (q.adicCompletion E) x)) =
        AlgEquiv.toAlgHom ρ (placeEmbedding z ⟨q, inferInstance⟩ x)
    rw [finiteCompletionEquiv_coe]
    exact h x)
  have ht : t ∈ AlgHom.equalizer f₁ f₂ := hS ▸ Algebra.mem_top
  exact ht

/-- Reading a unit at a place `w` as a unit at an equal place `q`. -/
theorem exists_ofAdicCompletion_eq_of_eq {q w : Langlands.Global.FinitePlace E}
    [q.asIdeal.LiesOver z.asIdeal] [w.asIdeal.LiesOver z.asIdeal] (h : q = w)
    (b : (w.adicCompletion E)ˣ) :
    ∃ t : (q.adicCompletion E)ˣ,
      IdeleClassGroup.ofAdicCompletion (𝓞 E) E q t =
          IdeleClassGroup.ofAdicCompletion (𝓞 E) E w b ∧
        completionClosureEmbedding z q (t : q.adicCompletion E) =
          completionClosureEmbedding z w (b : w.adicCompletion E) := by
  subst h
  exact ⟨b, rfl, rfl⟩

end Places

section Injectivity

variable {E : Type u} [Field E] [NumberField E]

/-- The map from the units of one completion to the idele classes is injective. -/
theorem ofAdicCompletion_injective (w : Langlands.Global.FinitePlace E) :
    Function.Injective (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  rw [IdeleClassGroup.ofAdicCompletion, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hb
  obtain ⟨x, hx⟩ := hb
  have h₁ : algebraMap E (InfiniteAdeleRing E) (x : E) = 1 :=
    congrArg (fun y : IdeleGroup (𝓞 E) E => (y : AdeleRing (𝓞 E) E).1) hx
  have hx₁ : x = 1 :=
    Units.ext ((algebraMap E (InfiniteAdeleRing E)).injective (h₁.trans (map_one _).symm))
  subst hx₁
  rw [map_one] at hx
  have h₂ := congrArg (ideleCoordinate w) hx
  rw [map_one, ideleCoordinate_ofAdicCompletion_self] at h₂
  exact h₂.symm

end Injectivity

section Descent

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (z : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver z.asIdeal]

/-- Let `w` have ramification index one over `z`, let `y ∈ W_{F_z}` have degree one, and let
`σ ∈ Gal(E/F)` act through `E → E_w → \bar{F_z}` as the Galois image of `y`. If the idele
class of `b ∈ E_wˣ` is fixed by `σ`, then `b` lies in `F_z`. -/
theorem exists_completionMap_eq_of_ideleClassEquiv
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1) (σ : E ≃ₐ[F] E)
    (y : Weil.Local.localWeilGroup (padicField z))
    (hy : Weil.Local.localDegree (padicField z) y = Multiplicative.ofAdd (1 : ℤ))
    (hσ : ∀ x : E, placeEmbedding z ⟨w, inferInstance⟩ (σ x) =
      AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) y)
        (placeEmbedding z ⟨w, inferInstance⟩ x))
    (b : (w.adicCompletion E)ˣ)
    (hb : ideleClassEquiv σ.toRingEquiv (IdeleClassGroup.ofAdicCompletion (𝓞 E) E w b) =
      IdeleClassGroup.ofAdicCompletion (𝓞 E) E w b) :
    ∃ a : z.adicCompletion F, FiniteExtension.completionMap z w a = b := by
  let ρ := Weil.Local.localProjection (padicField z) y
  have hP : finitePlaceEquiv σ.toRingEquiv w = w :=
    finitePlaceEquiv_eq_of_placeEmbedding z σ ⟨w, inferInstance⟩ ⟨w, inferInstance⟩ ρ hσ
  have := Langlands.ClassField.Global.liesOver_finitePlaceEquiv z w σ
  obtain ⟨t, ht₁, ht₂⟩ := exists_ofAdicCompletion_eq_of_eq z hP b
  have hφ : finiteCompletionEquiv σ.toRingEquiv w (t : _) = (b : w.adicCompletion E) := by
    have h₁ := ideleClassEquiv_ofAdicCompletion σ.toRingEquiv w t
    rw [ht₁, hb] at h₁
    exact congrArg Units.val (ofAdicCompletion_injective w h₁).symm
  have hu : (⟨finitePlaceEquiv σ.toRingEquiv w, inferInstance⟩ : FinitePlacesAbove E z) =
      ⟨w, inferInstance⟩ := Subtype.ext hP
  have hR := completionClosureEmbedding_finiteCompletionEquiv z σ ⟨w, inferInstance⟩ ρ
    (fun x => by rw [hu]; exact hσ x) (t : _)
  let β := completionClosureEmbedding z w (b : w.adicCompletion E)
  -- `β` is fixed by the Galois image of `y`.
  have hyβ : AlgEquiv.toAlgHom ρ β = β := by
    calc AlgEquiv.toAlgHom ρ β
        = AlgEquiv.toAlgHom ρ (completionClosureEmbedding z (finitePlaceEquiv σ.toRingEquiv w)
            (t : _)) := by rw [ht₂]
      _ = completionClosureEmbedding z w (finiteCompletionEquiv σ.toRingEquiv w (t : _)) :=
          hR.symm
      _ = β := by rw [hφ]
  -- `β` is fixed by the image of `G_{E_w}`.
  have hfixE : ∀ τ ∈ (Weil.Local.extensionGaloisMap (padicField z) (towerPadicField z w)
      (completionPadicAlgHom z w)).toMonoidHom.range, AlgEquiv.toAlgHom τ β = β := by
    intro τ hτ
    rw [Weil.Local.extensionGaloisMap_range] at hτ
    exact (IntermediateField.mem_fixingSubgroup_iff _ τ).mp hτ β
      ((Weil.Local.mem_extensionIntermediateField (padicField z) (towerPadicField z w)
        (completionPadicAlgHom z w) β).mpr ⟨(b : w.adicCompletion E), rfl⟩)
  -- `β` is fixed by the Galois image of every element of `W_{F_z}`.
  let S : Subgroup (Weil.Local.localWeilGroup (padicField z)) :=
    (MulAction.stabilizer (AlgebraicClosure (padicField z).Carrier ≃ₐ[(padicField z).Carrier]
      AlgebraicClosure (padicField z).Carrier) β).comap
      (Weil.Local.localProjection (padicField z)).toMonoidHom
  have hS : ∀ g, g ∈ S ↔ AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) g) β = β :=
    fun g => Iff.rfl
  have hW : ∀ g, g ∈ S := by
    intro g
    set d := Weil.Local.localDegreeInt (padicField z) g with hd
    have h₀ : Weil.Local.localDegreeInt (padicField z) ((y ^ d)⁻¹ * g) = 0 := by
      unfold Weil.Local.localDegreeInt
      rw [map_mul, map_inv, map_zpow, hy, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd, hd]
      unfold Weil.Local.localDegreeInt
      simp
    obtain ⟨h', hh'⟩ := (mem_completionWeilMap_range_iff z w he _).mpr (h₀ ▸ dvd_zero _)
    have hg : g = y ^ d * completionWeilMap z w h' := by
      change g = y ^ d * (completionWeilMap z w).toMonoidHom h'
      rw [hh', mul_inv_cancel_left]
    rw [hg]
    refine S.mul_mem (S.zpow_mem ((hS y).mpr hyβ) d) ((hS _).mpr ?_)
    rw [Weil.Local.localProjection_extensionWeilMap]
    exact hfixE _ ⟨_, rfl⟩
  -- Hence `β` is fixed by `G_{F_z}`.
  have hall : ∀ τ : AlgebraicClosure (padicField z).Carrier ≃ₐ[(padicField z).Carrier]
      AlgebraicClosure (padicField z).Carrier, τ β = β := by
    intro τ'
    let τ : Field.absoluteGaloisGroup (padicField z).Carrier := τ'
    change AlgEquiv.toAlgHom τ β = β
    obtain ⟨ℓ, hℓ⟩ := exists_localProjection_placeEmbedding (K := E) z ⟨w, inferInstance⟩ τ
    have h₁ := hfixE (τ⁻¹ * Weil.Local.localProjection (padicField z) ℓ)
      ((placeEmbedding_fixed_iff z ⟨w, inferInstance⟩ _).mp fun k => by
        change AlgEquiv.toAlgHom τ⁻¹
          (AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) ℓ)
            (placeEmbedding z ⟨w, inferInstance⟩ k)) = _
        rw [hℓ k, absoluteGalois_inv_apply_apply])
    have h₂ : AlgEquiv.toAlgHom τ⁻¹ β = β := by
      have h₃ := (hS ℓ).mp (hW ℓ)
      change AlgEquiv.toAlgHom τ⁻¹
        (AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) ℓ) β) = β at h₁
      rwa [h₃] at h₁
    calc AlgEquiv.toAlgHom τ β = AlgEquiv.toAlgHom τ (AlgEquiv.toAlgHom τ⁻¹ β) := by rw [h₂]
      _ = β := by
        change AlgEquiv.toAlgHom (τ * τ⁻¹) β = β
        rw [mul_inv_cancel]
        rfl
  have : CharZero (padicField z).Carrier :=
    charZero_of_injective_algebraMap (algebraMap F (z.adicCompletion F)).injective
  have : IsGalois (padicField z).Carrier (AlgebraicClosure (padicField z).Carrier) := ⟨⟩
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed β).mpr hall
  refine ⟨a, (completionClosureEmbedding z w).injective ?_⟩
  change completionClosureEmbedding z w
    (algebraMap (z.adicCompletion F) (w.adicCompletion E) a) = β
  rw [completionClosureEmbedding_algebraMap]
  exact ha

end Descent

section Transfer

variable (c : FundamentalClass.ClassFamily.{u}) {F E : Type u}
  [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
  (z : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver z.asIdeal] (h : FundamentalClass.Restriction c)

include h in
/-- Let `w` have ramification index one over `z` and let `ι : W_{F_z} → W_{E/F}` be a local
relative Weil map for `w`. For every `y ∈ W_{F_z}` of degree one, the transfer
`W_{E/F} → C_F` sends `ι y` to `[a]_z⁻¹` for some `a ∈ F_zˣ` of valuation `exp (-1)`. -/
theorem exists_transfer_eq_inv_ofAdicCompletion
    (he : w.asIdeal.ramificationIdx (𝓞 F) = 1)
    (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField z w))
    (ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E)
    (hι : IsLocalRelativeWeilMap z w e ι)
    (y : Weil.Local.localWeilGroup (padicField z))
    (hy : Weil.Local.localDegree (padicField z) y = Multiplicative.ofAdd (1 : ℤ)) :
    ∃ a : (z.adicCompletion F)ˣ, Valued.v (a : z.adicCompletion F) = WithZero.exp (-1 : ℤ) ∧
      transfer c F E (ι y) = (IdeleClassGroup.ofAdicCompletion (𝓞 F) F z a)⁻¹ := by
  obtain ⟨heF, hιc, hι3⟩ := hι
  have hι' : ∀ (g : Weil.Local.localWeilGroup (padicField z)) (x : E),
      closurePlaceEmbedding z w (projection c F E (ι.toMonoidHom g) x) =
        AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField z) g)
          (closurePlaceEmbedding z w x) := hιc
  set f := Weil.Local.extensionResidueDegree (padicField z) (towerPadicField z w)
    (completionPadicAlgHom z w) with hf
  have hfpos : 0 < f := Weil.Local.extensionResidueDegree_pos _ _ _
  -- `y ^ f` is the image of an element of degree one of `W_{E_w}`.
  have hdeg_yf : Weil.Local.localDegreeInt (padicField z) (y ^ f) = f := by
    unfold Weil.Local.localDegreeInt
    rw [map_pow, hy, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one]
  obtain ⟨h0, hh0⟩ := (mem_completionWeilMap_range_iff z w he (y ^ f)).mpr
    (by rw [hdeg_yf])
  have hh0' : completionWeilMap z w h0 = y ^ f := hh0
  have hdeg0 : Weil.Local.localDegree (towerPadicField z w) h0 =
      Multiplicative.ofAdd (1 : ℤ) := by
    have h1 := Weil.Local.localDegreeInt_extensionWeilMap (padicField z) (towerPadicField z w)
      (completionPadicAlgHom z w) h0
    rw [hh0', hdeg_yf] at h1
    have hf0 : (f : ℤ) ≠ 0 := by exact_mod_cast hfpos.ne'
    have h2 : Weil.Local.localDegreeInt (towerPadicField z w) h0 = 1 :=
      mul_left_cancel₀ hf0 (h1.symm.trans (mul_one (f : ℤ)).symm)
    exact congrArg Multiplicative.ofAdd h2
  set b := LocalFactor.RankOne.reciprocityUnits (towerPadicField z w) e h0 with hb_def
  set X := IdeleClassGroup.ofAdicCompletion (𝓞 E) E w b with hX
  have hιyf : ι (y ^ f) = (inclusion c F E X)⁻¹ := by
    rw [← hh0', hι3 h0]
  -- `b` lies in `F_z`.
  have hcommute : Commute (ι y) (inclusion c F E X) := by
    have h1 : Commute (ι y) (ι (y ^ f)) := (Commute.self_pow y f).map ι
    rw [hιyf] at h1
    exact Commute.inv_right_iff.mp h1
  have hfix : ideleClassEquiv (projection c F E (ι y)).toRingEquiv X = X := by
    apply inclusion_injective c F E
    rw [← conjugation]
    exact hcommute.mul_inv_cancel
  obtain ⟨a₀, ha₀⟩ := exists_completionMap_eq_of_ideleClassEquiv z w he
    (projection c F E (ι y)) y hy (hιc y) b hfix
  have ha₀ne : a₀ ≠ 0 := by
    intro h0'
    apply b.ne_zero
    rw [← ha₀, h0', map_zero]
  let a : (z.adicCompletion F)ˣ := Units.mk0 a₀ ha₀ne
  have hab : Units.map (FiniteExtension.completionMap z w).toMonoidHom a = b := Units.ext ha₀
  -- The valuation of `a`.
  have hord : (towerPadicField z w).canonicalTopologicalData.ord
      (b : (towerPadicField z w).Carrier) = 1 :=
    Weil.Local.ord_reciprocityUnits_of_localDegree_eq_one (towerPadicField z w) e heF h0 hdeg0
  have hvb : Valued.v (b : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    unfold PadicField.TopologicalData.ord at hord
    rw [discreteValuation_padicFieldAt w] at hord
    have hne : Valued.v (b : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr b.ne_zero
    rw [← WithZero.exp_log hne]
    congr 1
    omega
  have hva : Valued.v (a : z.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [← hvb, ← ha₀, FiniteExtension.valuation_completionMap, he, pow_one]
    rfl
  refine ⟨a, hva, (eq_transfer_of_ideleClassInclusion_eq c F E ?_).symm⟩
  -- The double cosets `C_E \ W_{E/F} / ι(W_{F_z})` are indexed by the places above `z`.
  let x : FinitePlacesAbove E z → RelativeWeilGroup c F E := placeRepresentative c E z w
  have hx : ∀ u k, cosetEmbedding c E z w (x u) k = placeEmbedding z u k :=
    cosetEmbedding_placeRepresentative c E z w
  have hcover : ∀ g : RelativeWeilGroup c F E, ∃ (u : FinitePlacesAbove E z)
      (l : Weil.Local.localWeilGroup (padicField z)), ∃ hh ∈ ideleClassSubgroup c F E,
        g = ι.toMonoidHom l * (fun u => (x u)⁻¹) u * hh := by
    intro g
    obtain ⟨m, u, ℓ, hg⟩ := exists_eq_mul c E z w h ι.toMonoidHom hι' x hx g⁻¹
    refine ⟨u, ℓ⁻¹, (restrictionInclusion c F E E h m)⁻¹,
      (ideleClassSubgroup c F E).inv_mem
        ((mem_range_restrictionInclusion_self_iff c h _).mp ⟨m, rfl⟩), ?_⟩
    rw [← inv_inv g, hg]
    simp only [mul_inv_rev, map_inv, mul_assoc]
  have hdisj : ∀ (u u' : FinitePlacesAbove E z) (l : Weil.Local.localWeilGroup (padicField z)),
      ∀ hh ∈ ideleClassSubgroup c F E,
        (fun u => (x u)⁻¹) u' = ι.toMonoidHom l * (fun u => (x u)⁻¹) u * hh → u = u' := by
    intro u u' l hh hhH heq
    simp only at heq
    obtain ⟨m, hm⟩ := (mem_range_restrictionInclusion_self_iff c h _).mpr (inv_mem hhH)
    have hm' : restrictionInclusion c F E E h m = hh⁻¹ := hm
    apply place_eq_of_mul_eq c E z w h ι.toMonoidHom hι' x hx m 1 u u' l⁻¹ 1
    rw [map_one, one_mul, map_one, mul_one, hm']
    change hh⁻¹ * (x u * ι.toMonoidHom l⁻¹) = x u'
    rw [← inv_inv (x u'), heq]
    simp only [mul_inv_rev, inv_inv, map_inv, mul_assoc]
  let ψE : ideleClassSubgroup c F E →* IdeleClassGroup (𝓞 E) E :=
    (MonoidHom.ofInjective (inclusion_injective c F E)).symm.toMonoidHom
  have key := Langlands.GroupTheory.Transfer.transfer_comp_eq_prod_of_normal
    (A := IdeleClassGroup (𝓞 E) E) (H := ideleClassSubgroup c F E) (ψ := ι.toMonoidHom)
    (t := fun u => (x u)⁻¹) ψE hcover hdisj y
  -- Each factor is computed by the one-orbit transfer lemma.
  have hH : ∀ g, g ∈ (ideleClassSubgroup c F E).comap ι.toMonoidHom ↔
      (f : ℤ) ∣ ((Weil.Local.localDegree (padicField z)).toMonoidHom g).toAdd := by
    intro g
    rw [Subgroup.mem_comap]
    exact (mem_ideleClassSubgroup_iff c z w h ι.toMonoidHom hι' g).trans
      (mem_completionWeilMap_range_iff z w he g)
  have hinc : ∀ k : ideleClassSubgroup c F E, inclusion c F E (ψE k) = k :=
    MonoidHom.apply_ofInjective_symm (inclusion_injective c F E)
  have hfactor : ∀ u : FinitePlacesAbove E z,
      MonoidHom.transfer ((ψE.comp
        (Langlands.GroupTheory.Transfer.conjInv ((fun u => (x u)⁻¹) u))).comp
          (ι.toMonoidHom.subgroupComap (ideleClassSubgroup c F E))) y =
        (ideleClassEquiv (projection c F E (x u)).toRingEquiv X)⁻¹ := by
    intro u
    rw [Langlands.GroupTheory.Transfer.transfer_eq_of_degree _
      (Weil.Local.localDegree (padicField z)).toMonoidHom f hH _ y hy]
    apply inclusion_injective c F E
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hinc,
      Langlands.GroupTheory.Transfer.coe_conjInv, map_inv, ← conjugation]
    change (x u)⁻¹⁻¹ * ι (y ^ f) * (x u)⁻¹ = (x u * inclusion c F E X * (x u)⁻¹)⁻¹
    rw [inv_inv, hιyf]
    group
  -- Each place `u` above `z` is moved to `w` by exactly one representative.
  have hPu : ∀ u : FinitePlacesAbove E z,
      finitePlaceEquiv (projection c F E (x u)).toRingEquiv u.1 = w := fun u =>
    finitePlaceEquiv_eq_of_placeEmbedding z (projection c F E (x u)) u ⟨w, inferInstance⟩ 1
      (fun k => by
        change _ = placeEmbedding z ⟨w, inferInstance⟩ k
        rw [← hx u (projection c F E (x u) k), cosetEmbedding_apply, Algebra.algebraMap_self,
          RingHom.id_apply, aut_inv_apply_apply]
        rfl)
  have hσ : ∀ q : HeightOneSpectrum (𝓞 E), q.asIdeal.LiesOver z.asIdeal →
      ∃! u : FinitePlacesAbove E z, finitePlaceEquiv (projection c F E (x u)).toRingEquiv q = w := by
    intro q hq
    refine ⟨⟨q, hq⟩, hPu ⟨q, hq⟩, fun u hu => ?_⟩
    apply Subtype.ext
    exact ((finitePlaceEquiv _).injective (hu.trans (hPu u).symm)).symm
  have hprod := prod_relativeIdeleClassAut_ofAdicCompletion z w
    (fun u => projection c F E (x u)) hσ a
  rw [hab] at hprod
  rw [map_inv, ← hprod, ideleTransfer_apply]
  change _ = MonoidHom.transfer (A := IdeleClassGroup (𝓞 E) E) ψE (ι.toMonoidHom y)
  rw [key]
  refine (Finset.prod_inv_distrib (G := IdeleClassGroup (𝓞 E) E) (s := Finset.univ)
    (fun u => relativeIdeleClassAut F E (projection c F E (x u)) X)).symm.trans ?_
  exact Finset.prod_congr rfl fun u _ => (hfactor u).symm

end Transfer

end Langlands.ClassField.Global.RelativeWeilGroup
