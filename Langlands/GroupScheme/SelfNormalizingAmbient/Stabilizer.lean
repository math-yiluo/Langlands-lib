import Langlands.GroupScheme.CorepresentedLinearEmbedding
import Langlands.GroupScheme.CorepresentedNormalizer

/-! # Stabilizers of infinitesimal neighbourhoods in cut-out subgroups

Let `F` be a group-valued functor on commutative `R`-algebras corepresented by `B`. For an ideal
`K` of `B`, the points whose classifying map kills `K` form a subfunctor of `F`, which need not
be a subgroup. The points `g` for which conjugation by `g` and by `g⁻¹` preserves this
subfunctor after every algebra map are cut out by the Library ideal `subgroupNormalizerIdeal e K`
when `B ⧸ K` is projective.

For a subgroup family cut out by `J` and the augmentation ideal `I` of `B`, we apply this to the
jet ideals `J ⊔ I ^ (n + 1)`, which cut out the `n`-th infinitesimal neighbourhoods of the unit
in the subgroup. Conjugation preserves the infinitesimal neighbourhoods of the unit in `F`, so
the resulting stabilizer ideals increase with `n` and are contained in `J`.
-/

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

namespace Langlands.GroupScheme.Corepresented

open Langlands.Algebra.ProjectiveTensorCoefficients

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

section Stabilizer

variable (K : Ideal B)

/-- A point vanishes on `K` when its classifying algebra map kills `K`. -/
def VanishesOn {A : CommAlgCat.{u} R} (x : F.obj A) : Prop :=
  ∀ b ∈ K, (e.homEquiv.symm x).hom b = 0

/-- A point `g` stabilizes the subfunctor cut out by `K` when, after every algebra map,
conjugation by `g` and by `g⁻¹` maps points vanishing on `K` to points vanishing on `K`. -/
def Stabilizes {A : CommAlgCat.{u} R} (g : F.obj A) : Prop :=
  ∀ (A' : CommAlgCat.{u} R) (f : A ⟶ A') (x : F.obj A'), VanishesOn e K x →
    VanishesOn e K (F.map f g * x * (F.map f g)⁻¹) ∧
      VanishesOn e K ((F.map f g)⁻¹ * x * F.map f g)

variable {e K}

theorem vanishesOn_iff_le_ker {A : CommAlgCat.{u} R} (x : F.obj A) :
    VanishesOn e K x ↔ K ≤ RingHom.ker (e.homEquiv.symm x).hom :=
  ⟨fun h b hb => h b hb, fun h _ hb => h hb⟩

theorem VanishesOn.map {A A' : CommAlgCat.{u} R} (f : A ⟶ A') {x : F.obj A}
    (hx : VanishesOn e K x) : VanishesOn e K (F.map f x) := by
  intro b hb
  rw [homEquiv_symm_map, CommAlgCat.hom_comp, AlgHom.comp_apply, hx b hb, map_zero]

theorem VanishesOn.mono {K' : Ideal B} (h : K' ≤ K) {A : CommAlgCat.{u} R} {x : F.obj A}
    (hx : VanishesOn e K x) : VanishesOn e K' x :=
  fun b hb => hx b (h hb)

theorem vanishesOn_sup {K' : Ideal B} {A : CommAlgCat.{u} R} (x : F.obj A) :
    VanishesOn e (K ⊔ K') x ↔ VanishesOn e K x ∧ VanishesOn e K' x := by
  simp only [vanishesOn_iff_le_ker, sup_le_iff]

theorem vanishesOn_universalCutPoint (A : CommAlgCat.{u} R) :
    VanishesOn e K (universalCutPoint e K A) := by
  intro b hb
  rw [universalCutPoint, Equiv.symm_apply_apply]
  change Algebra.TensorProduct.includeRight (Ideal.Quotient.mk K b) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hb, map_zero]

/-- Every point vanishing on `K` over an `A`-algebra `A'` is the image of the universal point
under an algebra map `A ⊗[R] (B ⧸ K) ⟶ A'` restricting to the structure map on `A`. -/
theorem exists_universalCutPoint_of_vanishesOn {A A' : CommAlgCat.{u} R} (f : A ⟶ A')
    {x : F.obj A'} (hx : VanishesOn e K x) :
    ∃ h : tensorQuotient K A ⟶ A', tensorQuotientLeft K A ≫ h = f ∧
      F.map h (universalCutPoint e K A) = x := by
  let φ : quotientAlgebra K ⟶ A' :=
    CommAlgCat.ofHom (Ideal.Quotient.liftₐ K (e.homEquiv.symm x).hom hx)
  refine ⟨CommAlgCat.ofHom (Algebra.TensorProduct.lift f.hom φ.hom
    fun _ _ => Commute.all _ _), ?_, ?_⟩
  · ext a
    simp
  · rw [universalCutPoint]
    erw [← e.homEquiv_comp]
    rw [← Equiv.apply_symm_apply e.homEquiv x]
    congr 1
    ext b
    simp only [φ, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, AlgHom.coe_comp, Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact Ideal.Quotient.lift_mk _ _ _

/-- The stabilizer condition only needs to be tested on the universal cut point. -/
theorem stabilizes_iff_universal {A : CommAlgCat.{u} R} (g : F.obj A) :
    Stabilizes e K g ↔
      VanishesOn e K (F.map (tensorQuotientLeft K A) g * universalCutPoint e K A *
          (F.map (tensorQuotientLeft K A) g)⁻¹) ∧
        VanishesOn e K ((F.map (tensorQuotientLeft K A) g)⁻¹ * universalCutPoint e K A *
          F.map (tensorQuotientLeft K A) g) := by
  constructor
  · intro hg
    exact hg _ _ _ (vanishesOn_universalCutPoint A)
  · rintro ⟨h₁, h₂⟩ A' f x hx
    obtain ⟨h, hf, rfl⟩ := exists_universalCutPoint_of_vanishesOn f hx
    have hg : F.map f g = F.map h (F.map (tensorQuotientLeft K A) g) := by
      rw [← hf, F.map_comp, ConcreteCategory.comp_apply]
    rw [hg, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    exact ⟨h₁.map h, h₂.map h⟩

/-- After base change along `φ : B ⟶ A`, a point over `B ⊗[R] (B ⧸ K)` vanishes on `K`
exactly when `φ` kills the coefficient ideal of the image of `K` under its classifying map. -/
theorem vanishesOn_map_tensorQuotientMap_iff [Module.Projective R (B ⧸ K)]
    {A : CommAlgCat.{u} R} (φ : B ⟶ A) (y : F.obj (tensorQuotient K B)) :
    VanishesOn e K (F.map (tensorQuotientMap K φ) y) ↔
      coefficientIdeal ((e.homEquiv.symm y).hom '' (K : Set B) : Set (B ⊗[R] (B ⧸ K))) ≤
        RingHom.ker φ.hom.toRingHom := by
  rw [VanishesOn, coefficientIdeal_le_ker_iff, Set.forall_mem_image]
  have h : e.homEquiv.symm (F.map (tensorQuotientMap K φ) y) =
      e.homEquiv.symm y ≫ tensorQuotientMap K φ :=
    (e.homEquiv_symm_comp y (tensorQuotientMap K φ)).symm
  refine forall₂_congr fun b _ => ?_
  rw [h, CommAlgCat.hom_comp, AlgHom.comp_apply, tensorQuotientMap_apply]

/-- **The stabilizer of the subfunctor cut out by `K` is cut out by
`subgroupNormalizerIdeal e K`.** -/
theorem stabilizes_iff [Module.Projective R (B ⧸ K)] {A : CommAlgCat.{u} R} (φ : B ⟶ A) :
    Stabilizes e K (e.homEquiv φ) ↔
      subgroupNormalizerIdeal e K ≤ RingHom.ker φ.hom.toRingHom := by
  rw [stabilizes_iff_universal, ← map_universalConjugate, ← map_universalInvConjugate,
    vanishesOn_map_tensorQuotientMap_iff, vanishesOn_map_tensorQuotientMap_iff,
    subgroupNormalizerIdeal, sup_le_iff]

end Stabilizer

section Jets

/-- The augmentation ideal of `B`, the kernel of the counit. -/
def augIdeal : Ideal B :=
  RingHom.ker (LinearEmbedding.counit e).hom

/-- The jet ideal `J ⊔ I ^ (n + 1)`, cutting out the `n`-th infinitesimal neighbourhood of the
unit in the subfunctor cut out by `J`. -/
def jetIdeal (J : Ideal B) (n : ℕ) : Ideal B :=
  J ⊔ augIdeal e ^ (n + 1)

variable {e}

/-- A point that becomes the unit modulo an ideal `N` has its classifying map sending the
augmentation ideal into `N`. -/
theorem classify_mem_of_map_eq_one {A : CommAlgCat.{u} R} (N : Ideal A) (x : F.obj A)
    (hx : F.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)) x = 1) {b : B}
    (hb : b ∈ augIdeal e) : (e.homEquiv.symm x).hom b ∈ N := by
  have h := congrArg (fun y => (e.homEquiv.symm y).hom b) hx
  have hunit := LinearEmbedding.cls_one e (CommAlgCat.of R (A ⧸ N))
  dsimp only [LinearEmbedding.cls, LinearEmbedding.unitMap] at hunit
  simp only [homEquiv_symm_map, hunit, CommAlgCat.hom_comp, AlgHom.comp_apply,
    CommAlgCat.hom_ofHom] at h
  rw [augIdeal, RingHom.mem_ker] at hb
  rw [hb, map_zero, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h
  exact h

/-- A point whose classifying map sends the augmentation ideal into `N` becomes the unit
modulo `N`. -/
theorem map_eq_one_of_classify_mem {A : CommAlgCat.{u} R} (N : Ideal A) (x : F.obj A)
    (hx : ∀ b ∈ augIdeal e, (e.homEquiv.symm x).hom b ∈ N) :
    F.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)) x = 1 := by
  apply e.homEquiv.symm.injective
  have hunit := LinearEmbedding.cls_one e (CommAlgCat.of R (A ⧸ N))
  dsimp only [LinearEmbedding.cls, LinearEmbedding.unitMap] at hunit
  rw [homEquiv_symm_map, hunit]
  ext b
  simp only [CommAlgCat.hom_comp, AlgHom.comp_apply, CommAlgCat.hom_ofHom]
  have hmem : b - algebraMap R B ((LinearEmbedding.counit e).hom b) ∈ augIdeal e := by
    rw [augIdeal, RingHom.mem_ker, map_sub, AlgHom.commutes]
    exact sub_self _
  have h := hx _ hmem
  rw [map_sub, AlgHom.commutes] at h
  rw [Algebra.ofId_apply, ← (Ideal.Quotient.mkₐ R N).commutes, ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact h

/-- **Conjugation preserves the infinitesimal neighbourhoods of the unit.** -/
theorem VanishesOn.conj {m : ℕ} {A : CommAlgCat.{u} R} (g : F.obj A) {x : F.obj A}
    (hx : VanishesOn e (augIdeal e ^ m) x) :
    VanishesOn e (augIdeal e ^ m) (g * x * g⁻¹) := by
  set N : Ideal A := (augIdeal e).map (e.homEquiv.symm x).hom
  have h1 : F.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)) x = 1 :=
    map_eq_one_of_classify_mem N x fun b hb => Ideal.mem_map_of_mem _ hb
  have h2 : F.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)) (g * x * g⁻¹) = 1 := by
    rw [map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  have hle : (augIdeal e).map (e.homEquiv.symm (g * x * g⁻¹)).hom ≤ N :=
    Ideal.map_le_iff_le_comap.2 fun b hb => classify_mem_of_map_eq_one N _ h2 hb
  have hx' : (augIdeal e ^ m).map (e.homEquiv.symm x).hom = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).2 ((vanishesOn_iff_le_ker x).1 hx)
  rw [vanishesOn_iff_le_ker, ← Ideal.map_eq_bot_iff_le_ker, eq_bot_iff, Ideal.map_pow]
  rw [Ideal.map_pow] at hx'
  exact hx' ▸ Ideal.pow_right_mono hle m

variable {J : Ideal B} {n : ℕ}

theorem jetIdeal_succ_le : jetIdeal e J (n + 1) ≤ jetIdeal e J n :=
  sup_le_sup_left (Ideal.pow_le_pow_right (by omega)) _

theorem le_jetIdeal : J ≤ jetIdeal e J n :=
  le_sup_left

/-- Stabilizing the `(n + 1)`-st neighbourhood implies stabilizing the `n`-th one. -/
theorem Stabilizes.of_succ {A : CommAlgCat.{u} R} {g : F.obj A}
    (hg : Stabilizes e (jetIdeal e J (n + 1)) g) : Stabilizes e (jetIdeal e J n) g := by
  intro A' f x hx
  obtain ⟨h₁, h₂⟩ := hg A' f x (hx.mono jetIdeal_succ_le)
  simp only [jetIdeal, vanishesOn_sup] at hx h₁ h₂ ⊢
  refine ⟨⟨h₁.1, hx.2.conj _⟩, ⟨h₂.1, ?_⟩⟩
  simpa only [inv_inv] using hx.2.conj (F.map f g)⁻¹

/-- Points of a subgroup family cut out by `J` stabilize all its infinitesimal
neighbourhoods. -/
theorem stabilizes_of_mem {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)}
    (hH : IsCutOutBy e H J) {A : CommAlgCat.{u} R} {g : F.obj A} (hg : g ∈ H A) :
    Stabilizes e (jetIdeal e J n) g := by
  intro A' f x hx
  simp only [jetIdeal, vanishesOn_sup] at hx ⊢
  have hgf : F.map f g ∈ H A' := hH.map_mem f hg
  have hxH : x ∈ H A' := (hH A' x).2 hx.1
  refine ⟨⟨(hH A' _).1 ?_, hx.2.conj _⟩, ⟨(hH A' _).1 ?_, ?_⟩⟩
  · exact mul_mem (mul_mem hgf hxH) (inv_mem hgf)
  · exact mul_mem (mul_mem (inv_mem hgf) hxH) hgf
  · simpa only [inv_inv] using hx.2.conj (F.map f g)⁻¹

/-- The stabilizer ideals of the infinitesimal neighbourhoods are contained in `J`. -/
theorem subgroupNormalizerIdeal_jetIdeal_le {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)}
    (hH : IsCutOutBy e H J) [Module.Projective R (B ⧸ jetIdeal e J n)] :
    subgroupNormalizerIdeal e (jetIdeal e J n) ≤ J := by
  have hmem : e.homEquiv (quotientMap J) ∈ H (quotientAlgebra J) := by
    rw [hH, Equiv.symm_apply_apply]
    intro b hb
    exact Ideal.Quotient.eq_zero_iff_mem.2 hb
  have h := (stabilizes_iff (quotientMap J)).1 (stabilizes_of_mem (n := n) hH hmem)
  intro b hb
  have hb' := h hb
  rw [RingHom.mem_ker] at hb'
  exact Ideal.Quotient.eq_zero_iff_mem.1 hb'

/-- The stabilizer ideals of the infinitesimal neighbourhoods increase with `n`. -/
theorem subgroupNormalizerIdeal_jetIdeal_mono [Module.Projective R (B ⧸ jetIdeal e J n)]
    [Module.Projective R (B ⧸ jetIdeal e J (n + 1))] :
    subgroupNormalizerIdeal e (jetIdeal e J n) ≤
      subgroupNormalizerIdeal e (jetIdeal e J (n + 1)) := by
  set a := subgroupNormalizerIdeal e (jetIdeal e J (n + 1))
  have h := (stabilizes_iff (quotientMap a)).1
    ((stabilizes_iff (quotientMap a)).2 (by
      intro b hb
      rw [RingHom.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hb)).of_succ
  intro b hb
  have hb' := h hb
  rw [RingHom.mem_ker] at hb'
  exact Ideal.Quotient.eq_zero_iff_mem.1 hb'

end Jets

end Langlands.GroupScheme.Corepresented
