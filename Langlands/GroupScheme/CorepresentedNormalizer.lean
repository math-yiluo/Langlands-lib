import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.Algebra.ProjectiveTensorCoefficients

/-! # Normalizers and centralizers of cut-out algebra-point subgroups

For a group-valued functor `F` on commutative `R`-algebras corepresented by `B`, and subgroups
`H A ⊆ F A` cut out by an ideal `I` of `B`, the normalizer and centralizer families of `H`
(tested after every algebra extension) are again cut out by explicit ideals of `B`, provided
`B ⧸ I` is projective over `R`.
-/

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

namespace Langlands.GroupScheme.Corepresented

open Langlands.Algebra.ProjectiveTensorCoefficients

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}

section Families

variable (H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A))

/-- The normalizer family of `H`: `g ∈ F A` normalizes `H` when, after every algebra map
`f : A ⟶ A'`, conjugation by `F.map f g` and by its inverse maps `H A'` into itself. -/
def normalizerFamily (A : CommAlgCat.{u} R) : Subgroup (F.obj A) where
  carrier := {g | ∀ (A' : CommAlgCat.{u} R) (f : A ⟶ A') (x : F.obj A'), x ∈ H A' →
      F.map f g * x * (F.map f g)⁻¹ ∈ H A' ∧ (F.map f g)⁻¹ * x * F.map f g ∈ H A'}
  one_mem' := by
    intro A' f x hx
    simp only [map_one, inv_one, one_mul, mul_one]
    exact ⟨hx, hx⟩
  mul_mem' := by
    intro g h hg hh A' f x hx
    simp only [map_mul, mul_inv_rev]
    constructor
    · have h2 := (hg A' f _ (hh A' f x hx).1).1
      simpa only [mul_assoc] using h2
    · have h2 := (hh A' f _ (hg A' f x hx).2).2
      simpa only [mul_assoc] using h2
  inv_mem' := by
    intro g hg A' f x hx
    simp only [map_inv, inv_inv]
    exact ⟨(hg A' f x hx).2, (hg A' f x hx).1⟩

/-- The centralizer family of `H`: `g ∈ F A` centralizes `H` when, after every algebra map
`f : A ⟶ A'`, the image `F.map f g` commutes with every element of `H A'`. -/
def centralizerFamily (A : CommAlgCat.{u} R) : Subgroup (F.obj A) where
  carrier := {g | ∀ (A' : CommAlgCat.{u} R) (f : A ⟶ A') (x : F.obj A'), x ∈ H A' →
      Commute (F.map f g) x}
  one_mem' := by
    intro A' f x _
    rw [map_one]
    exact Commute.one_left x
  mul_mem' := by
    intro g h hg hh A' f x hx
    rw [map_mul]
    exact (hg A' f x hx).mul_left (hh A' f x hx)
  inv_mem' := by
    intro g hg A' f x hx
    rw [map_inv]
    exact (hg A' f x hx).inv_left

theorem mem_normalizerFamily {A : CommAlgCat.{u} R} {g : F.obj A} :
    g ∈ normalizerFamily H A ↔ ∀ (A' : CommAlgCat.{u} R) (f : A ⟶ A') (x : F.obj A'),
      x ∈ H A' → F.map f g * x * (F.map f g)⁻¹ ∈ H A' ∧ (F.map f g)⁻¹ * x * F.map f g ∈ H A' :=
  Iff.rfl

theorem mem_centralizerFamily {A : CommAlgCat.{u} R} {g : F.obj A} :
    g ∈ centralizerFamily H A ↔ ∀ (A' : CommAlgCat.{u} R) (f : A ⟶ A') (x : F.obj A'),
      x ∈ H A' → Commute (F.map f g) x :=
  Iff.rfl

end Families

section Universal

variable (e : (F ⋙ forget GrpCat).CorepresentableBy B) (I : Ideal B)

/-- The algebra `A ⊗[R] (B ⧸ I)` carrying the universal point of the subscheme cut out by `I`
after base change to `A`. -/
abbrev tensorQuotient (A : CommAlgCat.{u} R) : CommAlgCat.{u} R :=
  CommAlgCat.of R (A ⊗[R] (B ⧸ I))

/-- The left inclusion `A ⟶ A ⊗[R] (B ⧸ I)`. -/
abbrev tensorQuotientLeft (A : CommAlgCat.{u} R) : A ⟶ tensorQuotient I A :=
  CommAlgCat.ofHom Algebra.TensorProduct.includeLeft

/-- The right inclusion `B ⧸ I ⟶ A ⊗[R] (B ⧸ I)`. -/
abbrev tensorQuotientRight (A : CommAlgCat.{u} R) : quotientAlgebra I ⟶ tensorQuotient I A :=
  CommAlgCat.ofHom Algebra.TensorProduct.includeRight

/-- The map `B ⊗[R] (B ⧸ I) ⟶ A ⊗[R] (B ⧸ I)` induced by `φ : B ⟶ A`. -/
abbrev tensorQuotientMap {A : CommAlgCat.{u} R} (φ : B ⟶ A) :
    tensorQuotient I B ⟶ tensorQuotient I A :=
  CommAlgCat.ofHom (Algebra.TensorProduct.map φ.hom (AlgHom.id R (B ⧸ I)))

/-- The universal point of the subscheme cut out by `I`, over `A ⊗[R] (B ⧸ I)`. -/
def universalCutPoint (A : CommAlgCat.{u} R) : F.obj (tensorQuotient I A) :=
  e.homEquiv (quotientMap I ≫ tensorQuotientRight I A)

variable {e I}

theorem homEquiv_symm_map {A A' : CommAlgCat.{u} R} (y : F.obj A) (g : A ⟶ A') :
    e.homEquiv.symm (F.map g y) = e.homEquiv.symm y ≫ g :=
  (e.homEquiv_symm_comp y g).symm

theorem universalCutPoint_mem {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)}
    (hH : IsCutOutBy e H I) (A : CommAlgCat.{u} R) :
    universalCutPoint e I A ∈ H (tensorQuotient I A) := by
  rw [hH]
  intro b hb
  rw [universalCutPoint, Equiv.symm_apply_apply]
  change Algebra.TensorProduct.includeRight (Ideal.Quotient.mk I b) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hb, map_zero]

/-- Every point of `H` over an `A`-algebra `A'` is the image of the universal point under an
algebra map `A ⊗[R] (B ⧸ I) ⟶ A'` restricting to the structure map on `A`. -/
theorem exists_universalCutPoint {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)}
    (hH : IsCutOutBy e H I) {A A' : CommAlgCat.{u} R} (f : A ⟶ A') {x : F.obj A'}
    (hx : x ∈ H A') :
    ∃ h : tensorQuotient I A ⟶ A', tensorQuotientLeft I A ≫ h = f ∧
      F.map h (universalCutPoint e I A) = x := by
  rw [hH] at hx
  let φ : quotientAlgebra I ⟶ A' :=
    CommAlgCat.ofHom (Ideal.Quotient.liftₐ I (e.homEquiv.symm x).hom hx)
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

/-- Base change along `φ : B ⟶ A` of the left inclusion. -/
theorem tensorQuotientLeft_comp_map {A : CommAlgCat.{u} R} (φ : B ⟶ A) :
    tensorQuotientLeft I B ≫ tensorQuotientMap I φ = φ ≫ tensorQuotientLeft I A := by
  ext b
  change Algebra.TensorProduct.map φ.hom (AlgHom.id R (B ⧸ I)) (b ⊗ₜ 1) = φ b ⊗ₜ 1
  simp

theorem map_universalCutPoint {A : CommAlgCat.{u} R} (φ : B ⟶ A) :
    F.map (tensorQuotientMap I φ) (universalCutPoint e I B) = universalCutPoint e I A := by
  rw [universalCutPoint, universalCutPoint]
  erw [← e.homEquiv_comp]
  congr 1
  ext b
  change Algebra.TensorProduct.map φ.hom (AlgHom.id R (B ⧸ I)) (1 ⊗ₜ Ideal.Quotient.mk I b) =
    1 ⊗ₜ Ideal.Quotient.mk I b
  simp

theorem map_tensorQuotientLeft_universal {A : CommAlgCat.{u} R} (φ : B ⟶ A) :
    F.map (tensorQuotientMap I φ) (F.map (tensorQuotientLeft I B) (e.homEquiv (𝟙 B))) =
      F.map (tensorQuotientLeft I A) (e.homEquiv φ) := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, tensorQuotientLeft_comp_map, F.map_comp,
    ConcreteCategory.comp_apply]
  congr 1
  erw [← e.homEquiv_comp]
  rw [Category.id_comp]

/-- On linear maps, base change of `φ` is the right tensor of `φ` with `B ⧸ I`. -/
theorem tensorQuotientMap_apply {A : CommAlgCat.{u} R} (φ : B ⟶ A) (z : B ⊗[R] (B ⧸ I)) :
    (tensorQuotientMap I φ).hom z = φ.hom.toLinearMap.rTensor (B ⧸ I) z := by
  induction z with
  | tmul b q => rfl
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- After base change along `φ : B ⟶ A`, a point over `B ⊗[R] (B ⧸ I)` lies in a family cut out
by `I` exactly when `φ` kills the coefficient ideal of the image of `I` under its classifying
map. -/
theorem map_tensorQuotientMap_mem_iff {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)}
    (hH : IsCutOutBy e H I) [Module.Projective R (B ⧸ I)] {A : CommAlgCat.{u} R} (φ : B ⟶ A)
    (y : F.obj (tensorQuotient I B)) :
    F.map (tensorQuotientMap I φ) y ∈ H (tensorQuotient I A) ↔
      coefficientIdeal ((e.homEquiv.symm y).hom '' (I : Set B) : Set (B ⊗[R] (B ⧸ I))) ≤
        RingHom.ker φ.hom.toRingHom := by
  rw [hH, coefficientIdeal_le_ker_iff, Set.forall_mem_image]
  have h : e.homEquiv.symm (F.map (tensorQuotientMap I φ) y) =
      e.homEquiv.symm y ≫ tensorQuotientMap I φ :=
    (e.homEquiv_symm_comp y (tensorQuotientMap I φ)).symm
  refine forall₂_congr fun b _ => ?_
  rw [h, CommAlgCat.hom_comp, AlgHom.comp_apply, tensorQuotientMap_apply]

variable (e I)

/-- The universal point of `F`, pulled back to `B ⊗[R] (B ⧸ I)`. -/
abbrev universalLeftPoint : F.obj (tensorQuotient I B) :=
  F.map (tensorQuotientLeft I B) (e.homEquiv (𝟙 B))

/-- The universal conjugate `g x g⁻¹` of the universal cut point `x` by the universal point
`g`. -/
abbrev universalConjugate : F.obj (tensorQuotient I B) :=
  universalLeftPoint e I * universalCutPoint e I B * (universalLeftPoint e I)⁻¹

/-- The universal conjugate `g⁻¹ x g`. -/
abbrev universalInvConjugate : F.obj (tensorQuotient I B) :=
  (universalLeftPoint e I)⁻¹ * universalCutPoint e I B * universalLeftPoint e I

/-- The ideal of `B` cutting out the normalizer family: the coefficients, along `B ⧸ I`, of the
classifying maps of both universal conjugates applied to `I`. -/
def subgroupNormalizerIdeal : Ideal B :=
  coefficientIdeal ((e.homEquiv.symm (universalConjugate e I)).hom '' (I : Set B) :
      Set (B ⊗[R] (B ⧸ I))) ⊔
    coefficientIdeal ((e.homEquiv.symm (universalInvConjugate e I)).hom '' (I : Set B) :
      Set (B ⊗[R] (B ⧸ I)))

/-- The ideal of `B` cutting out the centralizer family: the coefficients, along `B ⧸ I`, of
the differences of the classifying maps of `g x` and `x g` for the universal points. -/
def subgroupCentralizerIdeal : Ideal B :=
  coefficientIdeal (Set.range fun b : B =>
    (e.homEquiv.symm (universalLeftPoint e I * universalCutPoint e I B)).hom b -
      (e.homEquiv.symm (universalCutPoint e I B * universalLeftPoint e I)).hom b)

variable {e I}

/-- The normalizer condition only needs to be tested on the universal cut point. -/
theorem mem_normalizerFamily_iff {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)}
    (hH : IsCutOutBy e H I) {A : CommAlgCat.{u} R} (g : F.obj A) :
    g ∈ normalizerFamily H A ↔
      F.map (tensorQuotientLeft I A) g * universalCutPoint e I A *
          (F.map (tensorQuotientLeft I A) g)⁻¹ ∈ H (tensorQuotient I A) ∧
        (F.map (tensorQuotientLeft I A) g)⁻¹ * universalCutPoint e I A *
          F.map (tensorQuotientLeft I A) g ∈ H (tensorQuotient I A) := by
  constructor
  · intro hg
    exact hg _ _ _ (universalCutPoint_mem hH A)
  · rintro ⟨h₁, h₂⟩ A' f x hx
    obtain ⟨h, hf, rfl⟩ := exists_universalCutPoint hH f hx
    have hg : F.map f g = F.map h (F.map (tensorQuotientLeft I A) g) := by
      rw [← hf, F.map_comp, ConcreteCategory.comp_apply]
    rw [hg, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    exact ⟨hH.map_mem h h₁, hH.map_mem h h₂⟩

/-- The centralizer condition only needs to be tested on the universal cut point. -/
theorem mem_centralizerFamily_iff {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)}
    (hH : IsCutOutBy e H I) {A : CommAlgCat.{u} R} (g : F.obj A) :
    g ∈ centralizerFamily H A ↔
      Commute (F.map (tensorQuotientLeft I A) g) (universalCutPoint e I A) := by
  constructor
  · intro hg
    exact hg _ _ _ (universalCutPoint_mem hH A)
  · rintro hc A' f x hx
    obtain ⟨h, hf, rfl⟩ := exists_universalCutPoint hH f hx
    have hg : F.map f g = F.map h (F.map (tensorQuotientLeft I A) g) := by
      rw [← hf, F.map_comp, ConcreteCategory.comp_apply]
    rw [hg]
    exact hc.map (F.map h).hom

theorem map_universalConjugate {A : CommAlgCat.{u} R} (φ : B ⟶ A) :
    F.map (tensorQuotientMap I φ) (universalConjugate e I) =
      F.map (tensorQuotientLeft I A) (e.homEquiv φ) * universalCutPoint e I A *
        (F.map (tensorQuotientLeft I A) (e.homEquiv φ))⁻¹ := by
  rw [map_mul, map_mul, map_inv, map_tensorQuotientLeft_universal, map_universalCutPoint]

theorem map_universalInvConjugate {A : CommAlgCat.{u} R} (φ : B ⟶ A) :
    F.map (tensorQuotientMap I φ) (universalInvConjugate e I) =
      (F.map (tensorQuotientLeft I A) (e.homEquiv φ))⁻¹ * universalCutPoint e I A *
        F.map (tensorQuotientLeft I A) (e.homEquiv φ) := by
  rw [map_mul, map_mul, map_inv, map_tensorQuotientLeft_universal, map_universalCutPoint]

/-- **The normalizer family is cut out by `subgroupNormalizerIdeal`.** -/
theorem isCutOutBy_normalizerFamily {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)}
    (hH : IsCutOutBy e H I) [Module.Projective R (B ⧸ I)] :
    IsCutOutBy e (normalizerFamily H) (subgroupNormalizerIdeal e I) := by
  intro A g
  obtain ⟨φ, rfl⟩ := e.homEquiv.surjective g
  rw [mem_normalizerFamily_iff hH, Equiv.symm_apply_apply, ← map_universalConjugate,
    ← map_universalInvConjugate, map_tensorQuotientMap_mem_iff hH,
    map_tensorQuotientMap_mem_iff hH, ← sup_le_iff]
  exact ⟨fun h b hb => h hb, fun h b hb => h b hb⟩

/-- **The centralizer family is cut out by `subgroupCentralizerIdeal`.** -/
theorem isCutOutBy_centralizerFamily {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)}
    (hH : IsCutOutBy e H I) [Module.Projective R (B ⧸ I)] :
    IsCutOutBy e (centralizerFamily H) (subgroupCentralizerIdeal e I) := by
  intro A g
  obtain ⟨φ, rfl⟩ := e.homEquiv.surjective g
  rw [mem_centralizerFamily_iff hH, Equiv.symm_apply_apply]
  have h₁ : F.map (tensorQuotientLeft I A) (e.homEquiv φ) * universalCutPoint e I A =
      F.map (tensorQuotientMap I φ) (universalLeftPoint e I * universalCutPoint e I B) := by
    rw [map_mul, map_tensorQuotientLeft_universal, map_universalCutPoint]
  have h₂ : universalCutPoint e I A * F.map (tensorQuotientLeft I A) (e.homEquiv φ) =
      F.map (tensorQuotientMap I φ) (universalCutPoint e I B * universalLeftPoint e I) := by
    rw [map_mul, map_tensorQuotientLeft_universal, map_universalCutPoint]
  have hk : subgroupCentralizerIdeal e I ≤ RingHom.ker φ.hom.toRingHom ↔
      ∀ b : B, (tensorQuotientMap I φ).hom
          ((e.homEquiv.symm (universalLeftPoint e I * universalCutPoint e I B)).hom b) =
        (tensorQuotientMap I φ).hom
          ((e.homEquiv.symm (universalCutPoint e I B * universalLeftPoint e I)).hom b) := by
    rw [subgroupCentralizerIdeal, coefficientIdeal_le_ker_iff, Set.forall_mem_range]
    refine forall_congr' fun b => ?_
    rw [← tensorQuotientMap_apply, map_sub, sub_eq_zero]
  rw [Commute, SemiconjBy, h₁, h₂]
  refine ⟨fun h c hc => hk.2 (fun b => ?_) hc, fun h => ?_⟩
  · have h' := congrArg (fun y => (e.homEquiv.symm y).hom b) h
    simp only at h'
    rwa [homEquiv_symm_map, homEquiv_symm_map, CommAlgCat.hom_comp,
      CommAlgCat.hom_comp, AlgHom.comp_apply, AlgHom.comp_apply] at h'
  · have hk' := hk.1 fun b hb => h b hb
    apply e.homEquiv.symm.injective
    rw [homEquiv_symm_map, homEquiv_symm_map]
    ext b
    exact hk' b

end Universal

end Langlands.GroupScheme.Corepresented
