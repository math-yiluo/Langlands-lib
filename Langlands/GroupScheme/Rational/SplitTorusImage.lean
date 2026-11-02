import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.Rational.Characters
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Images of split tori in affine group schemes over a field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace SplitTorusImage

open Corepresented Diagonalizable
open Corepresented.LinearEmbedding (comul)

variable {k : Type u} [Field k]

/-! ### Injectivity of tensor products of injective maps over a field -/

section Tensor

variable {A B C D : CommAlgCat.{u} (CommRingCat.of k)}

theorem tensorLift_inl_inr_toLinearMap (f : A ⟶ C) (g : B ⟶ D) :
    (tensorLift (f ≫ inl C D) (g ≫ inr C D)).hom.toLinearMap =
      TensorProduct.map f.hom.toLinearMap g.hom.toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  change (f.hom a ⊗ₜ[CommRingCat.of k] (1 : D)) * ((1 : C) ⊗ₜ[CommRingCat.of k] g.hom b) =
    f.hom a ⊗ₜ g.hom b
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Over a field, the tensor product of two injective algebra maps is injective. -/
theorem tensorLift_injective (f : A ⟶ C) (g : B ⟶ D) (hf : Function.Injective f.hom)
    (hg : Function.Injective g.hom) :
    Function.Injective (tensorLift (f ≫ inl C D) (g ≫ inr C D)).hom := by
  have h := TensorProduct.map_injective_of_flat_flat f.hom.toLinearMap g.hom.toLinearMap hf hg
  rw [← tensorLift_inl_inr_toLinearMap] at h
  exact h

end Tensor

/-! ### Coefficient extraction -/

section Extract

variable {Λ : Type u} [AddCommGroup Λ]

/-- The coefficient of `γ`, as a linear form on the group algebra. -/
def coeffAt (γ : Λ) : AddMonoidAlgebra k Λ →ₗ[k] k :=
  Finsupp.lapply γ ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

omit [AddCommGroup Λ] in
@[simp] theorem coeffAt_apply (γ : Λ) (p : AddMonoidAlgebra k Λ) : coeffAt γ p = p.coeff γ :=
  rfl

/-- The linear map `p ⊗ q ↦ q_γ • p`. -/
def extract (γ : Λ) :
    AddMonoidAlgebra k Λ ⊗[k] AddMonoidAlgebra k Λ →ₗ[k] AddMonoidAlgebra k Λ :=
  (TensorProduct.rid k (AddMonoidAlgebra k Λ)).toLinearMap ∘ₗ
    LinearMap.lTensor (AddMonoidAlgebra k Λ) (coeffAt γ)

@[simp] theorem extract_tmul (γ : Λ) (p q : AddMonoidAlgebra k Λ) :
    extract γ (p ⊗ₜ q) = q.coeff γ • p :=
  rfl

/-- Extracting the `γ`-coefficient of the comultiplication of `p` gives its `γ`-monomial. -/
theorem extract_comul (γ : Λ) (p : AddMonoidAlgebra k Λ) :
    extract γ ((comul (grpCorepresentation (CommRingCat.of k) Λ)).hom p) =
      p.coeff γ • AddMonoidAlgebra.single γ (1 : k) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, add_smul]
  | single δ r =>
    erw [comul_single]
    rw [extract_tmul, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single]
    by_cases h : δ = γ
    · subst h
      simp
    · simp [h]

/-- Extraction after the tensor square of an algebra map `f` factors through `f`. -/
theorem extract_tensorLift {B : CommAlgCat.{u} (CommRingCat.of k)}
    (f : B ⟶ algebra (CommRingCat.of k) Λ) (γ : Λ) :
    extract γ ∘ₗ (tensorLift (f ≫ inl _ _) (f ≫ inr _ _)).hom.toLinearMap =
      f.hom.toLinearMap ∘ₗ (TensorProduct.rid k B).toLinearMap ∘ₗ
        LinearMap.lTensor B (coeffAt γ ∘ₗ f.hom.toLinearMap) := by
  apply TensorProduct.ext'
  intro x y
  change extract γ ((f.hom x ⊗ₜ[CommRingCat.of k] (1 : AddMonoidAlgebra k Λ)) *
    ((1 : AddMonoidAlgebra k Λ) ⊗ₜ[CommRingCat.of k] f.hom y)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, extract_tmul]
  simp

end Extract

/-! ### The image of a homomorphism out of a diagonalizable group -/

section Core

variable {Λ : Type u} [AddCommGroup Λ] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (β : functor (CommRingCat.of k) Λ ⟶ F)

/-- The classifying map `B ⟶ k[Λ]` of the image of the universal character. -/
abbrev classifying : B ⟶ algebra (CommRingCat.of k) Λ :=
  classify (grpCorepresentation (CommRingCat.of k) Λ) e β

/-- Every monomial term of an element in the range of the classifying map lies in that range. -/
theorem coeff_smul_single_mem (a : B) (γ : Λ) :
    ((classifying e β).hom a).coeff γ • AddMonoidAlgebra.single γ (1 : k) ∈
      (classifying e β).hom.range := by
  have h := congrArg (fun f : B ⟶ _ => f.hom a)
    (classify_comul (grpCorepresentation (CommRingCat.of k) Λ) e β)
  simp only [CommAlgCat.hom_comp, AlgHom.comp_apply] at h
  rw [← extract_comul, h]
  have h' := LinearMap.congr_fun (extract_tensorLift (classifying e β) γ) ((comul e).hom a)
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply] at h'
  rw [h']
  exact ⟨_, rfl⟩

/-- The exponents whose monomials lie in the range of the classifying map. -/
def latticeSubgroup : AddSubgroup Λ where
  carrier := {γ | AddMonoidAlgebra.single γ (1 : k) ∈ (classifying e β).hom.range}
  zero_mem' := by
    change AddMonoidAlgebra.single (0 : Λ) (1 : k) ∈ (classifying e β).hom.range
    rw [← AddMonoidAlgebra.one_def]
    exact Subalgebra.one_mem _
  add_mem' := fun {γ δ} hγ hδ => by
    have h := Subalgebra.mul_mem (classifying e β).hom.range hγ hδ
    rwa [AddMonoidAlgebra.single_mul_single, mul_one] at h
  neg_mem' := fun {γ} hγ => by
    obtain ⟨x, hx⟩ := (AlgHom.mem_range _).mp hγ
    refine (AlgHom.mem_range _).mpr ⟨(antipode e).hom x, ?_⟩
    have h := congrArg (fun f : B ⟶ _ => f.hom x)
      (classify_antipode (grpCorepresentation (CommRingCat.of k) Λ) e β)
    simp only [CommAlgCat.hom_comp, AlgHom.comp_apply] at h
    rw [← h, hx]
    erw [antipode_single]

/-- The character lattice of the image, as a `ℤ`-submodule of `Λ`. -/
abbrev lattice : Submodule ℤ Λ :=
  (latticeSubgroup e β).toIntSubmodule

theorem mem_lattice_of_coeff_ne_zero {a : B} {γ : Λ}
    (h : ((classifying e β).hom a).coeff γ ≠ 0) : γ ∈ lattice e β := by
  have hm := Subalgebra.smul_mem _ (coeff_smul_single_mem e β a γ)
    (((classifying e β).hom a).coeff γ)⁻¹
  rw [smul_smul, inv_mul_cancel₀ h, one_smul] at hm
  exact hm

/-- The inclusion `k[L] → k[Λ]` of the image lattice. -/
abbrev latticeIncl : algebra (CommRingCat.of k) (lattice e β) ⟶ algebra (CommRingCat.of k) Λ :=
  incl (CommRingCat.of k) (lattice e β).subtype.toAddMonoidHom

theorem latticeIncl_injective : Function.Injective (latticeIncl e β).hom :=
  incl_injective _ _ Subtype.val_injective

theorem range_le_latticeIncl :
    (classifying e β).hom.range ≤ (latticeIncl e β).hom.range := by
  intro y hy
  obtain ⟨a, rfl⟩ := (AlgHom.mem_range _).mp hy
  rw [← AddMonoidAlgebra.sum_coeff_single ((classifying e β).hom a)]
  refine Subalgebra.sum_mem _ fun γ hγ => ?_
  have hmem := mem_lattice_of_coeff_ne_zero e β (Finsupp.mem_support_iff.mp hγ)
  exact (AlgHom.mem_range _).mpr
    ⟨AddMonoidAlgebra.single ⟨γ, hmem⟩ (((classifying e β).hom a).coeff γ), incl_single _ _ _ _⟩

theorem latticeIncl_range_le :
    (latticeIncl e β).hom.range ≤ (classifying e β).hom.range := by
  intro z hz
  obtain ⟨y, rfl⟩ := (AlgHom.mem_range _).mp hz
  clear hz
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact Subalgebra.zero_mem _
  | add y z hy hz => rw [map_add]; exact Subalgebra.add_mem _ hy hz
  | single γ r =>
    rw [incl_single]
    have hm := Subalgebra.smul_mem _ (show AddMonoidAlgebra.single (γ : Λ) (1 : k) ∈
      (classifying e β).hom.range from γ.2) r
    rwa [AddMonoidAlgebra.smul_single', mul_one] at hm

/-- The classifying map with values in the group algebra of the image lattice. -/
def corestrict : B ⟶ algebra (CommRingCat.of k) (lattice e β) :=
  CommAlgCat.ofHom ((AlgEquiv.ofInjective (latticeIncl e β).hom
    (latticeIncl_injective e β)).symm.toAlgHom.comp
      ((classifying e β).hom.codRestrict _ fun a => range_le_latticeIncl e β ⟨a, rfl⟩))

theorem corestrict_latticeIncl : corestrict e β ≫ latticeIncl e β = classifying e β := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  change (latticeIncl e β).hom ((AlgEquiv.ofInjective (latticeIncl e β).hom
    (latticeIncl_injective e β)).symm _) = _
  rw [← AlgEquiv.ofInjective_apply (latticeIncl e β).hom (latticeIncl_injective e β),
    AlgEquiv.apply_symm_apply]
  rfl

theorem corestrict_surjective : Function.Surjective (corestrict e β).hom := by
  intro y
  obtain ⟨a, ha⟩ := (AlgHom.mem_range _).mp (latticeIncl_range_le e β (AlgHom.mem_range_self _ y))
  refine ⟨a, latticeIncl_injective e β ?_⟩
  rw [← ha, ← CommAlgCat.comp_apply, corestrict_latticeIncl]

/-- The corestricted classifying map is compatible with the comultiplications. -/
theorem corestrict_comul :
    corestrict e β ≫ comul (grpCorepresentation (CommRingCat.of k) (lattice e β)) =
      comul e ≫ tensorLift (corestrict e β ≫ inl _ _) (corestrict e β ≫ inr _ _) := by
  have hinj := tensorLift_injective (latticeIncl e β) (latticeIncl e β)
    (latticeIncl_injective e β) (latticeIncl_injective e β)
  have lhs : (corestrict e β ≫ comul (grpCorepresentation (CommRingCat.of k) (lattice e β))) ≫
      tensorLift (latticeIncl e β ≫ inl _ _) (latticeIncl e β ≫ inr _ _) =
        comul e ≫ tensorLift (classifying e β ≫ inl _ _) (classifying e β ≫ inr _ _) := by
    rw [Category.assoc, comul_incl, ← Category.assoc, corestrict_latticeIncl, classify_comul]
  have rhs : (comul e ≫ tensorLift (corestrict e β ≫ inl _ _) (corestrict e β ≫ inr _ _)) ≫
      tensorLift (latticeIncl e β ≫ inl _ _) (latticeIncl e β ≫ inr _ _) =
        comul e ≫ tensorLift (classifying e β ≫ inl _ _) (classifying e β ≫ inr _ _) := by
    rw [Category.assoc, tensorLift_comp, Category.assoc, Category.assoc, inl_tensorLift,
      inr_tensorLift, ← Category.assoc, ← Category.assoc, corestrict_latticeIncl]
  have key := lhs.trans rhs.symm
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  apply hinj
  exact congrArg (fun f => f.hom a) key

/-- The natural homomorphism `Hom(L, Sˣ) → F(S)` given by `χ ↦ e(corestrict ≫ χ)`, where `L` is
the image lattice. -/
def imageTrans : functor (CommRingCat.of k) (lattice e β) ⟶ F where
  app S := GrpCat.ofHom (MonoidHom.mk'
    (fun χ => e.homEquiv (corestrict e β ≫
      (grpCorepresentation (CommRingCat.of k) (lattice e β)).homEquiv.symm χ))
    (fun χ₁ χ₂ => by
      rw [homEquiv_symm_mul, ← Category.assoc, corestrict_comul, Category.assoc, tensorLift_comp,
        Category.assoc, Category.assoc, inl_tensorLift, inr_tensorLift]
      have h := homEquiv_symm_mul e
        (e.homEquiv (corestrict e β ≫
          (grpCorepresentation (CommRingCat.of k) (lattice e β)).homEquiv.symm χ₁))
        (e.homEquiv (corestrict e β ≫
          (grpCorepresentation (CommRingCat.of k) (lattice e β)).homEquiv.symm χ₂))
      simp only [Equiv.symm_apply_apply] at h
      rw [← h, Equiv.apply_symm_apply]))
  naturality S S' g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    change e.homEquiv (corestrict e β ≫
        (grpCorepresentation (CommRingCat.of k) (lattice e β)).homEquiv.symm
          ((functor (CommRingCat.of k) (lattice e β)).map g χ)) =
      F.map g (e.homEquiv (corestrict e β ≫
        (grpCorepresentation (CommRingCat.of k) (lattice e β)).homEquiv.symm χ))
    have hχ : (grpCorepresentation (CommRingCat.of k) (lattice e β)).homEquiv.symm
        ((functor (CommRingCat.of k) (lattice e β)).map g χ) =
          (grpCorepresentation (CommRingCat.of k) (lattice e β)).homEquiv.symm χ ≫ g := by
      rw [Equiv.symm_apply_eq, homEquiv_comp', Equiv.apply_symm_apply]
    rw [hχ, ← Category.assoc, homEquiv_comp']

theorem imageTrans_app {S : CommAlgCat.{u} (CommRingCat.of k)}
    (χ : (functor (CommRingCat.of k) (lattice e β)).obj S) :
    (imageTrans e β).app S χ = e.homEquiv (corestrict e β ≫
      (grpCorepresentation (CommRingCat.of k) (lattice e β)).homEquiv.symm χ) :=
  rfl

/-- Restriction to the image lattice followed by `imageTrans` recovers `β`. -/
theorem restrict_imageTrans :
    restrict (CommRingCat.of k) (lattice e β).subtype.toAddMonoidHom ≫ imageTrans e β = β := by
  apply NatTrans.ext
  funext S
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  obtain ⟨f, rfl⟩ := (grpCorepresentation (CommRingCat.of k) Λ).homEquiv.surjective x
  change (imageTrans e β).app S ((restrict (CommRingCat.of k)
    (lattice e β).subtype.toAddMonoidHom).app S
      ((corepresentation (CommRingCat.of k) Λ).homEquiv f)) = _
  rw [restrict_homEquiv, imageTrans_app]
  erw [Equiv.symm_apply_apply]
  rw [← Category.assoc, corestrict_latticeIncl, app_homEquiv]

/-- The classifying map of `imageTrans` is the corestricted classifying map. -/
theorem classify_imageTrans :
    classify (grpCorepresentation (CommRingCat.of k) (lattice e β)) e (imageTrans e β) =
      corestrict e β := by
  change e.homEquiv.symm (e.homEquiv (corestrict e β ≫
    (grpCorepresentation (CommRingCat.of k) (lattice e β)).homEquiv.symm
      ((grpCorepresentation (CommRingCat.of k) (lattice e β)).homEquiv (𝟙 _)))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Category.comp_id]

/-- The homomorphism induced by `imageTrans` is a closed immersion. -/
theorem isClosedImmersion_imageTrans :
    IsClosedImmersion (groupSchemeMap (grpCorepresentation (CommRingCat.of k) (lattice e β)) e
      (imageTrans e β)).hom.hom.left := by
  rw [groupSchemeMap_hom_left, classify_imageTrans]
  exact IsClosedImmersion.spec_of_surjective _ (corestrict_surjective e β)

/-- If the values of `β` commute with all points, so do the values of `imageTrans`. -/
theorem commute_imageTrans
    (hβ : ∀ (S : CommAlgCat.{u} (CommRingCat.of k))
      (x : (functor (CommRingCat.of k) Λ).obj S) (y : F.obj S), Commute (β.app S x) y)
    (S : CommAlgCat.{u} (CommRingCat.of k))
    (χ : (functor (CommRingCat.of k) (lattice e β)).obj S) (y : F.obj S) :
    Commute ((imageTrans e β).app S χ) y := by
  let eL := grpCorepresentation (CommRingCat.of k) (lattice e β)
  let eD := grpCorepresentation (CommRingCat.of k) Λ
  let A := algebra (CommRingCat.of k) (lattice e β)
  let χ₀ : (functor (CommRingCat.of k) (lattice e β)).obj (tensorObj A B) :=
    eL.homEquiv (inl A B)
  let y₀ : F.obj (tensorObj A B) := e.homEquiv (inr A B)
  have huniv : Commute ((imageTrans e β).app _ χ₀) y₀ := by
    let β₁ : tensorObj A B ⟶ tensorObj (algebra (CommRingCat.of k) Λ) B :=
      tensorLift (latticeIncl e β ≫ inl _ B) (𝟙 B ≫ inr _ B)
    have hβ₁ : Function.Injective β₁.hom :=
      tensorLift_injective _ _ (latticeIncl_injective e β) Function.injective_id
    have hmap : Function.Injective (F.map β₁) := by
      intro u v huv
      have h1 : e.homEquiv.symm u ≫ β₁ = e.homEquiv.symm v ≫ β₁ := by
        apply e.homEquiv.injective
        rw [homEquiv_comp', homEquiv_comp', Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact huv
      have h2 : e.homEquiv.symm u = e.homEquiv.symm v := by
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro a
        apply hβ₁
        exact congrArg (fun f => f.hom a) h1
      exact e.homEquiv.symm.injective h2
    have himg : F.map β₁ ((imageTrans e β).app _ χ₀) = β.app _ (eD.homEquiv (inl _ B)) := by
      have hnat := ConcreteCategory.congr_hom ((imageTrans e β).naturality β₁) χ₀
      change (imageTrans e β).app _ ((functor (CommRingCat.of k) (lattice e β)).map β₁ χ₀) =
        F.map β₁ ((imageTrans e β).app _ χ₀) at hnat
      rw [← hnat]
      have hres : (functor (CommRingCat.of k) (lattice e β)).map β₁ χ₀ =
          (restrict (CommRingCat.of k) (lattice e β).subtype.toAddMonoidHom).app _
            (eD.homEquiv (inl _ B)) := by
        rw [restrict_homEquiv, ← homEquiv_comp', inl_tensorLift]
      rw [hres]
      exact ConcreteCategory.congr_hom (congrArg (fun α => α.app _) (restrict_imageTrans e β))
        (eD.homEquiv (inl _ B))
    show _ * _ = _ * _
    apply hmap
    rw [map_mul, map_mul, himg]
    exact (hβ _ _ _).eq
  let Lm : tensorObj A B ⟶ S := tensorLift (eL.homEquiv.symm χ) (e.homEquiv.symm y)
  have hχ : (functor (CommRingCat.of k) (lattice e β)).map Lm χ₀ = χ := by
    rw [← homEquiv_comp', inl_tensorLift, Equiv.apply_symm_apply]
  have hy : F.map Lm y₀ = y := by
    rw [← homEquiv_comp', inr_tensorLift, Equiv.apply_symm_apply]
  have hnat := ConcreteCategory.congr_hom ((imageTrans e β).naturality Lm) χ₀
  change (imageTrans e β).app _ ((functor (CommRingCat.of k) (lattice e β)).map Lm χ₀) =
    F.map Lm ((imageTrans e β).app _ χ₀) at hnat
  rw [← hχ, ← hy, hnat]
  exact huniv.map (F.map Lm).hom

end Core

end SplitTorusImage

open SplitTorusImage Corepresented Diagonalizable in
/-- Over a field `k`, every homomorphism `φ : D ⟶ H` from a split torus to an affine group
scheme factors as `π ≫ i = φ` through a split subtorus `i : D' ⟶ H`, i.e. a closed immersion of
a split torus; if `φ` is central, so is `i`. -/
theorem IsSplitTorus.exists_factor_isSplitSubtorus {k : Type u} [Field k]
    {D : CommGroupScheme (Spec (CommRingCat.of k))} (hD : IsSplitTorus D.toGrp)
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom] (φ : D.toGrp ⟶ H) :
    ∃ (D' : CommGroupScheme (Spec (CommRingCat.of k))) (π : D.toGrp ⟶ D'.toGrp)
      (i : D'.toGrp ⟶ H), IsSplitSubtorus i ∧ π ≫ i = φ ∧ (IsCentral φ → IsCentral i) := by
  classical
  obtain ⟨I, hI, ⟨eD⟩⟩ := hD
  let : Fintype I := Fintype.ofFinite I
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let G₀ := Corepresented.groupScheme (functor (CommRingCat.of k) (I → ℤ))
    (grpCorepresentation (CommRingCat.of k) (I → ℤ))
  let cH := AffineCoordinates.corepresentation H
  let Hc := Corepresented.groupScheme (AffineCoordinates.functor H) cH
  let eT : G₀ ≅ splitTorus (Spec (CommRingCat.of k)) I :=
    splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))
  let eH : Hc ≅ H := AffineCoordinates.groupSchemeIso H
  let φ₀ : G₀ ⟶ Hc := ((eT.hom ≫ eD.inv) ≫ φ) ≫ eH.symm.hom
  let β := pointsTrans (grpCorepresentation (CommRingCat.of k) (I → ℤ)) cH φ₀
  obtain ⟨n, v⟩ := Submodule.basisOfPid (Pi.basisFun ℤ I) (lattice cH β)
  let b : lattice cH β ≃+ (ULift.{u} (Fin n) → ℤ) :=
    (v.equivFun.trans (LinearEquiv.funCongrLeft ℤ ℤ Equiv.ulift)).toAddEquiv
  let Glat := Corepresented.groupScheme (functor (CommRingCat.of k) (lattice cH β))
    (grpCorepresentation (CommRingCat.of k) (lattice cH β))
  let p : G₀ ⟶ Glat := groupSchemeMap (grpCorepresentation (CommRingCat.of k) (I → ℤ))
    (grpCorepresentation (CommRingCat.of k) (lattice cH β))
    (restrict (CommRingCat.of k) (lattice cH β).subtype.toAddMonoidHom)
  let q : Glat ⟶ Hc :=
    groupSchemeMap (grpCorepresentation (CommRingCat.of k) (lattice cH β)) cH (imageTrans cH β)
  have hcomp : p ≫ q = φ₀ := by
    change groupSchemeMap _ _ _ ≫ groupSchemeMap _ _ _ = φ₀
    rw [groupSchemeMap_comp, restrict_imageTrans, groupSchemeMap_pointsTrans]
  refine ⟨groupScheme (CommRingCat.of k) (lattice cH β), (eD.hom ≫ eT.inv ≫ p : D.toGrp ⟶ Glat),
    (q ≫ eH.hom : Glat ⟶ H), ⟨isSplitTorus (CommRingCat.of k) b, ?_⟩, ?_, ?_⟩
  · have := isClosedImmersion_imageTrans cH β
    have : IsIso eH.hom.hom.hom.left :=
      (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eH)).hom)
    change IsClosedImmersion (q.hom.hom.left ≫ eH.hom.hom.hom.left)
    infer_instance
  · change (eD.hom ≫ eT.inv ≫ p) ≫ q ≫ eH.hom = φ
    rw [Category.assoc, Category.assoc, ← Category.assoc p, hcomp]
    simp only [φ₀, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.symm_hom,
      Iso.inv_hom_id, Category.comp_id]
  · intro hφ
    have hφ₀ : IsCentral φ₀ := (hφ.comp (eT.hom ≫ eD.inv)).comp_iso eH.symm
    exact (isCentral_groupSchemeMap _ cH _ (commute_imageTrans cH β
      (Corepresented.IsCentral.commute_pointsTrans _ cH hφ₀))).comp_iso eH

end Langlands.GroupScheme
