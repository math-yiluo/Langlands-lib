import Langlands.AlgebraicGeometry.FaithfullyFlatAmitsurDegreeOne
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Additive cocycles on affine faithfully flat covers

A natural additive cocycle with values in global functions, on pairs of points of an
affine flat surjective scheme over an affine base, is the coboundary of one global function.
The algebraic input is degree-one exactness of the Amitsur complex `B → B ⊗ B → B ⊗ B ⊗ B`.
-/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.AffineAdditiveCocycle

section Amitsur

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

open Algebra.TensorProduct

/-- The first face map `b ⊗ c ↦ b ⊗ c ⊗ 1`. -/
def face12 : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
  Algebra.TensorProduct.map (AlgHom.id A B) includeLeft

/-- The second face map `b ⊗ c ↦ b ⊗ 1 ⊗ c`. -/
def face13 : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
  Algebra.TensorProduct.map (AlgHom.id A B) includeRight

/-- The third face map `b ⊗ c ↦ 1 ⊗ b ⊗ c`. -/
def face23 : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
  includeRight

/-- The degree-zero differential `b ↦ 1 ⊗ b - b ⊗ 1`. -/
def e0 : B →ₗ[A] B ⊗[A] B :=
  (includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap -
    (includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap

/-- The degree-one differential: the alternating sum of the face maps. -/
def e1 : B ⊗[A] B →ₗ[A] B ⊗[A] (B ⊗[A] B) :=
  (face23 A B).toLinearMap - (face13 A B).toLinearMap + (face12 A B).toLinearMap

@[simp] theorem e0_apply (b : B) : e0 A B b = 1 ⊗ₜ[A] b - b ⊗ₜ[A] 1 := rfl

@[simp] theorem e1_tmul (b c : B) :
    e1 A B (b ⊗ₜ[A] c) =
      1 ⊗ₜ[A] (b ⊗ₜ[A] c) - b ⊗ₜ[A] (1 ⊗ₜ[A] c) + b ⊗ₜ[A] (c ⊗ₜ[A] 1) := rfl

theorem e1_e0 (b : B) : e1 A B (e0 A B b) = 0 := by
  simp only [e0_apply, map_sub, e1_tmul]
  abel

/-- Multiplying the first factor into the rest contracts the extended complex. -/
theorem contracting_identity (x : B ⊗[A] (B ⊗[A] B)) :
    (e0 A B).lTensor B (AmitsurDegreeOne.contraction A B (B ⊗[A] B) x) +
      AmitsurDegreeOne.contraction A B (B ⊗[A] (B ⊗[A] B)) ((e1 A B).lTensor B x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul b y =>
    induction y using TensorProduct.inductionOn with
    | tmul c d =>
      simp only [AmitsurDegreeOne.contraction_tmul, LinearMap.lTensor_tmul, e0_apply, e1_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.tmul_add, TensorProduct.tmul_sub,
        map_add, map_sub, mul_one]
      abel
    | add y y' hy hy' =>
      simp only [TensorProduct.tmul_add, map_add]
      rw [add_add_add_comm, hy, hy']
  | add x y hx hy =>
    simp only [map_add]
    rw [add_add_add_comm, hx, hy]

/-- Exactness after scalar extension along `A → B`, without a flatness assumption. -/
theorem baseChange_exact : Function.Exact ((e0 A B).lTensor B) ((e1 A B).lTensor B) := by
  intro x
  constructor
  · intro hx
    refine ⟨AmitsurDegreeOne.contraction A B (B ⊗[A] B) x, ?_⟩
    simpa [hx] using contracting_identity A B x
  · rintro ⟨y, rfl⟩
    have hcomp : (e1 A B).comp (e0 A B) = 0 := by
      apply LinearMap.ext
      intro z
      exact e1_e0 A B z
    rw [← LinearMap.lTensor_comp_apply, hcomp]
    simp

/-- Faithful flatness reflects the exactness. -/
theorem exact [Module.FaithfullyFlat A B] : Function.Exact (e0 A B) (e1 A B) :=
  Module.FaithfullyFlat.lTensor_reflects_exact A B _ _ (baseChange_exact A B)

/-- A degree-one Amitsur cocycle is the coboundary `b ⊗ 1 - 1 ⊗ b` of an element. -/
theorem exists_primitive [Module.FaithfullyFlat A B] (x : B ⊗[A] B)
    (hx : face13 A B x = face12 A B x + face23 A B x) :
    ∃ b : B, (includeLeft : B →ₐ[A] B ⊗[A] B) b - (includeRight : B →ₐ[A] B ⊗[A] B) b = x := by
  have h1 : e1 A B x = 0 := by
    change face23 A B x - face13 A B x + face12 A B x = 0
    rw [hx]
    abel
  obtain ⟨y, hy⟩ := (exact A B x).mp h1
  refine ⟨-y, ?_⟩
  rw [← hy, e0_apply, map_neg, map_neg, includeLeft_apply, includeRight_apply]
  abel

end Amitsur

section Scheme

variable {T₀ : Scheme.{u}}

/-- A natural additive cocycle on pairs of points of `U`, valued in global functions. -/
structure AddCocycle (U : Over T₀) where
  /-- The value on a pair of points of `U` over the same test scheme. -/
  toFun : ∀ {Z : Over T₀}, (Z ⟶ U) → (Z ⟶ U) → Γ(Z.left, ⊤)
  naturality : ∀ {Z Z' : Over T₀} (t : Z' ⟶ Z) (a b : Z ⟶ U),
    toFun (t ≫ a) (t ≫ b) = t.left.appTop (toFun a b)
  cocycle : ∀ {Z : Over T₀} (a b c : Z ⟶ U), toFun a c = toFun a b + toFun b c

variable [IsAffine T₀]

/-- The affine scheme `Spec C` over `T₀`, for a ring map from the global functions of `T₀`. -/
noncomputable def specOver {C : CommRingCat.{u}} (φC : Γ(T₀, ⊤) ⟶ C) : Over T₀ :=
  Over.mk (Spec.map φC ≫ T₀.isoSpec.inv)

/-- The point of an affine `U` over `Spec C` given by a compatible ring map. -/
noncomputable def specPoint (U : Over T₀) [IsAffine U.left] {C : CommRingCat.{u}}
    (φC : Γ(T₀, ⊤) ⟶ C) (ψ : Γ(U.left, ⊤) ⟶ C) (h : U.hom.appTop ≫ ψ = φC) :
    specOver φC ⟶ U :=
  Over.homMk (Spec.map ψ ≫ U.left.isoSpec.inv) (by
    simp only [specOver, Over.mk_hom, Category.assoc]
    rw [← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc, h])

/-- The morphism of spectra over `T₀` induced by a ring map under `Γ(T₀)`. -/
noncomputable def specMap {C C' : CommRingCat.{u}} (φC : Γ(T₀, ⊤) ⟶ C) (χ : C ⟶ C') :
    specOver (φC ≫ χ) ⟶ specOver φC :=
  Over.homMk (Spec.map χ) (by simp [specOver, Spec.map_comp])

theorem specMap_comp_specPoint (U : Over T₀) [IsAffine U.left] {C C' : CommRingCat.{u}}
    (φC : Γ(T₀, ⊤) ⟶ C) (χ : C ⟶ C') (ψ : Γ(U.left, ⊤) ⟶ C) (h : U.hom.appTop ≫ ψ = φC) :
    specMap φC χ ≫ specPoint U φC ψ h =
      specPoint U (φC ≫ χ) (ψ ≫ χ) (by rw [← Category.assoc, h]) := by
  apply Over.OverMorphism.ext
  change Spec.map χ ≫ Spec.map ψ ≫ U.left.isoSpec.inv = Spec.map (ψ ≫ χ) ≫ U.left.isoSpec.inv
  rw [Spec.map_comp, Category.assoc]

namespace AddCocycle

variable {U : Over T₀} [IsAffine U.left] (α : AddCocycle U)

/-- The cocycle evaluated on the spectrum of a ring, read as an element of that ring. -/
noncomputable def ringFun {C : CommRingCat.{u}} (φC : Γ(T₀, ⊤) ⟶ C)
    (ψ₁ ψ₂ : Γ(U.left, ⊤) ⟶ C) (h₁ : U.hom.appTop ≫ ψ₁ = φC) (h₂ : U.hom.appTop ≫ ψ₂ = φC) :
    C :=
  (Scheme.ΓSpecIso C).hom (α.toFun (specPoint U φC ψ₁ h₁) (specPoint U φC ψ₂ h₂))

theorem ringFun_map {C C' : CommRingCat.{u}} (χ : C ⟶ C') {φC : Γ(T₀, ⊤) ⟶ C}
    {φC' : Γ(T₀, ⊤) ⟶ C'} {ψ₁ ψ₂ : Γ(U.left, ⊤) ⟶ C} {ψ₁' ψ₂' : Γ(U.left, ⊤) ⟶ C'}
    (hφ : φC ≫ χ = φC') (hψ₁ : ψ₁ ≫ χ = ψ₁') (hψ₂ : ψ₂ ≫ χ = ψ₂')
    (h₁ : U.hom.appTop ≫ ψ₁ = φC) (h₂ : U.hom.appTop ≫ ψ₂ = φC)
    (h₁' : U.hom.appTop ≫ ψ₁' = φC') (h₂' : U.hom.appTop ≫ ψ₂' = φC') :
    α.ringFun φC' ψ₁' ψ₂' h₁' h₂' = χ (α.ringFun φC ψ₁ ψ₂ h₁ h₂) := by
  subst hφ hψ₁ hψ₂
  rw [ringFun, ringFun, ← specMap_comp_specPoint U φC χ ψ₁ h₁,
    ← specMap_comp_specPoint U φC χ ψ₂ h₂, α.naturality]
  exact congrArg (fun g : Γ(Spec C, ⊤) ⟶ C' =>
    g (α.toFun (specPoint U φC ψ₁ h₁) (specPoint U φC ψ₂ h₂))) (Scheme.ΓSpecIso_naturality χ)

theorem ringFun_cocycle {C : CommRingCat.{u}} (φC : Γ(T₀, ⊤) ⟶ C)
    (ψ₁ ψ₂ ψ₃ : Γ(U.left, ⊤) ⟶ C) (h₁ : U.hom.appTop ≫ ψ₁ = φC)
    (h₂ : U.hom.appTop ≫ ψ₂ = φC) (h₃ : U.hom.appTop ≫ ψ₃ = φC) :
    α.ringFun φC ψ₁ ψ₃ h₁ h₃ = α.ringFun φC ψ₁ ψ₂ h₁ h₂ + α.ringFun φC ψ₂ ψ₃ h₂ h₃ := by
  rw [ringFun, ringFun, ringFun, α.cocycle _ (specPoint U φC ψ₂ h₂)]
  exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso C).hom) _ _

open Algebra.TensorProduct in
/-- On spectra of rings the cocycle is the coboundary of one global function of `U`. -/
theorem exists_ringFun_eq [Flat U.hom] [Surjective U.hom] :
    ∃ β : Γ(U.left, ⊤), ∀ {C : CommRingCat.{u}} (φC : Γ(T₀, ⊤) ⟶ C)
      (ψ₁ ψ₂ : Γ(U.left, ⊤) ⟶ C) (h₁ : U.hom.appTop ≫ ψ₁ = φC)
      (h₂ : U.hom.appTop ≫ ψ₂ = φC), α.ringFun φC ψ₁ ψ₂ h₁ h₂ = ψ₁ β - ψ₂ β := by
  let A := Γ(T₀, ⊤)
  let B := Γ(U.left, ⊤)
  let : Algebra A B := U.hom.appTop.hom.toAlgebra
  have : Module.FaithfullyFlat A B :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine U.hom).mp
      ⟨inferInstance, inferInstance⟩
  -- Every algebra map out of `B` is compatible with the structure maps from `A`.
  have hcomm : ∀ (C : Type u) [CommRing C] [Algebra A C] (f : B →ₐ[A] C),
      U.hom.appTop ≫ CommRingCat.ofHom f.toRingHom = CommRingCat.ofHom (algebraMap A C) := by
    intro C _ _ f
    ext a
    exact f.commutes a
  let D₂ := B ⊗[A] B
  let D₃ := B ⊗[A] (B ⊗[A] B)
  let φ₂ : A ⟶ CommRingCat.of D₂ := CommRingCat.ofHom (algebraMap A D₂)
  let φ₃ : A ⟶ CommRingCat.of D₃ := CommRingCat.ofHom (algebraMap A D₃)
  let x : D₂ := α.ringFun φ₂ (CommRingCat.ofHom (includeLeft : B →ₐ[A] D₂).toRingHom)
    (CommRingCat.ofHom (includeRight : B →ₐ[A] D₂).toRingHom) (hcomm _ _) (hcomm _ _)
  let i₁ : B →ₐ[A] D₃ := includeLeft
  let i₂ : B →ₐ[A] D₃ := includeRight.comp includeLeft
  let i₃ : B →ₐ[A] D₃ := includeRight.comp includeRight
  have hface : ∀ (f : D₂ →ₐ[A] D₃) (g₁ g₂ : B →ₐ[A] D₃), f.comp includeLeft = g₁ →
      f.comp includeRight = g₂ →
      f x = α.ringFun φ₃ (CommRingCat.ofHom g₁.toRingHom) (CommRingCat.ofHom g₂.toRingHom)
        (hcomm _ _) (hcomm _ _) := by
    intro f g₁ g₂ hg₁ hg₂
    refine (α.ringFun_map (CommRingCat.ofHom f.toRingHom) ?_ ?_ ?_ _ _ _ _).symm
    · ext a
      exact f.commutes a
    · ext b
      exact congrArg (fun g : B →ₐ[A] D₃ => g b) hg₁
    · ext b
      exact congrArg (fun g : B →ₐ[A] D₃ => g b) hg₂
  have h12 : face12 A B x = α.ringFun φ₃ (CommRingCat.ofHom i₁.toRingHom)
      (CommRingCat.ofHom i₂.toRingHom) (hcomm _ _) (hcomm _ _) :=
    hface _ _ _ (by ext b; rfl) (by ext b; rfl)
  have h13 : face13 A B x = α.ringFun φ₃ (CommRingCat.ofHom i₁.toRingHom)
      (CommRingCat.ofHom i₃.toRingHom) (hcomm _ _) (hcomm _ _) :=
    hface _ _ _ (by ext b; rfl) (by ext b; rfl)
  have h23 : face23 A B x = α.ringFun φ₃ (CommRingCat.ofHom i₂.toRingHom)
      (CommRingCat.ofHom i₃.toRingHom) (hcomm _ _) (hcomm _ _) :=
    hface _ _ _ (by ext b; rfl) (by ext b; rfl)
  obtain ⟨β, hβ⟩ := exists_primitive A B x (by
    rw [h12, h13, h23]
    exact α.ringFun_cocycle _ _ _ _ _ _ _)
  refine ⟨β, fun {C} φC ψ₁ ψ₂ h₁ h₂ => ?_⟩
  let : Algebra A C := φC.hom.toAlgebra
  let f₁ : B →ₐ[A] C := { ψ₁.hom with commutes' := fun a => congrArg (fun g => g.hom a) h₁ }
  let f₂ : B →ₐ[A] C := { ψ₂.hom with commutes' := fun a => congrArg (fun g => g.hom a) h₂ }
  let χ : CommRingCat.of D₂ ⟶ C := CommRingCat.ofHom (productMap f₁ f₂).toRingHom
  rw [α.ringFun_map χ (φC := φ₂) (ψ₁ := CommRingCat.ofHom (includeLeft : B →ₐ[A] D₂).toRingHom)
    (ψ₂ := CommRingCat.ofHom (includeRight : B →ₐ[A] D₂).toRingHom) ?_ ?_ ?_ (hcomm _ _)
    (hcomm _ _) h₁ h₂]
  · change productMap f₁ f₂ x = _
    rw [← hβ, map_sub, includeLeft_apply, includeRight_apply, productMap_left_apply,
      productMap_right_apply]
    rfl
  · ext a
    exact (productMap f₁ f₂).commutes a
  · ext b
    exact productMap_left_apply f₁ f₂ b
  · ext b
    exact productMap_right_apply f₁ f₂ b

/-- A natural additive cocycle on an affine flat surjective scheme over an affine base is
the coboundary of one global function. -/
theorem exists_coboundary [Flat U.hom] [Surjective U.hom] :
    ∃ β : Γ(U.left, ⊤), ∀ {Z : Over T₀} (a b : Z ⟶ U),
      α.toFun a b = a.left.appTop β - b.left.appTop β := by
  obtain ⟨β, hβ⟩ := α.exists_ringFun_eq
  refine ⟨β, fun {Z} a b => ?_⟩
  let t : Z ⟶ specOver Z.hom.appTop := Over.homMk Z.left.toSpecΓ (by
    simp only [specOver, Over.mk_hom]
    rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id])
  have hpt : ∀ c : Z ⟶ U, U.hom.appTop ≫ c.left.appTop = Z.hom.appTop := fun c => by
    rw [← Scheme.Hom.comp_appTop, Over.w c]
  have ht : ∀ c : Z ⟶ U, t ≫ specPoint U Z.hom.appTop c.left.appTop (hpt c) = c := fun c => by
    apply Over.OverMorphism.ext
    change Z.left.toSpecΓ ≫ Spec.map c.left.appTop ≫ U.left.isoSpec.inv = c.left
    rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  have hn := α.naturality t (specPoint U Z.hom.appTop a.left.appTop (hpt a))
    (specPoint U Z.hom.appTop b.left.appTop (hpt b))
  rw [ht a, ht b] at hn
  rw [hn, ← hβ Z.hom.appTop a.left.appTop b.left.appTop (hpt a) (hpt b)]
  exact congrArg (fun g : Γ(Spec Γ(Z.left, ⊤), ⊤) ⟶ Γ(Z.left, ⊤) => g
    (α.toFun (specPoint U Z.hom.appTop a.left.appTop (hpt a))
      (specPoint U Z.hom.appTop b.left.appTop (hpt b)))) (Scheme.toSpecΓ_appTop Z.left)

end AddCocycle

end Scheme

end Langlands.AlgebraicGeometry.AffineAdditiveCocycle
