import Langlands.GroupScheme.IdentityJetConjugation
import Langlands.GroupScheme.GeneralLinearActionOfPoints
import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.IdentityJetLocallyFreeStatement
import Langlands.GroupScheme.MatrixRepresentation.JetConjugationRepresentationStatement

/-! # The conjugation representation on a finite free identity jet -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.AffinePoints
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.GeneralLinear

variable {m : ℕ} {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

/-- The point of `GL_m` over `Spec A` with a prescribed invertible matrix. -/
def pointOfMatrix (M : GL (Fin m) A) :
    specOver (R := R) A ⟶ (groupScheme (Fin m) (CommRingCat.of R)).X :=
  (pointsEquiv (Fin m) (CommRingCat.of R) (specOver A)).symm
    (Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom M)

@[simp]
theorem matrixOf_pointOfMatrix (M : GL (Fin m) A) :
    matrixOf (pointOfMatrix (R := R) M) = M := by
  rw [matrixOf, pointOfMatrix, MulEquiv.apply_symm_apply]
  ext i j
  simp

theorem pointOfMatrix_injective :
    Function.Injective (pointOfMatrix (R := R) (A := A) (m := m)) := fun M M' h => by
  simpa using congrArg matrixOf h

theorem pointOfMatrix_mul (M M' : GL (Fin m) A) :
    pointOfMatrix (R := R) (M * M') = pointOfMatrix M * pointOfMatrix M' :=
  matrixOf_injective (by rw [matrixOf_mul]; simp)

theorem pointOfMatrix_one : pointOfMatrix (R := R) (1 : GL (Fin m) A) = 1 :=
  matrixOf_injective (by rw [matrixOf_one]; simp)

theorem specMapOver_comp_pointOfMatrix {A' : Type u} [CommRing A'] [Algebra R A']
    (φ : A →ₐ[R] A') (M : GL (Fin m) A) :
    specMapOver φ ≫ pointOfMatrix (R := R) M =
      pointOfMatrix (Matrix.GeneralLinearGroup.map φ.toRingHom M) :=
  matrixOf_injective (by rw [matrixOf_comp]; simp)

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.GroupScheme.IdentityJet

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) (n : ℕ)
  {P : Type u} [CommRing P] [Algebra R P]
  (e : scheme G n ≅ Spec (CommRingCat.of P))
  (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) = projection G n)

include he

/-- The jet point of `G` classified by an algebra map from the jet coordinate ring. -/
def jetPoint {B : Type u} [CommRing B] [Algebra R B] (χ : P →ₐ[R] B) :
    specOver (R := R) B ⟶ G.X :=
  Over.homMk (Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ e.inv ≫ inclusion G n) (by
    have h₁ : e.inv ≫ projection G n = Spec.map (CommRingCat.ofHom (algebraMap R P)) := by
      rw [← he, Iso.inv_hom_id_assoc]
    change (Spec.map _ ≫ e.inv ≫ inclusion G n) ≫ G.X.hom = Spec.map _
    rw [Category.assoc, Category.assoc]
    change Spec.map _ ≫ e.inv ≫ projection G n = _
    rw [h₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f : R →+* B => Spec.map (CommRingCat.ofHom f))
      (RingHom.ext χ.commutes))

@[simp]
theorem jetPoint_left {B : Type u} [CommRing B] [Algebra R B] (χ : P →ₐ[R] B) :
    (jetPoint G n e he χ).left = Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ e.inv ≫ inclusion G n :=
  rfl

theorem isJetPoint_jetPoint {B : Type u} [CommRing B] [Algebra R B] (χ : P →ₐ[R] B) :
    IsJetPoint G n (jetPoint G n e he χ) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ e.inv, by simp⟩

/-- Jet points are natural in the algebra. -/
theorem specMapOver_comp_jetPoint {B C : Type u} [CommRing B] [Algebra R B] [CommRing C]
    [Algebra R C] (χ : P →ₐ[R] B) (ψ : B →ₐ[R] C) :
    specMapOver ψ ≫ jetPoint G n e he χ = jetPoint G n e he (ψ.comp χ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, specMapOver_left, jetPoint_left, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

theorem jetPoint_injective {B : Type u} [CommRing B] [Algebra R B] :
    Function.Injective (jetPoint G n e he (B := B)) := by
  intro χ χ' h
  have : IsClosedImmersion (inclusion G n) :=
    inferInstanceAs (IsClosedImmersion (ideal G n).subschemeι)
  have h₁ := congrArg CommaMorphism.left h
  simp only [jetPoint_left] at h₁
  have h₂ := (cancel_mono (e.inv ≫ inclusion G n)).mp (by simpa only [Category.assoc] using h₁)
  have h₃ := congrArg CommRingCat.Hom.hom (Spec.map_injective h₂)
  ext p
  exact congrArg (fun f : P →+* B => f p) h₃

/-- Every jet point on an affine test scheme is classified by an algebra map. -/
theorem exists_jetPoint {B : Type u} [CommRing B] [Algebra R B]
    {x : specOver (R := R) B ⟶ G.X} (hx : IsJetPoint G n x) :
    ∃ χ : P →ₐ[R] B, jetPoint G n e he χ = x := by
  obtain ⟨y, hy⟩ := hx
  let φ : P →+* B := (Spec.preimage (y ≫ e.hom)).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = y ≫ e.hom := by
    simp [φ]
  have hcomp : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R P)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [hφ, Category.assoc, he]
    change y ≫ inclusion G n ≫ G.X.hom = _
    rw [← Category.assoc, hy]
    exact Over.w x
  refine ⟨algHomOfSpec φ hcomp, ?_⟩
  apply Over.OverMorphism.ext
  rw [jetPoint_left, algHomOfSpec_toRingHom, hφ, Category.assoc, Iso.hom_inv_id_assoc, hy]

/-- The algebra map classifying a jet point. -/
def jetAlgHom {B : Type u} [CommRing B] [Algebra R B]
    {x : specOver (R := R) B ⟶ G.X} (hx : IsJetPoint G n x) : P →ₐ[R] B :=
  (exists_jetPoint G n e he hx).choose

@[simp]
theorem jetPoint_jetAlgHom {B : Type u} [CommRing B] [Algebra R B]
    {x : specOver (R := R) B ⟶ G.X} (hx : IsJetPoint G n x) :
    jetPoint G n e he (jetAlgHom G n e he hx) = x :=
  (exists_jetPoint G n e he hx).choose_spec

theorem jetAlgHom_jetPoint {B : Type u} [CommRing B] [Algebra R B] (χ : P →ₐ[R] B) :
    jetAlgHom G n e he (isJetPoint_jetPoint G n e he χ) = χ :=
  jetPoint_injective G n e he (jetPoint_jetAlgHom G n e he _)

omit he in
theorem specMapOver_comp_specMapOver {A B C : Type u} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [CommRing C] [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) :
    specMapOver ψ ≫ specMapOver φ = specMapOver (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, specMapOver_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

variable [IsSeparated G.X.hom]

section Conjugation

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The conjugate of the universal jet point over `A ⊗ P` by a point `g` over `A`. -/
def conjBeta (g : specOver (R := R) A ⟶ G.X) : P →ₐ[R] A ⊗[R] P :=
  jetAlgHom G n e he ((isJetPoint_jetPoint G n e he
    (Algebra.TensorProduct.includeRight : P →ₐ[R] A ⊗[R] P)).conj G g
    (specMapOver (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] P)))

theorem jetPoint_conjBeta (g : specOver (R := R) A ⟶ G.X) :
    jetPoint G n e he (conjBeta G n e he g) =
      (specMapOver (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] P) ≫ g) *
        jetPoint G n e he (Algebra.TensorProduct.includeRight : P →ₐ[R] A ⊗[R] P) *
        (specMapOver (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] P) ≫ g)⁻¹ :=
  jetPoint_jetAlgHom G n e he _

/-- Conjugating any jet point by the restriction of `g` is computed by `conjBeta`. -/
theorem conj_jetPoint (g : specOver (R := R) A ⟶ G.X) {B : Type u} [CommRing B]
    [Algebra R B] (ψ : A ⊗[R] P →ₐ[R] B) :
    (specMapOver (ψ.comp Algebra.TensorProduct.includeLeft) ≫ g) *
        jetPoint G n e he (ψ.comp Algebra.TensorProduct.includeRight) *
        (specMapOver (ψ.comp Algebra.TensorProduct.includeLeft) ≫ g)⁻¹ =
      jetPoint G n e he (ψ.comp (conjBeta G n e he g)) := by
  rw [← specMapOver_comp_specMapOver, ← specMapOver_comp_jetPoint, ← specMapOver_comp_jetPoint,
    jetPoint_conjBeta, Category.assoc, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]

/-- The `A`-algebra endomorphism of `A ⊗ P` extending `conjBeta`. -/
def conjAlg (g : specOver (R := R) A ⟶ G.X) : A ⊗[R] P →ₐ[A] A ⊗[R] P :=
  Algebra.TensorProduct.lift (Algebra.ofId A (A ⊗[R] P)) (conjBeta G n e he g)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem conjAlg_tmul (g : specOver (R := R) A ⟶ G.X) (a : A) (p : P) :
    conjAlg G n e he g (a ⊗ₜ p) = algebraMap A (A ⊗[R] P) a * conjBeta G n e he g p := by
  simp [conjAlg]

theorem conjAlg_comp_includeLeft (g : specOver (R := R) A ⟶ G.X) :
    ((conjAlg G n e he g).restrictScalars R).comp Algebra.TensorProduct.includeLeft =
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] P) := by
  ext a
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem conjAlg_comp_includeRight (g : specOver (R := R) A ⟶ G.X) :
    ((conjAlg G n e he g).restrictScalars R).comp Algebra.TensorProduct.includeRight =
      conjBeta G n e he g := by
  ext p
  simp [← Algebra.TensorProduct.one_def]

theorem conjBeta_one :
    conjBeta G n e he (1 : specOver (R := R) A ⟶ G.X) = Algebra.TensorProduct.includeRight := by
  apply jetPoint_injective G n e he
  rw [jetPoint_conjBeta, MonObj.comp_one, one_mul, inv_one, mul_one]

theorem conjBeta_mul (g h : specOver (R := R) A ⟶ G.X) :
    conjBeta G n e he (g * h) =
      ((conjAlg G n e he h).restrictScalars R).comp (conjBeta G n e he g) := by
  apply jetPoint_injective G n e he
  rw [← conj_jetPoint, conjAlg_comp_includeLeft, conjAlg_comp_includeRight, jetPoint_conjBeta,
    jetPoint_conjBeta, MonObj.comp_mul, mul_inv_rev]
  group

theorem conjAlg_one :
    conjAlg G n e he (1 : specOver (R := R) A ⟶ G.X) = AlgHom.id A (A ⊗[R] P) := by
  apply Algebra.TensorProduct.ext'
  intro a p
  simp [conjBeta_one, Algebra.TensorProduct.algebraMap_apply]

theorem conjAlg_mul (g h : specOver (R := R) A ⟶ G.X) :
    conjAlg G n e he (g * h) = (conjAlg G n e he h).comp (conjAlg G n e he g) := by
  apply Algebra.TensorProduct.ext'
  intro a p
  simp only [conjAlg_tmul, conjBeta_mul, AlgHom.comp_apply, map_mul, AlgHom.commutes]
  rfl

theorem conjBeta_specMapOver {A' : Type u} [CommRing A'] [Algebra R A'] (φ : A →ₐ[R] A')
    (g : specOver (R := R) A ⟶ G.X) :
    conjBeta G n e he (specMapOver φ ≫ g) =
      (Algebra.TensorProduct.map φ (AlgHom.id R P)).comp (conjBeta G n e he g) := by
  apply jetPoint_injective G n e he
  rw [← conj_jetPoint, Algebra.TensorProduct.map_comp_includeLeft,
    Algebra.TensorProduct.map_comp_includeRight, AlgHom.comp_id,
    ← specMapOver_comp_specMapOver, Category.assoc, jetPoint_conjBeta]

omit [IsSeparated G.X.hom] he in
/-- Every morphism of affine test schemes over `Spec R` comes from an algebra map. -/
theorem exists_specMapOver {B : Type u} [CommRing B] [Algebra R B]
    (t : specOver (R := R) B ⟶ specOver (R := R) A) :
    ∃ φ : A →ₐ[R] B, specMapOver φ = t := by
  have h : Spec.map (CommRingCat.ofHom (Spec.preimage t.left).hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact Over.w t
  refine ⟨algHomOfSpec _ h, ?_⟩
  apply Over.OverMorphism.ext
  rw [specMapOver_left, algHomOfSpec_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage]

/-- A point over `A` centralizes the jet exactly when it fixes the universal jet point. -/
theorem centralizesJet_iff_conjBeta (g : specOver (R := R) A ⟶ G.X) :
    CentralizesJet G n g ↔ conjBeta G n e he g = Algebra.TensorProduct.includeRight := by
  constructor
  · intro hg
    apply jetPoint_injective G n e he
    rw [jetPoint_conjBeta, hg _ _ _ (isJetPoint_jetPoint G n e he _), mul_inv_cancel_right]
  · intro h V a x hx
    apply over_hom_ext
    intro B _ _ t
    rw [MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc]
    obtain ⟨χ, hχ⟩ := exists_jetPoint G n e he (hx.comp G t)
    obtain ⟨φ, hφ⟩ := exists_specMapOver (t ≫ a)
    let ψ : A ⊗[R] P →ₐ[R] B :=
      Algebra.TensorProduct.lift φ χ (fun _ _ => Commute.all _ _)
    have h₁ : ψ.comp Algebra.TensorProduct.includeLeft = φ := by
      ext a'
      simp [ψ]
    have h₂ : ψ.comp Algebra.TensorProduct.includeRight = χ := by
      ext p
      simp [ψ]
    have key := conj_jetPoint G n e he g ψ
    rw [h₁, h₂, h, h₂, hφ, hχ] at key
    exact mul_inv_eq_iff_eq_mul.mp key

omit [IsSeparated G.X.hom] he in
/-- The jet points' centralizer condition can be tested on affine refinements. -/
theorem centralizesJet_of_affine {T : Over (Spec (CommRingCat.of R))} {x : T ⟶ G.X}
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] (t : specOver (R := R) A ⟶ T),
      CentralizesJet G n (t ≫ x)) : CentralizesJet G n x := by
  intro V a y hy
  apply over_hom_ext
  intro B _ _ s
  rw [MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc]
  have := h B (s ≫ a) (specOver (R := R) B) (𝟙 _) (s ≫ y) (hy.comp G s)
  simpa only [Category.id_comp] using this

section Matrix

variable {m : ℕ} (b : Module.Basis (Fin m) R P) {A : Type u} [CommRing A] [Algebra R A]

/-- The matrix of conjugation by the inverse point, in the base-changed jet basis. -/
def conjMatrix (g : specOver (R := R) A ⟶ G.X) : Matrix (Fin m) (Fin m) A :=
  LinearMap.toMatrix (Algebra.TensorProduct.basis A b) (Algebra.TensorProduct.basis A b)
    (conjAlg G n e he g⁻¹).toLinearMap

theorem conjMatrix_mul (g h : specOver (R := R) A ⟶ G.X) :
    conjMatrix G n e he b (g * h) = conjMatrix G n e he b g * conjMatrix G n e he b h := by
  rw [conjMatrix, conjMatrix, conjMatrix, ← LinearMap.toMatrix_comp, mul_inv_rev, conjAlg_mul]
  rfl

theorem conjMatrix_one : conjMatrix G n e he b (1 : specOver (R := R) A ⟶ G.X) = 1 := by
  rw [conjMatrix, inv_one, conjAlg_one]
  exact LinearMap.toMatrix_id _

theorem conjAlg_eq_id_iff (g : specOver (R := R) A ⟶ G.X) :
    conjAlg G n e he g = AlgHom.id A (A ⊗[R] P) ↔
      conjBeta G n e he g = Algebra.TensorProduct.includeRight := by
  constructor
  · intro h
    rw [← conjAlg_comp_includeRight, h]
    rfl
  · intro h
    apply Algebra.TensorProduct.ext'
    intro a p
    simp [h, Algebra.TensorProduct.algebraMap_apply]

theorem conjMatrix_eq_one_iff (g : specOver (R := R) A ⟶ G.X) :
    conjMatrix G n e he b g = 1 ↔ CentralizesJet G n g := by
  have hinv : CentralizesJet G n g⁻¹ ↔ CentralizesJet G n g := by
    constructor
    · intro h V a x hx
      have := h V a x hx
      rw [GrpObj.comp_inv] at this
      exact (Commute.inv_left_iff.mp this)
    · intro h V a x hx
      rw [GrpObj.comp_inv]
      exact Commute.inv_left_iff.mpr (h V a x hx)
  rw [← hinv, centralizesJet_iff_conjBeta G n e he, ← conjAlg_eq_id_iff, conjMatrix,
    ← LinearMap.toMatrix_id (Algebra.TensorProduct.basis A b)]
  rw [(LinearMap.toMatrix (Algebra.TensorProduct.basis A b)
    (Algebra.TensorProduct.basis A b)).injective.eq_iff]
  constructor
  · intro h
    exact AlgHom.toLinearMap_injective h
  · intro h
    rw [h]
    rfl

omit [IsSeparated G.X.hom] he in
theorem basis_repr_map {A' : Type u} [CommRing A'] [Algebra R A'] (φ : A →ₐ[R] A')
    (x : A ⊗[R] P) (i : Fin m) :
    (Algebra.TensorProduct.basis A' b).repr (Algebra.TensorProduct.map φ (AlgHom.id R P) x) i =
      φ ((Algebra.TensorProduct.basis A b).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a p => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem conjMatrix_specMapOver {A' : Type u} [CommRing A'] [Algebra R A'] (φ : A →ₐ[R] A')
    (g : specOver (R := R) A ⟶ G.X) :
    conjMatrix G n e he b (specMapOver φ ≫ g) = (conjMatrix G n e he b g).map φ := by
  ext i j
  rw [conjMatrix, conjMatrix, Matrix.map_apply, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply, ← GrpObj.comp_inv]
  simp only [AlgHom.toLinearMap_apply, Algebra.TensorProduct.basis_apply, conjAlg_tmul,
    map_one, one_mul, conjBeta_specMapOver, AlgHom.comp_apply]
  exact basis_repr_map b φ _ i

end Matrix

end Conjugation

section Representation

variable {m : ℕ} (b : Module.Basis (Fin m) R P)

/-- Conjugation by the inverse point on the jet, as an invertible matrix. -/
def conjGL {A : Type u} [CommRing A] [Algebra R A] (g : specOver (R := R) A ⟶ G.X) :
    GL (Fin m) A :=
  ⟨conjMatrix G n e he b g, conjMatrix G n e he b g⁻¹,
    by rw [← conjMatrix_mul, mul_inv_cancel, conjMatrix_one],
    by rw [← conjMatrix_mul, inv_mul_cancel, conjMatrix_one]⟩

theorem conjGL_mul {A : Type u} [CommRing A] [Algebra R A] (g h : specOver (R := R) A ⟶ G.X) :
    conjGL G n e he b (g * h) = conjGL G n e he b g * conjGL G n e he b h :=
  Units.ext (conjMatrix_mul G n e he b g h)

theorem conjGL_specMapOver {A A' : Type u} [CommRing A] [Algebra R A] [CommRing A']
    [Algebra R A'] (φ : A →ₐ[R] A') (g : specOver (R := R) A ⟶ G.X) :
    conjGL G n e he b (specMapOver φ ≫ g) =
      Matrix.GeneralLinearGroup.map φ.toRingHom (conjGL G n e he b g) :=
  Units.ext (conjMatrix_specMapOver G n e he b φ g)

theorem conjGL_eq_one_iff {A : Type u} [CommRing A] [Algebra R A]
    (g : specOver (R := R) A ⟶ G.X) :
    conjGL G n e he b g = 1 ↔ CentralizesJet G n g := by
  rw [← conjMatrix_eq_one_iff G n e he b, Units.ext_iff]
  rfl

/-- The scheme morphism to `GL_m` given on affine points by the conjugation matrices. -/
theorem exists_conjugationMorphism :
    ∃ f : G.X ⟶ (GeneralLinear.groupScheme (Fin m) (CommRingCat.of R)).X,
      ∀ (A : Type u) [CommRing A] [Algebra R A] (g : specOver (R := R) A ⟶ G.X),
        g ≫ f = GeneralLinear.pointOfMatrix (conjGL G n e he b g) :=
  exists_over_hom (fun A _ _ g => GeneralLinear.pointOfMatrix (conjGL G n e he b g))
    (fun A B _ _ _ _ φ g => by
      rw [conjGL_specMapOver, GeneralLinear.specMapOver_comp_pointOfMatrix])

include b in
/-- **The conjugation representation on a finite free identity jet.** If the order-`n`
jet of a separated group over `Spec R` is the spectrum of a free `R`-algebra of rank `m`,
then `G` has a matrix representation of degree `m` whose kernel on every test scheme is
exactly the centralizer of the jet. -/
theorem exists_jetRepresentation :
    ∃ ρ : MatrixRepresentation G (Fin m),
      ∀ (U : Over (Spec (CommRingCat.of R))) (g : U ⟶ G.X),
        g ≫ ρ.hom.hom = 1 ↔ CentralizesJet G n g := by
  obtain ⟨f, hf⟩ := exists_conjugationMorphism G n e he b
  have hmul : ∀ (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ G.X),
      (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
    intro T x y
    apply over_hom_ext
    intro A _ _ t
    rw [← Category.assoc, MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
    simp only [hf, conjGL_mul, GeneralLinear.pointOfMatrix_mul]
  let φ : ∀ T : Over (Spec (CommRingCat.of R)),
      (T ⟶ G.X) →* (T ⟶ (GeneralLinear.groupScheme (Fin m) (CommRingCat.of R)).X) :=
    fun T => MonoidHom.mk' (fun x => x ≫ f) (hmul T)
  refine ⟨homOfPoints φ (fun a x => Category.assoc a x f), fun U g => ?_⟩
  rw [comp_homOfPoints]
  change g ≫ f = 1 ↔ _
  constructor
  · intro h
    apply centralizesJet_of_affine G n
    intro A _ _ t
    rw [← conjGL_eq_one_iff G n e he b, ← (GeneralLinear.pointOfMatrix_injective (R := R) (A := A) (m := m)).eq_iff, ← hf,
      Category.assoc, h, MonObj.comp_one, GeneralLinear.pointOfMatrix_one]
  · intro h
    apply over_hom_ext
    intro A _ _ t
    rw [← Category.assoc, hf, MonObj.comp_one, (conjGL_eq_one_iff G n e he b _).mpr (h.comp t),
      GeneralLinear.pointOfMatrix_one]

end Representation

end Langlands.GroupScheme.IdentityJet

namespace Langlands.GroupScheme

/-- Local freeness of identity jets gives the conjugation representations on them. -/
theorem jetConjugationRepresentation_of
    (hfree : IdentityJetLocallyFreeStatement.{u}) :
    JetConjugationRepresentationStatement.{u} := by
  intro S G hsm hsep n s W hsW
  obtain ⟨R, i, hi, hs, hW, P, e, he, m, ⟨b⟩⟩ := hfree S G hsm hsep n s W hsW
  refine ⟨R, i, hi, hs, hW, m, ?_⟩
  have : IsSeparated G.X.hom := hsep
  have : IsSeparated ((GroupScheme.baseChange i).obj G).X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd G.X.hom i))
  exact IdentityJet.exists_jetRepresentation ((GroupScheme.baseChange i).obj G) n e he b

end Langlands.GroupScheme
