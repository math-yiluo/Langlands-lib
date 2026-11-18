import Langlands.GroupScheme.MatrixRepresentation.ScalarExtensionCoordinates
import Langlands.GroupScheme.CocharacterTransportNaturality

/-! # Galois twists of representations of a scalar-extended group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

section Transport

variable {B : Scheme.{u}} {R : CommRingCat.{u}} (b : Spec R ⟶ B) (a : Spec R ⟶ Spec R)
  (ha : a ≫ b = b) (G : GroupScheme B) {n : Type} [Fintype n] [DecidableEq n]

/-- Transport of a representation of `G_R` along an endomorphism `a` of `Spec R` over the base:
base change along `a`, the canonical descent identification of `G_R`, and the base-change
identification of `GL_{n,R}`. -/
def transport (ρ : MatrixRepresentation ((GroupScheme.baseChange b).obj G) n) :
    MatrixRepresentation ((GroupScheme.baseChange b).obj G) n :=
  (descentBaseChangeIso b a ha G).inv ≫ (Over.pullback a).mapGrp.map ρ ≫
    (GeneralLinear.baseChangeIso n a).hom

/-- On points, the transported representation evaluates the original representation at the same
point of `G`, seen with its `R`-structure changed by `a`. -/
theorem pointMatrix_transport (ρ : MatrixRepresentation ((GroupScheme.baseChange b).obj G) n)
    (T : Over (Spec R)) (y : T ⟶ ((GroupScheme.baseChange b).obj G).X) :
    (transport b a ha G ρ).pointMatrix T y =
      ρ.pointMatrix ((Over.map a).obj T) (descentPoint b a ha G T y) := by
  set y' := y ≫ (descentBaseChangeIso b a ha G).inv.hom.hom with hy'
  have h1 : (descentBaseChangeIso b a ha G).inv.hom.hom ≫
      (descentBaseChangeIso b a ha G).hom.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom) (descentBaseChangeIso b a ha G).inv_hom_id
  have hy : y = y' ≫ (descentBaseChangeIso b a ha G).hom.hom.hom := by
    rw [hy', Category.assoc, h1, Category.comp_id]
  have key := baseChangePointsEquiv_descent b a ha G T y'
  rw [← hy] at key
  have hd : descentPoint b a ha G T y = baseChangePointsEquiv a
      ((GroupScheme.baseChange b).obj G) T y' := by
    apply (baseChangePointsEquiv b G ((Over.map a).obj T)).injective
    rw [baseChangePointsEquiv_descentPoint, key, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  rw [hd, pointMatrix_apply, pointMatrix_apply]
  change GeneralLinear.pointsEquiv n R T ((y' ≫ ((Over.pullback a).mapGrp.map ρ).hom.hom) ≫
      (GeneralLinear.baseChangeIso n a).hom.hom.hom) = _
  rw [GeneralLinear.pointsEquiv_comp_baseChangeIso_hom, baseChangePointsEquiv_comp]

/-- A descended point is a precomposite, once the precomposite has the same underlying point of
the original group. -/
theorem descentPoint_eq_comp (T : Over (Spec R)) (Θ : (Over.map a).obj T ⟶ T)
    (y : T ⟶ ((GroupScheme.baseChange b).obj G).X)
    (h : (Over.map b).map Θ ≫ baseChangePointsEquiv b G T y =
      (descentTestIso b a ha T).inv ≫ baseChangePointsEquiv b G T y) :
    descentPoint b a ha G T y = Θ ≫ y := by
  apply (baseChangePointsEquiv b G ((Over.map a).obj T)).injective
  rw [baseChangePointsEquiv_descentPoint, baseChangePointsEquiv_naturality, h]

/-- On an affine test algebra, if the descended point is the precomposite with `Spec θ`, the
transported representation has the original matrix with `θ` applied entrywise. -/
theorem affineMatrix_transport_of_descentPoint
    (ρ : MatrixRepresentation ((GroupScheme.baseChange b).obj G) n)
    (S : Type u) [CommRing S] [Algebra R S]
    (y : (algSpec R).obj (op (CommAlgCat.of R S)) ⟶ ((GroupScheme.baseChange b).obj G).X)
    (θ : S →+* S)
    (Θ : (Over.map a).obj ((algSpec R).obj (op (CommAlgCat.of R S))) ⟶
      (algSpec R).obj (op (CommAlgCat.of R S)))
    (hΘ : Θ.left = Spec.map (CommRingCat.ofHom θ))
    (hy : descentPoint b a ha G _ y = Θ ≫ y) (i j : n) :
    (transport b a ha G ρ).affineMatrix (CommAlgCat.of R S) y i j =
      θ (ρ.affineMatrix (CommAlgCat.of R S) y i j) := by
  have hq : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
  apply hq
  have h1 := pointMatrix_eq_affineMatrix (transport b a ha G ρ) (CommAlgCat.of R S) y
  rw [pointMatrix_transport, hy, pointMatrix_naturality, pointMatrix_eq_affineMatrix] at h1
  have h2 := congrArg (fun M : GL n _ => M i j) h1
  simp only [Matrix.GeneralLinearGroup.map_apply] at h2
  have hnat := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom θ))
    (ρ.affineMatrix (CommAlgCat.of R S) y i j)
  rw [← hΘ] at hnat
  exact h2.symm.trans hnat.symm

end Transport

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The Galois twist of a representation of `G_K` along `Spec σ`. -/
abbrev galoisTwist (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n) :
    MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n :=
  transport (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) G ρ

section ScalarPoints

variable (R : Type u) [CommRing R] [Algebra k R]

/-- A point of `G` over a `k`-algebra `R`, seen as a point of `G_K` over `K ⊗[k] R` through the
right tensor factor. -/
def scalarPoint (g : G.affinePoints (CommAlgCat.of (CommRingCat.of k) R)) :
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).affinePoints
      (CommAlgCat.of (CommRingCat.of K) (K ⊗[k] R)) :=
  scalarExtensionPoint (K ⊗[k] R)
    ((algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R)).op ≫ g)

/-- The automorphism `σ ⊗ id` of `K ⊗[k] R`. -/
def galoisTensor (σ : K ≃ₐ[k] K) : K ⊗[k] R →ₐ[k] K ⊗[k] R :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k R)

@[simp] theorem galoisTensor_tmul (σ : K ≃ₐ[k] K) (c : K) (r : R) :
    galoisTensor R σ (c ⊗ₜ r) = σ c ⊗ₜ r := rfl

/-- `Spec (σ ⊗ id)`, as a morphism over `Spec σ`. -/
def galoisTensorHom (σ : K ≃ₐ[k] K) :
    (Over.map (galoisBaseMap k K σ)).obj
        ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of (CommRingCat.of K) (K ⊗[k] R)))) ⟶
      (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of (CommRingCat.of K) (K ⊗[k] R))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (galoisTensor R σ).toRingHom)) (by
    have hθ : (galoisTensor R σ).toRingHom.comp (algebraMap K (K ⊗[k] R)) =
        (algebraMap K (K ⊗[k] R)).comp σ.toRingHom := by
      ext c
      change galoisTensor R σ (c ⊗ₜ 1) = σ c ⊗ₜ 1
      rfl
    rw [Over.map_obj_hom, algSpec_obj_hom, galoisBaseMap, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hθ)

@[simp] theorem galoisTensorHom_left (σ : K ≃ₐ[k] K) :
    (galoisTensorHom R σ).left = Spec.map (CommRingCat.ofHom (galoisTensor R σ).toRingHom) :=
  rfl

/-- The descended scalar point is the scalar point precomposed with `Spec (σ ⊗ id)`. -/
theorem descentPoint_scalarPoint (σ : K ≃ₐ[k] K)
    (g : G.affinePoints (CommAlgCat.of (CommRingCat.of k) R)) :
    descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) G _
        (scalarPoint R g) =
      galoisTensorHom R σ ≫ scalarPoint R g := by
  apply descentPoint_eq_comp
  have key : (Over.map (algebraBaseMap k K)).map (galoisTensorHom R σ) ≫
      (CocharacterSplitting.testIso K (K ⊗[k] R)).hom ≫
        (algSpec (CommRingCat.of k)).map
          (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R)).op =
      (descentTestIso (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ)
          _).inv ≫ (CocharacterSplitting.testIso K (K ⊗[k] R)).hom ≫
        (algSpec (CommRingCat.of k)).map
          (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R)).op := by
    ext : 1
    simp only [Over.comp_left, Over.map_map_left, galoisTensorHom_left,
      CocharacterSplitting.testIso_hom_left, algSpec_map_left, descentTestIso]
    simp only [Over.isoMk_inv_left, Iso.refl_inv, Category.id_comp]
    have hθ : (galoisTensor R σ).toRingHom.comp
        (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).toRingHom =
          (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).toRingHom := by
      ext r
      change galoisTensor R σ (1 ⊗ₜ r) = 1 ⊗ₜ r
      rw [galoisTensor_tmul, map_one]
    rw [← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hθ
  simp only [scalarPoint, scalarExtensionPoint, MulEquiv.apply_symm_apply]
  simp only [← Category.assoc] at key ⊢
  rw [key]

theorem galoisTwist_eq_transport (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n) :
    galoisTwist σ ρ =
      transport (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) G ρ :=
  rfl

theorem galoisTensor_toRingHom_apply (σ : K ≃ₐ[k] K) (x : K ⊗[k] R) :
    (galoisTensor R σ).toRingHom x = galoisTensor R σ x :=
  rfl

/-- The Galois twist of a representation evaluated at a scalar point: apply `σ ⊗ id` to the
entries of the original matrix. -/
theorem affineMatrix_galoisTwist_scalarPoint (σ : K ≃ₐ[k] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (g : G.affinePoints (CommAlgCat.of (CommRingCat.of k) R)) (i j : n) :
    (galoisTwist σ ρ).affineMatrix (CommAlgCat.of (CommRingCat.of K) (K ⊗[k] R))
        (scalarPoint R g) i j =
      galoisTensor R σ
        (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of K) (K ⊗[k] R)) (scalarPoint R g) i j) := by
  have h := affineMatrix_transport_of_descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) G ρ (K ⊗[k] R) (scalarPoint R g) (galoisTensor R σ).toRingHom
    (galoisTensorHom R σ) (galoisTensorHom_left R σ) (descentPoint_scalarPoint R σ g) i j
  rw [galoisTensor_toRingHom_apply] at h
  rw [galoisTwist_eq_transport]
  exact h

end ScalarPoints

end Langlands.GroupScheme.MatrixRepresentation
