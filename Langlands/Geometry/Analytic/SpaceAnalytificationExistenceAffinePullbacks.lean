import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceAffineModels
import Langlands.Geometry.Analytic.AffineAnalytificationFibreProductStatement
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityStatement

/-! # Affine fibre squares in presheaf-model form

The affine fibre product statement, formulated with tensor products, together with localized
functoriality implies that every presheaf fibre square of affine tests over an affine test is
carried to a pullback square by affine analytification. Any affine model of the presheaf fibre
product is identified with the tensor product.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ExistenceReduction

open SaturatedAtlasPresentation AffineAnalytification
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Presheaf fibre squares of affine tests over an affine test go to pullbacks, assuming the
affine fibre product statement and localized functoriality. -/
theorem isPullback_localizedHom_of_isPullback_ty
    (hFib : AffineAnalytificationFibreProductStatement.{u, u, u, u})
    (hFun : AffineAnalytificationLocalizedFunctorialityStatement.{u, u, u, u})
    {A B C D : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (R : FinitePolynomialPresentation K C) (U : FinitePolynomialPresentation K D)
    (f : C →ₐ[K] A) (g : C →ₐ[K] B) (a : A →ₐ[K] D) (b : B →ₐ[K] D)
    (hsq : IsPullback (ty a) (ty b) (ty f) (ty g)) :
    IsPullback (localizedHom K P U a) (localizedHom K Q U b)
      (localizedHom K R P f) (localizedHom K R Q g) := by
  classical
  let : Algebra C A := f.toRingHom.toAlgebra
  let : Algebra C B := g.toRingHom.toAlgebra
  let : Algebra C D := (a.comp f).toRingHom.toAlgebra
  have : IsScalarTower K C A := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  have : IsScalarTower K C B := IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  have : IsScalarTower K C D :=
    IsScalarTower.of_algebraMap_eq (fun r => ((a.comp f).commutes r).symm)
  have hab : a.comp f = b.comp g := ty_injective (by rw [ty_comp, ty_comp, hsq.w])
  -- the comparison map from the tensor product
  let a' : A →ₐ[C] D := { a.toRingHom with commutes' := fun _ => rfl }
  let b' : B →ₐ[C] D :=
    { b.toRingHom with commutes' := fun c => (AlgHom.congr_fun hab c).symm }
  let φ : A ⊗[C] B →ₐ[K] D :=
    (Algebra.TensorProduct.lift a' b' (fun _ _ => Commute.all _ _)).restrictScalars K
  let iL : A →ₐ[K] A ⊗[C] B := Algebra.TensorProduct.includeLeft
  let iR : B →ₐ[K] A ⊗[C] B :=
    (Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars K
  have hφL : φ.comp iL = a := AlgHom.ext fun x => by
    change a x * b 1 = a x
    rw [map_one, mul_one]
  have hφR : φ.comp iR = b := AlgHom.ext fun y => by
    change a 1 * b y = b y
    rw [map_one, one_mul]
  have hi : iL.comp f = iR.comp g := AlgHom.ext fun c => by
    change f c ⊗ₜ[C] (1 : B) = (1 : A) ⊗ₜ[C] g c
    have hf : f c = c • (1 : A) := (Algebra.algebraMap_eq_smul_one c)
    have hg : g c = c • (1 : B) := (Algebra.algebraMap_eq_smul_one c)
    rw [hf, hg, TensorProduct.smul_tmul]
  -- the map to the tensor product from the presheaf pullback property
  obtain ⟨ψ, hψL, hψR⟩ := exists_algHom_of_isPullback hsq iL iR (by
    rw [← ty_comp, ← ty_comp, hi])
  have hφψ : φ.comp ψ = AlgHom.id K D := by
    apply ty_injective
    apply hsq.hom_ext
    · rw [← ty_comp, ← ty_comp, AlgHom.comp_assoc, hψL, hφL, AlgHom.id_comp]
    · rw [← ty_comp, ← ty_comp, AlgHom.comp_assoc, hψR, hφR, AlgHom.id_comp]
  have hψφ : ψ.comp φ = AlgHom.id K (A ⊗[C] B) := by
    refine AlgHom.ext fun t => ?_
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      change ψ (a x * b y) = x ⊗ₜ[C] y
      rw [map_mul, ← AlgHom.comp_apply ψ a, ← AlgHom.comp_apply ψ b, hψL, hψR]
      change (x ⊗ₜ[C] (1 : B)) * ((1 : A) ⊗ₜ[C] y) = x ⊗ₜ[C] y
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add s t hs ht => rw [map_add, map_add, hs, ht]
  -- a presentation of the tensor product transported from `D`
  let PT : FinitePolynomialPresentation K (A ⊗[C] B) :=
    { arity := U.arity
      map := ψ.comp U.map
      surjective := by
        intro t
        obtain ⟨p, hp⟩ := U.surjective (φ t)
        refine ⟨p, ?_⟩
        change ψ (U.map p) = t
        rw [hp, ← AlgHom.comp_apply, hψφ, AlgHom.id_apply] }
  have hT := hFib K C A B R P Q PT
  have hfA : IsScalarTower.toAlgHom K C A = f := AlgHom.ext fun _ => rfl
  have hgB : IsScalarTower.toAlgHom K C B = g := AlgHom.ext fun _ => rfl
  rw [hfA, hgB] at hT
  have hcomp := fun {X Y Z : Type u} [CommRing X] [Algebra K X] [CommRing Y] [Algebra K Y]
      [CommRing Z] [Algebra K Z] (PX : FinitePolynomialPresentation K X)
      (PY : FinitePolynomialPresentation K Y) (PZ : FinitePolynomialPresentation K Z)
      (u : X →ₐ[K] Y) (v : Y →ₐ[K] Z) => (hFun K X Y Z PX PX PY PZ u v).2.2.2.1
  have hid := fun {X : Type u} [CommRing X] [Algebra K X]
      (PX : FinitePolynomialPresentation K X) =>
    (hFun K X X X PX PX PX PX (AlgHom.id K X) (AlgHom.id K X)).2.2.1
  let e : localized K PT ≅ localized K U :=
    { hom := localizedHom K U PT ψ
      inv := localizedHom K PT U φ
      hom_inv_id := by rw [← hcomp, hψφ, hid]
      inv_hom_id := by rw [← hcomp, hφψ, hid] }
  refine hT.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · change localizedHom K P PT iL ≫ 𝟙 _ = localizedHom K U PT ψ ≫ localizedHom K P U a
    rw [Category.comp_id, ← hcomp, ← hφL, ← AlgHom.comp_assoc, hψφ, AlgHom.id_comp]
  · change localizedHom K Q PT iR ≫ 𝟙 _ = localizedHom K U PT ψ ≫ localizedHom K Q U b
    rw [Category.comp_id, ← hcomp, ← hφR, ← AlgHom.comp_assoc, hψφ, AlgHom.id_comp]

end Langlands.Analytic.SpaceAnalytification.ExistenceReduction
