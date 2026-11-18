import Langlands.Geometry.FormalGroup.ScalarTorsionTower
import Langlands.Geometry.FormalGroup.FiniteKernelGroupScheme

/-! # Diagrams of scalar-power torsion group schemes -/

noncomputable section
universe u v

namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ ω σ₃ τ₃ : Type}
variable [Finite σ] [Finite τ] [Finite υ] [Finite ω] [Finite σ₃] [Finite τ₃]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}
variable {V : ModuleLaw O R σ₃} {W : ModuleLaw O R τ₃}

namespace Hom.FiniteKernelModel

variable {f : Hom M N} {g : Hom P Q} {k : Hom V W}
variable (K : FiniteKernelModel f) (L : FiniteKernelModel g) (J : FiniteKernelModel k)

/-- Morphisms of the actual kernel schemes are determined by their affine point maps. -/
theorem hom_ext_affinePoints {a b : K.commGroupScheme ⟶ L.commGroupScheme}
    (h : ∀ (A : CommAlgCat.{v} R)
      (x : (algSpec (CommRingCat.of R)).obj (op A) ⟶ K.commGroupScheme.X),
      L.affinePointsEquiv A (x ≫ a.toMul.hom.hom) =
        L.affinePointsEquiv A (x ≫ b.toMul.hom.hom)) :
    a = b := by
  have hx : (𝟙 K.commGroupScheme.X) ≫ a.toMul.hom.hom =
      (𝟙 K.commGroupScheme.X) ≫ b.toMul.hom.hom :=
    (L.affinePointsEquiv K.coordinateAlgebra).injective (h K.coordinateAlgebra (𝟙 _))
  change Additive.ofMul a.toMul = Additive.ofMul b.toMul
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  simpa only [Category.id_comp] using hx

@[simp]
theorem commGroupSchemeMap_id :
    K.commGroupSchemeMap K (𝟙 f.kernelPointFunctor.{u, v, v}) = 𝟙 K.commGroupScheme := by
  apply hom_ext_affinePoints
  intro A x
  change K.affinePointsEquiv A (x ≫ (K.commGroupSchemeMap K (𝟙 _)).toMul.hom.hom) =
    K.affinePointsEquiv A (x ≫ 𝟙 _)
  rw [commGroupSchemeMap_affinePoints, Category.comp_id]
  rfl

theorem commGroupSchemeMap_comp (a : f.kernelPointFunctor.{u, v, v} ⟶ g.kernelPointFunctor)
    (b : g.kernelPointFunctor ⟶ k.kernelPointFunctor) :
    K.commGroupSchemeMap J (a ≫ b) = K.commGroupSchemeMap L a ≫ L.commGroupSchemeMap J b := by
  apply hom_ext_affinePoints
  intro A x
  change J.affinePointsEquiv A (x ≫ (K.commGroupSchemeMap J (a ≫ b)).toMul.hom.hom) =
    J.affinePointsEquiv A
      (x ≫ ((K.commGroupSchemeMap L a).toMul.hom.hom ≫
        (L.commGroupSchemeMap J b).toMul.hom.hom))
  rw [← Category.assoc, commGroupSchemeMap_affinePoints, commGroupSchemeMap_affinePoints,
    commGroupSchemeMap_affinePoints]
  rfl

end Hom.FiniteKernelModel

variable (M) (π : O)

@[simp]
theorem torsionIncl_refl (n : ℕ) : M.torsionIncl π (le_refl n) = 𝟙 _ := by
  apply NatTrans.ext
  funext A
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem torsionIncl_trans {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    M.torsionIncl π (h.trans k) = M.torsionIncl π h ≫ M.torsionIncl π k := by
  apply NatTrans.ext
  funext A
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

namespace IsPiDivisible

variable {M π} (hM : M.IsPiDivisible π)

/-- The actual finite kernel model at exponent n, chosen from scalar divisibility. -/
def torsionKernelModel (n : ℕ) : (M.scalarHom (π ^ n)).FiniteKernelModel :=
  Classical.choice (hM.scalarPower_finiteKernel n)

/-- Scalar-power torsion group schemes and their inclusions, indexed by the natural numbers. -/
def torsionSchemeInclusions : ℕ ⥤ Langlands.CommGroupScheme (Spec (CommRingCat.of R)) where
  obj n := (hM.torsionKernelModel n).commGroupScheme
  map {m n} i :=
    (hM.torsionKernelModel m).commGroupSchemeMap (hM.torsionKernelModel n)
      (M.torsionIncl π (leOfHom i))
  map_id n := by
    change (hM.torsionKernelModel n).commGroupSchemeMap _ (M.torsionIncl π (le_refl n)) = _
    rw [torsionIncl_refl]
    exact (hM.torsionKernelModel n).commGroupSchemeMap_id
  map_comp {l m n} i j := by
    change (hM.torsionKernelModel l).commGroupSchemeMap _
      (M.torsionIncl π ((leOfHom i).trans (leOfHom j))) = _
    rw [torsionIncl_trans]
    exact (hM.torsionKernelModel l).commGroupSchemeMap_comp
      (hM.torsionKernelModel m) (hM.torsionKernelModel n)
      (M.torsionIncl π (leOfHom i)) (M.torsionIncl π (leOfHom j))

/-- The same group schemes form the inverse system with scalar-multiplication transitions. -/
def torsionSchemeTower : ℕᵒᵖ ⥤ Langlands.CommGroupScheme (Spec (CommRingCat.of R)) where
  obj n := (hM.torsionKernelModel n.unop).commGroupScheme
  map {n m} i :=
    (hM.torsionKernelModel n.unop).commGroupSchemeMap (hM.torsionKernelModel m.unop)
      (M.torsionTransition π (leOfHom i.unop))
  map_id n := by
    change (hM.torsionKernelModel n.unop).commGroupSchemeMap _
      (M.torsionTransition π (le_refl n.unop)) = _
    rw [torsionTransition_refl]
    exact (hM.torsionKernelModel n.unop).commGroupSchemeMap_id
  map_comp {n m l} i j := by
    change (hM.torsionKernelModel n.unop).commGroupSchemeMap _
      (M.torsionTransition π ((leOfHom j.unop).trans (leOfHom i.unop))) = _
    rw [torsionTransition_trans]
    exact (hM.torsionKernelModel n.unop).commGroupSchemeMap_comp
      (hM.torsionKernelModel m.unop) (hM.torsionKernelModel l.unop)
      (M.torsionTransition π (leOfHom i.unop)) (M.torsionTransition π (leOfHom j.unop))

end IsPiDivisible
end Langlands.FormalGroup.ModuleLaw
