import Langlands.GroupScheme.Rational.OrderedProductMaps
import Langlands.GroupScheme.Rational.OrderedProductAlgebra
import Langlands.GroupScheme.Rational.FppfLocalLifting

/-! # Descent of ordered products through a central extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false

section KernelCoordinates

variable {n : ℕ} {H R : Fin n → GroupScheme B}

/-- Tuples of actual kernel points are exactly tuples whose quotient coordinates
are all the identity, on every test scheme. -/
def kernelFamilyPointsEquiv (p : ∀ i, H i ⟶ R i) (T : Over B) :
    (∀ i, T ⟶ (kernel (p i)).X) ≃
      {x : ∀ i, T ⟶ (H i).X // ∀ i, x i ≫ (p i).hom.hom = 1} where
  toFun x := ⟨fun i => (kernelPointsEquiv (p i) T (x i)).val,
    fun i => (kernelPointsEquiv (p i) T (x i)).property⟩
  invFun x i := (kernelPointsEquiv (p i) T).symm ⟨x.val i, x.property i⟩
  left_inv x := by
    funext i
    exact (kernelPointsEquiv (p i) T).symm_apply_apply (x i)
  right_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val
      ((kernelPointsEquiv (p i) T).apply_symm_apply ⟨x.val i, x.property i⟩)

@[simp]
theorem kernelFamilyPointsEquiv_apply (p : ∀ i, H i ⟶ R i)
    (T : Over B) (x : ∀ i, T ⟶ (kernel (p i)).X) (i : Fin n) :
    (kernelFamilyPointsEquiv p T x).val i = x i ≫ (kernelι (p i)).hom.hom := rfl

@[simp]
theorem kernelFamilyPointsEquiv_symm_ι (p : ∀ i, H i ⟶ R i)
    (T : Over B) (x : {x : ∀ i, T ⟶ (H i).X //
      ∀ i, x i ≫ (p i).hom.hom = 1}) (i : Fin n) :
    (kernelFamilyPointsEquiv p T).symm x i ≫ (kernelι (p i)).hom.hom = x.val i :=
  congrArg Subtype.val
    ((kernelPointsEquiv (p i) T).apply_symm_apply ⟨x.val i, x.property i⟩)

end KernelCoordinates

section Descent

variable {n : ℕ} {G Q : GroupScheme B} {H R : Fin n → GroupScheme B}
    (j : ∀ i, H i ⟶ G) (k : ∀ i, R i ⟶ Q)
    (q : G ⟶ Q) (p : ∀ i, H i ⟶ R i)
    (h : ∀ i, j i ≫ q = p i ≫ k i)
    (l : ∀ i, kernel (p i) ⟶ kernel q)
    (hl : ∀ i, l i ≫ kernelι q = kernelι (p i) ≫ j i)

include hl

/-- An actual kernel-product isomorphism gives uniqueness of the kernel
corrections in the original factor coordinates. -/
theorem kernel_coordinates_unique [IsIso (orderedMultiplication l)]
    (T : Over B) (z : ∀ i, T ⟶ (H i).X)
    (hz : ∀ i, z i ≫ (p i).hom.hom = 1)
    (hprod : orderedPoints j z = 1) :
    ∀ i, z i = 1 := by
  let t := (kernelFamilyPointsEquiv p T).symm ⟨z, hz⟩
  have ht : ∀ i, t i ≫ (kernelι (p i)).hom.hom = z i :=
    kernelFamilyPointsEquiv_symm_ι p T ⟨z, hz⟩
  have he : orderedPoints l t = 1 := by
    apply (cancel_mono (kernelι q).hom.hom).mp
    rw [orderedPoints_map l j (kernelι q) (fun i => kernelι (p i)) hl]
    simp_rw [ht]
    simpa only [MonObj.one_comp] using hprod
  have hinj := ((isIso_orderedMultiplication_iff l).mp inferInstance T).1
  have ht1 : t = fun i => 1 := by
    apply hinj
    simpa [orderedPoints] using he
  intro i
  rw [← ht i, ht1]
  exact MonObj.one_comp _

/-- An actual kernel-product isomorphism factors each point of the target
kernel by a tuple of points in the factor kernels. -/
theorem kernel_coordinates_exist [IsIso (orderedMultiplication l)]
    (T : Over B) (z : T ⟶ G.X) (hz : z ≫ q.hom.hom = 1) :
    ∃ t : ∀ i, T ⟶ (H i).X,
      (∀ i, t i ≫ (p i).hom.hom = 1) ∧ orderedPoints j t = z := by
  let z' : T ⟶ (kernel q).X := (kernelPointsEquiv q T).symm ⟨z, hz⟩
  obtain ⟨t, ht⟩ := ((isIso_orderedMultiplication_iff l).mp inferInstance T).2 z'
  refine ⟨(kernelFamilyPointsEquiv p T t).val,
    (kernelFamilyPointsEquiv p T t).property, ?_⟩
  have he := congrArg (fun x => x ≫ (kernelι q).hom.hom) ht
  rw [orderedPoints_map l j (kernelι q) (fun i => kernelι (p i)) hl] at he
  exact he.trans (congrArg Subtype.val
    ((kernelPointsEquiv q T).apply_symm_apply ⟨z, hz⟩))

include h

/-- Ordered factorization descends through an fppf family of factor quotients
and a central ambient kernel. Both quotient and kernel products are actual
scheme isomorphisms. -/
theorem isIso_orderedMultiplication_of_centralExtension
    [IsIso (orderedMultiplication k)] [IsIso (orderedMultiplication l)]
    (hf : ∀ i, Flat (p i).hom.hom.left)
    (hs : ∀ i, Surjective (p i).hom.hom.left)
    (hfp : ∀ i, LocallyOfFinitePresentation (p i).hom.hom.left)
    (hc : ∀ (T : Over B) (z : T ⟶ G.X), z ≫ q.hom.hom = 1 →
      ∀ g : T ⟶ G.X, Commute z g) :
    IsIso (orderedMultiplication j) := by
  have hinj : ∀ T : Over B, Function.Injective (orderedPoints j (T := T)) := by
    intro T
    let jT := fun i => ((pointsMap (j i)).app (op T)).hom
    let kT := fun i => ((pointsMap (k i)).app (op T)).hom
    let qT := ((pointsMap q).app (op T)).hom
    let pT := fun i => ((pointsMap (p i)).app (op T)).hom
    have hT : ∀ i x, qT (jT i x) = kT i (pT i x) := by
      intro i x
      have e := congrArg (fun f => f.hom.hom) (h i)
      change (j i).hom.hom ≫ q.hom.hom = (p i).hom.hom ≫ (k i).hom.hom at e
      exact (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) e).trans
        (Category.assoc _ _ _).symm)
    exact CentralExtension.injective_of_quotient_and_kernel jT kT qT pT hT
      (hc T) (((isIso_orderedMultiplication_iff k).mp inferInstance T).1)
      (fun z hz hprod => kernel_coordinates_unique j q p l hl T z hz hprod)
  let : Mono (orderedMultiplication j) := (mono_orderedMultiplication_iff j).mpr hinj
  let g : G.X ⟶ G.X := 𝟙 G.X
  obtain ⟨y, hy⟩ := ((isIso_orderedMultiplication_iff k).mp inferInstance G.X).2
    (g ≫ q.hom.hom)
  obtain ⟨V, a, haf, has, hafp, x, hx⟩ :=
    exists_fppf_lift_family n (fun i => (H i).X) (fun i => (R i).X)
      (fun i => (p i).hom.hom) hf hs hfp G.X y
  have hxq : orderedPoints k (fun i => x i ≫ (p i).hom.hom) =
      (a ≫ g) ≫ q.hom.hom := by
    simp_rw [← hx]
    rw [← orderedPoints_naturality, hy, Category.assoc]
  let jV := fun i => ((pointsMap (j i)).app (op V)).hom
  let kV := fun i => ((pointsMap (k i)).app (op V)).hom
  let qV := ((pointsMap q).app (op V)).hom
  let pV := fun i => ((pointsMap (p i)).app (op V)).hom
  have hV : ∀ i z, qV (jV i z) = kV i (pV i z) := by
    intro i z
    have e := congrArg (fun f => f.hom.hom) (h i)
    change (j i).hom.hom ≫ q.hom.hom = (p i).hom.hom ≫ (k i).hom.hom at e
    exact (Category.assoc _ _ _).trans ((congrArg (z ≫ ·) e).trans
      (Category.assoc _ _ _).symm)
  obtain ⟨z, hz⟩ := CentralExtension.exists_of_lifts_and_kernel jV kV qV pV hV
    (hc V) (fun t ht => kernel_coordinates_exist j q p l hl V t ht) (a ≫ g) x hxq
  have hz' : (finiteProductPointsEquiv H V).symm z ≫ orderedMultiplication j = a := by
    rw [finiteProductPointsEquiv_symm_orderedMultiplication]
    exact hz.trans (Category.comp_id a)
  let : Flat a.left := haf
  let : Surjective a.left := has
  let : LocallyOfFinitePresentation a.left := hafp
  exact isIso_of_effectiveEpi_factorization (orderedMultiplication j) a
    ((finiteProductPointsEquiv H V).symm z) hz'

end Descent

end Langlands.GroupScheme.RelativeRoot
