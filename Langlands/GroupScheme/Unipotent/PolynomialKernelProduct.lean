import Langlands.GroupScheme.Unipotent.KernelCoordinateTransport
import Langlands.GroupScheme.Unipotent.PolynomialKernelCoordinateReduction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-! # Splitting a zero coordinate from an additive polynomial kernel -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H L : GroupScheme S}

/-- The kernel of a homomorphism ignoring the first product factor is the
product of that factor with the original kernel. -/
def kernelSndIso (G : GroupScheme S) (f : H ⟶ L) :
    kernel (snd G H ≫ f) ≅ G ⊗ kernel f where
  hom := lift (kernelι (snd G H ≫ f) ≫ fst G H)
    (pullback.lift (kernelι (snd G H ≫ f) ≫ snd G H)
      (pullback.snd (snd G H ≫ f) (kernelUnit L))
      (by simp only [Category.assoc, kernelι, pullback.condition]))
  inv := pullback.lift (𝟙 G ⊗ₘ kernelι f)
    (snd G (kernel f) ≫ pullback.snd f (kernelUnit L))
    (by simp [kernelι, Category.assoc, pullback.condition])
  hom_inv_id := by
    apply pullback.hom_ext
    · apply hom_ext <;> simp [kernelι, Category.assoc]
    · simp [Category.assoc]
  inv_hom_id := by
    apply hom_ext
    · simp [kernelι]
    · apply pullback.hom_ext <;> simp [kernelι]

@[reassoc (attr := simp)]
theorem kernelSndIso_hom_fst (G : GroupScheme S) (f : H ⟶ L) :
    (kernelSndIso G f).hom ≫ fst _ _ = kernelι (snd G H ≫ f) ≫ fst G H := by
  simp [kernelSndIso]

@[reassoc (attr := simp)]
theorem kernelSndIso_hom_snd_ι (G : GroupScheme S) (f : H ⟶ L) :
    (kernelSndIso G f).hom ≫ snd _ _ ≫ kernelι f =
      kernelι (snd G H ≫ f) ≫ snd G H := by
  simp [kernelSndIso, kernelι]

@[reassoc (attr := simp)]
theorem kernelSndIso_inv_ι (G : GroupScheme S) (f : H ⟶ L) :
    (kernelSndIso G f).inv ≫ kernelι (snd G H ≫ f) = 𝟙 G ⊗ₘ kernelι f := by
  simp [kernelSndIso, kernelι]

namespace VectorGroup

variable {n : ℕ}

/-- Separate the distinguished coordinate from the remaining coordinates. -/
def splitCoordinates {A : Type*} [AddMonoid A] (j : Fin (n + 1)) :
    Multiplicative (Fin (n + 1) → A) ≃*
      Multiplicative (Fin 1 → A) × Multiplicative (Fin n → A) where
  toFun x := (Multiplicative.ofAdd fun _ => x.toAdd j,
    Multiplicative.ofAdd fun i => x.toAdd (j.succAbove i))
  invFun x := Multiplicative.ofAdd (j.insertNth (x.1.toAdd 0) x.2.toAdd)
  left_inv x := by
    apply Multiplicative.toAdd.injective
    exact Fin.insertNth_self_removeNth j x.toAdd
  right_inv x := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simp [hi]
    · apply Multiplicative.toAdd.injective
      funext i
      simp
  map_mul' _ _ := rfl

variable (R : CommRingCat.{u})

/-- Split a vector-group point into its distinguished and remaining coordinates. -/
def splitPoints (j : Fin (n + 1)) (T : Over (Spec R)) :
    (T ⟶ (groupScheme R (n + 1)).X) ≃*
      (T ⟶ (groupScheme R 1 ⊗ groupScheme R n).X) :=
  (coordinates R (n + 1) T).trans ((splitCoordinates j).trans
    ((MulEquiv.prodCongr (coordinates R 1 T).symm (coordinates R n T).symm).trans
      (productPointsEquiv _ _ T).symm))

@[simp]
theorem splitPoints_fst_coord (j : Fin (n + 1)) (T : Over (Spec R))
    (x : T ⟶ (groupScheme R (n + 1)).X) (i : Fin 1) :
    (coordinates R 1 T (splitPoints R j T x ≫ fst _ _)).toAdd i =
      (coordinates R (n + 1) T x).toAdd j := by
  change (coordinates R 1 T
    (productPointsEquiv _ _ T (splitPoints R j T x)).1).toAdd i = _
  simp only [splitPoints, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change (coordinates R 1 T ((coordinates R 1 T).symm _)).toAdd i = _
  rw [MulEquiv.apply_symm_apply]
  rfl

@[simp]
theorem splitPoints_snd_coord (j : Fin (n + 1)) (T : Over (Spec R))
    (x : T ⟶ (groupScheme R (n + 1)).X) (i : Fin n) :
    (coordinates R n T (splitPoints R j T x ≫ snd _ _)).toAdd i =
      (coordinates R (n + 1) T x).toAdd (j.succAbove i) := by
  change (coordinates R n T
    (productPointsEquiv _ _ T (splitPoints R j T x)).2).toAdd i = _
  simp only [splitPoints, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change (coordinates R n T ((coordinates R n T).symm _)).toAdd i = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem splitPoints_natural (j : Fin (n + 1))
    {T W : Over (Spec R)} (a : W ⟶ T) (x : T ⟶ (groupScheme R (n + 1)).X) :
    splitPoints R j W (a ≫ x) = a ≫ splitPoints R j T x := by
  apply (productPointsEquiv _ _ W).injective
  apply Prod.ext
  · apply points_ext
    intro i
    change (coordinates R 1 W (splitPoints R j W (a ≫ x) ≫ fst _ _)).toAdd i =
      (coordinates R 1 W ((a ≫ splitPoints R j T x) ≫ fst _ _)).toAdd i
    rw [splitPoints_fst_coord, Category.assoc, coordinates_comp, coordinates_comp]
    exact congrArg (fun y => a.left.appTop y) (splitPoints_fst_coord R j T x i).symm
  · apply points_ext
    intro i
    change (coordinates R n W (splitPoints R j W (a ≫ x) ≫ snd _ _)).toAdd i =
      (coordinates R n W ((a ≫ splitPoints R j T x) ≫ snd _ _)).toAdd i
    rw [splitPoints_snd_coord, Category.assoc, coordinates_comp, coordinates_comp]
    exact congrArg (fun y => a.left.appTop y) (splitPoints_snd_coord R j T x i).symm

/-- An actual vector-group isomorphism separating any chosen coordinate. -/
def splitIso (j : Fin (n + 1)) :
    groupScheme R (n + 1) ≅ groupScheme R 1 ⊗ groupScheme R n :=
  isoOfPoints (splitPoints R j) (splitPoints_natural R j)

end VectorGroup

namespace Unipotent

open OneDimensional RelativeRoot

variable {k : Type u} [Field k] {n : ℕ}

/-- A zero coordinate contributes nothing to the actual polynomial row. -/
theorem splitIso_hom_snd_comp_polynomialRow
    (f : Fin (n + 1) → k[X]) (hf : ∀ i, IsAdditive (f i))
    (j : Fin (n + 1)) (hj : f j = 0) :
    (VectorGroup.splitIso (CommRingCat.of k) j).hom ≫ snd _ _ ≫
      polynomialRow (fun i => f (j.succAbove i)) (fun i => hf (j.succAbove i)) =
        polynomialRow f hf := by
  apply hom_ext_points
  intro T x
  simp only [Grp.comp_hom_hom, ← Category.assoc, VectorGroup.splitIso,
    comp_isoOfPoints_hom, Grp.snd_hom_hom]
  rw [comp_polynomialRow, comp_polynomialRow]
  apply VectorGroup.points_ext
  intro i
  rw [polynomialRowPoints_coord, polynomialRowPoints_coord]
  simp_rw [VectorGroup.splitPoints_snd_coord]
  rw [Fin.sum_univ_succAbove
    (fun i => (f i).eval₂ (AdditiveGroupQuotient.structureMap T)
      ((VectorGroup.coordinates (CommRingCat.of k) (n + 1) T x).toAdd i)) j]
  simp [hj]

/-- The actual kernel of a row with a zero coordinate splits off that copy of
the additive group, leaving the kernel of the row in the remaining variables. -/
def polynomialKernelZeroCoordinateIso
    (f : Fin (n + 1) → k[X]) (hf : ∀ i, IsAdditive (f i))
    (j : Fin (n + 1)) (hj : f j = 0) :
    kernel (polynomialRow f hf) ≅
      VectorGroup.groupScheme (CommRingCat.of k) 1 ⊗
        kernel (polynomialRow (fun i => f (j.succAbove i))
          (fun i => hf (j.succAbove i))) :=
  (kernelCoordinateIso (snd _ _ ≫ polynomialRow (fun i => f (j.succAbove i))
      (fun i => hf (j.succAbove i))) (polynomialRow f hf)
    (VectorGroup.splitIso (CommRingCat.of k) j)
    (splitIso_hom_snd_comp_polynomialRow f hf j hj)) ≪≫ kernelSndIso _ _

/-- An ambient reduction with a zero row entry gives an actual additive direct
factor, with a polynomial kernel in one fewer variables as complement. -/
theorem exists_polynomialKernelAdditiveFactor_of_zeroCoordinate
    (f : Fin (n + 1) → k[X]) (hf : ∀ i, IsAdditive (f i))
    (h : HasPolynomialKernelZeroCoordinate f hf) :
    ∃ (g : Fin n → k[X]) (hg : ∀ i, IsAdditive (g i)),
      Nonempty (kernel (polynomialRow f hf) ≅
        VectorGroup.groupScheme (CommRingCat.of k) 1 ⊗ kernel (polynomialRow g hg)) := by
  obtain ⟨g, hg, e, he, j, hj⟩ := h
  exact ⟨fun i => g (j.succAbove i), fun i => hg (j.succAbove i),
    ⟨(kernelCoordinateIso (polynomialRow f hf) (polynomialRow g hg) e he).symm ≪≫
      polynomialKernelZeroCoordinateIso g hg j hj⟩⟩

/-- Failure of affine-line constancy splits off an actual additive direct
factor from a polynomial kernel over any field. -/
theorem exists_polynomialKernelAdditiveFactor_of_not_hasConstantAffineLineMaps
    (f : Fin (n + 1) → k[X]) (hf : ∀ i, IsAdditive (f i))
    (h : ¬ HasConstantAffineLineMaps (kernel (polynomialRow f hf))) :
    ∃ (g : Fin n → k[X]) (hg : ∀ i, IsAdditive (g i)),
      Nonempty (kernel (polynomialRow f hf) ≅
        VectorGroup.groupScheme (CommRingCat.of k) 1 ⊗ kernel (polynomialRow g hg)) :=
  exists_polynomialKernelAdditiveFactor_of_zeroCoordinate f hf
    (hasPolynomialKernelZeroCoordinate_of_not_hasConstantAffineLineMaps f hf h)

end Unipotent

end Langlands.GroupScheme
