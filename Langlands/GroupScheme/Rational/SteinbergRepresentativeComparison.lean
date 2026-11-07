import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.Rational.ClassFunctions
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # Torus comparisons of supplied simple-reflection representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem orderedProduct_telescope {A : Type*} [Group A] (r : ℕ)
    (a : Fin r → A) (b : Fin (r + 1) → A) :
    (List.ofFn fun j => b j.castSucc * a j * (b j.succ)⁻¹).prod =
      b 0 * (List.ofFn a).prod * (b (Fin.last r))⁻¹ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    have ht := ih (fun j => a j.succ) (fun j => b j.succ)
    simp only [Fin.succ_castSucc] at ht
    rw [ht]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    group

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G}

namespace SimpleReflectionRepresentative

variable {a : p.base.support} (n m : p.SimpleReflectionRepresentative a)

/-- The full split-torus automorphism is determined by its specified character action. -/
theorem torusAut_eq : n.torusAut = m.torusAut := by
  have hi : n.torusAut.inv = m.torusAut.inv :=
    p.isSplitTorus.hom_ext_characters fun χ => by
      have h := n.characterAut_eq.trans m.characterAut_eq.symm
      exact congrArg (fun q : characterLattice p.torus ≃ₗ[ℤ]
        characterLattice p.torus => q χ) h
  have h : n.torusAut.symm = m.torusAut.symm := Iso.ext hi
  exact congrArg Iso.symm h

/-- Two supplied representatives of one reflection differ by a unique rational torus point. -/
theorem existsUnique_torus_mul :
    ∃! t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X,
      n.point = (t ≫ p.inclusion.hom.hom) * m.point := by
  let : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono
  let : Mono p.inclusion.hom.hom := Over.mono_of_mono_left _
  have hn := n.normalizes.mul m.normalizes.inv
  rw [torusAut_eq n m, Iso.symm_self_id] at hn
  have hc : n.point * m.point⁻¹ ∈
      (torusCentralizer p.inclusion).carrier (Over.mk (𝟙 _)) := by
    rw [torusCentralizer_carrier_base]
    exact hn
  rw [maximalTorusCentralizer k G p.isConnectedReductive p.torus p.inclusion
    p.isMaximalTorus, SubgroupFunctor.mem_range] at hc
  obtain ⟨t, ht⟩ := hc
  have he : n.point = (t ≫ p.inclusion.hom.hom) * m.point := by
    rw [ht, mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨t, he, ?_⟩
  intro s hs
  apply (cancel_mono p.inclusion.hom.hom).mp
  exact mul_right_cancel (hs.symm.trans he)

/-- The actual rational torus ratio of two supplied reflection representatives. -/
def torusRatio : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X :=
  Classical.choose (existsUnique_torus_mul n m)

/-- The torus ratio compares the actual rational points of the ambient group. -/
theorem point_eq_torusRatio_mul :
    n.point = (torusRatio n m ≫ p.inclusion.hom.hom) * m.point :=
  (Classical.choose_spec (existsUnique_torus_mul n m)).1

end SimpleReflectionRepresentative

variable {r : ℕ}

local notation "V" => VectorGroup.groupScheme (CommRingCat.of k) r
local notation "coords" => VectorGroup.coordinates (CommRingCat.of k) r

/-- Scaling each standard coordinate by the corresponding root value of a rational torus point. -/
def torusScalePoint (a : Fin r → p.base.support)
    (s : Fin r → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X))
    (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ (V).X) : T ⟶ (V).X :=
  (coords T).symm (Multiplicative.ofAdd fun j =>
    VectorGroup.charValue (p.rootDatum.root (a j)) T (toUnit T ≫ s j) *
      (coords T v).toAdd j)

theorem coordinates_torusScalePoint (a : Fin r → p.base.support)
    (s : Fin r → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X))
    (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ (V).X) (j : Fin r) :
    (coords T (torusScalePoint a s T v)).toAdd j =
      VectorGroup.charValue (p.rootDatum.root (a j)) T (toUnit T ≫ s j) *
        (coords T v).toAdd j := by
  rw [torusScalePoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem torusScalePoint_comp (a : Fin r → p.base.support)
    (s : Fin r → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X))
    {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T) (v : T ⟶ (V).X) :
    f ≫ torusScalePoint a s T v = torusScalePoint a s W (f ≫ v) := by
  apply VectorGroup.points_ext
  intro j
  simp only [VectorGroup.coordinates_comp, coordinates_torusScalePoint, map_mul]
  congr 1
  rw [← VectorGroup.charValue_comp, ← Category.assoc,
    toUnit_unique (f ≫ toUnit T) (toUnit W)]

theorem torusScalePoint_one (a : Fin r → p.base.support)
    (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ (V).X) :
    torusScalePoint a 1 T v = v := by
  apply VectorGroup.points_ext
  intro j
  rw [coordinates_torusScalePoint]
  simp only [Pi.one_apply, MonObj.comp_one, VectorGroup.charValue_one, one_mul]

theorem torusScalePoint_mul (a : Fin r → p.base.support)
    (s t : Fin r → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X))
    (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ (V).X) :
    torusScalePoint a (s * t) T v =
      torusScalePoint a s T (torusScalePoint a t T v) := by
  apply VectorGroup.points_ext
  intro j
  simp only [coordinates_torusScalePoint, Pi.mul_apply, MonObj.comp_mul,
    VectorGroup.charValue_mul, mul_assoc]

theorem torusScalePoint_mul_right (a : Fin r → p.base.support)
    (s : Fin r → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X))
    (T : Over (Spec (CommRingCat.of k))) (v w : T ⟶ (V).X) :
    torusScalePoint a s T (v * w) =
      torusScalePoint a s T v * torusScalePoint a s T w := by
  apply VectorGroup.points_ext
  intro j
  simp only [coordinates_torusScalePoint, VectorGroup.coordinates_mul,
    Pi.add_apply, mul_add]

/-- Root-value scaling is an invertible natural transformation of the vector-group points. -/
def torusScalePointsEquiv (a : Fin r → p.base.support)
    (s : Fin r → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X))
    (T : Over (Spec (CommRingCat.of k))) : (T ⟶ (V).X) ≃* (T ⟶ (V).X) where
  toFun := torusScalePoint a s T
  invFun := torusScalePoint a s⁻¹ T
  left_inv v := by
    rw [← torusScalePoint_mul, inv_mul_cancel, torusScalePoint_one]
  right_inv v := by
    rw [← torusScalePoint_mul, mul_inv_cancel, torusScalePoint_one]
  map_mul' := torusScalePoint_mul_right a s T

/-- The actual diagonal coordinate isomorphism defined by rational torus root values. -/
def torusScaleIso (a : Fin r → p.base.support)
    (s : Fin r → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X)) : V ≅ V :=
  isoOfPoints (torusScalePointsEquiv a s) fun {_ _} f v =>
    (torusScalePoint_comp a s f v).symm

theorem comp_torusScaleIso_hom (a : Fin r → p.base.support)
    (s : Fin r → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X))
    (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ (V).X) :
    v ≫ (torusScaleIso a s).hom.hom.hom = torusScalePoint a s T v := by
  unfold torusScaleIso
  exact comp_isoOfPoints_hom (torusScalePointsEquiv a s)
    (fun {_ _} f w => (torusScalePoint_comp a s f w).symm) T v

variable (e : Fin r ≃ p.base.support)
    (n m : p.SimpleReflectionRepresentatives)

/-- A cyclic torus comparison of two supplied ordered representative families.
Its existence is a separate obligation. -/
structure CyclicTorusGauge where
  point : Fin (r + 1) → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ p.torus.X)
  closes : point (Fin.last r) = point 0
  factor_eq : ∀ j : Fin r,
    (m (e j)).point =
      (point j.castSucc ≫ p.inclusion.hom.hom) * (n (e j)).point *
        (point j.succ ≫ p.inclusion.hom.hom)⁻¹

namespace CyclicTorusGauge

variable {e n m} (g : p.CyclicTorusGauge e n m)
    (x : p.NormalizedSimpleRootParametrizations)

/-- The actual diagonal parameter isomorphism attached to the successive torus points. -/
def coordinateIso : V ≅ V :=
  torusScaleIso (fun j => e j) (fun j => g.point j.castSucc)

/-- The scaled ordered product is conjugate to the original product on every test scheme. -/
theorem productPoint_eq (T : Over (Spec (CommRingCat.of k)))
    (c : Fin r → Γ(T.left, ⊤)) :
    steinbergProductPoint e x m T (fun j =>
        VectorGroup.charValue (p.rootDatum.root (e j)) T
          (toUnit T ≫ g.point j.castSucc) * c j) =
      (toUnit T ≫ g.point 0 ≫ p.inclusion.hom.hom) *
        steinbergProductPoint e x n T c *
        (toUnit T ≫ g.point 0 ≫ p.inclusion.hom.hom)⁻¹ := by
  have hf (j : Fin r) :
      (x (e j)).point T
          (VectorGroup.charValue (p.rootDatum.root (e j)) T
            (toUnit T ≫ g.point j.castSucc) * c j) *
          (toUnit T ≫ (m (e j)).point) =
        (toUnit T ≫ g.point j.castSucc ≫ p.inclusion.hom.hom) *
          ((x (e j)).point T (c j) * (toUnit T ≫ (n (e j)).point)) *
          (toUnit T ≫ g.point j.succ ≫ p.inclusion.hom.hom)⁻¹ := by
    have hx := (x (e j)).torus_equivariant T
      (toUnit T ≫ g.point j.castSucc) (c j)
    change (toUnit T ≫ g.point j.castSucc ≫ p.inclusion.hom.hom) *
        (x (e j)).point T (c j) *
        (toUnit T ≫ g.point j.castSucc ≫ p.inclusion.hom.hom)⁻¹ =
      (x (e j)).point T
        (VectorGroup.charValue (p.rootDatum.root (e j)) T
          (toUnit T ≫ g.point j.castSucc) * c j) at hx
    rw [← hx, g.factor_eq, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
    simp only []
    group
  simp only [steinbergProductPoint, hf]
  have ht := orderedProduct_telescope r
    (fun j => (x (e j)).point T (c j) * (toUnit T ≫ (n (e j)).point))
    (fun j => toUnit T ≫ g.point j ≫ p.inclusion.hom.hom)
  rw [g.closes] at ht
  exact ht

/-- The canonical quotient composites agree after the actual parameter isomorphism. -/
theorem coordinateIso_comp_quotient :
    (g.coordinateIso).hom.hom.hom ≫ steinbergProduct e x m ≫ ClassFunctions.rho G =
      steinbergProduct e x n ≫ ClassFunctions.rho G := by
  have h := productPoint_eq g x (V).X
    (VectorGroup.coordinateSection (CommRingCat.of k) r)
  have hc :
      (g.coordinateIso).hom.hom.hom ≫ steinbergProduct e x m =
        steinbergProductPoint e x m (V).X (fun j =>
          VectorGroup.charValue (p.rootDatum.root (e j)) (V).X
              (toUnit (V).X ≫ g.point j.castSucc) *
            VectorGroup.coordinateSection (CommRingCat.of k) r j) := by
    have hs := comp_torusScaleIso_hom (fun j => e j)
      (fun j => g.point j.castSucc) (V).X (𝟙 (V).X)
    rw [Category.id_comp] at hs
    rw [comp_steinbergProduct]
    apply congrArg (steinbergProductPoint e x m (V).X)
    funext j
    rw [coordinateIso, hs, coordinates_torusScalePoint, VectorGroup.coordinates_apply]
    simp only [Over.id_left, Scheme.Hom.id_appTop, CategoryTheory.id_apply]
  rw [← Category.assoc, hc, h]
  exact ClassFunctions.rho_conjugation G _ _

include g in
/-- A supplied cyclic torus comparison preserves the desired quotient-isomorphism property. -/
theorem isIso_quotient_iff :
    IsIso (steinbergProduct e x m ≫ ClassFunctions.rho G) ↔
      IsIso (steinbergProduct e x n ≫ ClassFunctions.rho G) := by
  let : IsIso (g.coordinateIso).hom.hom.hom :=
    (Grp.forget _).map_isIso g.coordinateIso.hom
  rw [← coordinateIso_comp_quotient g x]
  exact (isIso_comp_left_iff _ _).symm

end CyclicTorusGauge

end SplitPinning

end Langlands.GroupScheme
