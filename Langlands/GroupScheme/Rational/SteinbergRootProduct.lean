import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Supplied normalized simple-root maps and the Steinberg ordered morphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace VectorGroup

variable (R : CommRingCat.{u})

/-- The standard vector-group model is affine over its coefficient ring. -/
instance isAffineHom_groupScheme (r : ℕ) : IsAffineHom (groupScheme R r).X.hom := by
  change IsAffineHom (Spec.map
    (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin r) R))))
  infer_instance

/-- The point of the standard additive group with global coordinate `c`. -/
def scalarPoint (T : Over (Spec R)) (c : Γ(T.left, ⊤)) :
    T ⟶ (groupScheme R 1).X :=
  (coordinates R 1 T).symm (Multiplicative.ofAdd fun _ => c)

@[simp]
theorem coordinates_scalarPoint (T : Over (Spec R)) (c : Γ(T.left, ⊤)) (j : Fin 1) :
    (coordinates R 1 T (scalarPoint R T c)).toAdd j = c :=
  congrArg (fun z => z.toAdd j) ((coordinates R 1 T).apply_symm_apply _)

/-- Scalar parameters pull back as global functions on every test scheme. -/
theorem scalarPoint_comp {T W : Over (Spec R)} (f : W ⟶ T) (c : Γ(T.left, ⊤)) :
    f ≫ scalarPoint R T c = scalarPoint R W (f.left.appTop c) := by
  apply points_ext
  intro j
  rw [coordinates_comp]
  simp only [coordinates_scalarPoint]

/-- The actual projection to the `j`-th standard additive coordinate. -/
def coordinateMorphism (r : ℕ) (j : Fin r) :
    (groupScheme R r).X ⟶ (groupScheme R 1).X :=
  scalarPoint R _ (coordinateSection R r j)

/-- Coordinate projection evaluates to the chosen global coordinate on every test. -/
theorem comp_coordinateMorphism {r : ℕ} (j : Fin r) {T : Over (Spec R)}
    (c : T ⟶ (groupScheme R r).X) :
    c ≫ coordinateMorphism R r j =
      scalarPoint R T ((coordinates R r T c).toAdd j) := by
  rw [coordinateMorphism, scalarPoint_comp, coordinates_apply]

variable (k : Type u) [Field k]

/-- The standard epsilon tangent vector, with epsilon coefficient one. -/
def standardEpsilon :
    Additive (lieKernel (groupScheme (CommRingCat.of k) 1) (CommRingCat.of k)) :=
  Additive.ofMul (RelativeRoot.vectorLiePoint (coordinates (CommRingCat.of k) 1)
    isNaturalVectorCoordinates (fun _ => (1 : k)))

end VectorGroup

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
  VectorGroup.isAffineHom_groupScheme (CommRingCat.of k) 1

/-- Supplied additive coordinates on one whole intrinsic simple-root subgroup,
with its torus weight and derivative normalized by the given Lie pinning. -/
structure NormalizedRootParametrization (a : p.base.support) where
  hom : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G
  represents : (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).IsRepresentedBy hom
  isClosedSubgroup : IsClosedSubgroup hom
  torus_equivariant : ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ p.torus.X)
    (c : Γ(T.left, ⊤)),
    (t ≫ p.inclusion.hom.hom) *
        (VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ hom.hom.hom) *
        (t ≫ p.inclusion.hom.hom)⁻¹ =
      VectorGroup.scalarPoint (CommRingCat.of k) T
        (VectorGroup.charValue (p.rootDatum.root a) T t * c) ≫ hom.hom.hom
  derivative : Lie.targetMapLinear hom (CommRingCat.of k) (VectorGroup.standardEpsilon k) =
    p.pinning.rootVector a

/-- A supplied normalized parametrization for each simple root; no existence is asserted. -/
def NormalizedSimpleRootParametrizations := ∀ a : p.base.support, p.NormalizedRootParametrization a

namespace NormalizedRootParametrization

variable {p} {a : p.base.support} (x : p.NormalizedRootParametrization a)

/-- Evaluate the root map at a global function, using standard additive coordinates. -/
def point (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤)) : T ⟶ G.X :=
  VectorGroup.scalarPoint (CommRingCat.of k) T c ≫ x.hom.hom.hom

/-- Evaluation of a supplied root parametrization is natural on every test. -/
theorem point_comp {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T)
    (c : Γ(T.left, ⊤)) :
    f ≫ x.point T c = x.point W (f.left.appTop c) := by
  rw [point, ← Category.assoc, VectorGroup.scalarPoint_comp, point]

/-- The image is the whole intrinsic root subgroup on every scheme test. -/
theorem mem_rootSubgroup_iff (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier T ↔
      ∃ c : Γ(T.left, ⊤), x.point T c = g := by
  rw [← x.represents.2, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨(VectorGroup.coordinates (CommRingCat.of k) 1 T v).toAdd 0, ?_⟩
    change VectorGroup.scalarPoint (CommRingCat.of k) T _ ≫ x.hom.hom.hom =
      v ≫ x.hom.hom.hom
    apply congrArg (fun z : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X =>
      z ≫ x.hom.hom.hom)
    apply VectorGroup.points_ext
    intro j
    rw [VectorGroup.coordinates_scalarPoint]
    exact congrArg (fun i => (VectorGroup.coordinates (CommRingCat.of k) 1 T v).toAdd i)
      (Subsingleton.elim 0 j)
  · rintro ⟨c, rfl⟩
    exact ⟨VectorGroup.scalarPoint (CommRingCat.of k) T c, rfl⟩

end NormalizedRootParametrization

/-- A supplied rational representative and actual torus automorphism realizing one
simple reflection, with the Library's contravariant character convention. -/
structure SimpleReflectionRepresentative (a : p.base.support) where
  point : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X
  torusAut : p.torus ≅ p.torus
  normalizes : IsNormalizingPoint p.inclusion point torusAut
  characterAut_eq : characterAut torusAut = p.rootDatum.reflection a

/-- Supplied simple-reflection representatives; no choices or descent laws are imposed. -/
def SimpleReflectionRepresentatives := ∀ a : p.base.support, p.SimpleReflectionRepresentative a

variable {p} {r : ℕ}
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (n : p.SimpleReflectionRepresentatives)

omit [IsAffineHom G.X.hom] in
private theorem comp_list_prod {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T)
    (l : List (T ⟶ G.X)) :
    f ≫ l.prod = (l.map (fun g => f ≫ g)).prod := by
  induction l with
  | nil => simp
  | cons g l ih => simp only [List.prod_cons, List.map_cons, MonObj.comp_mul, ih]

/-- The ordered simple-root product for global-function coordinates on any test.
`List.ofFn` takes the factors in increasing `Fin r` order. -/
def steinbergProductPoint (T : Over (Spec (CommRingCat.of k))) (c : Fin r → Γ(T.left, ⊤)) :
    T ⟶ G.X :=
  (List.ofFn fun j => (x (e j)).point T (c j) * (toUnit T ≫ (n (e j)).point)).prod

/-- The ordered formula commutes with arbitrary precomposition, pulling back each
coordinate and each rational representative along the test's structure map. -/
theorem steinbergProductPoint_comp {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T)
    (c : Fin r → Γ(T.left, ⊤)) :
    f ≫ steinbergProductPoint e x n T c =
      steinbergProductPoint e x n W (fun j => f.left.appTop (c j)) := by
  have hf : f ≫ toUnit T = toUnit W := toUnit_unique _ _
  simp only [steinbergProductPoint, comp_list_prod, List.map_ofFn, Function.comp_def,
    MonObj.comp_mul, NormalizedRootParametrization.point_comp, ← Category.assoc, hf]

/-- The actual Steinberg ordered morphism from standard affine `r`-space, relative
to the supplied root maps, representatives and ordering. It is a scheme morphism. -/
def steinbergProduct : (VectorGroup.groupScheme (CommRingCat.of k) r).X ⟶ G.X :=
  steinbergProductPoint e x n _ (VectorGroup.coordinateSection (CommRingCat.of k) r)

/-- Evaluation of the scheme morphism has the ordered global-coordinate formula
on every test over the field. -/
theorem comp_steinbergProduct {T : Over (Spec (CommRingCat.of k))}
    (c : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) r).X) :
    c ≫ steinbergProduct e x n =
      (List.ofFn fun j =>
        (x (e j)).point T ((VectorGroup.coordinates (CommRingCat.of k) r T c).toAdd j) *
          (toUnit T ≫ (n (e j)).point)).prod := by
  rw [steinbergProduct, steinbergProductPoint_comp]
  simp only [steinbergProductPoint, VectorGroup.coordinates_apply]

/-- The same formula can be evaluated at any specified family of global functions. -/
theorem coordinatesPoint_comp_steinbergProduct (T : Over (Spec (CommRingCat.of k)))
    (c : Fin r → Γ(T.left, ⊤)) :
    (VectorGroup.coordinates (CommRingCat.of k) r T).symm (Multiplicative.ofAdd c) ≫
        steinbergProduct e x n = steinbergProductPoint e x n T c := by
  rw [comp_steinbergProduct]
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd, steinbergProductPoint]

/-- The empty ordered product is the identity point on every test. -/
@[simp]
theorem steinbergProductPoint_zero (e : Fin 0 ≃ p.base.support)
    (T : Over (Spec (CommRingCat.of k))) (c : Fin 0 → Γ(T.left, ⊤)) :
    steinbergProductPoint e x n T c = 1 := by
  simp [steinbergProductPoint]

/-- In rank zero the actual morphism is the constant identity morphism. -/
@[simp]
theorem steinbergProduct_zero (e : Fin 0 ≃ p.base.support) :
    steinbergProduct e x n = 1 := by
  change steinbergProductPoint e x n _ _ = 1
  apply steinbergProductPoint_zero

end SplitPinning

end Langlands.GroupScheme
