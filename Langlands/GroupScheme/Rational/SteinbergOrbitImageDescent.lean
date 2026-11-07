import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.Rational.OrbitProductImageDescent

/-! # Actual Steinberg products and conditional orbit-image descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SteinbergOrbitImageDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option autoImplicit false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local notation "GK" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance : IsAffineHom (GK).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : Langlands.GroupScheme.SplitPinning
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    {r : ℕ} (I : Type u) (d : Fin r ≃ I)
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (n : p.SimpleReflectionRepresentatives)

local notation "R" => MvPolynomial I K

/-- Rename the standard finite coordinates by the supplied index equivalence. -/
def coordinateTestIso :
    (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K R)) ≅
      (VectorGroup.groupScheme (CommRingCat.of K) r).X :=
  (algSpec (CommRingCat.of K)).mapIso
    (CommAlgCat.isoMk (MvPolynomial.renameEquiv K d)).op

/-- Evaluate an actual root-and-representative factor on the renamed polynomial test. -/
def factorK (i : I) : Lie.AffinePoints GK R := by
  let T := (VectorGroup.groupScheme (CommRingCat.of K) r).X
  let a := (x (e (d.symm i))).point T
    (VectorGroup.coordinateSection (CommRingCat.of K) r (d.symm i))
  let b : T ⟶ (GK).X := toUnit T ≫ (n (e (d.symm i))).point
  exact (coordinateTestIso K I d).hom ≫ (a * b)

/-- The same actual factor viewed as a point of the original group. -/
def factor (i : I) : Lie.AffinePoints G R :=
  Lie.affineBaseChangeEquiv k K G R (factorK k K G p I d e x n i)

private theorem comp_list_prod {S : Scheme.{u}} (H : GroupScheme S)
    {T W : Over S} (f : W ⟶ T) (l : List (T ⟶ H.X)) :
    f ≫ l.prod = (l.map (fun g => f ≫ g)).prod := by
  induction l with
  | nil => simp
  | cons g l ih => simp only [List.prod_cons, List.map_cons, MonObj.comp_mul, ih]

omit [IsAffineHom G.X.hom] in
/-- Flattening the supplied blocks gives their ordinary ordered product. -/
theorem blockProduct_eq_flatten (blocks : List (List I))
    (f : I → Lie.AffinePoints G R) :
    OrbitProductPullback.blockProduct k K I G blocks f =
      (blocks.flatten.map f).prod := by
  induction blocks with
  | nil => rfl
  | cons l blocks ih =>
    change (l.map f).prod *
      OrbitProductPullback.blockProduct k K I G blocks f = _
    rw [ih]
    simp only [List.flatten_cons, List.map_append, List.prod_append]

/-- Exact coordinate order identifies the actual block product with the
supplied Steinberg morphism after the coordinate-test isomorphism. -/
theorem blockProduct_eq (blocks : List (List I))
    (horder : blocks.flatten = List.ofFn d) :
    OrbitProductPullback.blockProduct k K I G blocks (factor k K G p I d e x n) =
      Lie.affineBaseChangeEquiv k K G R
        ((coordinateTestIso K I d).hom ≫ SplitPinning.steinbergProduct e x n) := by
  rw [blockProduct_eq_flatten, horder, List.map_ofFn]
  unfold SplitPinning.steinbergProduct SplitPinning.steinbergProductPoint
  rw [
    comp_list_prod, List.map_ofFn, map_list_prod, List.map_ofFn]
  dsimp only [Function.comp_def, factor, factorK]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  rw [d.symm_apply_apply]

/-- The tensor-coordinate point is the supplied Steinberg morphism with
its source transported by the explicit coordinate isomorphism. -/
theorem point_blockProduct_eq (blocks : List (List I))
    (horder : blocks.flatten = List.ofFn d) :
    OrbitProductImageDescent.point k K I G
        (OrbitProductPullback.blockProduct k K I G blocks (factor k K G p I d e x n)) =
      (coordinateTestIso K I d).hom ≫ SplitPinning.steinbergProduct e x n := by
  apply (Lie.affineBaseChangeEquiv k K G R).injective
  rw [OrbitProductImageDescent.affineBaseChangeEquiv_point]
  exact blockProduct_eq k K G p I d e x n blocks horder

/-- Equality as actual scheme morphisms after changing polynomial coordinates. -/
theorem morphism_blockProduct_eq (blocks : List (List I))
    (horder : blocks.flatten = List.ofFn d) :
    OrbitProductImageDescent.morphism k K I G
        (OrbitProductPullback.blockProduct k K I G blocks (factor k K G p I d e x n)) =
      (coordinateTestIso K I d).hom.left ≫ (SplitPinning.steinbergProduct e x n).left :=
  congrArg (fun y : Lie.AffinePoints GK R => y.left)
    (point_blockProduct_eq k K G p I d e x n blocks horder)

/-- An isomorphism of the source preserves the full image ideal sheaf. -/
theorem imageIdeal_eq (blocks : List (List I))
    (horder : blocks.flatten = List.ofFn d) :
    (OrbitProductImageDescent.morphism k K I G
      (OrbitProductPullback.blockProduct k K I G blocks
        (factor k K G p I d e x n))).ker =
      (SplitPinning.steinbergProduct e x n).left.ker := by
  rw [morphism_blockProduct_eq k K G p I d e x n blocks horder]
  exact Scheme.Hom.ker_comp_of_isIso _ _

/-- Under actual factor transport and within-block commutation the full image
ideal of the supplied Steinberg morphism descends over any Galois extension. -/
def definingIdealDescent [IsGalois k K]
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm I) (blocks : List (List I))
    (horder : blocks.flatten = List.ofFn d)
    (hblocks : ∀ (σ : K ≃ₐ[k] K) l, l ∈ blocks → (l.map (ρ σ)).Perm l)
    (hcomm : ∀ l, l ∈ blocks → (l.map (factor k K G p I d e x n)).Pairwise Commute)
    (hf : ∀ (σ : K ≃ₐ[k] K) i,
      Lie.affineMap G (PolynomialGalois.orbitAction k K I ρ σ)
          (factor k K G p I d e x n i) = factor k K G p I d e x n (ρ σ i)) :
    DefiningIdealDescent (pullback.fst G.X.hom (algebraBaseMap k K))
      (SplitPinning.steinbergProduct e x n).left.ker := by
  rw [← imageIdeal_eq k K G p I d e x n blocks horder]
  exact OrbitProductImageDescent.blockProductDefiningIdealDescent k K I G
    ρ blocks (factor k K G p I d e x n) hblocks hcomm hf

end Langlands.GroupScheme.SteinbergOrbitImageDescent
