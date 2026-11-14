import Langlands.GroupScheme.Rational.TorusVectorLinearizationProof
import Langlands.GroupScheme.Rational.VectorDiagonalAction
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Rational.TorusLinearization.AdditivePolynomials

/-! # Weights and polynomial maps in actual vector-line coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]

/-- Every action of a specified split torus on an actual vector line has
all-test vector coordinates of a single actual character. -/
theorem exists_weightVectorCoordinates_of_dimension_one
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {V : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (hV : IsVectorGroupOfDimension V 1)
    (a : AutomorphicAction T.toGrp V) :
    ∃ (χ : characterLattice T)
      (e : ∀ U : Over (Spec (CommRingCat.of k)),
        (U ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤))),
      IsWeightVectorCoordinates a χ e := by
  let : IsAffineHom V.X.hom := hV.isAffineHom
  obtain ⟨e, he⟩ := torusVectorActionLinearization k T.toGrp V 1 hT.isTorus hV a
  let c := he.homogeneousCoordinates hT
  have hn : c.dimension = 1 :=
    (show IsVectorGroupOfDimension V c.dimension from
      ⟨c.coordinates, c.naturality⟩).dimension_eq hV
  rcases c with ⟨n, e', weight, hnatur, hact⟩
  change n = 1 at hn
  subst n
  refine ⟨weight 0, e', hnatur, ?_⟩
  intro U t x
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  simpa only [hj, Pi.smul_apply, smul_eq_mul] using hact U t x 0

namespace VectorLine

variable {V W : GroupScheme (Spec (CommRingCat.of k))}
    (e : ∀ U : Over (Spec (CommRingCat.of k)),
      (U ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)))
    (d : ∀ U : Over (Spec (CommRingCat.of k)),
      (U ⟶ W.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)))
    (f : V ⟶ W)

/-- The universal point of an actual vector line with coordinate `X`. -/
def universalPoint : Lie.AffinePoints V k[X] :=
  (vectorAffineCoordinates e k[X]).symm (Multiplicative.ofAdd fun _ => X)

/-- The polynomial of an actual group homomorphism in the supplied natural
vector-line coordinates. -/
def polynomial : k[X] :=
  (vectorAffineCoordinates d k[X] (universalPoint e ≫ f.hom.hom)).toAdd 0

variable (he : IsNaturalVectorCoordinates e) (hd : IsNaturalVectorCoordinates d)

include he in
/-- Every affine point is obtained from the universal line point by evaluating
its coordinate. -/
theorem affineMap_universalPoint {B : Type u} [CommRing B] [Algebra k B]
    (x : Lie.AffinePoints V B) :
    Lie.affineMap V (Polynomial.aeval ((vectorAffineCoordinates e B x).toAdd 0))
      (universalPoint e) = x := by
  apply (vectorAffineCoordinates e B).injective
  apply Multiplicative.toAdd.injective
  rw [he.vectorAffineCoordinates_naturality]
  funext j
  simp only [universalPoint, MulEquiv.apply_symm_apply, toAdd_ofAdd, aeval_X]
  exact congrArg ((vectorAffineCoordinates e B x).toAdd) (Subsingleton.elim 0 j)

include he hd

/-- The chosen polynomial evaluates to the coordinate of the actual map over
every coefficient algebra, including nonreduced algebras. -/
theorem polynomial_aeval {B : Type u} [CommRing B] [Algebra k B]
    (x : Lie.AffinePoints V B) :
    aeval ((vectorAffineCoordinates e B x).toAdd 0) (polynomial e d f) =
      (vectorAffineCoordinates d B (x ≫ f.hom.hom)).toAdd 0 := by
  let φ : k[X] →ₐ[k] B := aeval ((vectorAffineCoordinates e B x).toAdd 0)
  have h := congrFun (hd.vectorAffineCoordinates_naturality φ
    (universalPoint e ≫ f.hom.hom)) 0
  have hx := affineMap_universalPoint e he x
  have hx' : Lie.affineMap W φ (universalPoint e ≫ f.hom.hom) =
      x ≫ f.hom.hom := by
    change (Lie.affineMap V φ (universalPoint e)) ≫ f.hom.hom = _
    rw [hx]
  rw [hx'] at h
  exact h.symm

/-- Actual homomorphisms of vector lines give additive polynomials. -/
theorem polynomial_isAddPoly : TorusLinearization.IsAddPoly₁ (polynomial e d f) := by
  intro B _ _ x y
  let p : Lie.AffinePoints V B :=
    (vectorAffineCoordinates e B).symm (Multiplicative.ofAdd fun _ => x)
  let q : Lie.AffinePoints V B :=
    (vectorAffineCoordinates e B).symm (Multiplicative.ofAdd fun _ => y)
  have hp := polynomial_aeval e d f he hd p
  have hq := polynomial_aeval e d f he hd q
  have hpq := polynomial_aeval e d f he hd (p * q)
  simp only [MonObj.mul_comp, map_mul, toAdd_mul, Pi.add_apply] at hpq
  simpa only [p, q, MulEquiv.apply_symm_apply, toAdd_ofAdd] using
    hpq.trans (congrArg₂ (· + ·) hp hq).symm

end VectorLine

end Langlands.GroupScheme.RelativeRoot
