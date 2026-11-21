import Langlands.GroupScheme.Cartier.FiniteDualNaturalPairing
import Langlands.GroupScheme.Products

/-! # The alternating pairing on the actual product with a finite dual -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}}
variable (G : CommGroupScheme (Spec R)) [IsFinite G.X.hom] [Flat G.X.hom]
  [LocallyOfFinitePresentation G.X.hom]

/-- The full binary product with the actual finite dual spectrum. -/
def productWithDual : CommGroupScheme (Spec R) :=
  { G.toGrp ⊗ (schemeDual G).toGrp with
    comm := inferInstanceAs (IsCommMonObj (G.X ⊗ (schemeDual G).X)) }

/-- Points of the product are pairs of actual scheme points. -/
def productWithDualPoints (T : Over (Spec R)) :
    (T ⟶ (productWithDual G).X) ≃* (T ⟶ G.X) × (T ⟶ (schemeDual G).X) :=
  productPointsEquiv G.toGrp (schemeDual G).toGrp T

/-- The tautological alternating evaluation pairing on the product. -/
def productWithDualPairing (T : Over (Spec R)) (x : T ⟶ (productWithDual G).X) :
    (T ⟶ (productWithDual G).X) →* (T ⟶ (Gm (Spec R)).X) := by
  let e := productWithDualPoints G T
  let a := e x
  let u : (T ⟶ (schemeDual G).X) →* (T ⟶ (Gm (Spec R)).X) :=
    MonoidHom.mk' (fun y => finiteSchemePairing G T y a.1)
      (fun y z => finiteSchemePairing_mul G T y z a.1)
  exact u.comp ((MonoidHom.snd _ _).comp e.toMonoidHom) *
    ((finiteSchemePairing G T a.2).comp ((MonoidHom.fst _ _).comp e.toMonoidHom))⁻¹

@[simp]
theorem productWithDualPairing_apply (T : Over (Spec R)) (x y : T ⟶ (productWithDual G).X) :
    let e := productWithDualPoints G T
    productWithDualPairing G T x y =
      finiteSchemePairing G T (e y).2 (e x).1 * (finiteSchemePairing G T (e x).2 (e y).1)⁻¹ :=
  rfl

@[simp]
theorem productWithDualPairing_self (T : Over (Spec R)) (x : T ⟶ (productWithDual G).X) :
    productWithDualPairing G T x x = 1 := by
  rw [productWithDualPairing_apply]
  simp

/-- The actual product pairing interchanges its arguments by inversion. -/
theorem productWithDualPairing_swap (T : Over (Spec R)) (x y : T ⟶ (productWithDual G).X) :
    productWithDualPairing G T y x = (productWithDualPairing G T x y)⁻¹ := by
  rw [productWithDualPairing_apply, productWithDualPairing_apply]
  simp

/-- The pairing is multiplicative in the first point as well. -/
theorem productWithDualPairing_mul (T : Over (Spec R)) (x y z : T ⟶ (productWithDual G).X) :
    productWithDualPairing G T (x * y) z =
      productWithDualPairing G T x z * productWithDualPairing G T y z := by
  rw [productWithDualPairing_swap G T z (x * y), map_mul, mul_inv_rev,
    ← productWithDualPairing_swap G T z y, ← productWithDualPairing_swap G T z x, mul_comm]

/-- The product pairing is compatible with all coefficient tests. -/
theorem productWithDualPairing_naturality {T U : Over (Spec R)} (c : U ⟶ T)
    (x y : T ⟶ (productWithDual G).X) :
    productWithDualPairing G U (c ≫ x) (c ≫ y) = c ≫ productWithDualPairing G T x y := by
  let e := productWithDualPoints G T
  have hx : productWithDualPoints G U (c ≫ x) = (c ≫ (e x).1, c ≫ (e x).2) :=
    productPointsEquiv_naturality G.toGrp (schemeDual G).toGrp c x
  have hy : productWithDualPoints G U (c ≫ y) = (c ≫ (e y).1, c ≫ (e y).2) :=
    productPointsEquiv_naturality G.toGrp (schemeDual G).toGrp c y
  rw [productWithDualPairing_apply, productWithDualPairing_apply, hx, hy]
  simp only [finiteSchemePairing_naturality, MonObj.comp_mul, GrpObj.comp_inv]
  rfl

variable {G} {H : CommGroupScheme (Spec R)} [IsFinite H.X.hom] [Flat H.X.hom]
  [LocallyOfFinitePresentation H.X.hom]

/-- An actual group scheme map on each factor induces an actual product map. -/
def productWithDualMap (f : G ⟶ H) (g : schemeDual G ⟶ schemeDual H) :
    productWithDual G ⟶ productWithDual H :=
  Additive.ofMul (f.toMul ⊗ₘ g.toMul)

@[simp]
theorem productWithDualMap_id : productWithDualMap (𝟙 G) (𝟙 (schemeDual G)) = 𝟙 _ := by
  change Additive.ofMul ((𝟙 G.toGrp) ⊗ₘ (𝟙 (schemeDual G).toGrp)) =
    Additive.ofMul (𝟙 (productWithDual G).toGrp)
  simp
  rfl

variable {J : CommGroupScheme (Spec R)} [IsFinite J.X.hom] [Flat J.X.hom]
  [LocallyOfFinitePresentation J.X.hom]

@[simp]
theorem productWithDualMap_comp (f : G ⟶ H) (f' : H ⟶ J)
    (g : schemeDual G ⟶ schemeDual H) (g' : schemeDual H ⟶ schemeDual J) :
    productWithDualMap (f ≫ f') (g ≫ g') = productWithDualMap f g ≫ productWithDualMap f' g' :=
  congrArg Additive.ofMul (tensorHom_comp_tensorHom f.toMul g.toMul f'.toMul g'.toMul).symm

/-- The actual product map acts on the two component points by the specified maps. -/
theorem productWithDualPoints_map (f : G ⟶ H) (g : schemeDual G ⟶ schemeDual H)
    (T : Over (Spec R)) (x : T ⟶ (productWithDual G).X) :
    productWithDualPoints H T (x ≫ (productWithDualMap f g).toMul.hom.hom) =
      ((productWithDualPoints G T x).1 ≫ f.toMul.hom.hom,
       (productWithDualPoints G T x).2 ≫ g.toMul.hom.hom) := by
  apply Prod.ext
  · change (x ≫ (f.toMul.hom.hom ⊗ₘ g.toMul.hom.hom)) ≫ fst _ _ =
      (x ≫ fst _ _) ≫ f.toMul.hom.hom
    simp only [Category.assoc, tensorHom_fst]
  · change (x ≫ (f.toMul.hom.hom ⊗ₘ g.toMul.hom.hom)) ≫ snd _ _ =
      (x ≫ snd _ _) ≫ g.toMul.hom.hom
    simp only [Category.assoc, tensorHom_snd]

/-- The two product maps with interchanged dual components are adjoint for the alternating pairings. -/
theorem productWithDualPairing_adjoint (f : G ⟶ H) (g : H ⟶ G) (T : Over (Spec R))
    (x : T ⟶ (productWithDual G).X) (y : T ⟶ (productWithDual H).X) :
    productWithDualPairing H T (x ≫ (productWithDualMap f (schemeDualMap g)).toMul.hom.hom) y =
      productWithDualPairing G T x (y ≫ (productWithDualMap g (schemeDualMap f)).toMul.hom.hom) := by
  rw [productWithDualPairing_apply, productWithDualPairing_apply, productWithDualPoints_map,
    productWithDualPoints_map]
  exact congrArg₂ (fun a b : T ⟶ (Gm (Spec R)).X => a * b⁻¹)
    (finiteSchemePairing_dualMap f T (productWithDualPoints G T x).1 (productWithDualPoints H T y).2)
    (finiteSchemePairing_dualMap g T (productWithDualPoints H T y).1 (productWithDualPoints G T x).2).symm

end Langlands.GroupScheme.Cartier.FiniteDual
