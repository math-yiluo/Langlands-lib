import Langlands.Geometry.FormalGroup.PDivisibleRationalHom
import Langlands.Geometry.FormalGroup.PDivisibleSplitOrderAction

/-! # Cartier duality on actual rational tower morphisms -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TensorProduct AlgebraicGeometry

namespace Langlands.PDivisibleGroup

open GroupScheme.Cartier GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]
variable {G H J : PDivisibleGroup R p}
variable (hExact : FiniteCartierDualExactnessStatement.{u})

/-- Cartier duality preserves the natural p-adic scalar at every level. -/
theorem Hom.dual_padicAction (G : PDivisibleGroup R p) (a : ℤ_[p]) :
    Hom.dual (G.padicAction a).asHom hExact = ((G.dual hExact).padicAction a).asHom := by
  apply Hom.ext
  intro n
  have : IsFinite (G.inclusions.obj n).X.hom := (G.finiteLocallyFree n).1
  have : Flat (G.inclusions.obj n).X.hom := (G.finiteLocallyFree n).2.1
  have : LocallyOfFinitePresentation (G.inclusions.obj n).X.hom := (G.finiteLocallyFree n).2.2
  rw [Hom.dual_app, padicAction_app, padicAction_app]
  let L := schemeDualMapAdd (G := G.inclusions.obj n) (H := G.inclusions.obj n)
  change L (G.levelPadicAction n a).asHom = ((G.dual hExact).levelPadicAction n a).asHom
  rw [G.levelPadicAction_eq_nsmul_of_le (le_refl n),
    (G.dual hExact).levelPadicAction_eq_nsmul_of_le (le_refl n), map_nsmul]
  exact congrArg (((PadicInt.toZModPow n) a).val • ·) (schemeDualMap_id (G := G.inclusions.obj n))

/-- Actual integral Cartier duality is p-adic linear on the reversed Hom. -/
def Hom.dualLinear : (G ⟶ H) →ₗ[ℤ_[p]] (H.dual hExact ⟶ G.dual hExact) where
  toFun f := f.dual hExact
  map_add' f g := Hom.dual_add f g hExact
  map_smul' a f := by
    change Hom.dual (a • f) hExact = a • f.dual hExact
    rw [smul_eq_comp_padicAction, Hom.dual_comp, Hom.dual_padicAction, smul_eq_comp_padicAction]
    exact (H.dual hExact).padicAction_naturality (f.dual hExact) a

namespace RationalHom

/-- The Cartier dual on actual rationalized Hom. -/
def dualMap : RationalHom G H →ₗ[ℚ_[p]] RationalHom (H.dual hExact) (G.dual hExact) :=
  (Hom.dualLinear hExact).baseChange ℚ_[p]

@[simp] theorem dualMap_tmul (a : ℚ_[p]) (f : G ⟶ H) :
    dualMap hExact (a ⊗ₜ[ℤ_[p]] f) = a ⊗ₜ[ℤ_[p]] (f.dual hExact) := rfl

@[simp] theorem dualMap_ofHom (f : G ⟶ H) :
    dualMap hExact (ofHom f) = ofHom (f.dual hExact) := rfl

@[simp] theorem dualMap_id (G : PDivisibleGroup R p) :
    dualMap hExact (id G) = id (G.dual hExact) := by
  change ofHom ((𝟙 G : G ⟶ G).dual hExact) = ofHom (𝟙 (G.dual hExact))
  rw [Hom.dual_id]

@[simp] theorem dualMap_comp (f : RationalHom G H) (g : RationalHom H J) :
    dualMap hExact (comp f g) = comp (dualMap hExact g) (dualMap hExact f) := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp only [add_comp, comp_add, map_add, hf, hf']
  | tmul a f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp only [comp_add, add_comp, map_add, hg, hg']
    | tmul b g => simp only [comp_tmul, dualMap_tmul, Hom.dual_comp, mul_comm a b]

end RationalHom

/-- Cartier duality reverses an isomorphism of the actual towers up to isogeny. -/
def QuasiIsogeny.dual (e : QuasiIsogeny G H) : QuasiIsogeny (H.dual hExact) (G.dual hExact) where
  hom := RationalHom.dualMap hExact e.hom
  inv := RationalHom.dualMap hExact e.inv
  hom_inv_id := by
    have h : RationalHom.comp e.inv e.hom = RationalHom.id H := e.inv_hom_id
    change RationalHom.comp (RationalHom.dualMap hExact e.hom)
      (RationalHom.dualMap hExact e.inv) = RationalHom.id (H.dual hExact)
    rw [← RationalHom.dualMap_comp, h, RationalHom.dualMap_id]
  inv_hom_id := by
    have h : RationalHom.comp e.hom e.inv = RationalHom.id G := e.hom_inv_id
    change RationalHom.comp (RationalHom.dualMap hExact e.inv)
      (RationalHom.dualMap hExact e.hom) = RationalHom.id (G.dual hExact)
    rw [← RationalHom.dualMap_comp, h, RationalHom.dualMap_id]

end Langlands.PDivisibleGroup
