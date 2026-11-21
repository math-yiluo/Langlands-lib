import Langlands.Geometry.FormalGroup.PDivisibleGroupMorphisms
import Langlands.Geometry.FormalGroup.PDivisibleSplitPolarization
import Mathlib.Algebra.Ring.Prod

/-! # The exchange-involutive order action on a split p-divisible group -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.CommGroupScheme

variable {S : Scheme.{u}} {G H G' H' K : CommGroupScheme S}

/-- The two actual projections determine a group homomorphism into a product. -/
theorem prod_hom_ext {f g : K ⟶ prod G H} (hf : f ≫ prodFst G H = g ≫ prodFst G H)
    (hg : f ≫ prodSnd G H = g ≫ prodSnd G H) : f = g := by
  change Additive.ofMul f.toMul = Additive.ofMul g.toMul
  exact congrArg Additive.ofMul (CartesianMonoidalCategory.hom_ext f.toMul g.toMul
    (congrArg Additive.toMul hf) (congrArg Additive.toMul hg))

@[simp] theorem prodMap_zero : prodMap (0 : G ⟶ G') (0 : H ⟶ H') = 0 := by
  apply prod_hom_ext <;> simp

@[simp] theorem prodMap_add (f f' : G ⟶ G') (g g' : H ⟶ H') :
    prodMap (f + f') (g + g') = prodMap f g + prodMap f' g' := by
  apply prod_hom_ext <;> simp

end Langlands.CommGroupScheme

namespace Langlands.PDivisibleGroup

open CommGroupScheme GroupScheme GroupScheme.Cartier GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]

local instance actionLevelFinite (G : PDivisibleGroup R p) (n : ℕ) : IsFinite (G.inclusions.obj n).X.hom :=
  (G.finiteLocallyFree n).1
local instance actionLevelFlat (G : PDivisibleGroup R p) (n : ℕ) : Flat (G.inclusions.obj n).X.hom :=
  (G.finiteLocallyFree n).2.1
local instance actionLevelFinitePresentation (G : PDivisibleGroup R p) (n : ℕ) :
    LocallyOfFinitePresentation (G.inclusions.obj n).X.hom := (G.finiteLocallyFree n).2.2

namespace Hom

variable {G H J G' H' J' : PDivisibleGroup R p}

/-- Dualize the actual morphisms at every level and interchange the two adjoint arrows. -/
def dual (f : G ⟶ H) (hExact : FiniteCartierDualExactnessStatement.{u}) : H.dual hExact ⟶ G.dual hExact :=
  ofComponents (fun n => schemeDualMap (f.app n)) (by
    intro m n i
    change schemeDualMap (H.transfer i) ≫ schemeDualMap (f.app n) =
      schemeDualMap (f.app m) ≫ schemeDualMap (G.transfer i)
    rw [← schemeDualMap_comp, ← schemeDualMap_comp, f.transfer_naturality]) (by
    intro m n i
    change schemeDualMap (H.inclusions.map i) ≫ schemeDualMap (f.app m) =
      schemeDualMap (f.app n) ≫ schemeDualMap (G.inclusions.map i)
    rw [← schemeDualMap_comp, ← schemeDualMap_comp, f.naturality])

@[simp] theorem dual_app (f : G ⟶ H) (hExact : FiniteCartierDualExactnessStatement.{u}) (n : ℕ) :
    (f.dual hExact).app n = schemeDualMap (f.app n) := rfl

@[simp] theorem dual_id (G : PDivisibleGroup R p) (hExact : FiniteCartierDualExactnessStatement.{u}) :
    Hom.dual (𝟙 G) hExact = 𝟙 (G.dual hExact) := by
  apply Hom.ext
  intro n
  exact schemeDualMap_id (G := G.inclusions.obj n)

@[simp] theorem dual_comp (f : G ⟶ H) (g : H ⟶ J) (hExact : FiniteCartierDualExactnessStatement.{u}) :
    Hom.dual (f ≫ g) hExact = Hom.dual g hExact ≫ Hom.dual f hExact := by
  apply Hom.ext
  intro n
  exact schemeDualMap_comp (f.app n) (g.app n)

@[simp] theorem dual_zero (hExact : FiniteCartierDualExactnessStatement.{u}) :
    Hom.dual (0 : G ⟶ H) hExact = 0 := by
  apply Hom.ext
  intro n
  exact (schemeDualMapAdd (G := G.inclusions.obj n) (H := H.inclusions.obj n)).map_zero

@[simp] theorem dual_add (f g : G ⟶ H) (hExact : FiniteCartierDualExactnessStatement.{u}) :
    Hom.dual (f + g) hExact = Hom.dual f hExact + Hom.dual g hExact := by
  apply Hom.ext
  intro n
  exact schemeDualMap_add (f.app n) (g.app n)

/-- Two morphisms give the componentwise map between the actual product towers. -/
def prodMap (f : G ⟶ G') (g : H ⟶ H') : G.prod H ⟶ G'.prod H' :=
  ofComponents (fun n => CommGroupScheme.prodMap (f.app n) (g.app n)) (by
    intro m n i
    change CommGroupScheme.prodMap (G.inclusions.map i) (H.inclusions.map i) ≫
      CommGroupScheme.prodMap (f.app n) (g.app n) =
      CommGroupScheme.prodMap (f.app m) (g.app m) ≫
        CommGroupScheme.prodMap (G'.inclusions.map i) (H'.inclusions.map i)
    rw [← CommGroupScheme.prodMap_comp, ← CommGroupScheme.prodMap_comp, f.naturality, g.naturality]) (by
    intro m n i
    change CommGroupScheme.prodMap (G.transfer i) (H.transfer i) ≫ CommGroupScheme.prodMap (f.app m) (g.app m) =
      CommGroupScheme.prodMap (f.app n) (g.app n) ≫ CommGroupScheme.prodMap (G'.transfer i) (H'.transfer i)
    rw [← CommGroupScheme.prodMap_comp, ← CommGroupScheme.prodMap_comp, f.transfer_naturality,
      g.transfer_naturality])

@[simp] theorem prodMap_app (f : G ⟶ G') (g : H ⟶ H') (n : ℕ) :
    (prodMap f g).app n = CommGroupScheme.prodMap (f.app n) (g.app n) := rfl

@[simp] theorem prodMap_id (G H : PDivisibleGroup R p) : prodMap (𝟙 G) (𝟙 H) = 𝟙 (G.prod H) := by
  apply Hom.ext
  intro n
  exact CommGroupScheme.prodMap_id (G.inclusions.obj n) (H.inclusions.obj n)

@[simp] theorem prodMap_comp (f : G ⟶ G') (g : H ⟶ H') (f' : G' ⟶ J) (g' : H' ⟶ J') :
    prodMap (f ≫ f') (g ≫ g') = prodMap f g ≫ prodMap f' g' := by
  apply Hom.ext
  intro n
  exact CommGroupScheme.prodMap_comp (f.app n) (g.app n) (f'.app n) (g'.app n)

@[simp] theorem prodMap_zero : prodMap (0 : G ⟶ G') (0 : H ⟶ H') = 0 := by
  apply Hom.ext
  intro n
  exact CommGroupScheme.prodMap_zero

@[simp] theorem prodMap_add (f f' : G ⟶ G') (g g' : H ⟶ H') :
    prodMap (f + f') (g + g') = prodMap f g + prodMap f' g' := by
  apply Hom.ext
  intro n
  exact CommGroupScheme.prodMap_add (f.app n) (f'.app n) (g.app n) (g'.app n)

end Hom

/-- Cartier duality reverses the endomorphism ring of a p-divisible group. -/
def dualEnd (G : PDivisibleGroup R p) (hExact : FiniteCartierDualExactnessStatement.{u}) :
    (End G)ᵐᵒᵖ →+* End (G.dual hExact) where
  toFun f := Hom.dual f.unop hExact
  map_one' := Hom.dual_id G hExact
  map_zero' := Hom.dual_zero hExact
  map_add' f g := Hom.dual_add f.unop g.unop hExact
  map_mul' f g := Hom.dual_comp f.unop g.unop hExact

/-- A pair of endomorphisms acts componentwise on the actual product tower. -/
def prodEnd (G H : PDivisibleGroup R p) : End G × End H →+* End (G.prod H) where
  toFun f := Hom.prodMap f.1 f.2
  map_one' := Hom.prodMap_id G H
  map_zero' := Hom.prodMap_zero
  map_add' f g := Hom.prodMap_add f.1 g.1 f.2 g.2
  map_mul' f g := Hom.prodMap_comp g.1 g.2 f.1 f.2

/-- The ordinary order acts on the primal tower and its opposite acts by duality on
the dual tower. -/
def splitOrderAction {O : Type w} [Ring O] {G : PDivisibleGroup R p} (action : O →+* End G)
    (hExact : FiniteCartierDualExactnessStatement.{u}) : Oᵐᵒᵖ × O →+* End (G.splitWithDual hExact) :=
  (prodEnd G (G.dual hExact)).comp ((action.comp (RingHom.snd Oᵐᵒᵖ O)).prod
    ((G.dualEnd hExact).comp (action.op.comp (RingHom.fst Oᵐᵒᵖ O))))

/-- The action at a finite level is the actual primal map and the actual dual map
attached to the opposite component. -/
theorem splitOrderAction_app {O : Type w} [Ring O] {G : PDivisibleGroup R p} (action : O →+* End G)
    (hExact : FiniteCartierDualExactnessStatement.{u}) (a : Oᵐᵒᵖ × O) (n : ℕ) :
    Hom.app (splitOrderAction action hExact a) n =
      productWithDualMap (Hom.app (action a.2) n) (schemeDualMap (Hom.app (action a.1.unop) n)) := rfl

/-- Evaluation of the finite-level Cartier character of a polarized point. -/
def PrincipalPolarization.evaluate {G : PDivisibleGroup R p} (polarization : PrincipalPolarization G)
    (n : ℕ) (T : Over (Spec R)) (x : T ⟶ (G.inclusions.obj n).X) :
    (T ⟶ (G.inclusions.obj n).X) →* (T ⟶ (Gm (Spec R)).X) :=
  characterEvaluation ((polarization.perfect n).hom.app (op T) (Additive.ofMul x))

/-- The polarization on the actual split tower evaluates by the original
alternating pairing on its finite factors. -/
theorem splitPrincipalPolarization_evaluate (G : PDivisibleGroup R p)
    (hExact : FiniteCartierDualExactnessStatement.{u}) (n : ℕ) (T : Over (Spec R))
    (x y : T ⟶ ((G.splitWithDual hExact).inclusions.obj n).X) :
    (G.splitPrincipalPolarization hExact).evaluate n T x y =
      productWithDualPairing (G.inclusions.obj n) T x y :=
  splitPairingCharacters_evaluation (G.inclusions.obj n) T x y

/-- The polarization interchanges the two order factors in the adjoint action. -/
theorem splitOrderAction_adjoint {O : Type w} [Ring O] {G : PDivisibleGroup R p}
    (action : O →+* End G) (hExact : FiniteCartierDualExactnessStatement.{u})
    (a : Oᵐᵒᵖ × O) (n : ℕ) (T : Over (Spec R))
    (x y : T ⟶ ((G.splitWithDual hExact).inclusions.obj n).X) :
    let s := splitOrderAction action hExact
    let b : Oᵐᵒᵖ × O := (MulOpposite.op a.2, a.1.unop)
    (G.splitPrincipalPolarization hExact).evaluate n T (x ≫ (Hom.app (s a) n).toMul.hom.hom) y =
      (G.splitPrincipalPolarization hExact).evaluate n T x (y ≫ (Hom.app (s b) n).toMul.hom.hom) := by
  dsimp only
  rw [splitPrincipalPolarization_evaluate, splitPrincipalPolarization_evaluate,
    splitOrderAction_app, splitOrderAction_app]
  exact productWithDualPairing_adjoint (G := G.inclusions.obj n) (H := G.inclusions.obj n)
    (Hom.app (action a.2) n) (Hom.app (action a.1.unop) n) T x y

end Langlands.PDivisibleGroup
