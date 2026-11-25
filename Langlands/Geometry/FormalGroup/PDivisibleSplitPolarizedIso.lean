import Langlands.Geometry.FormalGroup.HarrisSplitPDivisiblePoint
import Langlands.Geometry.FormalGroup.PDivisibleRationalInjectivity
import Langlands.GroupScheme.Cartier.SplitFiniteSimilitude

/-! # Actual polarized isomorphisms of split towers -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.PDivisibleGroup

open GroupScheme.Cartier GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime] {G H J : PDivisibleGroup R p}
variable (hExact : FiniteCartierDualExactnessStatement.{u})

/-- Inverse Cartier dual of an integral tower isomorphism. -/
def inverseDualIso (e : G ≅ H) : G.dual hExact ≅ H.dual hExact where
  hom := e.inv.dual hExact
  inv := e.hom.dual hExact
  hom_inv_id := by rw [← Hom.dual_comp, e.hom_inv_id, Hom.dual_id]
  inv_hom_id := by rw [← Hom.dual_comp, e.inv_hom_id, Hom.dual_id]

/-- An integral primal isomorphism and its inverse dual give the split isomorphism. -/
def splitPolarizedIso (e : G ≅ H) : G.splitWithDual hExact ≅ H.splitWithDual hExact :=
  isoProdMap e (inverseDualIso hExact e)

@[simp] theorem splitPolarizedIso_refl (G : PDivisibleGroup R p) :
    splitPolarizedIso hExact (Iso.refl G) = Iso.refl (G.splitWithDual hExact) := by
  apply Iso.ext
  change Hom.prodMap (𝟙 G) (Hom.dual (𝟙 G) hExact) = _
  rw [Hom.dual_id, Hom.prodMap_id]
  rfl

@[simp] theorem splitPolarizedIso_trans (e : G ≅ H) (f : H ≅ J) :
    splitPolarizedIso hExact (e.trans f) = (splitPolarizedIso hExact e).trans (splitPolarizedIso hExact f) := by
  apply Iso.ext
  change Hom.prodMap (e.hom ≫ f.hom) ((f.inv ≫ e.inv).dual hExact) =
    Hom.prodMap e.hom (e.inv.dual hExact) ≫ Hom.prodMap f.hom (f.inv.dual hExact)
  rw [Hom.dual_comp, Hom.prodMap_comp]

/-- The rational map of the split isomorphism has multiplier one. -/
theorem splitPolarizedIso_ofHom (e : G ≅ H) :
    RationalHom.ofHom (splitPolarizedIso hExact e).hom =
      (splitRigidifier hExact (RationalCategory.inclusion.mapIso e) 1).hom := by
  change RationalHom.ofHom (Hom.prodMap e.hom (e.inv.dual hExact)) =
    RationalHom.prodMap (RationalHom.ofHom e.hom)
      ((↑(1 : ℚ_[p]ˣ) : ℚ_[p]) • RationalHom.dualMap hExact (RationalHom.ofHom e.inv))
  rw [Units.val_one, one_smul, RationalHom.dualMap_ofHom, RationalHom.prodMap_ofHom]

/-- An order-linear primal isomorphism gives an order-linear polarized isomorphism. -/
theorem splitPolarizedIso_order {A : Type v} [Ring A] {a : A →+* End G} {b : A →+* End H}
    (e : G ≅ H) (he : ∀ t, (a t).asHom ≫ e.hom = e.hom ≫ (b t).asHom) (t : Aᵐᵒᵖ × A) :
    (splitOrderAction a hExact t).asHom ≫ (splitPolarizedIso hExact e).hom =
      (splitPolarizedIso hExact e).hom ≫ (splitOrderAction b hExact t).asHom := by
  apply RationalHom.ofHom_injective
  rw [RationalHom.ofHom_comp, RationalHom.ofHom_comp, splitPolarizedIso_ofHom]
  exact (splitOrderRigidifier hExact (OrderQuasiIsogeny.ofIso (a := a) (b := b) e he) 1).commutes t

local instance splitIsoLevelFinite (X : PDivisibleGroup R p) (n : ℕ) : IsFinite (X.inclusions.obj n).X.hom :=
  (X.finiteLocallyFree n).1
local instance splitIsoLevelFlat (X : PDivisibleGroup R p) (n : ℕ) : Flat (X.inclusions.obj n).X.hom :=
  (X.finiteLocallyFree n).2.1
local instance splitIsoLevelFP (X : PDivisibleGroup R p) (n : ℕ) : LocallyOfFinitePresentation (X.inclusions.obj n).X.hom :=
  (X.finiteLocallyFree n).2.2

/-- The split isomorphism is a strict isometry on all actual finite levels. -/
theorem splitPolarizedIso_pairing (e : G ≅ H) (n : ℕ) (T : Over (Spec R))
    (x y : T ⟶ ((G.splitWithDual hExact).inclusions.obj n).X) :
    let f := ((splitPolarizedIso hExact e).hom.app n).toMul.hom.hom
    (H.splitPrincipalPolarization hExact).evaluate n T (x ≫ f) (y ≫ f) =
      (G.splitPrincipalPolarization hExact).evaluate n T x y := by
  let f := e.hom.app n
  let g := (e.inv.dual hExact).app n
  have he : e.inv.dual hExact ≫ e.hom.dual hExact = 𝟙 (G.dual hExact) :=
    (inverseDualIso hExact e).hom_inv_id
  have hn : g ≫ schemeDualMap f = 1 • 𝟙 (schemeDual (G.inclusions.obj n)) := by
    rw [one_nsmul]
    exact congrArg (fun m : G.dual hExact ⟶ G.dual hExact => m.app n) he
  have h := productWithDualPairing_similitude f g 1 hn T x y
  rw [pow_one] at h
  dsimp only
  rw [splitPrincipalPolarization_evaluate, splitPrincipalPolarization_evaluate]
  exact h

end Langlands.PDivisibleGroup

namespace Langlands.PDivisibleGroup

open GroupScheme.Cartier

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {p : ℕ} [Fact p.Prime] {G H : PDivisibleGroup (CommRingCat.of R) p}
variable (hExact : FiniteCartierDualExactnessStatement.{u})

local notation "F" => baseChangeFunctor R S p

/-- The split isomorphism commutes with the actual product and dual pullback comparisons. -/
theorem baseChangeSplitIso_splitPolarizedIso (e : G ≅ H) :
    (F).map (splitPolarizedIso hExact e).hom ≫ (baseChangeSplitIso (S := S) H hExact).hom =
      (baseChangeSplitIso (S := S) G hExact).hom ≫ (splitPolarizedIso hExact ((F).mapIso e)).hom := by
  let x := e.hom
  let y := e.inv
  let tG := (baseChangeProdIso (S := S) G (G.dual hExact)).hom
  let tH := (baseChangeProdIso (S := S) H (H.dual hExact)).hom
  let dG := (baseChangeDualIso (S := S) G hExact).hom
  let dH := (baseChangeDualIso (S := S) H hExact).hom
  change (F).map (Hom.prodMap x (y.dual hExact)) ≫ (tH ≫ Hom.prodMap (𝟙 ((F).obj H)) dH) =
    (tG ≫ Hom.prodMap (𝟙 ((F).obj G)) dG) ≫ Hom.prodMap ((F).map x) (((F).map y).dual hExact)
  rw [← Category.assoc, baseChangeProdIso_naturality, Category.assoc, Category.assoc,
    ← Hom.prodMap_comp, ← Hom.prodMap_comp, Category.comp_id, Category.id_comp,
    baseChangeDualIso_naturality]

end Langlands.PDivisibleGroup
