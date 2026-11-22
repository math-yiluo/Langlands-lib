import Langlands.Geometry.FormalGroup.PDivisibleSplitRigidifierTransport
import Langlands.Geometry.FormalGroup.PDivisibleSplitPairingBaseChange

/-! # Projection of the rigidifier on the original full split special fibres -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory

namespace Langlands.PDivisibleGroup

open GroupScheme.Cartier RationalHom

section Projection

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {p : ℕ} [Fact p.Prime]
variable (hExact : FiniteCartierDualExactnessStatement.{u})

local notation "F" => baseChangeFunctor R S p

/-- The canonical rational pullback comparison preserves the primal projection. -/
theorem rationalSplitBaseChangeIso_hom_fst (G : PDivisibleGroup (CommRingCat.of R) p) :
    comp (rationalSplitBaseChangeIso (S := S) hExact G).hom
        (ofHom (prodFst ((F).obj G) (((F).obj G).dual hExact))) =
      ofHom ((F).map (prodFst G (G.dual hExact))) := by
  let e := (baseChangeSplitIso (S := S) G hExact).hom
  let f := prodFst ((F).obj G) (((F).obj G).dual hExact)
  change comp (ofHom e) (ofHom f) = _
  rw [← ofHom_comp e f]
  exact congrArg (fun z : ((F).obj (G.splitWithDual hExact)) ⟶ ((F).obj G) => ofHom z)
    (baseChangeSplitIso_hom_fst (S := S) G hExact)

end Projection

private theorem conjugation_projection {p : ℕ} [Fact p.Prime]
    {R : CommRingCat.{u}} {G H J K P Q : PDivisibleGroup R p}
    (i : QuasiIsogeny G H) (j : QuasiIsogeny J K) (r : RationalHom H K)
    (p₁ : RationalHom G P) (p₂ : RationalHom J Q)
    (p₁' : RationalHom H P) (p₂' : RationalHom K Q) (q : RationalHom P Q)
    (hi : comp i.hom p₁' = p₁) (hj : comp j.hom p₂' = p₂)
    (hr : comp r p₂' = comp p₁' q) :
    comp (comp i.hom (comp r j.inv)) p₂ = comp p₁ q := by
  have hj' : comp j.inv j.hom = RationalHom.id K := j.inv_hom_id
  rw [← hj, comp_assoc i.hom, comp_assoc r, ← comp_assoc j.inv, hj', id_comp, hr,
    ← comp_assoc i.hom, hi]

variable {R₁ R₂ S : Type u} [CommRing R₁] [CommRing R₂] [CommRing S]
  [Algebra R₁ S] [Algebra R₂ S]
variable {p : ℕ} [Fact p.Prime]
variable {G : PDivisibleGroup (CommRingCat.of R₁) p} {H : PDivisibleGroup (CommRingCat.of R₂) p}
variable (hExact : FiniteCartierDualExactnessStatement.{u})

local notation "F₁" => baseChangeFunctor R₁ S p
local notation "F₂" => baseChangeFunctor R₂ S p

/-- The projection square for the rigidifier transported to the original full split pullbacks. -/
theorem splitQuasiIsogenyOnBaseChange_hom_fst
    (q : QuasiIsogeny ((F₁).obj G) ((F₂).obj H)) (c : ℚ_[p]ˣ) :
    comp (splitQuasiIsogenyOnBaseChange (G₁ := G) (G₂ := H) (S := S) hExact q c).hom
        (ofHom ((F₂).map (prodFst H (H.dual hExact)))) =
      comp (ofHom ((F₁).map (prodFst G (G.dual hExact)))) q.hom := by
  let i := rationalSplitBaseChangeIso (S := S) hExact G
  let j := rationalSplitBaseChangeIso (S := S) hExact H
  let r := (splitRigidifier hExact q c).hom
  let x := ofHom ((F₁).map (prodFst G (G.dual hExact)))
  let y := ofHom ((F₂).map (prodFst H (H.dual hExact)))
  let x' := ofHom (prodFst ((F₁).obj G) (((F₁).obj G).dual hExact))
  let y' := ofHom (prodFst ((F₂).obj H) (((F₂).obj H).dual hExact))
  have hi := rationalSplitBaseChangeIso_hom_fst (S := S) hExact G
  have hj := rationalSplitBaseChangeIso_hom_fst (S := S) hExact H
  have hr := prodMap_fst q.hom ((c : ℚ_[p]) • dualMap hExact q.inv)
  change comp (comp i.hom (comp r j.inv)) y = comp x q.hom
  exact conjugation_projection i j r x y x' y' q.hom hi hj hr

/-- The primal block of a rational morphism between two pulled-back split towers. -/
def pullbackPrimalBlock
    (r : RationalHom ((F₁).obj (G.splitWithDual hExact)) ((F₂).obj (H.splitWithDual hExact))) :
    RationalHom ((F₁).obj G) ((F₂).obj H) :=
    comp (ofHom ((F₁).map (prodInl G (G.dual hExact))))
      (comp r (ofHom ((F₂).map (prodFst H (H.dual hExact)))))

/-- Projecting the transported split rigidifier recovers the original primal map. -/
theorem splitQuasiIsogenyOnBaseChange_primal
    (q : QuasiIsogeny ((F₁).obj G) ((F₂).obj H)) (c : ℚ_[p]ˣ) :
    pullbackPrimalBlock (G := G) (H := H) (S := S) hExact
      (splitQuasiIsogenyOnBaseChange (G₁ := G) (G₂ := H) (S := S) hExact q c).hom = q.hom := by
  let f := prodInl G (G.dual hExact)
  let g := prodFst G (G.dual hExact)
  have h : (F₁).map f ≫ (F₁).map g = 𝟙 ((F₁).obj G) := by
    rw [← (F₁).map_comp, prodInl_fst, (F₁).map_id]
  rw [pullbackPrimalBlock, splitQuasiIsogenyOnBaseChange_hom_fst, ← comp_assoc, ← ofHom_comp, h, ofHom_id, id_comp]

end Langlands.PDivisibleGroup
