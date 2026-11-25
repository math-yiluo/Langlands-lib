import Langlands.Geometry.FormalGroup.PDivisibleRationalProductBaseChange
import Langlands.Geometry.FormalGroup.PDivisibleRationalSplitBaseChange

/-! # Pullback of the rational split rigidifier -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace Langlands.PDivisibleGroup

open RationalHom GroupScheme.Cartier

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {p : ℕ} [Fact p.Prime]
variable {G G' : PDivisibleGroup (CommRingCat.of R) p}

local notation "F" => baseChangeFunctor R S p

private theorem baseChangeProdMap_square {H H' : PDivisibleGroup (CommRingCat.of R) p}
    {C C' : PDivisibleGroup (CommRingCat.of S) p}
    (f : RationalHom G G') (g : RationalHom H H') (h : RationalHom C C')
    (d : RationalHom (H.baseChange (S := S)) C) (d' : RationalHom (H'.baseChange (S := S)) C')
    (i : RationalHom ((G.prod H).baseChange (S := S)) ((G.baseChange (S := S)).prod C))
    (i' : RationalHom ((G'.prod H').baseChange (S := S)) ((G'.baseChange (S := S)).prod C'))
    (dual : comp (baseChangeMap (S := S) g) d' = comp d h)
    (source : i = comp (baseChangeRationalProdIso (S := S) G H).hom
        (prodMap (id (G.baseChange (S := S))) d))
    (target : i' = comp (baseChangeRationalProdIso (S := S) G' H').hom
        (prodMap (id (G'.baseChange (S := S))) d')) :
    comp (baseChangeMap (S := S) (prodMap f g)) i' =
      comp i (prodMap (baseChangeMap (S := S) f) h) := by
  let b := (baseChangeRationalProdIso (S := S) G H).hom
  let b' := (baseChangeRationalProdIso (S := S) G' H').hom
  let t := baseChangeMap (S := S) (prodMap f g)
  have ht : comp t b' = comp b (prodMap (baseChangeMap (S := S) f) (baseChangeMap (S := S) g)) :=
    baseChangeRationalProdIso_naturality (S := S) f g
  change comp t i' = comp i (prodMap (baseChangeMap (S := S) f) h)
  rw [source, target, ← comp_assoc t, ht, comp_assoc b, comp_assoc b, prodMap_comp, prodMap_comp]
  let fS : RationalHom (G.baseChange (S := S)) (G'.baseChange (S := S)) := baseChangeMap (S := S) f
  have primal : comp fS (id (G'.baseChange (S := S))) = comp (id (G.baseChange (S := S))) fS :=
    (comp_id fS).trans (id_comp fS).symm
  exact congrArg₂ (fun (a : RationalHom (G.baseChange (S := S)) (G'.baseChange (S := S)))
    (k : RationalHom (H.baseChange (S := S)) C') => comp b (prodMap a k)) primal dual

variable (hExact : FiniteCartierDualExactnessStatement.{u})

private theorem baseChangeDualIso_smul_naturality
    (f : RationalHom G' G) (c : ℚ_[p]) :
    comp (baseChangeMap (S := S) (c • dualMap hExact f))
        (ofHom (baseChangeDualIso (S := S) G' hExact).hom) =
      comp (ofHom (baseChangeDualIso (S := S) G hExact).hom)
        (c • dualMap hExact (baseChangeMap (S := S) f)) := by
  let g : RationalHom (G.dual hExact) (G'.dual hExact) := dualMap hExact f
  let g' : RationalHom (((F).obj G).dual hExact) (((F).obj G').dual hExact) :=
    dualMap hExact (baseChangeMap (S := S) f)
  let d := ofHom (baseChangeDualIso (S := S) G hExact).hom
  let d' := ofHom (baseChangeDualIso (S := S) G' hExact).hom
  have h := baseChangeDualIso_rational (S := S) (G := G') (H := G) hExact f
  change comp (baseChangeMap (S := S) (c • g)) d' = comp d (c • g')
  rw [map_smul, smul_comp, comp_smul]
  exact congrArg ((c : ℚ_[p]) • ·) h

private theorem rationalSplitBaseChangeIso_hom_factor (G : PDivisibleGroup (CommRingCat.of R) p) :
    (rationalSplitBaseChangeIso (S := S) hExact G).hom =
      comp (baseChangeRationalProdIso (S := S) G (G.dual hExact)).hom
        (prodMap (id ((F).obj G)) (ofHom (baseChangeDualIso (S := S) G hExact).hom)) := by
  change ofHom ((baseChangeProdIso (S := S) G (G.dual hExact)).hom ≫
      Hom.prodMap (𝟙 ((F).obj G)) (baseChangeDualIso (S := S) G hExact).hom) = _
  rw [ofHom_comp, ← prodMap_ofHom, ofHom_id]
  rfl

private theorem baseChangeSplitBlock_square (f : RationalHom G G') (g : RationalHom G' G) (c : ℚ_[p]) :
    comp (baseChangeMap (S := S) (prodMap f (c • dualMap hExact g)))
        (rationalSplitBaseChangeIso (S := S) hExact G').hom =
      comp (rationalSplitBaseChangeIso (S := S) hExact G).hom
        (prodMap (baseChangeMap (S := S) f) (c • dualMap hExact (baseChangeMap (S := S) g))) :=
  baseChangeProdMap_square (H := G.dual hExact) (H' := G'.dual hExact)
    (C := (G.baseChange (S := S)).dual hExact) (C' := (G'.baseChange (S := S)).dual hExact)
    f (c • dualMap hExact g) (c • dualMap hExact (baseChangeMap (S := S) g))
    (ofHom (baseChangeDualIso (S := S) G hExact).hom)
    (ofHom (baseChangeDualIso (S := S) G' hExact).hom)
    (rationalSplitBaseChangeIso (S := S) hExact G).hom
    (rationalSplitBaseChangeIso (S := S) hExact G').hom
    (baseChangeDualIso_smul_naturality (S := S) hExact g c)
    (rationalSplitBaseChangeIso_hom_factor (S := S) hExact G)
    (rationalSplitBaseChangeIso_hom_factor (S := S) hExact G')

private theorem baseChange_inv (e : QuasiIsogeny G G') :
    (e.baseChange (S := S)).inv = baseChangeMap (S := S) e.inv :=
  rfl

/-- Pull back the original rigidifier and compare its target with the split pulled-back primal. -/
def pullbackSplitRigidifier (e : QuasiIsogeny G G') (c : ℚ_[p]ˣ) :
    QuasiIsogeny ((G.splitWithDual hExact).baseChange (S := S))
      ((G'.baseChange (S := S)).splitWithDual hExact) :=
  ((splitRigidifier hExact e c).baseChange (S := S)).trans
    (rationalSplitBaseChangeIso (S := S) hExact G')

/-- Pull back the full rational rigidifier through the canonical split comparisons. -/
theorem baseChangeSplitRigidifier_hom (e : QuasiIsogeny G G') (c : ℚ_[p]ˣ) :
    comp (baseChangeMap (S := S) (splitRigidifier hExact e c).hom)
        (rationalSplitBaseChangeIso (S := S) hExact G').hom =
      comp (rationalSplitBaseChangeIso (S := S) hExact G).hom
        (splitRigidifier hExact (e.baseChange (S := S)) c).hom := by
  simp only [splitRigidifier_hom, QuasiIsogeny.baseChange_hom, baseChange_inv]
  dsimp only [splitWithDual]
  exact baseChangeSplitBlock_square (S := S) (G := G) (G' := G') hExact e.hom e.inv (c : ℚ_[p])

end Langlands.PDivisibleGroup
