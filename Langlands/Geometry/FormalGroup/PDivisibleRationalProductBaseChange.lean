import Langlands.Geometry.FormalGroup.PDivisibleProductBaseChange
import Langlands.Geometry.FormalGroup.PDivisibleRationalBaseChange
import Langlands.Geometry.FormalGroup.PDivisibleRationalProduct

/-! # Pullback of products in the rational category of actual p-divisible groups -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace Langlands.PDivisibleGroup

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {p : ℕ} [Fact p.Prime]

open RationalHom

local notation "F" => baseChangeFunctor R S p

/-- The integral product comparison viewed in the rational category. -/
def baseChangeRationalProdIso (G H : PDivisibleGroup (CommRingCat.of R) p) :
    QuasiIsogeny ((F).obj (G.prod H)) (((F).obj G).prod ((F).obj H)) :=
  RationalCategory.inclusion.mapIso (baseChangeProdIso (S := S) G H)

variable {G H G' H' : PDivisibleGroup (CommRingCat.of R) p}

/-- Pullback of a rational block map commutes with the product comparisons. -/
theorem baseChangeRationalProdIso_naturality (f : RationalHom G G') (g : RationalHom H H') :
    comp (baseChangeMap (S := S) (prodMap f g)) (baseChangeRationalProdIso (S := S) G' H').hom =
      comp (baseChangeRationalProdIso (S := S) G H).hom
        (prodMap (baseChangeMap (S := S) f) (baseChangeMap (S := S) g)) := by
  let a := (baseChangeProdIso (S := S) G H).hom
  let b := (baseChangeProdIso (S := S) G' H').hom
  let x : RationalHom ((F).obj (G.prod H)) ((F).obj (G'.prod H')) :=
    baseChangeMap (S := S) (prodMap f g)
  let fS : RationalHom ((F).obj G) ((F).obj G') := baseChangeMap (S := S) f
  let gS : RationalHom ((F).obj H) ((F).obj H') := baseChangeMap (S := S) g
  change comp x (ofHom b) = comp (ofHom a) (prodMap fS gS)
  apply prod_hom_ext
  · let l := prodFst ((F).obj G) ((F).obj H)
    let l' := prodFst ((F).obj G') ((F).obj H')
    have ha : a ≫ l = (F).map (prodFst G H) := baseChangeProdIso_hom_fst G H
    have hb : b ≫ l' = (F).map (prodFst G' H') := baseChangeProdIso_hom_fst G' H'
    have hp : comp x (ofHom ((F).map (prodFst G' H'))) =
        comp (ofHom ((F).map (prodFst G H))) fS := by
      have h := congrArg (baseChangeMap (S := S)) (prodMap_fst f g)
      simp only [baseChangeMap_comp, baseChangeMap_ofHom] at h
      exact h
    change comp (comp x (ofHom b)) (ofHom l') = comp (comp (ofHom a) (prodMap fS gS)) (ofHom l')
    rw [comp_assoc, ← ofHom_comp b l', hb, hp, comp_assoc (ofHom a), prodMap_fst,
      ← comp_assoc (ofHom a), ← ofHom_comp a l, ha]
  · let r := prodSnd ((F).obj G) ((F).obj H)
    let r' := prodSnd ((F).obj G') ((F).obj H')
    have ha : a ≫ r = (F).map (prodSnd G H) := baseChangeProdIso_hom_snd G H
    have hb : b ≫ r' = (F).map (prodSnd G' H') := baseChangeProdIso_hom_snd G' H'
    have hp : comp x (ofHom ((F).map (prodSnd G' H'))) =
        comp (ofHom ((F).map (prodSnd G H))) gS := by
      have h := congrArg (baseChangeMap (S := S)) (prodMap_snd f g)
      simp only [baseChangeMap_comp, baseChangeMap_ofHom] at h
      exact h
    change comp (comp x (ofHom b)) (ofHom r') = comp (comp (ofHom a) (prodMap fS gS)) (ofHom r')
    rw [comp_assoc, ← ofHom_comp b r', hb, hp, comp_assoc (ofHom a), prodMap_snd,
      ← comp_assoc (ofHom a), ← ofHom_comp a r, ha]

end Langlands.PDivisibleGroup
