import Langlands.Geometry.FormalGroup.PDivisibleProductBaseChange
import Langlands.Geometry.FormalGroup.PDivisibleBaseChangeCoherence

/-! # Coherence of the product comparison for p-divisible tower pullback -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace Langlands.PDivisibleGroup

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
variable (G H : PDivisibleGroup (CommRingCat.of R) p)

/-- The product comparison is compatible with the identity map of the base. -/
theorem baseChangeProdIso_id :
    (baseChangeProdIso (S := R) G H).hom ≫ Hom.prodMap (baseChangeIdIso G).hom (baseChangeIdIso H).hom =
      (baseChangeIdIso (G.prod H)).hom := by
  let F := baseChangeFunctor R R p
  let a := (baseChangeProdIso (S := R) G H).hom
  apply Hom.prod_hom_ext
  · let r := prodFst G H
    let r' := prodFst (F.obj G) (F.obj H)
    have h : F.map r ≫ (baseChangeIdIso G).hom = (baseChangeIdIso (G.prod H)).hom ≫ r :=
      (baseChangeIdNatIso R p).hom.naturality r
    rw [Category.assoc, Hom.prodMap_fst]
    change a ≫ r' ≫ (baseChangeIdIso G).hom = _
    rw [← Category.assoc a, baseChangeProdIso_hom_fst]
    exact h
  · let r := prodSnd G H
    let r' := prodSnd (F.obj G) (F.obj H)
    have h : F.map r ≫ (baseChangeIdIso H).hom = (baseChangeIdIso (G.prod H)).hom ≫ r :=
      (baseChangeIdNatIso R p).hom.naturality r
    rw [Category.assoc, Hom.prodMap_snd]
    change a ≫ r' ≫ (baseChangeIdIso H).hom = _
    rw [← Category.assoc a, baseChangeProdIso_hom_snd]
    exact h

variable {S T : Type u} [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

local notation "F" => baseChangeFunctor R S p
local notation "J" => baseChangeFunctor S T p
local notation "K" => baseChangeFunctor R T p

/-- Compare the direct pullback of a product with the product of the successive pullbacks. -/
def baseChangeProdCompIso :
    (K).obj (G.prod H) ≅ ((J).obj ((F).obj G)).prod ((J).obj ((F).obj H)) :=
  baseChangeCompIso (S := S) (T := T) (G.prod H) ≪≫
    (J).mapIso (baseChangeProdIso (S := S) G H) ≪≫
    baseChangeProdIso (S := T) ((F).obj G) ((F).obj H)

/-- The direct product comparison agrees with the two successive comparisons. -/
theorem baseChangeProdIso_comp :
    (baseChangeProdCompIso (S := S) (T := T) G H).hom =
      (baseChangeProdIso (S := T) G H).hom ≫
        Hom.prodMap (baseChangeCompIso (S := S) (T := T) G).hom
          (baseChangeCompIso (S := S) (T := T) H).hom := by
  change (baseChangeCompIso (S := S) (T := T) (G.prod H)).hom ≫
      (J).map (baseChangeProdIso (S := S) G H).hom ≫
        (baseChangeProdIso (S := T) ((F).obj G) ((F).obj H)).hom = _
  let a := (baseChangeProdIso (S := S) G H).hom
  let d := (baseChangeProdIso (S := T) G H).hom
  let i := (baseChangeCompIso (S := S) (T := T) (G.prod H)).hom
  let iG := (baseChangeCompIso (S := S) (T := T) G).hom
  let iH := (baseChangeCompIso (S := S) (T := T) H).hom
  apply Hom.prod_hom_ext
  · let r := prodFst G H
    have h : (K).map r ≫ iG = i ≫ (J).map ((F).map r) :=
      (baseChangeCompNatIso R S T p).hom.naturality r
    have hr : Hom.prodMap iG iH ≫ prodFst ((J).obj ((F).obj G)) ((J).obj ((F).obj H)) =
        prodFst ((K).obj G) ((K).obj H) ≫ iG := Hom.prodMap_fst iG iH
    simp only [Category.assoc, baseChangeProdIso_hom_fst]
    change i ≫ (J).map a ≫ (J).map (prodFst ((F).obj G) ((F).obj H)) =
      d ≫ Hom.prodMap iG iH ≫ prodFst ((J).obj ((F).obj G)) ((J).obj ((F).obj H))
    rw [hr, ← (J).map_comp, baseChangeProdIso_hom_fst, ← Category.assoc d,
      baseChangeProdIso_hom_fst]
    exact h.symm
  · let r := prodSnd G H
    have h : (K).map r ≫ iH = i ≫ (J).map ((F).map r) :=
      (baseChangeCompNatIso R S T p).hom.naturality r
    have hr : Hom.prodMap iG iH ≫ prodSnd ((J).obj ((F).obj G)) ((J).obj ((F).obj H)) =
        prodSnd ((K).obj G) ((K).obj H) ≫ iH := Hom.prodMap_snd iG iH
    simp only [Category.assoc, baseChangeProdIso_hom_snd]
    change i ≫ (J).map a ≫ (J).map (prodSnd ((F).obj G) ((F).obj H)) =
      d ≫ Hom.prodMap iG iH ≫ prodSnd ((J).obj ((F).obj G)) ((J).obj ((F).obj H))
    rw [hr, ← (J).map_comp, baseChangeProdIso_hom_snd, ← Category.assoc d,
      baseChangeProdIso_hom_snd]
    exact h.symm

end Langlands.PDivisibleGroup
