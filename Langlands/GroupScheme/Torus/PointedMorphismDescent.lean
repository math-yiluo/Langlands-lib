import Langlands.GroupScheme.Torus.PointedMorphism
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Absolute.CocharacterDescentGroup

/-! # Pointed morphisms of arbitrary tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {D H : GroupScheme (Spec (CommRingCat.of k))}

/-- Transport pointed-morphism rigidity through splitting isomorphisms. -/
theorem IsSplitTorus.isMonHom_of_pointed_morphism
    (hD : IsSplitTorus D) (hH : IsSplitTorus H)
    (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X]) : IsMonHom p := by
  classical
  obtain ⟨I, hI, ⟨eD⟩⟩ := hD
  obtain ⟨J, hJ, ⟨eH⟩⟩ := hH
  let : Fintype I := Fintype.ofFinite I
  let p' := eD.inv.hom.hom ≫ p ≫ eH.hom.hom.hom
  have hp' : η[(splitTorus (Spec (CommRingCat.of k)) I).X] ≫ p' =
      η[(splitTorus (Spec (CommRingCat.of k)) J).X] := by
    simp only [p', IsMonHom.one_hom_assoc]
    rw [← Category.assoc, hp, IsMonHom.one_hom]
  let f' := splitTorus.homOfPointedMorphism I J p' hp'
  let f : D ⟶ H := eD.hom ≫ f' ≫ eH.inv
  have hf : f.hom.hom = p := by
    change eD.hom.hom.hom ≫ f'.hom.hom ≫ eH.inv.hom.hom = p
    rw [show f'.hom.hom = p' from
      splitTorus.homOfPointedMorphism_hom I J p' hp']
    change (eD.hom.hom.hom ≫ eD.inv.hom.hom) ≫ p ≫
      (eH.hom.hom.hom ≫ eH.inv.hom.hom) = p
    change ((eD.hom ≫ eD.inv).hom.hom ≫ p ≫
      (eH.hom ≫ eH.inv).hom.hom) = p
    simp only [Iso.hom_inv_id, Grp.id_hom_hom, Category.id_comp, Category.comp_id]
  rw [← hf]
  infer_instance

open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal in
/-- A field pullback preserves the pointedness equation for an underlying
scheme morphism of group schemes. -/
theorem pointed_morphism_algebraPullback
    (K : Type u) [Field K] [Algebra k K]
    (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X]) :
    η[((GroupScheme.baseChange (algebraBaseMap k K)).obj D).X] ≫
        (Over.pullback (algebraBaseMap k K)).map p =
      η[((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X] := by
  change
    (ε (Over.pullback (algebraBaseMap k K)) ≫
      (Over.pullback (algebraBaseMap k K)).map η[D.X]) ≫
      (Over.pullback (algebraBaseMap k K)).map p =
    ε (Over.pullback (algebraBaseMap k K)) ≫
      (Over.pullback (algebraBaseMap k K)).map η[H.X]
  rw [Category.assoc, ← Functor.map_comp, hp]

/-- Pointed rigidity for a split source and an arbitrary torus target follows
by faithful pullback to a field splitting the target. -/
theorem IsSplitTorus.isMonHom_to_torus_of_pointed_morphism
    (hD : IsSplitTorus D) (hH : IsTorus H)
    (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X]) : IsMonHom p := by
  obtain ⟨K, hK, aK, hHK⟩ := hH
  let := hK
  let := aK
  let := GaloisCocharacterDescent.faithful_algebraPullback k K
  have : IsMonHom ((Over.pullback (algebraBaseMap k K)).map p) :=
    (hD.baseChange (algebraBaseMap k K)).isMonHom_of_pointed_morphism hHK _
      (pointed_morphism_algebraPullback K p hp)
  exact GaloisCocharacterDescent.isMonHom_of_faithfulMap
    (Over.pullback (algebraBaseMap k K)) p

/-- Every identity-preserving scheme morphism between tori preserves
the group laws, over every ground field. -/
theorem IsTorus.isMonHom_of_pointed_morphism
    (hD : IsTorus D) (hH : IsTorus H)
    (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X]) : IsMonHom p := by
  obtain ⟨K, hK, aK, hDK⟩ := hD
  let := hK
  let := aK
  let := GaloisCocharacterDescent.faithful_algebraPullback k K
  have : IsMonHom ((Over.pullback (algebraBaseMap k K)).map p) :=
    hDK.isMonHom_to_torus_of_pointed_morphism hH.baseChange _
      (pointed_morphism_algebraPullback K p hp)
  exact GaloisCocharacterDescent.isMonHom_of_faithfulMap
    (Over.pullback (algebraBaseMap k K)) p

/-- The actual group-scheme homomorphism of tori associated to a pointed
scheme morphism. -/
def IsTorus.homOfPointedMorphism
    (hD : IsTorus D) (hH : IsTorus H)
    (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X]) : D ⟶ H :=
  letI := hD.isMonHom_of_pointed_morphism hH p hp
  Grp.homMk p

@[simp] theorem IsTorus.homOfPointedMorphism_hom
    (hD : IsTorus D) (hH : IsTorus H)
    (p : D.X ⟶ H.X) (hp : η[D.X] ≫ p = η[H.X]) :
    (hD.homOfPointedMorphism hH p hp).hom.hom = p := rfl

end Langlands.GroupScheme
