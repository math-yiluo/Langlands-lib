import Langlands.GroupScheme.Reductive.LocalSplitCommonTorus
import Langlands.GroupScheme.Reductive.LocalSplitPositiveProducts

/-! # Torus compatibility of coordinate cell isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace splitTorus

variable (S : Scheme.{u}) {I I' : Type u} [Fintype I] [Fintype I']
  [DecidableEq I] [DecidableEq I']

/-- The torus isomorphism attached to an integral lattice equivalence has its
prescribed contravariant monomial action on every test scheme. -/
theorem pointsEquiv_exponentEquivGroupIso
    (e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ)) (U : Over S)
    (x : U ⟶ (splitTorus S I).X) (m : I' → ℤ) :
    ∏ j', pointsEquiv I' U
        (x ≫ (LocalSplitCell.exponentEquivGroupIso S e).hom.hom.hom) j' ^ m j' =
      ∏ j, pointsEquiv I U x j ^ e.symm m j := by
  rw [← pointsEquiv_exponentCharacter, ← pointsEquiv_exponentCharacter]
  change Gm.pointsEquiv S U
      (x ≫ (CommGroupScheme.groupHom
        (exponentHom S I I' e.symm.toLinearMap)).hom.hom ≫
        (CommGroupScheme.groupHom (exponentCharacter S I' m)).hom.hom) = _
  rw [← Grp.comp_hom_hom]
  change Gm.pointsEquiv S U
      (x ≫ (CommGroupScheme.groupHom
        (exponentHom S I I' e.symm.toLinearMap ≫ exponentCharacter S I' m)).hom.hom) = _
  rw [exponentHom_comp_exponentCharacter]
  rfl

end splitTorus

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- The canonical torus section of the coordinate cell, with all negative and
positive root coordinates zero. -/
def cellTorusSection (R : Type u) [CommRing R] (I : Type u) [Fintype I] (m n : ℕ) :
    (splitTorus (Spec (CommRingCat.of R)) I).X ⟶ cellObj R I m n :=
  mkCellPoint _ 0 (splitTorus.pointsEquiv I _ (𝟙 _)) 0

/-- Zero root coordinates restrict the coordinate cell map to the supplied
torus, over every test scheme. -/
theorem mkCellPoint_zero_comp_cellMap
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (u : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    mkCellPoint Z 0 (splitTorus.pointsEquiv I Z t) 0 ≫ cellMap i u neg pos =
      t ≫ i.hom.hom := by
  have ht : torusCoord (mkCellPoint Z (0 : Fin m → Γ(Z.left, ⊤))
      (splitTorus.pointsEquiv I Z t) (0 : Fin n → Γ(Z.left, ⊤))) = t :=
    (splitTorus.pointsEquiv I Z).injective (by rw [torusCoord_mkCellPoint])
  rw [comp_cellMap, cellPoint, negCoord_mkCellPoint, posCoord_mkCellPoint, ht,
    orderedProduct_zero, orderedProduct_zero, one_mul, mul_one]

/-- Composing the torus section with any coordinate cell map recovers its
supplied torus embedding. -/
theorem cellTorusSection_comp_cellMap
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (u : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J) :
    cellTorusSection R I m n ≫ cellMap i u neg pos = i.hom.hom := by
  simpa only [cellTorusSection, Category.id_comp] using
    mkCellPoint_zero_comp_cellMap i u neg pos
      (splitTorus (Spec (CommRingCat.of R)) I).X (𝟙 _)

/-- An isomorphism matching coordinate cell maps also matches their torus
embeddings. No local-ring or reducedness hypothesis is needed. -/
theorem torus_comp_of_cellMap_comp
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H}
    {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}
    (ψ : G ⟶ H)
    (hψ : cellMap i u neg pos ≫ ψ.hom.hom = cellMap i' u' neg pos) :
    i ≫ ψ = i' := by
  apply Grp.hom_ext
  have h := congrArg (fun q => cellTorusSection R I m n ≫ q) hψ
  rw [← Category.assoc, cellTorusSection_comp_cellMap, cellTorusSection_comp_cellMap] at h
  exact h

end LocalSplitCell

end Langlands.GroupScheme
