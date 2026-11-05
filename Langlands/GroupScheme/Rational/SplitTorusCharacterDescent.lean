import Langlands.GroupScheme.Torus.PointedMorphismDescent
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Rational.TorusDominationBaseChange
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Rational.AffineEmbeddingHomDescent
import Langlands.GroupScheme.Torus.LatticeBaseInvariants

/-! # Character descent from pointed split-torus domination -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {P : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}

/-- Composing a geometric character with a pointed split-torus morphism
produces the base change of an actual ground-field character of the torus. -/
theorem IsSplitTorus.exists_character_of_pointed_composite
    (hP : IsSplitTorus P.toGrp) (p : P.X ⟶ H.X)
    (hp : η[P.X] ≫ p = η[H.X])
    (χ : (GroupScheme.baseChange (algebraBaseMap k K)).obj H ⟶
      (Gm (Spec (CommRingCat.of K))).toGrp) :
    ∃ ψ : characterLattice P,
      (Over.pullback (algebraBaseMap k K)).map p ≫ χ.hom.hom =
        (Over.pullback (algebraBaseMap k K)).map
            (CommGroupScheme.groupHom ψ).hom.hom ≫
          (Gm.baseChangeIso (algebraBaseMap k K)).hom.hom.hom := by
  let b := algebraBaseMap k K
  let pχ := (Over.pullback b).map p ≫ χ.hom.hom
  have hpχ : η[((GroupScheme.baseChange b).obj P.toGrp).X] ≫ pχ =
      η[(Gm (Spec (CommRingCat.of K))).X] := by
    dsimp only [pχ]
    rw [← Category.assoc, pointed_morphism_algebraPullback K p hp,
      IsMonHom.one_hom]
  let f := ((hP.baseChange b).isTorus).homOfPointedMorphism
    isSplitTorus_gm.isTorus pχ hpχ
  let ψK : characterLattice ((CommGroupScheme.baseChange b).obj P) := Additive.ofMul f
  obtain ⟨ψ, hψ⟩ := (hP.characterLattice_baseChange_bijective b P).surjective ψK
  refine ⟨ψ, ?_⟩
  have hψ' := congrArg (fun q => (CommGroupScheme.groupHom q).hom.hom) hψ
  change (Over.pullback b).map (CommGroupScheme.groupHom ψ).hom.hom ≫
      (Gm.baseChangeIso b).hom.hom.hom = pχ at hψ'
  exact hψ'.symm

end Langlands.GroupScheme

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.AffineEmbeddingDescent
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {H : GroupScheme (Spec (CommRingCat.of k))}

/-- Every geometric character of a reduced affine group dominated by a
pointed split torus is defined over the ground field. -/
theorem HasPointedSplitTorusDomination.exists_character
    [IsReduced H.X.left] [IsAffineHom H.X.hom]
    (hH : HasPointedSplitTorusDomination H)
    (χ : (GroupScheme.baseChange (algebraBaseMap k K)).obj H ⟶
      (Gm (Spec (CommRingCat.of K))).toGrp) :
    ∃ χ₀ : H ⟶ (Gm (Spec (CommRingCat.of k))).toGrp,
      (GroupScheme.baseChange (algebraBaseMap k K)).map χ₀ ≫
        (Gm.baseChangeIso (algebraBaseMap k K)).hom = χ := by
  obtain ⟨P, p, hP, hd, hp⟩ := hH
  let PC : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { P with comm := hP.isCommMonObj }
  have hp' : η[P.X] ≫ p = η[H.X] := by
    change (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ P.X) ≫ p =
      (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) at hp
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using hp
  obtain ⟨ψ, hψ⟩ := hP.exists_character_of_pointed_composite (P := PC) p hp' χ
  let b := algebraBaseMap k K
  change (Over.pullback b).map p ≫ χ.hom.hom =
    (Over.pullback b).map (CommGroupScheme.groupHom ψ).hom.hom ≫
      (Gm.baseChangeIso b).hom.hom.hom at hψ
  let g := χ ≫ (Gm.baseChangeIso b).inv
  have he : (Over.pullback b).map p ≫ g.hom.hom =
      (Over.pullback b).map (CommGroupScheme.groupHom ψ).hom.hom := by
    dsimp only [g]
    rw [Grp.comp_hom_hom, ← Category.assoc, hψ]
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id]
    exact Category.comp_id _
  have : IsAffine P.X.left := SplittingAssembly.isAffine_of_isTorus P hP.isTorus
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsAffine (Gm (Spec (CommRingCat.of k))).X.left :=
    SplittingAssembly.isAffine_of_isTorus _ isSplitTorus_gm.isTorus
  have : IsDominant p.left := hd
  have : IsSchemeTheoreticallyDominant p.left :=
    IsSchemeTheoreticallyDominant.of_isDominant p.left
  have : QuasiCompact p.left := inferInstance
  have hgh : (scalarExtension k K).map p ≫
      (Over.map b).map g.hom.hom ≫
        projection (Gm (Spec (CommRingCat.of k))).X =
      projection P.X ≫ (CommGroupScheme.groupHom ψ).hom.hom := by
    change (Over.map b).map ((Over.pullback b).map p) ≫ _ ≫ _ = _
    rw [← Functor.map_comp_assoc, he]
    exact projection_natural (CommGroupScheme.groupHom ψ).hom.hom
  obtain ⟨χ₀, hχ₀, -⟩ := AffineEmbeddingHomDescent.existsUnique_hom
    p g (CommGroupScheme.groupHom ψ).hom.hom hgh
  refine ⟨χ₀, ?_⟩
  rw [hχ₀]
  change (χ ≫ (Gm.baseChangeIso b).inv) ≫ (Gm.baseChangeIso b).hom = χ
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable [IsReduced H.X.left] [IsAffineHom H.X.hom]

/-- Actual characters are unchanged by arbitrary field extension for a
reduced affine group with pointed split-torus domination. -/
theorem HasPointedSplitTorusDomination.character_baseChange_bijective
    (hH : HasPointedSplitTorusDomination H) :
    Function.Bijective
      (rationalCharacters.baseChange (algebraBaseMap k K) (G := H)) := by
  refine ⟨rationalCharacters.algebraBaseChange_injective k K H, ?_⟩
  intro χ
  obtain ⟨χ₀, hχ₀⟩ := hH.exists_character χ.toMul
  exact ⟨Additive.ofMul χ₀, congrArg Additive.ofMul hχ₀⟩

/-- The actual character equivalence furnished by pointed split-torus
domination; its inverse is descent to the ground field. -/
def HasPointedSplitTorusDomination.characterEquiv
    (hH : HasPointedSplitTorusDomination H) :
    rationalCharacters H ≃+
      rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj H) :=
  AddEquiv.ofBijective (rationalCharacters.baseChange (algebraBaseMap k K))
    hH.character_baseChange_bijective

/-- The forward equivalence is the original base-change map. -/
@[simp]
theorem HasPointedSplitTorusDomination.characterEquiv_apply
    (hH : HasPointedSplitTorusDomination H) (χ : rationalCharacters H) :
    hH.characterEquiv (K := K) χ =
      rationalCharacters.baseChange (algebraBaseMap k K) χ := rfl

/-- The descended character recovers the supplied extension-field character. -/
@[simp]
theorem HasPointedSplitTorusDomination.baseChange_characterEquiv_symm
    (hH : HasPointedSplitTorusDomination H)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj H)) :
    rationalCharacters.baseChange (algebraBaseMap k K)
      ((hH.characterEquiv (K := K)).symm χ) = χ :=
  (hH.characterEquiv (K := K)).apply_symm_apply χ

/-- Every extension-field character is fixed by actual descent transport. -/
theorem HasPointedSplitTorusDomination.transportCharacter_eq
    (hH : HasPointedSplitTorusDomination H)
    (a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
    (ha : a ≫ algebraBaseMap k K = algebraBaseMap k K)
    (χ : (GroupScheme.baseChange (algebraBaseMap k K)).obj H ⟶
      (Gm (Spec (CommRingCat.of K))).toGrp) :
    transportCharacter (algebraBaseMap k K) a ha H χ = χ := by
  obtain ⟨χ₀, hχ₀⟩ := hH.character_baseChange_bijective.surjective
    (Additive.ofMul χ)
  have he := congrArg Additive.toMul hχ₀
  change (rationalCharacters.baseChange (algebraBaseMap k K) χ₀).toMul = χ at he
  rw [← he]
  exact rationalCharacters.transportCharacter_baseChange
    (algebraBaseMap k K) a ha χ₀

end Langlands.GroupScheme
