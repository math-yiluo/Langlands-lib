import Langlands.GroupScheme.HomScheme.SmoothSplitSourceRepresentabilityProof
import Langlands.AlgebraicGeometry.SmoothPointedEtaleSectionConstruction

/-! # Pointed etale lifting of homomorphisms from split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.HomScheme

/-- A prescribed homomorphism from a split torus into a residue fibre of a smooth
affine group extends over a pointed etale neighbourhood, with exact recovery
under the relative Hom evaluation map. -/
theorem exists_pointed_etale_lift
    (S : Scheme.{u}) (H G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hH : IsSplitTorus H)
    (s : S) (i₀ : RelativeHom H G (Over.mk (S.fromSpecResidueField s))) :
    ∃ (U : Scheme.{u}) (p : U ⟶ S), Etale p ∧
      ∃ (b : Spec (S.residueField s) ⟶ U)
        (hb : b ≫ p = S.fromSpecResidueField s)
        (i : RelativeHom H G (Over.mk p)),
        evaluate (show Over.mk (S.fromSpecResidueField s) ⟶ Over.mk p from
          Over.homMk b hb) i = i₀ := by
  obtain ⟨M, j, hj, hM⟩ := smoothSplitSourceRepresentability S H G hH
  obtain ⟨x, hx⟩ := (hj (Over.mk (S.fromSpecResidueField s))).surjective i₀
  change evaluate x j = i₀ at hx
  obtain ⟨U, p, b, a, hp, hb, ha, hba⟩ :=
    Langlands.AlgebraicGeometry.exists_pointed_etale_section
      M.hom s x.left (Over.w x)
  let aM : Over.mk p ⟶ M := Over.homMk a ha
  let bU : Over.mk (S.fromSpecResidueField s) ⟶ Over.mk p := Over.homMk b hb
  have hbx : bU ≫ aM = x := by
    apply Over.OverMorphism.ext
    exact hba
  refine ⟨U, p, hp, b, hb, evaluate aM j, ?_⟩
  change evaluate bU (evaluate aM j) = i₀
  rw [← evaluate_comp, hbx, hx]

/-- A pointed etale neighbourhood carrying a lift of a prescribed residue
homomorphism, including its exact evaluation equation. -/
structure PointedEtaleHomLiftData
    (S : Scheme.{u}) (H G : GroupScheme S) (s : S)
    (i₀ : RelativeHom H G (Over.mk (S.fromSpecResidueField s))) where
  neighbourhood : Scheme.{u}
  projection : neighbourhood ⟶ S
  etale : Etale projection
  residuePoint : Spec (S.residueField s) ⟶ neighbourhood
  residue_over : residuePoint ≫ projection = S.fromSpecResidueField s
  homomorphism : RelativeHom H G (Over.mk projection)
  recovers : evaluate
    (show Over.mk (S.fromSpecResidueField s) ⟶ Over.mk projection from
      Over.homMk residuePoint residue_over) homomorphism = i₀

/-- Choose a pointed etale lift of the prescribed split-torus homomorphism. -/
def pointedEtaleHomLift
    (S : Scheme.{u}) (H G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hH : IsSplitTorus H)
    (s : S) (i₀ : RelativeHom H G (Over.mk (S.fromSpecResidueField s))) :
    PointedEtaleHomLiftData S H G s i₀ :=
  Classical.choice <| by
    obtain ⟨U, p, hp, b, hb, i, hi⟩ := exists_pointed_etale_lift S H G hH s i₀
    exact ⟨⟨U, p, hp, b, hb, i, hi⟩⟩

end Langlands.GroupScheme.HomScheme
