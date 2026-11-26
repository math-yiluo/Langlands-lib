import Langlands.GroupScheme.Absolute.BorelPairConjugacyStatement
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof

/-! # Conjugacy of Borel pairs -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A single rational point conjugates both embeddings in a Borel pair to the
corresponding embeddings in any other Borel pair (Milne, Proposition 17.13). -/
theorem borelPairConjugacy : BorelPairConjugacyStatement.{u} := by
  intro k _ _ G _ _ _ B B' T T' i j i' j' h h'
  obtain ⟨hi, hj, f, hf⟩ := h
  obtain ⟨hi', hj', f', hf'⟩ := h'
  obtain ⟨g, φ, hg⟩ := (borelConjugacy k G).2 B B' i i' hi hi'
  let : Smooth B'.X.hom := hi'.smooth
  let : ConnectedSpace B'.X.left := hi'.connectedSpace
  let : IsClosedImmersion i'.hom.hom.left := hi'.isClosedSubgroup
  let : IsAffineHom B'.X.hom := by
    rw [← Over.w i'.hom.hom]
    infer_instance
  have hmax : IsMaximalTorus (f ≫ φ.hom) :=
    (IsMaximalTorus.of_comp hi.isClosedSubgroup (hf.symm ▸ hj)).comp_iso φ
  have hmax' : IsMaximalTorus f' :=
    IsMaximalTorus.of_comp hi'.isClosedSubgroup (hf'.symm ▸ hj')
  obtain ⟨b, ψ, hb⟩ := maximalTorusConjugacy k B' T T' (f ≫ φ.hom) f' hmax hmax'
  let bG : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := b ≫ i'.hom.hom
  have hconj : i' ≫ (G.innerIso bG).hom = (B'.innerIso b).hom ≫ i' :=
    (innerIso_hom_comp i' b).symm
  have hfg : j ≫ (G.innerIso g).hom = (f ≫ φ.hom) ≫ i' := by
    rw [← hf]
    simpa only [Category.assoc] using congrArg (fun a => f ≫ a) hg
  refine ⟨bG * g, φ ≪≫ B'.innerIso b, ψ, ?_, ?_⟩
  · rw [innerIso_mul_hom, ← Category.assoc, hg, Category.assoc, hconj,
      Iso.trans_hom, Category.assoc]
  · rw [innerIso_mul_hom, ← Category.assoc, hfg, Category.assoc, hconj,
      ← Category.assoc, hb, Category.assoc, hf']

end Langlands.GroupScheme
