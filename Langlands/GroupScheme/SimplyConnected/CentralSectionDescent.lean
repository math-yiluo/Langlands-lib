import Langlands.GroupScheme.Derived.CentralKernelCancellation
import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.Descent.FpqcHomDescent

/-! # Descent of sections of central extensions of perfect field groups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace CentralSectionDescent

open Descent

variable {k : Type u} [Field k] {S : Scheme.{u}}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (q : H ⟶ G) (hq : IsCentral (kernelι q)) (hG : derivedSubgroup G = ⊤)
  (p : S ⟶ Spec (CommRingCat.of k)) [IsAffineHom p]
  (s : (baseChange p).obj G ⟶ (baseChange p).obj H)
  (hs : s ≫ (baseChange p).map q = 𝟙 _)

include hq hG hs

/-- A homomorphic section of a central extension of a perfect affine field group
automatically respects the canonical descent data. -/
theorem compatible :
    Compatible (canonicalDatum p G) (canonicalDatum p H) s := by
  let : IsAffineHom (fst p) := MorphismProperty.pullback_fst p p inferInstance
  let e := pullbackComparison p (fst p) (fst p ≫ p) rfl G
  have hperfect :
      derivedSubgroup ((baseChange (fst p)).obj ((baseChange p).obj G)) = ⊤ := by
    rw [← derivedSubgroup_comap_iso e,
      derivedSubgroup_eq_top_baseChange hG (fst p ≫ p)]
    ext T x
    exact Iff.rfl
  let q₂ := (baseChange (snd p)).map ((baseChange p).map q)
  have hcentral : IsCentral (kernelι q₂) :=
    (hq.kernel_baseChange p).kernel_baseChange (snd p)
  let : IsAffineHom ((baseChange p).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom p)
    exact MorphismProperty.pullback_snd _ _ inferInstance
  let : IsAffineHom ((baseChange p).obj H).X.hom := by
    change IsAffineHom (pullback.snd H.X.hom p)
    exact MorphismProperty.pullback_snd _ _ inferInstance
  let : IsAffineHom ((baseChange (snd p)).obj ((baseChange p).obj G)).X.hom := by
    change IsAffineHom (pullback.snd ((baseChange p).obj G).X.hom (snd p))
    exact MorphismProperty.pullback_snd _ _ inferInstance
  let : IsAffineHom ((baseChange (snd p)).obj ((baseChange p).obj H)).X.hom := by
    change IsAffineHom (pullback.snd ((baseChange p).obj H).X.hom (snd p))
    exact MorphismProperty.pullback_snd _ _ inferInstance
  let : IsAffineHom (kernel q₂).X.hom := by
    rw [← Over.w (kernelι q₂).hom.hom]
    infer_instance
  apply centralKernel_cancel_of_perfect hperfect q₂ hcentral
  have hqcomp := canonicalDatum_compatible p q
  change (baseChange (fst p)).map ((baseChange p).map q) ≫
      (canonicalOverlap p G).hom =
    (canonicalOverlap p H).hom ≫
      (baseChange (snd p)).map ((baseChange p).map q) at hqcomp
  change ((baseChange (fst p)).map s ≫ (canonicalOverlap p H).hom) ≫ q₂ =
    ((canonicalOverlap p G).hom ≫ (baseChange (snd p)).map s) ≫ q₂
  dsimp only [q₂]
  rw [Category.assoc, ← hqcomp, ← Category.assoc, ← Functor.map_comp, hs,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, ← Functor.map_comp, hs,
    CategoryTheory.Functor.map_id, Category.comp_id]

variable [Flat p] [Surjective p] [QuasiCompact p]

/-- Descend a section through an affine fpqc change of base. -/
def sectionHom : G ⟶ H :=
  Descent.FpqcHomDescent.hom p s (compatible q hq hG p s hs)

/-- Pullback recovers the given section exactly. -/
theorem baseChange_sectionHom :
    (baseChange p).map (sectionHom q hq hG p s hs) = s :=
  Descent.FpqcHomDescent.baseChange_hom p s (compatible q hq hG p s hs)

/-- The descended homomorphism is still a section of the original quotient. -/
@[reassoc]
theorem sectionHom_comp :
    sectionHom q hq hG p s hs ≫ q = 𝟙 G := by
  apply Grp.hom_ext
  apply (Over.pullback p).map_injective
  change ((baseChange p).map (sectionHom q hq hG p s hs ≫ q)).hom.hom =
    ((baseChange p).map (𝟙 G)).hom.hom
  rw [Functor.map_comp, baseChange_sectionHom, hs, CategoryTheory.Functor.map_id]

/-- A section after affine fpqc base change gives a section over the original field. -/
theorem exists_section :
    ∃ t : G ⟶ H, t ≫ q = 𝟙 G :=
  ⟨sectionHom q hq hG p s hs, sectionHom_comp q hq hG p s hs⟩

end CentralSectionDescent

end Langlands.GroupScheme
