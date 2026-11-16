import Langlands.GroupScheme.RelativeLevi.ModuliValue
import Langlands.GroupScheme.RelativeLevi.ConjugacyProof

/-! # Simple transitivity on actual relative Levi images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi.LeviImage

variable {S : Scheme.{u}} {G P U : GroupScheme S}
    (i : P ⟶ G) (r : U ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hr : IsRelativeUnipotentRadical r)

include i hG hi hr

/-- The supplied radical acts simply transitively on actual Levi subgroup images.
No Levi presentation is included in the equality of moduli points. -/
theorem existsUnique_conjugate (F F' : LeviImage P) :
    ∃! g : Over.mk (𝟙 S) ⟶ U.X,
      F.conjugate (g ≫ r.hom.hom) = F' := by
  obtain ⟨L, l, hl, hF⟩ := F.exists_presentation
  obtain ⟨L', l', hl', hF'⟩ := F'.exists_presentation
  obtain ⟨g, hg, huniq⟩ :=
    relativeLeviConjugacy S G P U L L' i r l l' hG hi hr hl hl'
  have he (v : Over.mk (𝟙 S) ⟶ U.X) :
      F.conjugate (v ≫ r.hom.hom) = F' ↔
        SubgroupFunctor.range l' =
          SubgroupFunctor.range (l ≫ (P.innerIso (v ≫ r.hom.hom)).hom) := by
    constructor
    · intro hv
      have heq := congrArg (fun K : LeviImage P => K.val) hv
      change conjugateImage (v ≫ r.hom.hom) F.val = F'.val at heq
      rw [← hF, ← hF', conjugateImage_range] at heq
      exact heq.symm
    · intro hv
      apply ext
      change conjugateImage (v ≫ r.hom.hom) F.val = F'.val
      rw [← hF, ← hF', conjugateImage_range]
      exact hv.symm
  exact ⟨g, (he g).mpr hg, fun v hv => huniq v ((he v).mp hv)⟩

/-- A supplied Levi image identifies its conjugation orbit with all actual Levi
images. The source of a presenting Levi is not used in this equivalence. -/
def conjugationEquiv (F : LeviImage P) :
    (Over.mk (𝟙 S) ⟶ U.X) ≃ LeviImage P :=
  Equiv.ofBijective (fun g => F.conjugate (g ≫ r.hom.hom)) ⟨
    fun g h he => by
      obtain ⟨v, hv, huniq⟩ := existsUnique_conjugate i r hG hi hr F
        (F.conjugate (h ≫ r.hom.hom))
      exact (huniq g he).trans (huniq h rfl).symm,
    fun F' => (existsUnique_conjugate i r hG hi hr F F').exists⟩

@[simp]
theorem conjugationEquiv_apply (F : LeviImage P)
    (g : Over.mk (𝟙 S) ⟶ U.X) :
    conjugationEquiv i r hG hi hr F g = F.conjugate (g ≫ r.hom.hom) := rfl

/-- The orbit identification intertwines multiplication with the actual
conjugation operation, in the orientation used by the torsor target. -/
theorem conjugationEquiv_mul (F : LeviImage P)
    (g h : Over.mk (𝟙 S) ⟶ U.X) :
    conjugationEquiv i r hG hi hr F (g * h) =
      (conjugationEquiv i r hG hi hr F h).conjugate (g ≫ r.hom.hom) := by
  apply ext
  change conjugateImage ((g * h) ≫ r.hom.hom) F.val =
    conjugateImage (g ≫ r.hom.hom) (conjugateImage (h ≫ r.hom.hom) F.val)
  rw [MonObj.mul_comp, conjugateImage_mul]

end Langlands.GroupScheme.RelativeLevi.LeviImage
