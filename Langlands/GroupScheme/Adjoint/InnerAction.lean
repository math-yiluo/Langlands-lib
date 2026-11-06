import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.GroupScheme.ActionDescent

/-! # The actual inner action of an adjoint quotient on its source -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {S : Scheme.{u}} {G A : GroupScheme S} {q : G ⟶ A}

/-- The full central kernel acts trivially by conjugation on all relative tests. -/
theorem conjugation_kernelActsTrivially
    (hker : IsSchemeTheoreticCenter (kernelι q)) :
    (conjugation (𝟙 G)).KernelActsTrivially q := by
  intro T k g
  have hz := hker.isCentral T k
  have hc := hz T (𝟙 T) g
  simp only [Category.id_comp] at hc
  simp only [restrict_act, conjugation_act, Grp.id_hom_hom, Category.comp_id]
  rw [hc.eq, mul_inv_cancel_right]

end AutomorphicAction

namespace IsAdjointQuotient

variable {K : Type u} [Field K]
    {G A : GroupScheme (Spec (CommRingCat.of K))}
    {q : G ⟶ A} (hq : IsAdjointQuotient q)

/-- The supplied adjoint quotient acts on its original reductive group by inner
scheme automorphisms, including on points without a global quotient lift. -/
def innerAction : AutomorphicAction A G := by
  letI := hq.flat
  letI := hq.surjective
  letI := hq.isConnectedReductive.isAffineHom
  letI := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  exact (AutomorphicAction.conjugation (𝟙 G)).quotientAction q
    (AutomorphicAction.conjugation_kernelActsTrivially hq.kernelCenter)

/-- Evaluating the descended inner action at a lifted quotient point is conjugation. -/
theorem innerAction_act_lift {T : Over (Spec (CommRingCat.of K))}
    (h g : T ⟶ G.X) :
    hq.innerAction.act (h ≫ q.hom.hom) g = h * g * h⁻¹ := by
  let := hq.flat
  let := hq.surjective
  let := hq.isConnectedReductive.isAffineHom
  let := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  exact ((AutomorphicAction.conjugation (𝟙 G)).quotientAction_act_lift q
    (AutomorphicAction.conjugation_kernelActsTrivially hq.kernelCenter) h g).trans
      (by simp only [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id])

end IsAdjointQuotient

end Langlands.GroupScheme
