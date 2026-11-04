import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.GroupScheme.QuotientAction

/-! # Automorphic actions on actual full-centre quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {B : Scheme.{u}} {S G Q : GroupScheme B}

/-- Every automorphic action preserves the full centre after every refinement
of a test scheme. No reducedness or smoothness is required. -/
theorem isStable_center (b : AutomorphicAction S G) : b.IsStable (center G) := by
  intro T s g hg U a x
  rw [b.naturality]
  have hc := hg U a (b.act (a ≫ s)⁻¹ x)
  have he := congrArg (b.act (a ≫ s)) hc.eq
  apply (commute_iff_eq _ _).mpr
  simpa only [b.act_mul_right, b.act_act_inv] using he

variable (b : AutomorphicAction S G) (q : G ⟶ Q)
    (hcenter : SubgroupFunctor.range (kernelι q) = center G)
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]

/-- The canonical action on a supplied fpqc quotient by the entire centre.
The centre and the quotient may be nonsmooth. -/
def onCenterQuotient : AutomorphicAction S Q :=
  b.onQuotient q (by rw [hcenter]; exact b.isStable_center)

/-- The supplied full-centre quotient is equivariant for the constructed action. -/
theorem onCenterQuotient_isEquivariant :
    b.IsEquivariant (b.onCenterQuotient q hcenter) q :=
  b.onQuotient_isEquivariant q _

/-- Equivariance uniquely determines the action on the supplied quotient. -/
theorem onCenterQuotient_unique (c : AutomorphicAction S Q)
    (hc : b.IsEquivariant c q) : c = b.onCenterQuotient q hcenter :=
  b.onQuotient_unique q _ c hc

end AutomorphicAction

namespace IsAdjointQuotient

variable {k : Type u} [Field k]
    {S G Q : GroupScheme (Spec (CommRingCat.of k))}
    {q : G ⟶ Q} (hq : IsAdjointQuotient q)

/-- The canonical actual action on a supplied adjoint quotient, with no
smoothness hypothesis on its full central kernel. -/
def action (b : AutomorphicAction S G) : AutomorphicAction S Q := by
  letI := hq.flat
  letI := hq.surjective
  letI := hq.isConnectedReductive.isAffineHom
  letI := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  exact b.onCenterQuotient q hq.kernel_range_eq_center

/-- The adjoint quotient intertwines the source and canonical target actions
on every test scheme. -/
theorem action_isEquivariant (b : AutomorphicAction S G) :
    b.IsEquivariant (hq.action b) q := by
  let := hq.flat
  let := hq.surjective
  let := hq.isConnectedReductive.isAffineHom
  let := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  intro T s g
  exact b.onCenterQuotient_isEquivariant q hq.kernel_range_eq_center s g

/-- A supplied compatible action on the adjoint quotient is the canonical one. -/
theorem action_unique (b : AutomorphicAction S G) (c : AutomorphicAction S Q)
    (hc : b.IsEquivariant c q) : c = hq.action b := by
  let := hq.flat
  let := hq.surjective
  let := hq.isConnectedReductive.isAffineHom
  let := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  exact b.onCenterQuotient_unique q hq.kernel_range_eq_center c hc

variable {H R : GroupScheme (Spec (CommRingCat.of k))} {p : H ⟶ R}

/-- An equivariant homomorphism and a commuting square of supplied adjoint
quotients induce equivariance on the quotients, even for nonsmooth kernels.
The descended homomorphism is supplied; its existence and closedness are
separate from this compatibility assertion. -/
theorem action_isEquivariant_of_square (hp : IsAdjointQuotient p)
    (b : AutomorphicAction S G) (c : AutomorphicAction S H)
    (i : H ⟶ G) (j : R ⟶ Q) (hsq : i ≫ q = p ≫ j)
    (hi : c.IsEquivariant b i) :
    (hp.action c).IsEquivariant (hq.action b) j := by
  let := hp.flat
  let := hp.surjective
  let := hp.isConnectedReductive.isAffineHom
  let := hp.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsAffine R.X.left := isAffine_of_isAffineHom R.X.hom
  have hs : i.hom.hom ≫ q.hom.hom = p.hom.hom ≫ j.hom.hom :=
    congrArg (fun f => f.hom.hom) hsq
  intro T s x
  apply AutomorphicAction.hom_ext_of_local_quotient_lift p x
  intro U a y hy
  simp only [← Category.assoc, (hp.action c).naturality,
    (hq.action b).naturality]
  rw [hy, ← hp.action_isEquivariant c, Category.assoc, ← hs,
    ← Category.assoc, hi, Category.assoc, hq.action_isEquivariant b]
  simp only [Category.assoc, hs]

end IsAdjointQuotient

end Langlands.GroupScheme
