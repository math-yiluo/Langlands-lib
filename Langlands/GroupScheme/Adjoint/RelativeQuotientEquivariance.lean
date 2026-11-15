import Langlands.GroupScheme.Adjoint.RelativeQuotientIsomorphism
import Langlands.GroupScheme.RelativeInnerCocycle
import Langlands.GroupScheme.Rational.InnerDiscrepancyComposition

/-! # Inner-discrepancy transport through relative full-centre quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot.IsFppfQuotient

variable {S : Scheme.{u}} {G H K A B : GroupScheme S} {U V : Over S}
    {q : G ⟶ A} {p : H ⟶ B}
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (hp : RelativeRoot.IsFppfQuotient (center H) p)
    (a : AutomorphicAction A G) (b : AutomorphicAction B H)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G))
    (hb : b.restrict p = AutomorphicAction.conjugation (𝟙 H))

include hq hp ha hb

/-- The supplied central-quotient actions are intertwined by the original and induced
local isomorphisms on every test scheme. -/
theorem localIso_equivariant (e : LocalGroupIso G H U)
    {T : Over S} (c : T ⟶ U) (x : T ⟶ A.X) (g : T ⟶ G.X) :
    e.toFun c (a.act x g) = b.act ((hq.localIso hp e).toFun c x) (e.toFun c g) := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  apply AutomorphicAction.hom_ext_of_fppf_quotient_lift q x
  intro W t h ht
  rw [← e.naturality, a.naturality, b.naturality,
    ← (hq.localIso hp e).naturality, ← e.naturality,
    ht, AutomorphicAction.centralQuotient_act_lift q a ha,
    hq.localIso_square hp e, AutomorphicAction.centralQuotient_act_lift p b hb]
  simp only [map_mul, map_inv]

/-- The induced local quotient isomorphism together with its equivariance proof. -/
def equivariantLocalIso (e : LocalGroupIso G H U) :
    {d : LocalGroupIso A B U //
      ∀ {T : Over S} (c : T ⟶ U) (x : T ⟶ A.X) (g : T ⟶ G.X),
        e.toFun c (a.act x g) = b.act (d.toFun c x) (e.toFun c g)} :=
  ⟨hq.localIso hp e, hq.localIso_equivariant hp a b ha hb e⟩

/-- Innerness passes to the inverse family for the specified central-quotient actions. -/
theorem hasInnerDiscrepancy_symm (e : LocalGroupIso G H U)
    (he : e.HasInnerDiscrepancy a) : e.symm.HasInnerDiscrepancy b :=
  LocalGroupIso.HasInnerDiscrepancy.symm_of_equivariant e a b
    (hq.localIso hp e) (hq.localIso_equivariant hp a b ha hb e) he

/-- Inner local families compose for full-centre quotients. -/
theorem hasInnerDiscrepancy_trans (e : LocalGroupIso G H U) (f : LocalGroupIso H K U)
    (he : e.HasInnerDiscrepancy a) (hf : f.HasInnerDiscrepancy b) :
    (e.trans f).HasInnerDiscrepancy a :=
  LocalGroupIso.HasInnerDiscrepancy.trans_of_equivariant e a b
    (hq.localIso hp e) (hq.localIso_equivariant hp a b ha hb e) he hf

/-- Two inner local families from one source have an inner comparison family. -/
theorem hasInnerDiscrepancy_compare (e : LocalGroupIso G H U) (f : LocalGroupIso G K U)
    (he : e.HasInnerDiscrepancy a) (hf : f.HasInnerDiscrepancy a) :
    (e.compare f).HasInnerDiscrepancy b :=
  LocalGroupIso.HasInnerDiscrepancy.compare_of_equivariant e a b
    (hq.localIso hp e) (hq.localIso_equivariant hp a b ha hb e) he hf

/-- Composition of inner local families also works after a common cover refinement. -/
theorem hasInnerDiscrepancy_transOnProduct
    (e : LocalGroupIso G H U) (f : LocalGroupIso H K V)
    (he : e.HasInnerDiscrepancy a) (hf : f.HasInnerDiscrepancy b) :
    (e.transOnProduct f).HasInnerDiscrepancy a :=
  LocalGroupIso.HasInnerDiscrepancy.transOnProduct_of_equivariant e a b
    (hq.localIso hp e) (hq.localIso_equivariant hp a b ha hb e) he hf

/-- Inner families on distinct covers have an inner comparison over the fibre product. -/
theorem hasInnerDiscrepancy_compareOnProduct
    (e : LocalGroupIso G H U) (f : LocalGroupIso G K V)
    (he : e.HasInnerDiscrepancy a) (hf : f.HasInnerDiscrepancy a) :
    (e.compareOnProduct f).HasInnerDiscrepancy b :=
  LocalGroupIso.HasInnerDiscrepancy.compareOnProduct_of_equivariant e a b
    (hq.localIso hp e) (hq.localIso_equivariant hp a b ha hb e) he hf

end Langlands.GroupScheme.RelativeRoot.IsFppfQuotient
