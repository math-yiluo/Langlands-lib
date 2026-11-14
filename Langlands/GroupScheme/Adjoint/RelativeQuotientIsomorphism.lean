import Langlands.GroupScheme.Adjoint.QuotientDescent
import Langlands.GroupScheme.Adjoint.CenterQuotientReduction
import Langlands.GroupScheme.Adjoint.LocalIsomorphism
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Isomorphisms on full-centre fppf quotients over arbitrary bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace RelativeRoot.IsFppfQuotient

variable {S : Scheme.{u}} {G H A B : GroupScheme S}
    {q : G ⟶ A} {p : H ⟶ B}
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (hp : RelativeRoot.IsFppfQuotient (center H) p)

include hq in
/-- The supplied quotient kills the full scheme-theoretic centre on every test. -/
theorem killsCenter : KillsCenter q := by
  intro T x hx
  apply (mem_range_kernelι_iff q x).mp
  rw [hq.2.2.2]
  exact hx

/-- Descent of group homomorphisms through a full-centre fppf quotient.
The range equality alone suffices; a closed kernel representative is not needed. -/
def desc {K : GroupScheme S} (f : G ⟶ K) (hf : KillsCenter f) : A ⟶ K := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  let d := CenterQuotientDescent.overHom q hq.2.2.2
    f.hom.hom hf.isInvariantUnderCenter
  have hd : q.hom.hom ≫ d = f.hom.hom :=
    CenterQuotientDescent.fac_overHom q hq.2.2.2
      f.hom.hom hf.isInvariantUnderCenter
  haveI : IsMonHom d := {
    one_hom := by
      rw [← IsMonHom.one_hom q.hom.hom, Category.assoc, hd,
        IsMonHom.one_hom]
    mul_hom := by
      have := CenterQuotientDescent.epi_tensorHom (q := q)
      apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom)).mp
      rw [← IsMonHom.mul_hom_assoc, hd, IsMonHom.mul_hom,
        tensorHom_comp_tensorHom_assoc, hd] }
  exact Grp.homMk d

@[reassoc]
theorem comp_desc {K : GroupScheme S} (f : G ⟶ K) (hf : KillsCenter f) :
    q ≫ hq.desc f hf = f := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  exact Grp.hom_ext _ _ (CenterQuotientDescent.fac_overHom q hq.2.2.2
    f.hom.hom hf.isInvariantUnderCenter)

include hq in
/-- Equality of quotient homomorphisms is checked after the fppf quotient map. -/
theorem hom_ext {K : GroupScheme S} {f g : A ⟶ K}
    (h : q ≫ f = q ≫ g) : f = g := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi q.hom.hom.left).mp
  exact congrArg (fun z => z.hom.hom.left) h

include hp in
/-- An isomorphism followed by the target quotient kills the source centre. -/
theorem killsCenter_iso_comp (e : G ≅ H) : KillsCenter (e.hom ≫ p) := by
  intro T x hx
  change (x ≫ e.hom.hom.hom) ≫ p.hom.hom = 1
  exact hp.killsCenter T _ (mem_center_comp_iso e hx)

/-- An isomorphism of groups induces an isomorphism of supplied full-centre quotients. -/
def mapIso (e : G ≅ H) : A ≅ B where
  hom := hq.desc (e.hom ≫ p) (hp.killsCenter_iso_comp e)
  inv := hp.desc (e.inv ≫ q) (hq.killsCenter_iso_comp e.symm)
  hom_inv_id := by
    apply hq.hom_ext
    rw [← Category.assoc, comp_desc, Category.assoc, comp_desc,
      ← Category.assoc, e.hom_inv_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply hp.hom_ext
    rw [← Category.assoc, comp_desc, Category.assoc, comp_desc,
      ← Category.assoc, e.inv_hom_id, Category.id_comp, Category.comp_id]

/-- The induced quotient isomorphism commutes with the given quotient maps. -/
theorem comp_mapIso_hom (e : G ≅ H) :
    q ≫ (hq.mapIso hp e).hom = e.hom ≫ p :=
  hq.comp_desc _ (hp.killsCenter_iso_comp e)

/-- The inverse quotient isomorphism also commutes with the given quotient maps. -/
theorem comp_mapIso_inv (e : G ≅ H) :
    p ≫ (hq.mapIso hp e).inv = e.inv ≫ q :=
  hp.comp_desc _ (hq.killsCenter_iso_comp e.symm)

/-- The quotient square uniquely determines the induced isomorphism. -/
theorem mapIso_unique (e : G ≅ H) (d : A ≅ B)
    (hd : q ≫ d.hom = e.hom ≫ p) : d = hq.mapIso hp e := by
  apply Iso.ext
  exact hq.hom_ext (hd.trans (hq.comp_mapIso_hom hp e).symm)

/-- Natural local group isomorphisms induce local isomorphisms of full-centre quotients. -/
def localIso {U : Over S} (e : LocalGroupIso G H U) : LocalGroupIso A B U :=
  LocalGroupIso.ofBaseChangeIso
    ((hq.baseChange_center U.hom).mapIso (hp.baseChange_center U.hom) e.toBaseChangeIso)

/-- The induced local family commutes with the quotient maps on every relative test. -/
theorem localIso_square {U T : Over S} (e : LocalGroupIso G H U)
    (a : T ⟶ U) (g : T ⟶ G.X) :
    (hq.localIso hp e).toFun a (g ≫ q.hom.hom) =
      e.toFun a g ≫ p.hom.hom := by
  have h := LocalGroupIso.ofBaseChangeIso_square q p e.toBaseChangeIso
    ((hq.baseChange_center U.hom).mapIso (hp.baseChange_center U.hom) e.toBaseChangeIso)
    ((hq.baseChange_center U.hom).comp_mapIso_hom (hp.baseChange_center U.hom)
      e.toBaseChangeIso) a g
  rw [LocalGroupIso.ofBaseChangeIso_toBaseChangeIso] at h
  exact h

end RelativeRoot.IsFppfQuotient
end Langlands.GroupScheme
