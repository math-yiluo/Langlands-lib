import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Torus.DiagonalizableFixedSmoothStatement

/-! # Smoothness transport for character-kernel centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {B : Scheme.{u}} {H K G : GroupScheme B} (a : AutomorphicAction H G)

/-- Reparametrize the acting group by an actual group-scheme isomorphism. -/
def reparametrize (e : K ≅ H) : AutomorphicAction K G :=
  a.restrict e.hom

@[simp] theorem reparametrize_act (e : K ≅ H) {T : Over B}
    (h : T ⟶ K.X) (g : T ⟶ G.X) :
    (a.reparametrize e).act h g = a.act (h ≫ e.hom.hom.hom) g :=
  a.restrict_act e.hom h g

/-- Restriction along an isomorphism preserves fixedness on every refinement. -/
theorem isFixed_restrict_iso (e : K ≅ H) {T : Over B} (g : T ⟶ G.X) :
    (a.restrict e.hom).IsFixed g ↔ a.IsFixed g := by
  constructor
  · intro hg V b h
    have hh := hg V b (h ≫ e.inv.hom.hom)
    rw [restrict_act] at hh
    have he : (h ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = h := by
      rw [Category.assoc]
      change h ≫ (e.inv ≫ e.hom).hom.hom = h
      rw [e.inv_hom_id]
      exact Category.comp_id h
    rwa [he] at hh
  · intro hg V b h
    simpa only [restrict_act] using hg V b (h ≫ e.hom.hom.hom)

/-- Replacing the acting group by an isomorphic group preserves the actual functor. -/
theorem fixedSubgroup_restrict_iso (e : K ≅ H) :
    (a.restrict e.hom).fixedSubgroup = a.fixedSubgroup := by
  apply SubgroupFunctor.ext
  intro T
  ext g
  exact a.isFixed_restrict_iso e g

theorem fixedSubgroup_reparametrize (e : K ≅ H) :
    (a.reparametrize e).fixedSubgroup = a.fixedSubgroup :=
  a.fixedSubgroup_restrict_iso e

end AutomorphicAction

namespace Diagonalizable

/-- The general diagonalizable smoothness statement applies to any isomorphic
acting group, without a smoothness hypothesis on that group. -/
theorem fixedSubgroup_smooth_of_actingIso
    (h : FixedSubgroupSmoothStatement.{u})
    {k : Type u} [Field k] {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ]
    {H G C : GroupScheme (Spec (CommRingCat.of k))}
    (a : AutomorphicAction H G)
    (e : H ≅ (groupScheme (CommRingCat.of k) Λ).toGrp)
    (hG : Smooth G.X.hom) (hAff : IsAffineHom G.X.hom)
    (j : C ⟶ G) (hj : a.fixedSubgroup.IsRepresentedBy j)
    (hclosed : IsClosedSubgroup j) : Smooth C.X.hom := by
  have hj' : (a.reparametrize e.symm).fixedSubgroup.IsRepresentedBy j := by
    rw [AutomorphicAction.fixedSubgroup_reparametrize]
    exact hj
  exact h k Λ G hG hAff (a.reparametrize e.symm) C j hj' hclosed

end Diagonalizable

namespace RelativeRoot

/-- Smoothness of the represented kernel centralizer reduces to the general
diagonalizable theorem and an actual diagonalizable model of the kernel. -/
theorem kernelCentralizer_smooth_of_diagonalizableIso
    (h : Diagonalizable.FixedSubgroupSmoothStatement.{u})
    {k : Type u} [Field k] {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ G) (a : characterLattice S)
    (e : characterKernel a ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (hG : Smooth G.X.hom) (hAff : IsAffineHom G.X.hom)
    (j : C ⟶ G) (hj : (kernelCentralizer i a).IsRepresentedBy j)
    (hclosed : IsClosedSubgroup j) : Smooth C.X.hom :=
  Diagonalizable.fixedSubgroup_smooth_of_actingIso h
    ((AutomorphicAction.conjugation i).restrict (characterKernelι a))
    e hG hAff j hj hclosed

end RelativeRoot

end Langlands.GroupScheme
