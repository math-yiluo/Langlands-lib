import Langlands.GroupScheme.HopfPrimitiveQuotient
import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.UnipotentClosedSubgroupStatement

/-! # Formal assembly of a unipotent kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Kernel

variable {S : Scheme.{u}} {G H P : GroupScheme S}

/-- A homomorphism killed by `q` has its full range in the scheme-theoretic kernel. -/
theorem range_le_kernelι_of_comp_eq_zero (w : P ⟶ G) (q : G ⟶ H)
    (hw : w ≫ q = 0) :
    SubgroupFunctor.range w ≤ SubgroupFunctor.range (kernelι q) := by
  rintro T x ⟨y, rfl⟩
  change T ⟶ P.X at y
  apply (mem_range_kernelι_iff q _).mpr
  change (y ≫ w.hom.hom) ≫ q.hom.hom = 1
  rw [Category.assoc, ← Grp.comp_hom_hom, hw]
  change y ≫ (1 : P.X ⟶ H.X) = 1
  exact MonObj.comp_one y

/-- The map between kernels induced by precomposing a homomorphism. -/
def kernelCompHom (j : G ⟶ P) (q : P ⟶ H) : kernel (j ≫ q) ⟶ kernel q :=
  pullback.lift (kernelι (j ≫ q) ≫ j) (pullback.snd (j ≫ q) (kernelUnit H)) (by
    change (pullback.fst (j ≫ q) (kernelUnit H) ≫ j) ≫ q = _
    rw [Category.assoc, pullback.condition]
    rfl)

@[simp] theorem kernelCompHom_comp_kernelι (j : G ⟶ P) (q : P ⟶ H) :
    kernelCompHom j q ≫ kernelι q = kernelι (j ≫ q) ≫ j := by
  apply pullback.lift_fst

/-- A closed subgroup induces a closed subgroup between these kernels. -/
theorem isClosedSubgroup_kernelCompHom (j : G ⟶ P) (q : P ⟶ H)
    [IsSeparated H.X.hom] (hj : IsClosedSubgroup j) :
    IsClosedSubgroup (kernelCompHom j q) := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion
      ((kernelCompHom j q).hom.hom.left ≫ (kernelι q).hom.hom.left) := by
    change IsClosedImmersion ((kernelCompHom j q ≫ kernelι q).hom.hom.left)
    rw [kernelCompHom_comp_kernelι]
    change IsClosedImmersion ((kernelι (j ≫ q)).hom.hom.left ≫ j.hom.hom.left)
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (kernelCompHom j q).hom.hom.left (kernelι q).hom.hom.left

/-- The induced kernel map, expressed in any isomorphic presentation of the ambient kernel. -/
def kernelCompTo {U : GroupScheme S} (j : G ⟶ P) (q : P ⟶ H) (e : U ≅ kernel q) :
    kernel (j ≫ q) ⟶ U :=
  kernelCompHom j q ≫ e.inv

/-- A closed subgroup remains closed after changing the ambient kernel presentation. -/
theorem isClosedSubgroup_kernelCompTo {U : GroupScheme S} (j : G ⟶ P) (q : P ⟶ H)
    (e : U ≅ kernel q) [IsSeparated H.X.hom] (hj : IsClosedSubgroup j) :
    IsClosedSubgroup (kernelCompTo j q e) := by
  have : IsClosedImmersion (kernelCompHom j q).hom.hom.left :=
    isClosedSubgroup_kernelCompHom j q hj
  have : IsIso e.inv.hom.hom.left :=
    ((Grp.forget (Over S)) ⋙ Over.forget S).map_isIso e.inv
  change IsClosedImmersion ((kernelCompHom j q).hom.hom.left ≫ e.inv.hom.hom.left)
  infer_instance

end Kernel

section Field

variable {k : Type u} [Field k]
  {G T : GroupScheme (Spec (CommRingCat.of k))}

/-- Every unipotent group mapping into `G` lies in the kernel of a split-torus-valued map. -/
theorem IsUnipotent.range_le_kernelι_of_isSplitTorus
    {W : GroupScheme (Spec (CommRingCat.of k))} (hW : IsUnipotent W)
    (hT : IsSplitTorus T) (w : W ⟶ G) (q : G ⟶ T) :
    SubgroupFunctor.range w ≤ SubgroupFunctor.range (kernelι q) :=
  range_le_kernelι_of_comp_eq_zero w q (hW.hom_eq_zero_of_isSplitTorus hT (w ≫ q))

/-- Closed-subgroup inheritance transfers unipotence from an ambient kernel presentation. -/
theorem isUnipotent_kernel_comp_of_closedSubgroup
    (hsub : UnipotentClosedSubgroupStatement.{u})
    {P U : GroupScheme (Spec (CommRingCat.of k))}
    (j : G ⟶ P) (q : P ⟶ T) (e : U ≅ kernel q)
    [IsSeparated T.X.hom] [IsAffineHom U.X.hom] [LocallyOfFiniteType U.X.hom]
    (hj : IsClosedSubgroup j) (hu : IsUnipotent U) :
    IsUnipotent (kernel (j ≫ q)) :=
  hsub k U (kernel (j ≫ q)) (kernelCompTo j q e)
    (isClosedSubgroup_kernelCompTo j q e hj) hu

/-- Smoothness, connectedness and unipotence of a split-torus kernel suffice to assemble
all properties required of a unipotent part, including all-test maximality. -/
theorem exists_unipotent_part_of_split_torus_kernel (q : G ⟶ T) (hT : IsSplitTorus T)
    (hs : Smooth (kernel q).X.hom) (hc : ConnectedSpace (kernel q).X.left)
    (hu : IsUnipotent (kernel q)) :
    ∃ (Hu : GroupScheme (Spec (CommRingCat.of k))) (h : Hu ⟶ G),
      IsClosedSubgroup h ∧ Smooth Hu.X.hom ∧ ConnectedSpace Hu.X.left ∧ IsUnipotent Hu ∧
        (SubgroupFunctor.range h).IsNormal ∧
        ∀ (W : GroupScheme (Spec (CommRingCat.of k))) (w : W ⟶ G),
          IsClosedSubgroup w → IsUnipotent W →
            SubgroupFunctor.range w ≤ SubgroupFunctor.range h := by
  have : IsAffineHom T.X.hom := hT.isAffineHom
  refine ⟨kernel q, kernelι q, ?_, hs, hc, hu, HopfPrimitive.isNormal_range_kernelι q, ?_⟩
  · change IsClosedImmersion (kernelι q).hom.hom.left
    infer_instance
  · intro W w _ hW
    exact hW.range_le_kernelι_of_isSplitTorus hT w q

end Field

end Langlands.GroupScheme
