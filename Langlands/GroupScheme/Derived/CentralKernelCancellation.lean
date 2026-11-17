import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupScheme.SemidirectProduct

/-! # Cancellation through central kernels for perfect source groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section ArbitraryBase

variable {S S' : Scheme.{u}} {C H G : GroupScheme S}

/-- The difference of two homomorphisms with the same composite is multiplicative
when the full kernel of the composite map is central. -/
theorem kernelDifference_isMonHom
    (q : H ⟶ G) (hq : IsCentral (kernelι q))
    (a b : C ⟶ H) (hab : a ≫ q = b ≫ q) :
    IsMonHom (kernelDifference q a b hab) := by
  apply Semidirect.isMonHom_of_mul_comp
  intro T x y
  apply (cancel_mono (kernelι q).hom.hom).mp
  simp only [Category.assoc, kernelDifference_comp, GrpObj.comp_div, MonObj.mul_comp]
  have hk : (y ≫ a.hom.hom / (y ≫ b.hom.hom)) ≫ q.hom.hom = 1 := by
    rw [GrpObj.div_comp, Category.assoc, Category.assoc,
      ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hab, div_self']
  have hc := commute_of_mem_center
    ((isCentral_kernelι_iff q).mp hq T _ hk) (x ≫ b.hom.hom)⁻¹
  calc
    ((x ≫ a.hom.hom) * (y ≫ a.hom.hom)) /
        ((x ≫ b.hom.hom) * (y ≫ b.hom.hom)) =
        (x ≫ a.hom.hom) *
          ((y ≫ a.hom.hom / (y ≫ b.hom.hom)) * (x ≫ b.hom.hom)⁻¹) := by
            simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
    _ = (x ≫ a.hom.hom) *
          ((x ≫ b.hom.hom)⁻¹ * (y ≫ a.hom.hom / (y ≫ b.hom.hom))) := by rw [hc.eq]
    _ = (x ≫ a.hom.hom / (x ≫ b.hom.hom)) *
          (y ≫ a.hom.hom / (y ≫ b.hom.hom)) := by
            simp only [div_eq_mul_inv, mul_assoc]

/-- The actual kernel-valued difference homomorphism for two lifts through a
homomorphism with central kernel. -/
def centralKernelDifference
    (q : H ⟶ G) (hq : IsCentral (kernelι q))
    (a b : C ⟶ H) (hab : a ≫ q = b ≫ q) : C ⟶ kernel q :=
  letI := kernelDifference_isMonHom q hq a b hab
  Grp.homMk (kernelDifference q a b hab)

/-- The constructed difference has the prescribed underlying quotient of maps. -/
theorem centralKernelDifference_comp
    (q : H ⟶ G) (hq : IsCentral (kernelι q))
    (a b : C ⟶ H) (hab : a ≫ q = b ≫ q) :
    (centralKernelDifference q hq a b hab).hom.hom ≫ (kernelι q).hom.hom =
      a.hom.hom / b.hom.hom :=
  kernelDifference_comp q a b hab

/-- A perfect group admits at most one lift through a homomorphism whose full
kernel is central and separated, over any base scheme. -/
theorem centralKernel_cancel_of_perfect
    (hC : derivedSubgroup C = ⊤) (q : H ⟶ G)
    (hq : IsCentral (kernelι q)) [IsSeparated (kernel q).X.hom]
    {a b : C ⟶ H} (hab : a ≫ q = b ≫ q) : a = b := by
  let : IsCommMonObj (kernel q).X := hq.isCommMonObj
  have hid : IsDerivedSubgroup (𝟙 C) :=
    ⟨(derivedSubgroup_total_admissible C).1, (SubgroupFunctor.range_id C).trans hC.symm⟩
  have hd : centralKernelDifference q hq a b hab = 1 := by
    simpa only [Category.id_comp] using
      hid.comp_eq_one (centralKernelDifference q hq a b hab)
  have hd' : kernelDifference q a b hab = 1 :=
    congrArg (fun f : C ⟶ kernel q => f.hom.hom) hd
  apply Grp.hom_ext
  apply div_eq_one.mp
  rw [← kernelDifference_comp q a b hab, hd', MonObj.one_comp]

/-- Centrality of the actual kernel is preserved by every base change. -/
theorem IsCentral.kernel_baseChange
    {q : H ⟶ G} (hq : IsCentral (kernelι q)) (b : S' ⟶ S) :
    IsCentral (kernelι ((GroupScheme.baseChange b).map q)) := by
  have hc := (hq.baseChange b).comp (kernelBaseChangeIso b q).inv
  simpa only [kernelBaseChangeIso_inv_ι] using hc

end ArbitraryBase

section Field

variable {k : Type u} [Field k] {S : Scheme.{u}}
  {C H G : GroupScheme (Spec (CommRingCat.of k))}

/-- Perfectness of an affine field group persists under every affine change of
base, including scalar extensions to nonreduced algebras. -/
theorem derivedSubgroup_eq_top_baseChange
    [IsAffineHom C.X.hom] (hC : derivedSubgroup C = ⊤)
    (b : S ⟶ Spec (CommRingCat.of k)) [IsAffineHom b] :
    derivedSubgroup ((GroupScheme.baseChange b).obj C) = ⊤ := by
  rw [← derivedSubgroup_baseChange_eq_of_field b C, hC, SubgroupFunctor.top_baseChange]

/-- Homomorphisms from a semisimple field group remain cancellable through a
central kernel after an arbitrary affine change of base. -/
theorem IsSemisimple.centralKernel_cancel_baseChange
    (hC : IsSemisimple C) (q : H ⟶ G) (hq : IsCentral (kernelι q))
    (b : S ⟶ Spec (CommRingCat.of k)) [IsAffineHom b]
    [IsSeparated (kernel ((GroupScheme.baseChange b).map q)).X.hom]
    {a a' : (GroupScheme.baseChange b).obj C ⟶ (GroupScheme.baseChange b).obj H}
    (haa' : a ≫ (GroupScheme.baseChange b).map q =
      a' ≫ (GroupScheme.baseChange b).map q) : a = a' := by
  let : IsAffineHom C.X.hom := hC.isConnectedReductive.isAffineHom
  exact centralKernel_cancel_of_perfect
    (derivedSubgroup_eq_top_baseChange (semisimplePerfect k C hC) b)
    ((GroupScheme.baseChange b).map q) (hq.kernel_baseChange b) haa'

end Field

end Langlands.GroupScheme
