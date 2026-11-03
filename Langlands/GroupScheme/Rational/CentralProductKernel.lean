import Langlands.GroupScheme.Rational.OrderedProductDescent
import Langlands.GroupScheme.Rational.SemigroupTransport
import Langlands.GroupScheme.Rational.FppfQuotientSmooth

/-! # Actual factor kernels and central ordered-product descent -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section KernelFactor

variable {B : Scheme.{u}} {G Q Z H R : GroupScheme B}
    (q : G ⟶ Q) (z : Z ⟶ G)
    (hz : (SubgroupFunctor.range (kernelι q)).IsRepresentedBy z)
    (j : H ⟶ G) (l : R ⟶ Q) (p : H ⟶ R)
    (h : j ≫ q = p ≫ l)

include h in
/-- The kernel of a factor quotient maps into the represented ambient kernel. -/
theorem range_factorKernel_le :
    SubgroupFunctor.range (kernelι p ≫ j) ≤ SubgroupFunctor.range (kernelι q) := by
  rintro T x ⟨y, rfl⟩
  change T ⟶ (kernel p).X at y
  apply (mem_range_kernelι_iff q _).mpr
  have hp := (kernelPointsEquiv p T y).property
  change (y ≫ (kernelι p).hom.hom) ≫ p.hom.hom = 1 at hp
  have hh := congrArg (fun f => f.hom.hom) h
  change j.hom.hom ≫ q.hom.hom = p.hom.hom ≫ l.hom.hom at hh
  change (y ≫ (kernelι p).hom.hom ≫ j.hom.hom) ≫ q.hom.hom = 1
  calc
    ((y ≫ (kernelι p).hom.hom) ≫ j.hom.hom) ≫ q.hom.hom =
        (y ≫ (kernelι p).hom.hom) ≫ (j.hom.hom ≫ q.hom.hom) :=
      Category.assoc _ _ _
    _ = (y ≫ (kernelι p).hom.hom) ≫ (p.hom.hom ≫ l.hom.hom) := by rw [hh]
    _ = ((y ≫ (kernelι p).hom.hom) ≫ p.hom.hom) ≫ l.hom.hom :=
      (Category.assoc _ _ _).symm
    _ = 1 := by rw [hp, MonObj.one_comp]

/-- The canonical actual factor-kernel map into a chosen ambient kernel. -/
def factorKernelHom : kernel p ⟶ Z :=
  hz.factorHom (kernelι p ≫ j) (range_factorKernel_le q j l p h)

/-- The actual factor-kernel map retains its original ambient inclusion. -/
theorem factorKernelHom_comp :
    factorKernelHom q z hz j l p h ≫ z = kernelι p ≫ j :=
  hz.factorHom_comp _ _

/-- If the quotient-factor inclusion is monic, the factor kernel represents
exactly the original factor's preimage in the ambient kernel. -/
theorem factorKernelHom_isRepresentedBy
    {F : SubgroupFunctor G} (hj : F.IsRepresentedBy j) [Mono l.hom.hom] :
    (F.comap z).IsRepresentedBy (factorKernelHom q z hz j l p h) := by
  let v := factorKernelHom q z hz j l p h
  have hv : v.hom.hom ≫ z.hom.hom = (kernelι p).hom.hom ≫ j.hom.hom :=
    congrArg (fun f => f.hom.hom) (factorKernelHom_comp q z hz j l p h)
  let : Mono j.hom.hom := hj.1
  refine ⟨mono_of_mono_fac hv, ?_⟩
  ext T x
  constructor
  · rintro ⟨y, rfl⟩
    change T ⟶ (kernel p).X at y
    change (y ≫ v.hom.hom) ≫ z.hom.hom ∈ F.carrier T
    rw [Category.assoc, hv, ← hj.2]
    refine ⟨y ≫ (kernelι p).hom.hom, ?_⟩
    change (y ≫ (kernelι p).hom.hom) ≫ j.hom.hom =
      y ≫ (kernelι p).hom.hom ≫ j.hom.hom
    exact Category.assoc _ _ _
  · intro hx
    change x ≫ z.hom.hom ∈ F.carrier T at hx
    rw [← hj.2] at hx
    obtain ⟨y, hy⟩ := hx
    change y ≫ j.hom.hom = x ≫ z.hom.hom at hy
    have hzq : (x ≫ z.hom.hom) ≫ q.hom.hom = 1 :=
      (mem_range_kernelι_iff q _).mp (hz.pointsHom T x).property
    have hh := congrArg (fun f => f.hom.hom) h
    change j.hom.hom ≫ q.hom.hom = p.hom.hom ≫ l.hom.hom at hh
    have hyp : y ≫ p.hom.hom = 1 := by
      apply (cancel_mono l.hom.hom).mp
      rw [MonObj.one_comp, Category.assoc, ← hh, ← Category.assoc, hy]
      exact hzq
    let t := (kernelPointsEquiv p T).symm ⟨y, hyp⟩
    have ht : t ≫ (kernelι p).hom.hom = y :=
      congrArg Subtype.val ((kernelPointsEquiv p T).apply_symm_apply ⟨y, hyp⟩)
    refine ⟨t, ?_⟩
    apply hz.1.right_cancellation
    change (t ≫ v.hom.hom) ≫ z.hom.hom = x ≫ z.hom.hom
    rw [Category.assoc, hv, ← Category.assoc, ht, hy]

end KernelFactor

section Representatives

variable {B : Scheme.{u}} {G : GroupScheme B} {n : ℕ}
    {H R : Fin n → GroupScheme B}

/-- Replacing each factor by any representative of the same all-test subgroup
preserves the original ordered-product isomorphism. -/
theorem isIso_orderedMultiplication_of_same_representatives
    (F : Fin n → SubgroupFunctor G) (j : ∀ r, H r ⟶ G) (l : ∀ r, R r ⟶ G)
    (hj : ∀ r, (F r).IsRepresentedBy (j r))
    (hl : ∀ r, (F r).IsRepresentedBy (l r))
    (hprod : IsIso (orderedMultiplication j)) : IsIso (orderedMultiplication l) := by
  let e : ∀ r, H r ≅ R r := fun r => (hj r).isoOfIsRepresentedBy (hl r)
  have he (r : Fin n) : j r ≫ 𝟙 G = (e r).hom ≫ l r := by
    simpa only [Category.comp_id] using
      ((hj r).isoOfIsRepresentedBy_hom_comp (hl r)).symm
  apply (isIso_orderedMultiplication_iff l).mpr
  intro T
  let E : (∀ r, T ⟶ (H r).X) ≃ (∀ r, T ⟶ (R r).X) :=
    Equiv.piCongrRight (fun r => (isoPointsEquiv (e r) T).toEquiv)
  have hm : (orderedPoints l (T := T)) ∘ E = orderedPoints j := by
    funext x
    have hh := orderedPoints_map j l (𝟙 G) (fun r => (e r).hom) he x
    have hE : E x = fun r => x r ≫ (e r).hom.hom.hom := by
      funext r
      exact isoPointsEquiv_apply (e r) T (x r)
    simpa only [Function.comp_apply, hE,
      Grp.id_hom_hom, Category.comp_id] using hh.symm
  exact (Function.Bijective.of_comp_iff _ E.bijective).mp
    (hm.symm ▸ (isIso_orderedMultiplication_iff j).mp hprod T)

end Representatives

end Langlands.GroupScheme.RelativeRoot
