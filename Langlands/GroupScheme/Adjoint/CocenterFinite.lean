import Langlands.GroupScheme.SmoothConnectedFiniteKernel
import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.GroupScheme.Derived.CentralIntersectionProof
import Langlands.GroupScheme.ProductProperties

/-! # Finiteness of the joint adjoint and cocenter homomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Joint
variable {S : Scheme.{u}} {G A Q : GroupScheme S}

/-- The kernel of a paired homomorphism is the intersection of the kernels. -/
theorem comp_lift_eq_one_iff (q : G ⟶ A) (p : G ⟶ Q)
    (T : Over S) (x : T ⟶ G.X) :
    x ≫ (lift q p).hom.hom = (1 : T ⟶ (A ⊗ Q).X) ↔
      x ≫ q.hom.hom = 1 ∧ x ≫ p.hom.hom = 1 := by
  change x ≫ lift q.hom.hom p.hom.hom = 1 ↔ _
  constructor
  · intro hx
    constructor
    · have h := congrArg (fun z => z ≫ fst A.X Q.X) hx
      simpa only [Category.assoc, lift_fst, MonObj.one_comp] using h
    · have h := congrArg (fun z => z ≫ snd A.X Q.X) hx
      simpa only [Category.assoc, lift_snd, MonObj.one_comp] using h
  · rintro ⟨hq, hp⟩
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, lift_fst, MonObj.one_comp] using hq
    · simpa only [Category.assoc, lift_snd, MonObj.one_comp] using hp

end Joint

set_option linter.defProp false in
set_option backward.isDefEq.respectTransparency false in
/-- The joint map to an actual full-center adjoint quotient and a quotient by
an actual derived subgroup is finite. -/
@[instance_reducible]
def isFinite_adjoint_cocenter
    {k : Type u} [Field k]
    {G D A Q : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (d : D ⟶ G) (hd : IsDerivedSubgroup d)
    (q : G ⟶ A) (hq : IsAdjointQuotient q)
    (p : G ⟶ Q) (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) p)
    [LocallyOfFiniteType Q.X.hom] [IsAffineHom Q.X.hom] :
    IsFinite (lift q p).hom.hom.left := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let hA := hq.isAdjoint.isSemisimple.isConnectedReductive
  let : IsAffineHom A.X.hom := hA.isAffineHom
  let : Smooth A.X.hom := hA.smooth
  let : IsAffineHom (A ⊗ Q).X.hom := by
    let : IsAffineHom (Limits.pullback.fst A.X.hom Q.X.hom) :=
      MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom Q.X.hom)
    change IsAffineHom (Limits.pullback.fst A.X.hom Q.X.hom ≫ A.X.hom)
    infer_instance
  let : LocallyOfFiniteType (A ⊗ Q).X.hom :=
    prop_tensor_hom (@LocallyOfFiniteType) A.X Q.X inferInstance inferInstance
  obtain ⟨C, c, hc, hcr, hCf⟩ := derivedCentralIntersectionFiniteness k G D d hG hd
  let : IsClosedImmersion c.hom.hom.left := hc
  let : IsClosedImmersion d.hom.hom.left := hd.1
  let : IsClosedImmersion (c ≫ d).hom.hom.left := by
    change IsClosedImmersion (c.hom.hom.left ≫ d.hom.hom.left)
    infer_instance
  let : Mono (c ≫ d).hom.hom := Over.mono_of_mono_left _
  let : IsFinite C.X.hom := hCf
  have hk : SubgroupFunctor.range (c ≫ d) =
      SubgroupFunctor.range (kernelι (lift q p)) := by
    ext T x
    rw [mem_range_kernelι_iff, comp_lift_eq_one_iff]
    constructor
    · rw [SubgroupFunctor.mem_range]
      rintro ⟨z, rfl⟩
      have hz : z ≫ c.hom.hom ∈ ((center G).comap d).carrier T := by
        rw [← hcr]
        exact ⟨z, rfl⟩
      constructor
      · exact (hq.mem_center_iff_comp_eq_one T _).1 hz
      · apply (mem_range_kernelι_iff p _).1
        rw [hp.2.2.2]
        rw [SubgroupFunctor.mem_range]
        exact ⟨z ≫ c.hom.hom, Category.assoc _ _ _⟩
    · rintro ⟨hxq, hxp⟩
      have hxD : x ∈ (SubgroupFunctor.range d).carrier T := by
        rw [← hp.2.2.2]
        exact (mem_range_kernelι_iff p x).2 hxp
      rw [SubgroupFunctor.mem_range] at hxD
      obtain ⟨y, hy⟩ := hxD
      have hyC : y ∈ (SubgroupFunctor.range c).carrier T := by
        rw [hcr]
        change y ≫ d.hom.hom ∈ (center G).carrier T
        rw [hy]
        exact (hq.mem_center_iff_comp_eq_one T x).2 hxq
      rw [SubgroupFunctor.mem_range] at hyC ⊢
      obtain ⟨z, hz⟩ := hyC
      exact ⟨z, by change z ≫ (c.hom.hom ≫ d.hom.hom) = x; rw [← Category.assoc, hz, hy]⟩
  have hr : (SubgroupFunctor.range (c ≫ d)).IsRepresentedBy (c ≫ d) :=
    ⟨inferInstance, rfl⟩
  have hr' : (SubgroupFunctor.range (c ≫ d)).IsRepresentedBy
      (kernelι (lift q p)) := ⟨inferInstance, hk.symm⟩
  let e : C ≅ kernel (lift q p) := hr.isoOfIsRepresentedBy hr'
  let : IsIso e.inv.hom.hom := (Grp.forget (Over _)).map_isIso e.inv
  let : IsIso e.inv.hom.hom.left := (Over.forget _).map_isIso e.inv.hom.hom
  let : IsFinite (kernel (lift q p)).X.hom := by
    rw [← Over.w e.inv.hom.hom]
    infer_instance
  exact isFinite_hom_of_finite_kernel (lift q p)

end Langlands.GroupScheme
