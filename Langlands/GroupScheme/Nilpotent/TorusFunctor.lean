import Langlands.GroupScheme.Nilpotent.CentralQuotient

/-! # Canonical maps between central maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G H K : GroupScheme (Spec (CommRingCat.of k))}

namespace NilpotentCentralTorusQuotientData

variable (D : NilpotentCentralTorusQuotientData G)

/-- The chosen closed torus represents its all-test range. -/
theorem represented_torus :
    (SubgroupFunctor.range D.inclusion).IsRepresentedBy D.inclusion := by
  have : IsClosedImmersion D.inclusion.hom.hom.left := D.maximal_torus.2.1
  exact ⟨Over.mono_of_mono_left _, rfl⟩

/-- Every torus homomorphism into the ambient group lands in the chosen torus. -/
theorem torus_range_le (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsTorus T.toGrp) (f : T.toGrp ⟶ G) :
    SubgroupFunctor.range f ≤ SubgroupFunctor.range D.inclusion := by
  intro U x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← D.fppf_quotient.2.2.2, mem_range_kernelι_iff, Category.assoc,
    ← Grp.comp_hom_hom]
  have ht : t ≫ (f ≫ D.projection).hom.hom ∈
      (SubgroupFunctor.range (f ≫ D.projection)).carrier U :=
    SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩
  rwa [D.no_tori T hT _, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at ht

/-- Factor any torus homomorphism through the chosen torus inclusion. -/
def torusFactor (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsTorus T.toGrp) (f : T.toGrp ⟶ G) : T.toGrp ⟶ D.torus.toGrp :=
  D.represented_torus.factorHom f (D.torus_range_le T hT f)

@[simp] theorem torusFactor_comp (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsTorus T.toGrp) (f : T.toGrp ⟶ G) :
    D.torusFactor T hT f ≫ D.inclusion = f :=
  D.represented_torus.factorHom_comp f (D.torus_range_le T hT f)

/-- The torus factorization is determined by its composite with the inclusion. -/
theorem torusFactor_unique (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsTorus T.toGrp) (f : T.toGrp ⟶ G)
    (a : T.toGrp ⟶ D.torus.toGrp) (ha : a ≫ D.inclusion = f) :
    a = D.torusFactor T hT f :=
  D.represented_torus.hom_ext (ha.trans (D.torusFactor_comp T hT f).symm)

variable (E : NilpotentCentralTorusQuotientData H)

/-- Every ambient homomorphism induces a unique homomorphism of the chosen tori. -/
def torusMap (f : G ⟶ H) : D.torus.toGrp ⟶ E.torus.toGrp :=
  E.torusFactor D.torus D.maximal_torus.1 (D.inclusion ≫ f)

@[simp] theorem torusMap_comp_inclusion (f : G ⟶ H) :
    D.torusMap E f ≫ E.inclusion = D.inclusion ≫ f :=
  E.torusFactor_comp _ _ _

/-- Maps into the chosen torus are determined by the ambient inclusion. -/
theorem torusMap_unique (f : G ⟶ H) (a : D.torus.toGrp ⟶ E.torus.toGrp)
    (ha : a ≫ E.inclusion = D.inclusion ≫ f) : a = D.torusMap E f :=
  E.represented_torus.hom_ext (ha.trans (D.torusMap_comp_inclusion E f).symm)

@[simp] theorem torusMap_id : D.torusMap D (𝟙 G) = 𝟙 D.torus.toGrp := by
  apply D.represented_torus.hom_ext
  simp only [torusMap_comp_inclusion, Category.comp_id, Category.id_comp]

@[simp] theorem torusMap_comp (F : NilpotentCentralTorusQuotientData K)
    (f : G ⟶ H) (g : H ⟶ K) :
    D.torusMap F (f ≫ g) = D.torusMap E f ≫ E.torusMap F g := by
  apply F.represented_torus.hom_ext
  simp only [Category.assoc, torusMap_comp_inclusion]
  rw [← Category.assoc (D.torusMap E f), torusMap_comp_inclusion, Category.assoc]

/-- An ambient isomorphism induces an actual isomorphism of the chosen tori. -/
def torusMapIso (e : G ≅ H) : D.torus.toGrp ≅ E.torus.toGrp where
  hom := D.torusMap E e.hom
  inv := E.torusMap D e.inv
  hom_inv_id := by
    rw [← torusMap_comp, e.hom_inv_id, torusMap_id]
  inv_hom_id := by
    rw [← torusMap_comp, e.inv_hom_id, torusMap_id]

@[simp] theorem torusMapIso_hom_comp (e : G ≅ H) :
    (D.torusMapIso E e).hom ≫ E.inclusion = D.inclusion ≫ e.hom :=
  D.torusMap_comp_inclusion E e.hom

/-- Two choices over the same ambient group are uniquely isomorphic over that group. -/
def torusIso (E : NilpotentCentralTorusQuotientData G) : D.torus.toGrp ≅ E.torus.toGrp :=
  D.torusMapIso E (Iso.refl G)

@[simp] theorem torusIso_hom_comp (E : NilpotentCentralTorusQuotientData G) :
    (D.torusIso E).hom ≫ E.inclusion = D.inclusion := by
  change D.torusMap E (𝟙 G) ≫ E.inclusion = D.inclusion
  simpa only [Category.comp_id] using D.torusMap_comp_inclusion E (𝟙 G)

/-- Every maximal torus of the ambient group is the chosen torus as a subgroup functor. -/
theorem maximal_torus_range_eq
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) : SubgroupFunctor.range i = SubgroupFunctor.range D.inclusion := by
  let a := D.torusFactor T hi.1 i
  have ha : a ≫ D.inclusion = i := D.torusFactor_comp T hi.1 i
  have : IsIso a := hi.2.2 D.torus D.inclusion a
    D.maximal_torus.1 D.maximal_torus.2.1 ha
  rw [← ha]
  exact SubgroupFunctor.range_iso_comp (asIso a) D.inclusion

/-- The chosen torus range is invariant under every ambient automorphism over the base field. -/
theorem torus_range_comp_aut (e : G ≅ G) :
    SubgroupFunctor.range (D.inclusion ≫ e.hom) = SubgroupFunctor.range D.inclusion := by
  rw [← D.torusMap_comp_inclusion D e.hom]
  exact SubgroupFunctor.range_iso_comp (D.torusMapIso D e) D.inclusion

end NilpotentCentralTorusQuotientData

end Langlands.GroupScheme
