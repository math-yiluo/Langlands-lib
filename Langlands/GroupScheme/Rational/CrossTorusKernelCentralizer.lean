import Langlands.GroupScheme.Rational.CrossTorusRootTransport

/-! # Full character-kernel centralizer transport between acting groups -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}} {S S' : CommGroupScheme B} {G H : GroupScheme B}
variable {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}

/-- Postcomposition along a commuting square preserves commutation with the
entire character kernel, on every scheme test and refinement. -/
theorem comp_mem_kernelCentralizer_of_transport (e : S ≅ S') (f : G ⟶ H)
    (h : i ≫ f = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) {U : Over B} {g : U ⟶ G.X}
    (hg : g ∈ (kernelCentralizer i a).carrier U) :
    g ≫ f.hom.hom ∈ (kernelCentralizer j (characterLattice.congr e a)).carrier U := by
  rw [mem_kernelCentralizer] at hg ⊢
  intro V b c
  have hK : (characterKernelCongr e a).inv ≫ characterKernelι a ≫ i ≫ f =
      characterKernelι (characterLattice.congr e a) ≫ j := by
    rw [← Category.assoc, ← Category.assoc, characterKernelCongr_inv_ι,
      Category.assoc, Category.assoc, h]
    change characterKernelι (characterLattice.congr e a) ≫
      CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ j = _
    rw [Iso.inv_hom_id]
    rfl
  have hc := hg V b (c ≫ (characterKernelCongr e a).inv.hom.hom)
  have hm := congrArg (fun x : V ⟶ G.X => x ≫ f.hom.hom) hc.eq
  simp only [MonObj.mul_comp] at hm
  have hKv : c ≫ (characterKernelCongr e a).inv.hom.hom ≫
      (characterKernelι a ≫ i).hom.hom ≫ f.hom.hom =
      c ≫ (characterKernelι (characterLattice.congr e a) ≫ j).hom.hom := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun k => c ≫ k.hom.hom) hK
  change (b ≫ g ≫ f.hom.hom) * _ = _ * (b ≫ g ≫ f.hom.hom)
  simpa only [Category.assoc, hKv] using hm

/-- A commuting square of isomorphisms identifies the full centralizer functors. -/
theorem kernelCentralizer_comap_of_transport (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) :
    (kernelCentralizer j (characterLattice.congr e a)).comap f.hom =
      kernelCentralizer i a := by
  ext U g
  rw [SubgroupFunctor.mem_comap]
  constructor
  · intro hg
    have hm := comp_mem_kernelCentralizer_of_transport e.symm f.inv
      (inverse_transport_square e f h) (characterLattice.congr e a) hg
    have ha : characterLattice.congr e.symm (characterLattice.congr e a) = a := by
      simp [characterLattice.congr_apply]
    rw [ha] at hm
    simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id] using hm
  · exact comp_mem_kernelCentralizer_of_transport e f.hom h a

/-- Membership in either full centralizer is equivalent under the ambient isomorphism. -/
theorem mem_kernelCentralizer_transport_iff (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) {U : Over B} (g : U ⟶ G.X) :
    g ≫ f.hom.hom.hom ∈ (kernelCentralizer j (characterLattice.congr e a)).carrier U ↔
      g ∈ (kernelCentralizer i a).carrier U := by
  change g ∈ ((kernelCentralizer j (characterLattice.congr e a)).comap f.hom).carrier U ↔ _
  rw [kernelCentralizer_comap_of_transport e f h a]

/-- The actual ambient isomorphism restricts to a multiplicative equivalence
of full character-kernel centralizer points on every scheme test. -/
def kernelCentralizerTransportEquiv (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (U : Over B) :
    (kernelCentralizer i a).carrier U ≃*
      (kernelCentralizer j (characterLattice.congr e a)).carrier U where
  toFun x := ⟨x.val ≫ f.hom.hom.hom,
    comp_mem_kernelCentralizer_of_transport e f.hom h a x.property⟩
  invFun x := ⟨x.val ≫ f.inv.hom.hom, by
    apply (le_of_eq (kernelCentralizer_comap_of_transport e f h a)) U
    change (x.val ≫ f.inv.hom.hom) ≫ f.hom.hom.hom ∈
      (kernelCentralizer j (characterLattice.congr e a)).carrier U
    simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id] using x.property⟩
  left_inv x := Subtype.ext (by
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id])
  right_inv x := Subtype.ext (by
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id])
  map_mul' x y := Subtype.ext (MonObj.mul_comp _ _ _)

@[simp] theorem kernelCentralizerTransportEquiv_apply (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (U : Over B) (x : (kernelCentralizer i a).carrier U) :
    (kernelCentralizerTransportEquiv e f h a U x : U ⟶ H.X) =
      x.val ≫ f.hom.hom.hom := rfl

@[simp] theorem kernelCentralizerTransportEquiv_symm_apply (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (U : Over B)
    (x : (kernelCentralizer j (characterLattice.congr e a)).carrier U) :
    ((kernelCentralizerTransportEquiv e f h a U).symm x : U ⟶ G.X) =
      x.val ≫ f.inv.hom.hom := rfl

/-- Transport commutes with pullback along every refinement of test schemes. -/
theorem kernelCentralizerTransportEquiv_naturality (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) {U V : Over B} (b : V ⟶ U)
    (x : (kernelCentralizer i a).carrier U) :
    b ≫ (kernelCentralizerTransportEquiv e f h a U x : U ⟶ H.X) =
      (kernelCentralizerTransportEquiv e f h a V
        ⟨b ≫ x.val, (kernelCentralizer i a).comp_mem b x.property⟩ : V ⟶ H.X) :=
  (Category.assoc _ _ _).symm

/-- Specialization to the same actual point that transports the acting groups. -/
def kernelCentralizerTransporterConjEquiv {j : S'.toGrp ⟶ G}
    (e : S ≅ S') (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (U : Over B) :
    (kernelCentralizer i a).carrier U ≃*
      (kernelCentralizer j (characterLattice.congr e a)).carrier U :=
  kernelCentralizerTransportEquiv e (G.innerIso g) h a U

@[simp] theorem kernelCentralizerTransporterConjEquiv_apply {j : S'.toGrp ⟶ G}
    (e : S ≅ S') (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (U : Over B) (x : (kernelCentralizer i a).carrier U) :
    (kernelCentralizerTransporterConjEquiv e g h a U x : U ⟶ G.X) =
      G.constantPoint g U * x.val * (G.constantPoint g U)⁻¹ :=
  comp_innerIso_hom G g U x.val

@[simp] theorem kernelCentralizerTransporterConjEquiv_symm_apply {j : S'.toGrp ⟶ G}
    (e : S ≅ S') (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (U : Over B)
    (x : (kernelCentralizer j (characterLattice.congr e a)).carrier U) :
    ((kernelCentralizerTransporterConjEquiv e g h a U).symm x : U ⟶ G.X) =
      (G.constantPoint g U)⁻¹ * x.val * G.constantPoint g U := by
  change x.val ≫ (G.innerIso g).inv.hom.hom = _
  rw [← innerIso_inv_hom, comp_innerIso_hom, constantPoint_inv, inv_inv]

end Langlands.GroupScheme.RelativeRoot
