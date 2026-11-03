import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Actual character kernels and root subgroup transport between acting tori -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {B : Scheme.{u}} {S S' : CommGroupScheme B} {G H : GroupScheme B}

private def underlyingGroupIso (e : S ≅ S') : S.toGrp ≅ S'.toGrp where
  hom := CommGroupScheme.groupHom e.hom
  inv := CommGroupScheme.groupHom e.inv
  hom_inv_id := congrArg Additive.toMul e.hom_inv_id
  inv_hom_id := congrArg Additive.toMul e.inv_hom_id

/-- The actual character kernels are identified by an isomorphism of the acting
commutative group schemes. No smoothness of either kernel is required. -/
def characterKernelCongr (e : S ≅ S') (a : characterLattice S) :
    characterKernel a ≅ characterKernel (characterLattice.congr e a) :=
  asIso (pullback.map (CommGroupScheme.groupHom a) (kernelUnit (Gm B).toGrp)
    (CommGroupScheme.groupHom (characterLattice.congr e a)) (kernelUnit (Gm B).toGrp)
    (underlyingGroupIso e).hom (𝟙 _) (𝟙 _)
    (by
      rw [Category.comp_id]
      change CommGroupScheme.groupHom a =
        CommGroupScheme.groupHom (e.hom ≫ e.inv ≫ a)
      rw [Iso.hom_inv_id_assoc])
    (by simp))

/-- The kernel comparison is the original torus isomorphism on every kernel point. -/
@[reassoc] theorem characterKernelCongr_hom_ι (e : S ≅ S') (a : characterLattice S) :
    (characterKernelCongr e a).hom ≫ characterKernelι (characterLattice.congr e a) =
      characterKernelι a ≫ CommGroupScheme.groupHom e.hom := by
  exact pullback.lift_fst _ _ _

/-- The inverse comparison is the inverse torus isomorphism on the full kernel. -/
@[reassoc] theorem characterKernelCongr_inv_ι (e : S ≅ S') (a : characterLattice S) :
    (characterKernelCongr e a).inv ≫ characterKernelι a =
      characterKernelι (characterLattice.congr e a) ≫ CommGroupScheme.groupHom e.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, characterKernelCongr_hom_ι, Category.assoc]
  change characterKernelι a =
    characterKernelι a ≫ CommGroupScheme.groupHom (e.hom ≫ e.inv)
  rw [Iso.hom_inv_id]
  exact (Category.comp_id _).symm

/-- Reparametrization of a full torus orbit allows a different acting group scheme. -/
theorem orbit_precomp_torus_hom (i : S.toGrp ⟶ G) (τ : S' ⟶ S)
    {U : Over B} (g : U ⟶ G.X) :
    orbit (CommGroupScheme.groupHom τ ≫ i) g =
      U ◁ (CommGroupScheme.groupHom τ).hom.hom ≫ orbit i g := by
  simp only [orbit, AutomorphicAction.conjugation_act, Grp.comp_hom_hom,
    MonObj.comp_mul, GrpObj.comp_inv, whiskerLeft_snd_assoc,
    whiskerLeft_fst_assoc]

/-- Reparametrizing both the torus map and the character preserves the actual extension. -/
theorem IsOrbitExtension.precomp_torus_hom (i : S.toGrp ⟶ G)
    (a : characterLattice S) (τ : S' ⟶ S) {U : Over B} {g : U ⟶ G.X}
    {v : U ⊗ AffineLine.scheme B ⟶ G.X} (hv : IsOrbitExtension i a g v) :
    IsOrbitExtension (CommGroupScheme.groupHom τ ≫ i) (τ ≫ a) g v := by
  rw [IsOrbitExtension, orbit_precomp_torus_hom]
  change U ◁ ((CommGroupScheme.groupHom τ).hom.hom ≫
    (CommGroupScheme.groupHom a).hom.hom ≫ AffineLine.unitInclusion B) ≫ v = _
  rw [whiskerLeft_comp, Category.assoc, hv]

/-- Reparametrization preserves root subgroup membership on all scheme tests. -/
theorem mem_subgroup_precomp_torus_hom (i : S.toGrp ⟶ G)
    (a : characterLattice S) (τ : S' ⟶ S) {U : Over B} {g : U ⟶ G.X}
    (hg : g ∈ (subgroup i a).carrier U) :
    g ∈ (subgroup (CommGroupScheme.groupHom τ ≫ i) (τ ≫ a)).carrier U := by
  obtain ⟨v, hv, hv0⟩ := hg
  exact ⟨v, hv.precomp_torus_hom i a τ, hv0⟩

variable {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}

/-- A commuting square of torus and ambient group isomorphisms also commutes in reverse. -/
theorem inverse_transport_square (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    j ≫ f.inv = CommGroupScheme.groupHom e.inv ≫ i := by
  rw [Iso.comp_inv_eq, Category.assoc, h, ← Category.assoc]
  change j = CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ j
  rw [Iso.inv_hom_id]
  exact (Category.id_comp _).symm

/-- A commuting square carries the full root subgroup to the transported character. -/
theorem comp_mem_subgroup_of_transport (e : S ≅ S') (f : G ⟶ H)
    (h : i ≫ f = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) {U : Over B} {g : U ⟶ G.X}
    (hg : g ∈ (subgroup i a).carrier U) :
    g ≫ f.hom.hom ∈ (subgroup j (characterLattice.congr e a)).carrier U := by
  have hc : CommGroupScheme.groupHom e.inv ≫ (i ≫ f) = j := by
    rw [h, ← Category.assoc]
    change CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ j = j
    rw [Iso.inv_hom_id]
    exact Category.id_comp _
  have hm := mem_subgroup_precomp_torus_hom (i ≫ f) a e.inv
    (comp_mem_subgroup i a f hg)
  rwa [hc] at hm

/-- The actual root subgroup functors agree under the supplied isomorphisms, on every test. -/
theorem subgroup_comap_of_transport (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) (a : characterLattice S) :
    (subgroup j (characterLattice.congr e a)).comap f.hom = subgroup i a := by
  ext U g
  rw [SubgroupFunctor.mem_comap]
  constructor
  · intro hg
    have hm := comp_mem_subgroup_of_transport e.symm f.inv
      (inverse_transport_square e f h) (characterLattice.congr e a) hg
    have ha : characterLattice.congr e.symm (characterLattice.congr e a) = a := by
      simp [characterLattice.congr_apply]
    rw [ha] at hm
    simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id] using hm
  · exact comp_mem_subgroup_of_transport e f.hom h a

/-- Actual multiplicative equivalences of root subgroup points between two acting tori. -/
def subgroupTransportEquiv (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (U : Over B) :
    (subgroup i a).carrier U ≃*
      (subgroup j (characterLattice.congr e a)).carrier U where
  toFun x := ⟨x.val ≫ f.hom.hom.hom, comp_mem_subgroup_of_transport e f.hom h a x.property⟩
  invFun x := ⟨x.val ≫ f.inv.hom.hom, by
    apply (le_of_eq (subgroup_comap_of_transport e f h a)) U
    change (x.val ≫ f.inv.hom.hom) ≫ f.hom.hom.hom ∈
      (subgroup j (characterLattice.congr e a)).carrier U
    simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id] using x.property⟩
  left_inv x := Subtype.ext (by
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id])
  right_inv x := Subtype.ext (by
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id])
  map_mul' x y := Subtype.ext (MonObj.mul_comp _ _ _)

@[simp] theorem subgroupTransportEquiv_apply (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (U : Over B) (x : (subgroup i a).carrier U) :
    (subgroupTransportEquiv e f h a U x : U ⟶ H.X) = x.val ≫ f.hom.hom.hom := rfl

@[simp] theorem subgroupTransportEquiv_symm_apply (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (U : Over B)
    (x : (subgroup j (characterLattice.congr e a)).carrier U) :
    ((subgroupTransportEquiv e f h a U).symm x : U ⟶ G.X) = x.val ≫ f.inv.hom.hom := rfl

/-- Specialization to the same actual conjugating point used by the transporter. -/
def transporterConjEquiv {j : S'.toGrp ⟶ G}
    (e : S ≅ S') (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (U : Over B) :
    (subgroup i a).carrier U ≃*
      (subgroup j (characterLattice.congr e a)).carrier U :=
  subgroupTransportEquiv e (G.innerIso g) h a U

@[simp] theorem transporterConjEquiv_apply {j : S'.toGrp ⟶ G}
    (e : S ≅ S') (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (U : Over B) (x : (subgroup i a).carrier U) :
    (transporterConjEquiv e g h a U x : U ⟶ G.X) =
      G.constantPoint g U * x.val * (G.constantPoint g U)⁻¹ :=
  comp_innerIso_hom G g U x.val

@[simp] theorem transporterConjEquiv_symm_apply {j : S'.toGrp ⟶ G}
    (e : S ≅ S') (g : Over.mk (𝟙 B) ⟶ G.X)
    (h : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom e.hom ≫ j)
    (a : characterLattice S) (U : Over B)
    (x : (subgroup j (characterLattice.congr e a)).carrier U) :
    ((transporterConjEquiv e g h a U).symm x : U ⟶ G.X) =
      (G.constantPoint g U)⁻¹ * x.val * G.constantPoint g U := by
  change x.val ≫ (G.innerIso g).inv.hom.hom = _
  rw [← innerIso_inv_hom, comp_innerIso_hom, constantPoint_inv, inv_inv]

end RelativeRoot

end Langlands.GroupScheme
