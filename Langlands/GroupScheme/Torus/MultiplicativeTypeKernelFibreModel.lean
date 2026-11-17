import Langlands.GroupScheme.Torus.DiagonalizableClosedSubgroupModel
import Langlands.GroupScheme.Torus.RelativeDiagonalizableExactQuotient
import Langlands.GroupScheme.Torus.DiagonalizableAutomorphismLocality
import Langlands.GroupScheme.Unipotent.KernelCoordinateTransport

/-! # Extending a split multiplicative-type fibre kernel to the base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable {S : Scheme.{u}} {R : CommRingCat.{u}}

/-- The actual affine model of the base change of `D_S(M)` to an affine scheme. -/
def affineBaseChangeIso (b : Spec R ⟶ S) (M : Type u) [AddCommGroup M] :
    (baseChange b).obj (diagonalizable S M) ≅ (Diagonalizable.groupScheme R M).toGrp :=
  (baseChangeCompIso (Gm.toSpecZ S) b
    (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) M).toGrp).symm ≪≫
      Diagonalizable.baseChangeIso (b ≫ Gm.toSpecZ S) M

/-- The affine model preserves every supplied full-character restriction map. -/
theorem affineBaseChangeIso_diagonalizableMap
    (b : Spec R ⟶ S) {M N : Type u} [AddCommGroup M] [AddCommGroup N] (p : M →+ N) :
    (baseChange b).map (diagonalizableMap S p) ≫ (affineBaseChangeIso b M).hom =
      (affineBaseChangeIso b N).hom ≫ Diagonalizable.restrictMap R p := by
  let r := Diagonalizable.restrictMap (CommRingCat.of (ULift.{u} ℤ)) p
  let eM := baseChangeCompIso (Gm.toSpecZ S) b
    (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) M).toGrp
  let eN := baseChangeCompIso (Gm.toSpecZ S) b
    (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) N).toGrp
  have hn :
      (baseChange (b ≫ Gm.toSpecZ S)).map r ≫ eM.hom =
        eN.hom ≫ (baseChange b).map (diagonalizableMap S p) :=
    ((Functor.mapGrpNatIso (Over.pullbackComp b (Gm.toSpecZ S))) ≪≫
      Functor.mapGrpCompIso).hom.naturality r
  have hn' : (baseChange b).map (diagonalizableMap S p) ≫ eM.inv =
      eN.inv ≫ (baseChange (b ≫ Gm.toSpecZ S)).map r := by
    apply (cancel_mono eM.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn, Iso.inv_hom_id_assoc]
  change
    (baseChange b).map (diagonalizableMap S p) ≫
        eM.inv ≫ (Diagonalizable.baseChangeIso (b ≫ Gm.toSpecZ S) M).hom =
      (eN.inv ≫ (Diagonalizable.baseChangeIso (b ≫ Gm.toSpecZ S) N).hom) ≫
        Diagonalizable.restrictMap R p
  rw [← Category.assoc, hn', Category.assoc,
    Diagonalizable.baseChangeIso_restrictMap, ← Category.assoc]

variable {k : Type u} [Field k] {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    {G : GroupScheme S} [IsSeparated G.X.hom]
    (f : diagonalizable S M ⟶ G) (b : Spec (CommRingCat.of k) ⟶ S)

/-- The given homomorphism on the actual affine diagonalizable fibre model. -/
def affineFibreHom :
    (Diagonalizable.groupScheme (CommRingCat.of k) M).toGrp ⟶ (baseChange b).obj G :=
  (affineBaseChangeIso b M).inv ≫ (baseChange b).map f

/-- A compatible full-character model of the actual fibre kernel. -/
def fibreClosedSubgroupModel :
    Diagonalizable.ClosedSubgroupModel (kernelι (affineFibreHom f b)) := by
  have : IsSeparated ((baseChange b).obj G).X.hom := by
    change IsSeparated (CategoryTheory.Limits.pullback.snd _ _)
    infer_instance
  exact Diagonalizable.kernelModel (affineFibreHom f b)

/-- Extend the fibre kernel character group as a split group over the whole base. -/
def fibreSubgroup : GroupScheme S :=
  diagonalizable S (fibreClosedSubgroupModel f b).characters

/-- Extend the fibre kernel inclusion by its actual full-character surjection. -/
def fibreSubgroupHom : fibreSubgroup f b ⟶ diagonalizable S M :=
  diagonalizableMap S (fibreClosedSubgroupModel f b).restriction

/-- The extended fibre subgroup is closed over the original base. -/
theorem isClosedSubgroup_fibreSubgroupHom :
    IsClosedSubgroup (fibreSubgroupHom f b) :=
  isClosedSubgroup_diagonalizableMap S (fibreClosedSubgroupModel f b).restriction
    (fibreClosedSubgroupModel f b).surjective

/-- The extended subgroup is diagonalizable over the original base. -/
theorem isDiagonalizable_fibreSubgroup : IsDiagonalizable (fibreSubgroup f b) :=
  ⟨(fibreClosedSubgroupModel f b).characters, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩

/-- The fibre of the extended subgroup is the actual fibre kernel. -/
def fibreSubgroupKernelIso :
    (baseChange b).obj (fibreSubgroup f b) ≅ kernel ((baseChange b).map f) :=
  affineBaseChangeIso b (fibreClosedSubgroupModel f b).characters ≪≫
    (fibreClosedSubgroupModel f b).iso.symm ≪≫
      kernelCoordinateIso ((baseChange b).map f) (affineFibreHom f b)
        (affineBaseChangeIso b M).symm rfl

/-- The kernel comparison preserves the extended inclusion as an actual homomorphism. -/
theorem fibreSubgroupKernelIso_hom_comp :
    (fibreSubgroupKernelIso f b).hom ≫ kernelι ((baseChange b).map f) =
      (baseChange b).map (fibreSubgroupHom f b) := by
  let m := fibreClosedSubgroupModel f b
  have hm : m.iso.inv ≫ kernelι (affineFibreHom f b) =
      Diagonalizable.restrictMap (CommRingCat.of k) m.restriction := by
    calc
      _ = m.iso.inv ≫
          (m.iso.hom ≫ Diagonalizable.restrictMap (CommRingCat.of k) m.restriction) :=
        congrArg (fun t => m.iso.inv ≫ t) m.inclusion.symm
      _ = _ := by rw [Iso.inv_hom_id_assoc]
  dsimp only [fibreSubgroupKernelIso, fibreSubgroup, fibreSubgroupHom,
    Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, kernelCoordinateIso_hom_ι]
  rw [← Category.assoc (fibreClosedSubgroupModel f b).iso.inv, hm]
  apply (cancel_mono (affineBaseChangeIso b M).hom).mp
  simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
  exact (affineBaseChangeIso_diagonalizableMap b m.restriction).symm

/-- The full fibre kernel range is the full range of the extended subgroup fibre. -/
theorem kernel_range_eq_fibreSubgroup :
    SubgroupFunctor.range (kernelι ((baseChange b).map f)) =
      SubgroupFunctor.range ((baseChange b).map (fibreSubgroupHom f b)) := by
  have h := SubgroupFunctor.range_iso_comp (fibreSubgroupKernelIso f b)
    (kernelι ((baseChange b).map f))
  rw [fibreSubgroupKernelIso_hom_comp] at h
  exact h.symm

/-- On the chosen fibre, the original homomorphism kills the extended subgroup. -/
theorem fibreSubgroupHom_comp_fibre_eq_one :
    ((baseChange b).map (fibreSubgroupHom f b ≫ f)).hom.hom = 1 := by
  have hi : ((baseChange b).map (fibreSubgroupHom f b)).hom.hom ∈
      (SubgroupFunctor.range (kernelι ((baseChange b).map f))).carrier
        ((baseChange b).obj (fibreSubgroup f b)).X := by
    rw [kernel_range_eq_fibreSubgroup]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  simpa only [Functor.map_comp, Grp.comp_hom_hom] using
    (mem_range_kernelι_iff ((baseChange b).map f) _).mp hi

end Langlands.GroupScheme.RelativeMultiplicativeType
