import Langlands.AlgebraicGeometry.Picard.SquareZeroUnitKernels
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Square-zero ideal kernels and actual unit-kernel sheaves -/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroUnitKernels

section Sheaves

variable {X : TopCat.{u}} {F G : X.Presheaf CommRingCat.{u}}
  (η : F ⟶ G) (hF : TopCat.Presheaf.IsSheaf F) (hG : TopCat.Presheaf.IsSheaf G)

include hF hG in
/-- Actual additive kernels of a morphism of ring sheaves are sheaves. -/
lemma additiveKernelPresheaf_isSheaf :
    TopCat.Presheaf.IsSheaf (additiveKernelPresheaf η) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hval : TopCat.Presheaf.IsCompatible F U (fun i ↦ (sf i).val) := by
    intro i j
    exact congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, huniq⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing hF U _ hval
  have hker : (η.app (op (iSup U))).hom s = 0 := by
    apply TopCat.Sheaf.eq_of_locally_eq (⟨G, hG⟩ : X.Sheaf CommRingCat) U
    intro i
    have hn := congrArg (fun q ↦ q.hom s) (η.naturality (Opens.leSupr U i).op)
    change (η.app (op (U i))).hom (F.map (Opens.leSupr U i).op s) =
      G.map (Opens.leSupr U i).op ((η.app (op (iSup U))).hom s) at hn
    rw [← hn, hs i, map_zero]
    exact RingHom.mem_ker.mp (sf i).property
  refine ⟨⟨s, hker⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact hs i
  · intro t ht
    apply Subtype.ext
    apply huniq
    intro i
    exact congrArg Subtype.val (ht i)

/-- The additive ideal kernel, with the actual sectionwise kernel as its carrier. -/
def additiveKernelSheaf : X.Sheaf AddCommGrpCat.{u} :=
  ⟨additiveKernelPresheaf η, additiveKernelPresheaf_isSheaf η hF hG⟩

variable (h : ∀ U, SquareZeroKernel (η.app U).hom)

include hF hG h in
/-- Square-zero unit kernels satisfy the sheaf condition. -/
lemma unitKernelPresheaf_isSheaf : TopCat.Presheaf.IsSheaf (unitKernelPresheaf η) :=
  TopCat.Presheaf.isSheaf_of_iso (kernelPresheafIso η h)
    (additiveKernelPresheaf_isSheaf η hF hG)

/-- Actual units reducing to one, written additively as a sheaf of abelian groups. -/
def unitKernelSheaf : X.Sheaf AddCommGrpCat.{u} :=
  ⟨unitKernelPresheaf η, unitKernelPresheaf_isSheaf η hF hG h⟩

/-- The actual additive-kernel/unit-kernel comparison at the sheaf level. -/
def kernelSheafIso : additiveKernelSheaf η hF hG ≅ unitKernelSheaf η hF hG h where
  hom := ⟨(kernelPresheafIso η h).hom⟩
  inv := ⟨(kernelPresheafIso η h).inv⟩
  hom_inv_id := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (kernelPresheafIso η h).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (kernelPresheafIso η h).inv_hom_id

end Sheaves

section Schemes

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [QuasiCompact i]

/-- A square-zero scheme-morphism kernel has square-zero actual section kernels
on every open, not only on affine opens. -/
lemma squareZeroKernel_app (hi : i.ker ^ 2 = ⊥) (U : X.Opens) :
    SquareZeroKernel (i.app U).hom := by
  intro a b
  apply TopCat.Presheaf.IsSheaf.section_ext X.sheaf.property
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  refine ⟨V, hVU, hxV, ?_⟩
  have hI : (RingHom.ker (i.app V).hom) ^ 2 = ⊥ := by
    rw [← i.ker_apply ⟨V, hV⟩]
    change (i.ker ^ 2).ideal ⟨V, hV⟩ = _
    rw [hi]
    rfl
  have hpair := (squareZeroKernel_iff_ker_sq_eq_bot (i.app V).hom).mpr hI
  let aV := additiveKernelMap (i.app U).hom (i.app V).hom
    (X.presheaf.map (homOfLE hVU).op).hom
    (((Opens.map i.base).op ⋙ Y.presheaf).map (homOfLE hVU).op).hom
    (restriction_square i.c (homOfLE hVU).op) a
  let bV := additiveKernelMap (i.app U).hom (i.app V).hom
    (X.presheaf.map (homOfLE hVU).op).hom
    (((Opens.map i.base).op ⋙ Y.presheaf).map (homOfLE hVU).op).hom
    (restriction_square i.c (homOfLE hVU).op) b
  change (X.presheaf.map (homOfLE hVU).op).hom (a.val * b.val) =
    (X.presheaf.map (homOfLE hVU).op).hom 0
  have hab := hpair aV bV
  dsimp [aV, bV, additiveKernelMap] at hab
  rw [map_mul, map_zero]
  exact hab

/-- The actual kernel of the structure-ring morphism as an abelian-group sheaf. -/
def schemeAdditiveKernelSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  additiveKernelSheaf i.c X.sheaf.property
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf i.base Y.sheaf.property)

/-- Actual units whose restriction along the scheme morphism is one. -/
def schemeUnitKernelSheaf (hi : i.ker ^ 2 = ⊥) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  unitKernelSheaf i.c X.sheaf.property
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf i.base Y.sheaf.property)
    (fun U ↦ squareZeroKernel_app i hi U.unop)

/-- For an arbitrary quasi-compact scheme morphism with square-zero kernel,
`a ↦ 1 + a` identifies its actual additive kernel and its actual unit kernel. -/
def schemeKernelSheafIso (hi : i.ker ^ 2 = ⊥) :
    schemeAdditiveKernelSheaf i ≅ schemeUnitKernelSheaf i hi :=
  kernelSheafIso i.c X.sheaf.property
    (TopCat.Sheaf.pushforward_sheaf_of_sheaf i.base Y.sheaf.property)
    (fun U ↦ squareZeroKernel_app i hi U.unop)

end Schemes

end Langlands.AlgebraicGeometry.Picard.SquareZeroUnitKernels
