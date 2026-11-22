import Langlands.Geometry.FormalGroup.PDivisibleGroupTatePolarization
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.TransferInstance

/-! # The p-adic integer action on schematic Tate points -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.PDivisibleGroup

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]
variable (G : PDivisibleGroup R p) (T : Over (Spec R))

private abbrev finitePoints (n : ℕᵒᵖ) := (G.schematicTateTestDiagram T).obj n

private abbrev finiteProjection (n : ℕ) :
    ((schematicTatePointFunctor R p).obj G).obj (op T) ⟶ finitePoints G T (op n) :=
  (G.schematicTatePointProjection n).app (op T)

/-- The residue ring acts on actual finite points through their additive group law. -/
@[instance_reducible] def schematicTateLevelResidueModule (n : ℕᵒᵖ) :
    Module (ZMod (p ^ n.unop)) (finitePoints G T n) :=
  AddCommGroup.zmodModule (schematicTateLevel_nsmul (G := G) T n.unop)

/-- At level `n`, the action of `ℤ_p` factors through its standard residue map. -/
@[instance_reducible] def schematicTateLevelPadicModule (n : ℕᵒᵖ) :
    Module ℤ_[p] (finitePoints G T n) :=
  letI := G.schematicTateLevelResidueModule T n
  Module.compHom _ (PadicInt.toZModPow n.unop)

private theorem schematicTateTestMap_padic {n m : ℕᵒᵖ} (i : n ⟶ m)
    (a : ℤ_[p]) (x : finitePoints G T n) :
    letI := G.schematicTateLevelPadicModule T n
    letI := G.schematicTateLevelPadicModule T m
    (G.schematicTateTestDiagram T).map i (a • x) =
      a • (G.schematicTateTestDiagram T).map i x := by
  let := G.schematicTateLevelResidueModule T n
  let := G.schematicTateLevelResidueModule T m
  let f := ((G.schematicTateTestDiagram T).map i).hom
  change f (PadicInt.toZModPow n.unop a • x) =
    PadicInt.toZModPow m.unop a • f x
  have h := DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow m.unop n.unop (leOfHom i.unop)) a
  change ZMod.castHom (pow_dvd_pow p (leOfHom i.unop)) (ZMod (p ^ m.unop))
    (PadicInt.toZModPow n.unop a) = PadicInt.toZModPow m.unop a at h
  rw [← h]
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (PadicInt.toZModPow n.unop a)
  rw [← hz, map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]

private def schematicTateSectionSubmodule :
    letI (n : ℕᵒᵖ) := G.schematicTateLevelPadicModule T n
    Submodule ℤ_[p] (∀ n : ℕᵒᵖ, finitePoints G T n) := by
  letI (n : ℕᵒᵖ) := G.schematicTateLevelPadicModule T n
  exact
    { G.schematicTateSections T with
      smul_mem' := by
        intro a x hx n m i
        change (G.schematicTateTestDiagram T).map i (a • x n) = a • x m
        exact (G.schematicTateTestMap_padic T i a (x n)).trans (congrArg (a • ·) (hx i)) }

private def schematicTatePointEquivSectionSubmodule :
    ((schematicTatePointFunctor R p).obj G).obj (op T) ≃+
      G.schematicTateSectionSubmodule T :=
  G.schematicTatePointEquivSections T

/-- Compatible residues make all schematic Tate sections into a `ℤ_p`-module. -/
@[instance_reducible] def schematicTatePadicModule :
    Module ℤ_[p] (((schematicTatePointFunctor R p).obj G).obj (op T)) :=
  (G.schematicTatePointEquivSectionSubmodule T).module ℤ_[p]

/-- Scalar multiplication projects to the usual residue action on every actual finite level. -/
theorem schematicTatePadicModule_projection_smul (n : ℕ) (a : ℤ_[p])
    (x : ((schematicTatePointFunctor R p).obj G).obj (op T)) :
    letI := G.schematicTatePadicModule T
    letI := G.schematicTateLevelResidueModule T (op n)
    G.finiteProjection T n (a • x) = PadicInt.toZModPow n a • G.finiteProjection T n x := by
  let := G.schematicTatePadicModule T
  let := G.schematicTateLevelResidueModule T (op n)
  let (j : ℕᵒᵖ) := G.schematicTateLevelPadicModule T j
  let : Module ℤ_[p] ↥(G.schematicTateSectionSubmodule T) := inferInstance
  let e := G.schematicTatePointEquivSectionSubmodule T
  change (e (e.symm (a • e x))).val (op n) = _
  rw [e.apply_symm_apply]
  rfl

variable {T}

private theorem schematicTatePadic_restrict_smul {U : Over (Spec R)} (b : U ⟶ T)
    (a : ℤ_[p]) (x : ((schematicTatePointFunctor R p).obj G).obj (op T)) :
    letI := G.schematicTatePadicModule T
    letI := G.schematicTatePadicModule U
    ((schematicTatePointFunctor R p).obj G).map b.op (a • x) =
      a • ((schematicTatePointFunctor R p).obj G).map b.op x := by
  let := G.schematicTatePadicModule T
  let := G.schematicTatePadicModule U
  let F := (schematicTatePointFunctor R p).obj G
  apply schematicTatePoint_ext
  intro n
  let := G.schematicTateLevelResidueModule T (op n)
  let := G.schematicTateLevelResidueModule U (op n)
  let f : finitePoints G T (op n) →+ finitePoints G U (op n) :=
    ((GroupScheme.additivePoints (G.inclusions.obj n).toGrp).map b.op).hom
  have h (z : F.obj (op T)) : G.finiteProjection U n (F.map b.op z) =
      f (G.finiteProjection T n z) :=
    ConcreteCategory.congr_hom ((G.schematicTatePointProjection n).naturality b.op) z
  change G.finiteProjection U n (F.map b.op (a • x)) =
    G.finiteProjection U n (a • F.map b.op x)
  rw [h (a • x), G.schematicTatePadicModule_projection_smul T n,
    G.schematicTatePadicModule_projection_smul U n, h x]
  exact ZMod.map_smul f _ _

/-- The `ℤ_p`-module structure on Tate points is natural in the scheme test. -/
def schematicTatePadicPresheaf : (Over (Spec R))ᵒᵖ ⥤ ModuleCat.{u} ℤ_[p] where
  obj T := @ModuleCat.of ℤ_[p] _ (((schematicTatePointFunctor R p).obj G).obj T) _
    (G.schematicTatePadicModule T.unop)
  map {T U} b := by
    letI := G.schematicTatePadicModule T.unop
    letI := G.schematicTatePadicModule U.unop
    exact ModuleCat.ofHom
      { (((schematicTatePointFunctor R p).obj G).map b).hom with
        map_smul' a x := G.schematicTatePadic_restrict_smul b.unop a x }
  map_id T := by
    apply (forget₂ (ModuleCat.{u} ℤ_[p]) AddCommGrpCat.{u}).map_injective
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact ConcreteCategory.congr_hom (((schematicTatePointFunctor R p).obj G).map_id T) x
  map_comp b c := by
    apply (forget₂ (ModuleCat.{u} ℤ_[p]) AddCommGrpCat.{u}).map_injective
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact ConcreteCategory.congr_hom (((schematicTatePointFunctor R p).obj G).map_comp b c) x

/-- Forgetting the scalars recovers the actual additive schematic Tate point presheaf. -/
def schematicTatePadicPresheafForgetIso :
    G.schematicTatePadicPresheaf ⋙ forget₂ _ AddCommGrpCat.{u} ≅
      (schematicTatePointFunctor R p).obj G :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun b => by
    let β := ((schematicTatePointFunctor R p).obj G).map b
    change β ≫ 𝟙 _ = 𝟙 _ ≫ β
    exact (Category.comp_id β).trans (Category.id_comp β).symm

/-- The p-adic Tate module presheaf is a sheaf for subcanonical topologies. -/
theorem isSheaf_schematicTatePadic (J : GrothendieckTopology (Over (Spec R))) [J.Subcanonical] :
    Presheaf.IsSheaf J G.schematicTatePadicPresheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ (ModuleCat.{u} ℤ_[p]) AddCommGrpCat.{u})
  exact (Presheaf.isSheaf_of_iso_iff (J := J) G.schematicTatePadicPresheafForgetIso).mpr
    (G.isSheaf_schematicTatePoints J)

end Langlands.PDivisibleGroup
