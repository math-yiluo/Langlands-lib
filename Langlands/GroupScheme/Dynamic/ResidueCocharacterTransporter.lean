import Langlands.GroupScheme.Dynamic.PresentationComparison
import Langlands.GroupScheme.Torus.TransporterFunctoriality
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Canonical residue transporters from equality at a field-valued point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Dynamic

variable {S T : Scheme.{u}} {G : GroupScheme S}

/-- Faithful pullback reflects equality of normalized cocharacters. -/
theorem baseChangeCocharacter_injective (p : T ⟶ S) [(Over.pullback p).Faithful] :
    Function.Injective (baseChangeCocharacter (G := G) p) := by
  intro χ ψ h
  have hh : (baseChange p).map χ = (baseChange p).map ψ :=
    (cancel_epi (Gm.baseChangeIso p).inv).mp h
  apply Grp.hom_ext
  exact (Over.pullback p).map_injective (congrArg (fun f => f.hom.hom) hh)

/-- Equality at a supplied field-valued point reflects to its canonical residue point. -/
theorem cocharacter_eq_residue_of_fieldPoint
    (χ ψ : (Gm S).toGrp ⟶ G)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (heq : baseChangeCocharacter b χ = baseChangeCocharacter b ψ) :
    baseChangeCocharacter
        (S.fromSpecResidueField (b (IsLocalRing.closedPoint k))) χ =
      baseChangeCocharacter
        (S.fromSpecResidueField (b (IsLocalRing.closedPoint k))) ψ := by
  let s := b (IsLocalRing.closedPoint k)
  let a := S.fromSpecResidueField s
  let c := Spec.map (fieldPointResidueMap b)
  let : Algebra (S.residueField s) k := (fieldPointResidueMap b).hom.toAlgebra
  have hc : c = Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) k)) := rfl
  have hfpqc := fieldExtension_fpqc (S.residueField s) k
  let : Flat c := hc.symm ▸ hfpqc.2.1
  let : Surjective c := hc.symm ▸ hfpqc.1
  let : QuasiCompact c := hc.symm ▸ hfpqc.2.2
  apply baseChangeCocharacter_injective c
  apply (cancel_mono
    (Descent.pullbackComparison a c b (fieldPointResidueMap_factorization b) G).hom).mp
  exact (baseChangeCocharacter_tower a c b (fieldPointResidueMap_factorization b) χ).trans
    (heq.trans
      (baseChangeCocharacter_tower a c b (fieldPointResidueMap_factorization b) ψ).symm)

/-- A canonical residue point with an actual transporter between two cocharacters. -/
structure ResidueCocharacterTransporterData (χ ψ : (Gm S).toGrp ⟶ G) where
  point : S
  transporter : Over.mk (𝟙 (Spec (S.residueField point))) ⟶
    ((baseChange (S.fromSpecResidueField point)).obj G).X
  transports : PointwiseSchemeAction.IsTransporter
    ((baseChange (S.fromSpecResidueField point)).map ψ)
    ((baseChange (S.fromSpecResidueField point)).map χ) transporter

/-- Equal cocharacters at any field-valued point supply the identity transporter
at the canonical residue point of its image. -/
def residueCocharacterTransporter
    (χ ψ : (Gm S).toGrp ⟶ G)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (heq : baseChangeCocharacter b χ = baseChangeCocharacter b ψ) :
    ResidueCocharacterTransporterData χ ψ := by
  let s := b (IsLocalRing.closedPoint k)
  let a := S.fromSpecResidueField s
  have hχψ : (baseChange a).map χ = (baseChange a).map ψ :=
    (cancel_epi (Gm.baseChangeIso a).inv).mp
      (cocharacter_eq_residue_of_fieldPoint χ ψ b heq)
  refine ⟨s, 1, ?_⟩
  intro V e x
  simp only [MonObj.comp_one, mul_one, one_mul]
  exact congrArg (fun f => x ≫ f.hom.hom) hχψ.symm

end Langlands.GroupScheme.Dynamic
