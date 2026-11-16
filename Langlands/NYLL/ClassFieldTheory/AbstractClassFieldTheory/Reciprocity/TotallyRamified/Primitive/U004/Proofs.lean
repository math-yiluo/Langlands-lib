/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5264, 15 November 2026:
Extract the proof of M083.004 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published Primitive Statements module and the
published proofs of M072.005 tateHMinusOne_isZero, of the cyclic norm-kernel
lemma normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero and of M073.004
extensionFixedRepresentation_action_coe, and give the theorem the published
proposition abstractReciprocity_exists_hMinusOne_primitiveStatement as its type.
The source applies extensionFixedRepresentation_norm_coe (M073.005), whose
proof is not yet published. Its source proof is therefore reproduced as the
private theorem extensionFixedRepresentation_norm_coe_aux, with that theorem's
own use of relativeNorm_apply_coe (M024.010, also unpublished) replaced by its
source proof rfl. Because the statement of tateHMinusOne_isZero is a Prop-valued
definition, the source simpa call also unfolds tateHMinusOne_isZeroStatement.
The rest of the proof is the source's. Omit the noncomputable section and all
other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamified.Primitive.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.Action.U004.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.U007.Proofs

/-!
# The `H⁻¹` primitive of a difference with equal norms
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

open CategoryTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The source proof of M073.005 `extensionFixedRepresentation_norm_coe`
(not yet published): the norm in the descended representation is the actual
relative norm on the underlying fixed coefficient. -/
private theorem extensionFixedRepresentation_norm_coe_aux
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    letI := hnormal
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    ((extensionFixedRepresentation A K L hLK hnormal).norm.hom a).1 =
      ((relativeNorm A K L hLK
        (extensionFixedRepresentationEquiv A K L hLK hnormal a) :
          ambientFixedAddSubgroup A K) : A.V) := by
  let := hnormal
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  -- The source rewrites with M024.010 `relativeNorm_apply_coe`, whose source
  -- proof is `rfl`.
  have hcoe :
      ((relativeNorm A K L hLK
        (extensionFixedRepresentationEquiv A K L hLK hnormal a) :
          ambientFixedAddSubgroup A K) : A.V) =
        relativeNormValue A K L hLK
          (extensionFixedRepresentationEquiv A K L hLK hnormal a) :=
    rfl
  rw [hcoe]
  simp only [Rep.norm, Representation.norm, relativeNormValue]
  let M := extensionFixedRepresentation A K L hLK hnormal
  let : Module ℤ M.V := M.hV2
  change ((∑ q, M.ρ q) a).1 =
    ∑ q, relativeCosetAction A K L hLK
      (extensionFixedRepresentationEquiv A K L hLK hnormal a) q
  rw [LinearMap.sum_apply]
  let coeToAmbient :
      (extensionFixedRepresentation A K L hLK hnormal).V →+ A.V :=
    { toFun := fun x => x.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change coeToAmbient (∑ q, M.ρ q a) =
    ∑ q, relativeCosetAction A K L hLK
      (extensionFixedRepresentationEquiv A K L hLK hnormal a) q
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact extensionFixedRepresentation_action_coe A K L hLK hnormal q a

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The class-field axiom, in representative form: equality of two actual relative
norms yields the element `a` for which `a^σ-a = v-u`. -/
theorem abstractReciprocity_exists_hMinusOne_primitive
    (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (u w : ambientFixedAddSubgroup A E.field.field)
    (hnorm : relativeNorm A E.base.field E.field.field E.below w =
      relativeNorm A E.base.field E.field.field E.below u) :
    abstractReciprocity_exists_hMinusOne_primitiveStatement
      hcf E hnormal g hg u w hnorm := by
  show
    let M := extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal
    ∃ a : M.V,
      M.ρ g a - a =
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal).symm
          (w - u)
  let := hnormal
  let := E.finiteQuotient
  let := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
  let M := extensionFixedRepresentation A E.base.field E.field.field
    E.below hnormal
  let z : M.V :=
    (extensionFixedRepresentationEquiv A E.base.field E.field.field
      E.below hnormal).symm (w - u)
  have hzNorm : M.norm.hom z = 0 := by
    apply Subtype.ext
    calc
      (M.norm.hom z).1 =
          ((relativeNorm A E.base.field E.field.field E.below (w - u) :
            ambientFixedAddSubgroup A E.base.field) : A.V) :=
        -- The source applies M073.005 `extensionFixedRepresentation_norm_coe`.
        extensionFixedRepresentation_norm_coe_aux A E.base.field E.field.field
          E.below hnormal z
      _ = ((relativeNorm A E.base.field E.field.field E.below w -
          relativeNorm A E.base.field E.field.field E.below u :
            ambientFixedAddSubgroup A E.base.field) : A.V) := by
        rw [map_sub]
      _ = 0 := by rw [hnorm, sub_self]; rfl
  let Ecf : FiniteCyclicSubextension E.base :=
    { field := E.field.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }
  have hzero : Limits.IsZero (tateCohomology M (-1)) := by
    simpa [Ecf, SatisfiesClassFieldAxiom.tateHMinusOne_isZeroStatement,
      FiniteCyclicSubextension.fixedRepresentation] using
        hcf.tateHMinusOne_isZero E.base Ecf
  obtain ⟨a, ha⟩ :=
    CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
      M g hg hzero z hzNorm
  exact ⟨a, ha⟩

end ValuationData

end Langlands.NYLL.ClassFormation
