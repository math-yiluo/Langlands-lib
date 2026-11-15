/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.ToClosure.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.GaloisSubextension.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse

/-!
# Towers of Frobenius fixed fields

Modified by Worker 5264, 15 November 2026: extract M041.001
`frobeniusFixedAbstractField`, M041.002 `FrobeniusFixedFieldTower`, M041.003
`FrobeniusFixedFieldTower.base`, M041.004 `FrobeniusFixedFieldTower.field`,
M041.005 `FrobeniusFixedFieldTower.toGaloisSubextension`, M041.006
`FrobeniusFixedFieldTower.extension`, the structures M041.007
`FrobeniusFixedFieldTower.Representative` and M041.009
`FrobeniusFixedFieldTower.CyclicGenerator`, the instances M041.008, M041.010,
M041.011 and M041.012, M041.013 `FiniteAmbientFrobeniusFixedFieldTower` and
its instances M041.014 and M041.015 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefixing the namespace with
`Langlands.NYLL`. The source imports are replaced by focused published
imports. As in the published sibling modules, every
`extensionSubgroup A B h` is expanded to its exact abbreviation body
`B.toSubgroup.subgroupOf A.toSubgroup`, which drops its unused proof
argument `h`. The unused source
`universe u`, `open KummerTheory` and `open CyclicCohomology` are omitted.
The source variable declarations, docstrings, binders, structure fields and
construction bodies are otherwise retained. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The Frobenius fixed field bundled with its proved absolute finiteness.
This is the field object used by valuation and unit APIs. -/
noncomputable def frobeniusFixedAbstractField
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : DegreeData.FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    [Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
        (baseField G).toSubgroup)] :
    FiniteAbstractField G where
  field := D.frobeniusFixedField K L hLK σ
  finite := inferInstance

/-- A finite normal tower between two Frobenius fixed fields.

The ambient Galois extension, both Frobenius elements, the fixed-field
inclusion, and exactly the finiteness hypotheses needed by the unit
representation are stored once.  In particular, downstream statements no
longer re-thread the proof-dependent subgroup inclusions and quotient
instances independently. -/
structure FrobeniusFixedFieldTower
    (D : DegreeData G) [IsTopologicalGroup G] where
  /-- The finite-residue field in which the ambient Galois extension begins. -/
  ambientBase : DegreeData.FiniteResidueAbstractField D
  /-- The ambient Galois subextension. -/
  ambient : GaloisSubextension ambientBase.field
  /-- The Frobenius element whose fixed field is the base of the tower. -/
  baseFrobenius :
    D.FrobeniusElements ambientBase ambient.field ambient.below
  /-- The Frobenius element whose fixed field is the top of the tower. -/
  fieldFrobenius :
    D.FrobeniusElements ambientBase ambient.field ambient.below
  /-- Inclusion of the top fixed field into the base fixed field. -/
  field_le_base :
    (D.frobeniusFixedField ambientBase ambient.field ambient.below
        fieldFrobenius).toSubgroup ≤
      (D.frobeniusFixedField ambientBase ambient.field ambient.below
        baseFrobenius).toSubgroup
  /-- The relative quotient between the two fixed fields is finite. -/
  finiteQuotient :
    Finite
      ((D.frobeniusFixedField ambientBase ambient.field ambient.below
          baseFrobenius).toSubgroup ⧸
        (D.frobeniusFixedField ambientBase ambient.field ambient.below
            fieldFrobenius).toSubgroup.subgroupOf
          (D.frobeniusFixedField ambientBase ambient.field ambient.below
            baseFrobenius).toSubgroup)
  /-- The base fixed field is finite over the distinguished base. -/
  baseAbsoluteFinite :
    Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField ambientBase ambient.field ambient.below
            baseFrobenius).toSubgroup.subgroupOf
          (baseField G).toSubgroup)
  /-- The top fixed field is finite over the distinguished base. -/
  fieldAbsoluteFinite :
    Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField ambientBase ambient.field ambient.below
            fieldFrobenius).toSubgroup.subgroupOf
          (baseField G).toSubgroup)
  /-- The relative subgroup between the fixed fields is normal. -/
  normal :
    ((D.frobeniusFixedField ambientBase ambient.field ambient.below
        fieldFrobenius).toSubgroup.subgroupOf
      (D.frobeniusFixedField ambientBase ambient.field ambient.below
        baseFrobenius).toSubgroup).Normal
  /-- The two chosen ambient Frobenius elements commute. -/
  commute :
    baseFrobenius.1 * fieldFrobenius.1 =
      fieldFrobenius.1 * baseFrobenius.1

namespace FrobeniusFixedFieldTower

variable {D : DegreeData G} [IsTopologicalGroup G]

/-- The lower fixed field, finite over the distinguished base. -/
noncomputable def base (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractField G := by
  letI : Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
            T.baseFrobenius).toSubgroup.subgroupOf
          (baseField G).toSubgroup) :=
    T.baseAbsoluteFinite
  exact D.frobeniusFixedAbstractField T.ambientBase T.ambient.field
    T.ambient.below T.baseFrobenius

/-- The upper fixed field, finite over the distinguished base. -/
noncomputable def field (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractField G := by
  letI : Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
            T.fieldFrobenius).toSubgroup.subgroupOf
          (baseField G).toSubgroup) :=
    T.fieldAbsoluteFinite
  exact D.frobeniusFixedAbstractField T.ambientBase T.ambient.field
    T.ambient.below T.fieldFrobenius

/-- The fixed-field inclusion as a bundled Galois subextension. -/
noncomputable def toGaloisSubextension (T : FrobeniusFixedFieldTower D) :
    GaloisSubextension T.base.field where
  field := T.field.field
  below := T.field_le_base
  normal := T.normal

/-- The finite extension between the two bundled fixed fields. -/
noncomputable def extension (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractFieldExtension G where
  field := T.field
  base := T.base
  below := T.field_le_base
  finiteQuotient := T.finiteQuotient

/-- A concrete lower-fixed-field element representing its Frobenius class. -/
structure Representative (T : FrobeniusFixedFieldTower D) where
  /-- The chosen element in the base fixed-field subgroup. -/
  element : T.extension.base.field.toSubgroup
  /-- The chosen element maps to the prescribed ambient Frobenius class. -/
  mapsToFrobenius :
    D.frobeniusFixedFieldToClosure T.ambientBase T.ambient.field
        T.ambient.below T.baseFrobenius element =
      D.frobeniusInClosure T.ambientBase T.ambient.field
        T.ambient.below T.baseFrobenius

/-- The extension subgroup of a bundled Frobenius fixed-field tower is normal. -/
instance extensionNormal (T : FrobeniusFixedFieldTower D) :
    (T.extension.field.field.toSubgroup.subgroupOf
      T.extension.base.field.toSubgroup).Normal :=
  T.normal

/-- A representative which generates the finite fixed-field quotient. -/
structure CyclicGenerator (T : FrobeniusFixedFieldTower D)
    extends Representative T where
  /-- Every relative Galois element is a power of the representative's class. -/
  generates :
    ∀ x :
      T.extension.base.field.toSubgroup ⧸
        T.extension.field.field.toSubgroup.subgroupOf
          T.extension.base.field.toSubgroup,
      x ∈ Subgroup.zpowers (QuotientGroup.mk toRepresentative.element)

/-- The Galois quotient of a bundled Frobenius fixed-field extension is finite. -/
instance extensionFinite (T : FrobeniusFixedFieldTower D) :
    Finite
      (T.extension.base.field.toSubgroup ⧸
        T.extension.field.field.toSubgroup.subgroupOf
          T.extension.base.field.toSubgroup) :=
  T.finiteQuotient

/-- The lower Frobenius fixed field in the tower is finite over the distinguished base field. -/
instance baseAbsoluteFiniteInstance (T : FrobeniusFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
            T.baseFrobenius).toSubgroup.subgroupOf
          (baseField G).toSubgroup) :=
  T.baseAbsoluteFinite

/-- The upper Frobenius fixed field in the tower is finite over the distinguished base field. -/
instance fieldAbsoluteFiniteInstance (T : FrobeniusFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField T.ambientBase T.ambient.field T.ambient.below
            T.fieldFrobenius).toSubgroup.subgroupOf
          (baseField G).toSubgroup) :=
  T.fieldAbsoluteFinite

end FrobeniusFixedFieldTower

/-- A Frobenius fixed-field tower whose ambient Galois extension is finite.
The additional finiteness is stored on the opaque quotient object exposed by
`GaloisSubextension`. -/
structure FiniteAmbientFrobeniusFixedFieldTower
    (D : DegreeData G) [IsTopologicalGroup G]
    extends FrobeniusFixedFieldTower D where
  /-- The ambient Galois quotient is finite. -/
  ambientFinite : Finite toFrobeniusFixedFieldTower.ambient.extensionQuotient

namespace FiniteAmbientFrobeniusFixedFieldTower

variable {D : DegreeData G} [IsTopologicalGroup G]

/--
The ambient Galois quotient stored in a finite Frobenius fixed-field tower is finite.
-/
instance ambientQuotientFinite
    (T : FiniteAmbientFrobeniusFixedFieldTower D) :
    Finite T.ambient.extensionQuotient :=
  T.ambientFinite

/-- Finiteness transported to the quotient presentation required by the
underlying Frobenius calculations. -/
noncomputable instance ambientRepresentedQuotientFinite
    (T : FiniteAmbientFrobeniusFixedFieldTower D) :
    Finite
      (T.ambientBase.field.toSubgroup ⧸
        T.ambient.field.toSubgroup.subgroupOf T.ambientBase.field.toSubgroup) :=
  Finite.of_equiv T.ambient.extensionQuotient
    T.ambient.extensionQuotientMulEquiv

end FiniteAmbientFrobeniusFixedFieldTower

end DegreeData

end

end Langlands.NYLL.ClassFormation
