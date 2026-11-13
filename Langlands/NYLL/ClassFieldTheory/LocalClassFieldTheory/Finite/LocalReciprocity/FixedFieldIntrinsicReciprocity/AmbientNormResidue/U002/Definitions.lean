/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only M282.002 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientNormResidue.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and keep the structure's parameters, docstrings and fields. Replace
the source imports by the published modules defining finite abstract
fields, finite Galois subextensions and abstract fixed fields (the last
imports closed fixing subgroups) together with the Mathlib modules for
separable closures, nonarchimedean local fields and valuation extensions,
and open only the namespaces of closedFixingSubgroup and of the two class
formation structures. Omit all other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions

/-!
# Ambient fixed-field presentations of embedded Galois extensions

A bundled presentation of a finite Galois extension `E / F` of local fields,
embedded over `K` into the separable closure of `K`, by actual fixed fields
of closed subgroups of the absolute Galois group of `K`.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.RamificationTheory Langlands.NYLL.ClassFormation

/-- A finite fixed-field presentation of an embedded finite Galois extension.

The object records the actual ambient fixed-field quotient, its realization of
the embedded base field, and the quotient map to the original Galois group.
It is the common interface for calculations that use the ambient
norm-residue value without unfolding the construction of that presentation. -/
structure AmbientEmbeddedFixedFieldPresentation
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) where
  /-- The given base field embedded in the ambient separable closure. -/
  baseEmbedding : F →ₐ[K] SeparableClosure K
  /-- The finite ambient fixed field representing the embedded base field. -/
  base : FiniteAbstractField Gal(SeparableClosure K / K)
  /-- The finite Galois ambient fixed-field extension representing `E / F`. -/
  extension : FiniteGaloisSubextension base.field
  /-- The base embedding is induced by the embedding of the top field. -/
  baseEmbedding_eq :
    baseEmbedding = j.comp (IsScalarTower.toAlgHom K F E)
  /-- The ambient base subgroup fixes precisely the range of the base embedding. -/
  base_field_eq :
    base.field =
      closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange baseEmbedding)
  /-- The ambient top subgroup fixes precisely the range of the top embedding. -/
  extension_field_eq :
    extension.field =
      closedFixingSubgroup K (SeparableClosure K)
        (AlgHom.fieldRange j)
  /-- The actual equivalence from the given base field to its ambient fixed field. -/
  baseEquiv :
    F ≃ₐ[K] abstractFixedField K (SeparableClosure K) base.field
  /-- The base-field equivalence realizes the chosen ambient embedding. -/
  baseEquiv_apply (x : F) :
    ((baseEquiv x :
      abstractFixedField K (SeparableClosure K) base.field) :
        SeparableClosure K) =
      baseEmbedding x
  /-- The actual quotient equivalence to the original Galois group. -/
  quotientEquiv : extension.extensionQuotient ≃* Gal(E / F)
  /-- The quotient equivalence acts through the supplied ambient embedding. -/
  quotientEquiv_mk_apply
      (sigma : base.field.toSubgroup) (x : E) :
    j (quotientEquiv (extension.extensionQuotientMk sigma) x) =
      sigma.1 (j x)

end Langlands.NYLL.LocalClassFieldTheory

end
