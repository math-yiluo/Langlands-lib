/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.DeligneLaumon.ConstructibleTruncations
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport
import WeilConjectures.SmoothPurity.Sf.SfConstructibleHeart
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology

/-! # Exactness and lower bounds for field-coefficient compact support

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7, Lemmas 6.1.11--6.1.13;
Stacks Project, Tag 0G2A, part (3)
(blueprint: lem-zl-field-shriek-lower-bound).

Both coefficient categories and all morphism actions are the recorded constructions.
The common-stage assertion applies to every normalized compact-support coefficient action.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

open CategoryTheory.Triangulated

universe uC vC

open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport

end WeilConjectures
