/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper, Kevin Buzzard, Ruben Van de Velde

Until 22 November 2026 this module held the Library's adaptation (2026) of the canonical maps
of Imperial FLT, commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean:28-91 and
FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean:40-88. All its declarations have the names
that the Imperial project gives them, so they moved to the staged files
`Langlands/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` and
`Langlands/Mathlib/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean` (Imperial commit
019805815d7da565ed1e9f427b6fbd0cbc9d00d3). The upstream license is retained at
licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Langlands.Mathlib.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct

/-!
# Tensor product distributing over a restricted product: the canonical maps

This module declares nothing. It imports the staged modules that hold
`RestrictedProduct.mapAlongLinearMap`, `RestrictedProduct.mapAlongLinearMap_apply`,
`RestrictedProduct.inclusionLinearMap`, `RestrictedProduct.rangeLTensor`,
`RestrictedProduct.rangeLTensorLeft`, `RestrictedProduct.lTensor`, `RestrictedProduct.lTensorLeft`,
`RestrictedProduct.lTensor_tmul` and `RestrictedProduct.lTensorLeft_tmul`, so that the statement and
proof modules of this directory, which import it, keep their place in the import graph.
-/
