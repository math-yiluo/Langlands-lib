/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# Equivariant multiplicative homomorphisms as integral representation morphisms

Modified by Worker 5454: extract M116.002
`CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantRepHom` (lines 32–43)
and M116.004 `CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantShortComplex`
(lines 52–65) from the pinned NYLL
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/TateComparison.lean` and
prefix the namespace with `Langlands.NYLL`. The section `variable` commands of
source lines 27–30 are kept verbatim, so each definition includes exactly the
section variables it uses, as in the source. The source's NYLL imports are
replaced by the two Mathlib modules that supply `Rep.ofMulDistribMulAction`,
`Rep.ofHom` and `ShortComplex`. The unused `universe u w` (needed in the source
only by the private theorem of lines 20–25, which is not part of this unit) is
omitted. The constructions, including their proof fields, are unchanged. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

open CategoryTheory

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

noncomputable section

variable {G A B C : Type}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

/-- An equivariant homomorphism of multiplicative `G`-modules, regarded as
the corresponding morphism between mathlib's additive `ℤ`-representations. -/
def equivariantRepHom (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    Rep.ofMulDistribMulAction G A ⟶ Rep.ofMulDistribMulAction G B :=
  Rep.ofHom <|
    (MonoidHom.toAdditive f).toIntLinearMap.intertwiningMap_of_isIntertwiningMap
      (Rep.ofMulDistribMulAction G A).ρ
      (Rep.ofMulDistribMulAction G B).ρ <| by
      intro g a
      apply Additive.ofMul.injective
      exact hf g a.toMul

/-- The short complex of mathlib representations associated to two
equivariant multiplicative homomorphisms whose composite is trivial. -/
def equivariantShortComplex
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b) :
    ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (equivariantRepHom i hi) (equivariantRepHom j hj) <| by
    apply Rep.hom_ext
    ext a
    change Additive.ofMul (j (i a.toMul)) = 0
    apply Additive.ofMul.injective
    exact (hker (i a.toMul)).2 ⟨a.toMul, rfl⟩

end

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
