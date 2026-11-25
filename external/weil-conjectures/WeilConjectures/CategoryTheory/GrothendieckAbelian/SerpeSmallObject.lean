/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.SmallObject.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.GeneratingMonoQuasiIsos
public import WeilConjectures.Mathlib.CategoryTheory.Subobject.HasCardinalLT

/-!
# The small object argument for monomorphic quasi-isomorphisms

Let `C` be a Grothendieck abelian category, `G : C` an object and `κ` a cardinal. In this file
we show that the family `CochainComplex.generatingMonoQuasiIsos G κ` of monomorphic
quasi-isomorphisms permits the small object argument.

The argument is the one used in `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/`
`EnoughInjectives.lean` for the family of inclusions of subobjects of a generator, transposed
to the Grothendieck abelian category `CochainComplex C ℤ`: the witnessing cardinal is a
regular cardinal `κ₂` strictly larger than the cardinality of the lattice of subobjects of
`CochainComplex.diskCopower G κ`. Every source of a map of the family is a subquotient of
that complex, so its lattice of subobjects is also of cardinality `< κ₂`, and the functor it
corepresents therefore commutes with the `κ₂`-filtered colimits of monomorphisms produced by
the small object argument.

## Main results

- `CochainComplex.hasSmallObjectArgument_generatingMonoQuasiIsos`: the family
  `CochainComplex.generatingMonoQuasiIsos G κ` permits the small object argument.
-/

@[expose] public section

universe w v u

namespace CochainComplex

open CategoryTheory Limits MorphismProperty

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (κ : Cardinal.{w})

instance hasSmallObjectArgument_generatingMonoQuasiIsos :
    HasSmallObjectArgument.{w} (generatingMonoQuasiIsos G κ) := by
  obtain ⟨κ₂, hκ₂', hκ₂⟩ :=
    HasCardinalLT.exists_regular_cardinal.{w} (Subobject (diskCopower G κ))
  have : Fact κ₂.IsRegular := ⟨hκ₂'⟩
  have : Nonempty κ₂.ord.ToType := by simpa using hκ₂'.ne_zero
  have := WellFoundedLT.toOrderBot κ₂.ord.ToType
  exact ⟨κ₂, inferInstance, inferInstance,
    { preservesColimit {A B X Y} i hi f hf := by
        let hf' : (monomorphisms (CochainComplex C ℤ)).TransfiniteCompositionOfShape
            κ₂.ord.ToType f :=
          { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
            map_mem j hj := by
              have := (hf.attachCells j hj).pushouts_coproducts
              simp only [ofHoms_homFamily] at this
              refine (?_ : _ ≤ monomorphisms _) _ this
              simp only [pushouts_le_iff, coproducts_le_iff]
              exact (generatingMonoQuasiIsos_le G κ).trans inf_le_left }
        have (j j' : κ₂.ord.ToType) (φ : j ⟶ j') : Mono (hf'.F.map φ) := hf'.mem_map φ
        apply IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono (Y := hf'.F) (κ := κ₂)
        obtain ⟨p⟩ := hi
        exact Subobject.hasCardinalLT_of_mono
          (Subobject.hasCardinalLT_of_epi (Subobject.hasCardinalLT_of_mono hκ₂ p.V.arrow)
            (cokernel.π p.K.arrow)) p.T.arrow }⟩

end CochainComplex
