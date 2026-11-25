/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.FieldTheory.NormalExtensionFixedFieldPurelyInseparable
import WeilConjectures.FieldTheory.NormalExtensionFixedFieldGalois

/-!
# The fixed field of all automorphisms of a normal extension

Source: Stacks Project, Fields, Lemma 030M (2), `lemma-normal-case`
(blueprint: lem-weil-pbc-normal-extension-purely-inseparable-then-galois).
-/

@[expose] public section

universe u v

namespace Normal

/-- For an algebraic normal extension `E/F`, its intermediate field fixed by all
`F`-automorphisms is purely inseparable over `F`, and `E` is separable algebraic and normal
 over that fixed field. Source: Stacks Project, Fields, Lemma 030M (2).
(blueprint: lem-weil-pbc-normal-extension-purely-inseparable-then-galois)

Proof:
1. Write `G = Aut(E/F)`. The elements fixed by `G` contain the image of `F` and are closed
under addition, subtraction, multiplication and inversion, since all elements of `G` are
`F`-algebra automorphisms. Thus they form the intermediate field `S = fixedField ⊤` below.
2. For each `a : E`, the roots in `E` of its minimal polynomial over `F` form a finite set.
Every automorphism permutes this set; conversely each root is the image of `a` under some
`F`-automorphism, by lem-weil-pbc-normal-extension-conjugate-by-automorphism (Stacks 0BME).
3. If `a` is fixed, normality and step 2 imply its minimal polynomial is `(T-a)^d`.
In characteristic zero the coefficient `-d*a` shows `a` lies in `F`. In characteristic `p`,
write `d = p^e*m` with `p` not dividing `m`. The coefficient of `T^(p^e*(m-1))` is
`-m*a^(p^e)`, so `a^(p^e)` lies in `F`. Hence `S/F` is purely inseparable
(def-weil-pbc-finite-purely-inseparable-extension, Stacks 09HE).
4. The extension `E/S` is algebraic and normal by
lem-weil-pbc-normal-extension-normal-over-intermediate (Stacks 09HN).
5. For `a : E`, form the monic product of `T-b` over the distinct roots `b` from step 2.
Its coefficients are fixed by `G`, hence lie in `S`. It vanishes at `a`, so the minimal
polynomial of `a` over `S` divides it. The product is separable, and so is this divisor,
by lem-weil-pbc-distinct-linear-factors-separable (Stacks 09H3). Thus `E/S` is separable
algebraic (def-weil-pbc-separable-algebraic-extension).
6. Steps 4 and 5 say `E/S` is Galois (Stacks 09I0); together with steps 1 and 3 they
prove all the asserted clauses, with no finiteness requirement on `G` or `E/F`. -/
theorem fixedField_purelyInseparable_and_galois
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [Normal F E] :
    IsPurelyInseparable F (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) ∧
      Algebra.IsSeparable (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E ∧
      Normal (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E := by
  let S := IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))
  have hp : IsPurelyInseparable F S :=
    fixedField_purelyInseparable F E
  have hg : Algebra.IsSeparable S E ∧ Normal S E :=
    fixedField_separable_normal F E
  exact ⟨hp, hg.1, hg.2⟩

end Normal
