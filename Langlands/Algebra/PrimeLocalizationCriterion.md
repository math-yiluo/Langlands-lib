# Prime-localization criteria

These elementary internal helpers support the local algebra approximation construction for Stacks 00QV. They are derived directly from Mathlib's characterization of localization, rather than additional assumptions on the system.

The first theorem uses a local target and fractions with denominators whose images are units. Its kernel hypothesis asserts that an element sent to zero is annihilated by such a denominator. The prime is the inverse image of the maximal ideal of the target. The proof checks the three localization axioms; the equality axiom follows by applying the kernel condition to a difference.

The second theorem specializes the criterion to an existing localization at an arbitrary submonoid and a local target. Fractions and annihilators come from the existing localization.

The common-localization consequence uses two localizations of a common ring with a supplied compatible algebra structure between them. It enlarges the final denominator submonoid to the complement of the contracted maximal ideal, then applies Mathlib’s intermediate-localization theorem. The conclusion keeps the supplied algebra structure, so it can later be applied to an actual tensor transition.

The tensor helper considers a pushout `Q'` of `Q` along `A → B`, and an existing localization `L` of `Q`. A supplied `B`-algebra map `ψ : Q' → L ⊗[A] B` is required to agree with the canonical map from `Q`. The tensor product is then a localization of `Q'` at the image of the original denominator submonoid, using precisely `ψ.toAlgebra`. The proof uses composition of pushout squares and Mathlib's equivalence between localization base change and pushouts.

The final consequence accepts an actual ring map `f : L ⊗[A] B → C`, where `C` is a local localization of `Q'`. The compatibility equation `f ∘ ψ = algebraMap Q' C` is required. It proves the prime-localization condition with exactly `f.toAlgebra`; the prime is the inverse image under `f` of the maximal ideal of `C`. The proof combines the tensor-localization helper with the common-localization criterion. No tensor equivalence replaces the actual map.

The canonical `tensorPushoutMap` constructs the supplied map `ψ` from the pushout universal property, and `tensorPushoutMap_comp` checks its agreement with the original algebra `Q`. These are small interface helpers; no localization hypothesis is needed for them.

The compatibility lemma `comp_tensorPushoutMap` proves equality after composition with this canonical map by checking the original algebra `Q` and the new base ring `B`. Its proof pulls back along the pushout equivalence and checks pure tensors and addition. The canonical version of the prime-localization theorem uses those two checks in place of supplying `ψ` and its composite equality. It still concludes localization for precisely the supplied ring map `f`.
