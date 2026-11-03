# Sections of split-unipotent torsors over affine schemes

`Langlands.GroupScheme.SplitUnipotentAffineTorsorStatement` is a proposition
target, at arbitrary universe `u` and over every field `k`. It states that an
actual fpqc torsor under a smooth affine split-unipotent `k`-group has a section
over every affine `k`-scheme.

The group `H` is an existing actual `GroupScheme (Spec k)`. Split unipotence
uses `RelativeRoot.IsSplitUnipotent` unchanged: a finite normal series with
represented fppf quotients that are one-dimensional vector groups. No selected
series, coordinates, rational-point lift, or cohomology-vanishing theorem is an
additional premise.

The affine base is any relative scheme `T` over `Spec k`, with no reducedness,
finite-type, smoothness or nonemptiness restriction. The acting group over
`T.left` is the actual scheme pullback
`(GroupScheme.baseChange T.hom).obj H`. The scheme `X` lies over `T.left`, and
`ModObj` supplies its lawful left action. Flatness, surjectivity and
quasi-compactness of `X.hom`, together with invertibility of the actual shear
`(h,x) ↦ (h • x,x)`, express the fpqc torsor condition. Products and the shear
are in the slice over `T.left`; thus their target is the fiber product over
that affine base. The conclusion is an actual scheme morphism
`s : T.left ⟶ X.left` satisfying `s ≫ X.hom = 𝟙 T.left`.

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), the first paragraph of the proof of Lemma C.2.1, printed p.592 /
one-based PDF p.618. It explicitly uses vanishing of `H¹(X,U)` for every
affine `k`-scheme and split-unipotent `U`, reducing along a split series to the
additive group and then to quasi-coherent cohomology on an affine scheme.
The present target isolates that input from the induction on the ambient
group in C.2.1. It includes finite fields, since this input does not use the
infinite-field assumption of the subsequent quotient argument.

This is a derived formulation of that source passage. It uses actual left
actions and fpqc torsors instead of the passage's pointed étale cohomology
sets. For a smooth affine group the torsor descriptions agree: a torsor is
locally isomorphic to the group, is smooth over its base, and admits étale
local sections. These comparisons and the vanishing argument remain proof
obligations. This file proves neither the torsor statement nor the
pseudo-parabolic rational-lifting theorem, and supplies no quotient existence
or split-radical reduction theorem.
