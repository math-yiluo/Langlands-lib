# Transporting a common split torus into two supplied Levi subgroups

This internal reduction isolates the operation of moving an ambient maximal
split torus of an actual parabolic into a supplied rational Levi, and proves
the representative clause of `RepresentedParabolicDoubleCosetStatement`
from this operation and an actual common maximal split torus. The two structural
inputs remain hypotheses. The final assembly also retains the three hypotheses
of the separate finiteness reduction; it does not prove the closed target.

`ParabolicSplitTorusLeviConjugacyStatement` concerns an arbitrary field,
connected reductive `G`, actual parabolic `p : P ⟶ G`, supplied rational Levi
`l : M ⟶ P`, ambient maximal split torus `i : T.toGrp ⟶ G`, and supplied
factorization `f ≫ p = i`. It asserts the existence of a point `u ∈ P(k)`
and a morphism `a : T.toGrp ⟶ M` with
`a ≫ l ≫ p = i ≫ Int(p(u))`. Thus the torus parameter is preserved, and
containment is an equality of group-scheme morphisms.

The elementary transport lemma starts with a common torus `i` and points
`u ∈ P(k)`, `v ∈ Q(k)` moving `i` into `M` and `g⁻¹ i g` into `L`.
Writing `U = p(u)`, `V = q(v)`, it takes `z = U g V⁻¹`.
Then `g = U⁻¹ z V` proves equality of the literal double cosets.
The torus `i' = Int(U) ∘ i` remains maximal split under this ambient
isomorphism. Its factor through `M` is the supplied `a`. Its factor through
`z L z⁻¹` is the supplied `b`: composition with `Int(V)` and then `Int(z)`
equals composition with `Int(g)` and then `Int(U)`, since `z V = U g`.
The preceding `Int(g)⁻¹` therefore cancels.

The common-torus reduction applies
`ParabolicIntersectionSplitTorusStatement` to `p` and `q ≫ Int(g)`.
It applies the moving-torus statement first inside `P`, and then inside `Q`
to the torus `i ≫ Int(g)⁻¹`, using the supplied common-torus factors.
The elementary lemma produces exactly the representative, ambient maximal
split torus, and two factors requested by the published proposition.
The final assembly combines this result with
`finite_parabolicDoubleCosets_of_bruhat_minimal_conjugacy`.

The representative construction is derived from Borel–Tits, *Groupes réductifs*
(1965), 4.18, printed p.92 / PDF p.39, and the torus and Levi conjugacy
argument underlying 5.15, printed p.100 / PDF p.47. It expresses the same
common-torus consequence as Renard, *Représentations des groupes réductifs
p-adiques* (2026), V.4.7, printed pp.121–122 / PDF pp.127–128. The supplied
moving-torus assertion is an internal interface for that step, and neither
source is claimed to state it in this exact form.
