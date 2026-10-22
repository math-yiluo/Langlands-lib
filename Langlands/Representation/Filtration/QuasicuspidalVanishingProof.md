# Proof of the quasicuspidal-subquotient vanishing criterion

Author: Worker 221.

This pair proves the exact Library proposition
`Langlands.CuspidalSupport.PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement`
from `Langlands.Representation.Filtration.VanishingStatement`, as the theorem
`Langlands.CuspidalSupport.padicLeviFiltrationNoQuasicuspidalSubquotients`.
The carrier universe `uV` precedes the field universe `uF` in the universe
arguments, exactly as in the statement, and the two stay independent. The
statement pair and everything it imports are unchanged.

## Provenance and route

The statement is an internal derived criterion behind Bernstein and
Zelevinsky, *Induced representations of reductive p-adic groups. I*,
Ann. Sci. ENS (4) 10 (1977), Corollary 2.13(a),(b) (printed p.449), using
finite gluing by actual successive quotients (§1.10–1.11, printed p.445)
and the remark of §2.4 (printed p.446) that subquotients of quasicuspidal
representations are quasicuspidal.

The route sketched in the statement's Markdown would induce a filtration on
the tested subquotient, use hereditary quasicuspidality to make each induced
graded piece quasicuspidal, and then apply the zero criterion. The
implemented proof avoids hereditary quasicuspidality for subrepresentations
(which relies on the exactness of the Jacquet functor, BZ77 §2.3(a)). It
only uses that
quasicuspidality passes to *quotients*, which follows from right exactness
of coinvariants, and runs a downward induction on the induced filtration
instead.

## Auxiliary results

All auxiliary declarations live in this module.

- `SmoothRep.kernelLift` and `SmoothRep.kernelLift_mkQ`. For smooth
  morphisms `φ : P ⟶ Z` and `ψ : P ⟶ Y` with `ker φ ≤ ker ψ`, the morphism
  `ψ` descends to a smooth morphism from the actual quotient
  `SmoothRep.quotient P (ker φ)` to `Y`, built from `Submodule.liftQ`; on
  classes it is `ψ`.
- `SmoothRep.isSubquotient_of_ker_le`. If moreover `ψ` is surjective, then
  `Y` is a smooth subquotient of `Z`. Using the Library characterization
  `SmoothRep.isSubquotient_iff_exists` (some smooth representation embeds in
  `Z` and maps onto `Y`), the witness is `P / ker φ`, embedded in `Z` by the
  descent of `φ` (injective by construction) and mapped onto `Y` by the
  descent of `ψ`.
- `CuspidalSupport.isLeviQuasicuspidal_of_surjective`. A surjective
  intertwiner `f` from `ρ` to `σ` (representations of `B.Levi F` on possibly
  different carrier universes) transports quasicuspidality from `ρ` to `σ`.
  For each proper standard block refinement `S`, `f` induces the map
  `Representation.Coinvariants.map` of actual unipotent coinvariant modules
  for `refinedUnipotent F B S` (via `Jacquet.restrictMap`). This map is
  surjective because `Jacquet.mk` is surjective and `f` is, so the target is
  a subsingleton when the source is (`Function.Surjective.subsingleton`).
- `ObjectRepFiltration.pullStep` and `ObjectRepFiltration.imageStep`. Given
  a filtration `s` of `M` with steps `S_k`, a morphism `i : C ⟶ M` and a
  morphism `q : C ⟶ X`, `pullStep s i k` is the invariant subspace
  `i⁻¹(S_k)` of `C`, and `imageStep s i q k` is its image `q(i⁻¹(S_k))`
  in `X`. When `i` is injective and `q` surjective, these images form the
  filtration that `s` induces on the subquotient `X`.
- `ObjectRepFiltration.pullStepRestrict`. The restriction of `i` to an
  intertwiner from `i⁻¹(S_k)` (with its smooth subrepresentation structure)
  to `S_k`.
- `ObjectRepFiltration.isSubquotient_quotient_imageStep`. Let `j : Fin r`
  and suppose `imageStep s i q (j+1)` is all of `X`. Let `Q` be smooth and
  `e` an actual equivalence from the `j`th graded representation to `Q`.
  Then the actual quotient `X / imageStep s i q j` is a smooth subquotient
  of `Q`. Proof: with `P` the smooth subrepresentation `i⁻¹(S_(j+1))` of
  `C`, take `φ : P ⟶ Q` to be `e` after the graded projection after
  `pullStepRestrict`, and `ψ : P ⟶ X / imageStep s i q j` to be the
  inclusion, then `q`, then the quotient map. The map `ψ` is surjective
  because every vector of `X` is `q v` for some `v` in `i⁻¹(S_(j+1))`. If
  `φ v = 0`, injectivity of `e` makes the graded class of `i v` zero, and
  `Submodule.Quotient.mk_eq_zero` (the graded quotient is the quotient of
  `S_(j+1)` by the inverse image of `S_j`) gives `i v ∈ S_j`, so
  `q v ∈ imageStep s i q j` and `ψ v = 0`. Thus
  `ker φ ≤ ker ψ`, and `isSubquotient_of_ker_le` applies.

## Main proof

Fix the data of the statement, with the local instance `T.topology`, and a
smooth subquotient `D` of `A` with `IsLeviQuasicuspidal B D.representation`.
By `SmoothRep.isSubquotient_iff_exists`, choose smooth `C` with an
injective `i : C ⟶ A` and a surjective `q : C ⟶ D`.

Claim: for every `k : Fin (r + 1)`, every vector of `D` lies in
`imageStep s i q k`. The proof is downward induction with
`Fin.reverseInduction`.

- For `k = r`, the step `S_r` is everything (`subrepresentation_last`), so
  `i⁻¹(S_r)` is all of `C`, and every vector of `D` is `q v` by
  surjectivity of `q`.
- For `k = j < r`, assume the claim at `j + 1`. The hypothesis on `s` gives
  `Q`, an equivalence `e`, and the vanishing property of `Q`. By
  `isSubquotient_quotient_imageStep`, the quotient `D / imageStep s i q j`
  is a smooth subquotient of `Q`. It is also quasicuspidal by
  `isLeviQuasicuspidal_of_surjective` applied to the surjective quotient
  map from `D`. The hypothesis therefore makes it a subsingleton, so every
  class in it is zero, and every vector of `D` lies in
  `imageStep s i q j` (`Submodule.Quotient.mk_eq_zero`).

At `k = 0`, any `x : D` is `q v` with `i v ∈ S_0 = ⊥`
(`subrepresentation_zero`), so `i v = 0`. Injectivity of `i` gives `v = 0`,
hence `x = q 0 = 0`. Thus every vector of `D` is zero and `D` is a
subsingleton.

No admissibility, irreducibility, finiteness or positive-rank assumption is
used, and length `r = 0` is covered by the same argument (the induction has
only its base case). The zero criterion
`Langlands.objectRepFiltrationSubsingleton` is not invoked, and this module
does not import its proof module; it imports only the statement module and
`Langlands.Representation.Classification.SupercuspidalSupport` (for
`SmoothRep.isSubquotient_iff_exists`).

## Axioms

`lean_check` inspection reports only `propext`, `Classical.choice` and
`Quot.sound`.
