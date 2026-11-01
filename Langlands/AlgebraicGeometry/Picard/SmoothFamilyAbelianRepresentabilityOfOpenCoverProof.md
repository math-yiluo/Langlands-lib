# Proof: Zariski-local existence of an abelian-scheme smooth-family representer

The theorem `Langlands.AbelianScheme.smoothFamilyAbelianRepresentabilityOfOpenCover`
proves the published
`Langlands.AbelianScheme.SmoothFamilyAbelianRepresentabilityOfOpenCoverStatement.{u}`
without hypotheses.

It is assembled in two steps. First,
`Langlands.AbelianScheme.SmoothFamilyOpenCover.smoothFamilyAbelianRepresentabilityOfOpenCover_of`
derives the target from the two published statements
`RigidifiedClassesZariskiGluingStatement.{u}` (Zariski gluing of actual
rigidified classes) and `AbelianSchemeStructureOfOpenCoverStatement.{u}`
(an abelian-scheme structure on a scheme with a section that is locally
isomorphic to abelian schemes). Second, both premises are discharged by
published theorems:

- `Langlands.AbelianScheme.abelianSchemeStructureOfOpenCover` (module
  `Langlands.AbelianScheme.AbelianSchemeStructureOfOpenCoverProof`) proves the
  abelian-structure statement. Applying it gives
  `SmoothFamilyOpenCover.smoothFamilyAbelianRepresentabilityOfOpenCover_of_gluing`,
  whose only hypothesis is the gluing statement.
- `Langlands.AbelianScheme.rigidifiedClassesZariskiGluing` (module
  `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiGluingProof`)
  proves the gluing statement. Applying `_of_gluing` to it gives the final
  theorem.

The statement quantifies over a quasi-separated `S : Scheme.{u}`, an abelian
scheme `A` over `S` and an open cover `𝒰` of `S` indexed in universe `u`. It
assumes that each restriction `(baseChange (𝒰.f i)).obj A` has an abelian
scheme `B i` over `𝒰.X i` with a family `L i` universal on quasi-separated
tests, and concludes that `A` has such a pair over `S`.

## Proof

1. **Translation.** `M i := (familyBaseChangeInverse (𝒰.f i) A (B i).X).obj (L i)`
   is a family for `A` on `chartParam 𝒰.f B i`, which is `(B i).X` viewed
   over `S` through `𝒰.f i`. It is universal over the range of `𝒰.f i`
   (`isUniversalOn_familyBaseChangeInverse`) and smooth-family
   algebraically trivial. The structure map is proper followed by an open
   immersion, hence quasi-separated. These data form `chartData`.
2. **Gluing.** [`SmoothFamilyOpenCoverGluing`](SmoothFamilyOpenCoverGluing.md)
   glues the parameters over the basis cover `basisCover` of `S`, whose
   members are the opens contained in some range of `𝒰.f i`. With the gluing
   statement, `exists_universal` gives a universal family `L₀` on the glued
   parameter `P`.
3. **A section.** The trivial rigidified family on `Over.mk (𝟙 S)` satisfies
   the smooth-family condition (`isAlgebraicallyTrivialFamily_trivial`). On
   each geometric fibre it is the trivial bundle, witnessed by the constant
   trivial family on the fibre abelian variety itself, which is geometrically
   integral by the published `smoothGeometricIntegrality`
   (`isAlgebraicallyTrivialViaSmoothFamily_trivial`). Since `S` is
   quasi-separated, universality of `L₀` gives its classifying map, a section
   `s` of `P`.
4. **Local charts.** For each basis open `V` inside the range of `𝒰.f i`,
   `exists_chart` identifies `(Over.pullback V.ι).obj P` with the base change
   of `B i` along the lift `V ⟶ 𝒰.X i`. It composes the pullback square
   `isPullback_natTrans_ι_toBase` of relative gluing with the square
   expressing the preimage of `V` in `B i` as a pullback
   (`pullbackIsPullbackOfCompMono`).
5. **Abelian structure.** The abelian-structure statement, applied to `P`,
   `s` and the basis cover, gives `B' : AbelianScheme S` and `e : P ≅ B'.X`.
   Its section-compatibility conclusion is not needed.
6. **Transport.** `isUniversal_of_iso` shows that `(rp e.inv).obj L₀` on `B'.X`
   is universal on quasi-separated tests. Pullback preserves the smooth-family
   condition (`smoothFamilyPullback`), and classifying maps correspond by
   composition with `e`.

The proof adds no hypothesis on `S` beyond quasi-separatedness, and none on
the cover. It uses quasi-separatedness of `S` for the local parameters and
for `Over.mk (𝟙 S)` as a test. The universal property and the conclusion
concern the actual published `IsUniversalSmoothFamilyOnQuasiSeparatedTests`
predicate.

## Provenance

This is an internal derived argument. It reconstructs a representing object
from local ones (Yoneda), uses Mathlib's relative gluing (Stacks 01LH), and
relies on the published Zariski separatedness of rigidified classes. It also
uses the two split statements named above, which were stated and proved in
separate tasks. Their published proofs are imported by Lean name.
