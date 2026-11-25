# Reductions between the totally complex forms of the cuspidal-pair and associated-factor statements

**Scope.** The module `Langlands.Automorphic.AssociatedFactorTCReductionStatement`
defines three propositions and proves nothing. Each is an implication between totally
complex forms stated in `Langlands.Global.Factors.CuspidalPairFunctionalEquationTCStatement`
and `Langlands.Automorphic.AssociatedFactorTCStatement`. Each is the totally complex
form of one link of the Library's route from the global functional equations to
Henniart's Corollaire 2.4. The three links are proved in separate modules:
`cuspidalPairFunctionalEquationReductionTC`
(`Langlands.Global.Factors.CuspidalPairFunctionalEquationReductionTCProof`),
`associatedGammaReductionTC` (`Langlands.Automorphic.AssociatedGammaTCReductionProof`) and
`associatedCuspidalFactorReductionTC` (`Langlands.Automorphic.AssociatedCuspidalFactorReductionTC`).

| New proposition | Universes | Implication |
|---|---|---|
| `Langlands.Global.CuspidalPairFunctionalEquationReductionTCStatement` | `u uQ` | local data, A1TC, A2TC ⟹ A3TC |
| `Langlands.ClassFieldTheory.Global.RelativeWeilGroup.AssociatedGammaReductionTCStatement` | `u uV uP uQ uE` | A3TC at `{u, u}` ⟹ B1TC |
| `Langlands.ClassFieldTheory.Global.RelativeWeilGroup.AssociatedCuspidalFactorReductionTCStatement` | `u uV uP uQ uE` | B3TC, B2TC ⟹ B4TC |

Here A1TC–A3TC are `CuspidalArchimedeanParameterExistenceTCStatement`,
`CuspidalPairCompletedEquationTCStatement` and
`CuspidalPairGlobalFunctionalEquationTCStatement`, and B1TC–B4TC are
`AssociatedGammaTCStatement`, `AssociatedTemperedFactorTCStatement`,
`AssociatedSupercuspidalInductionTCStatement` and `AssociatedCuspidalFactorTCStatement`
(see the paired Markdown of those two modules). The principal declaration of the module
is `Langlands.ClassFieldTheory.Global.RelativeWeilGroup.AssociatedGammaReductionTCStatement`.

## 1. The three implications

1. **Link 1, the functional equation from its parts.**
   `CuspidalPairFunctionalEquationReductionTCStatement.{u, uQ}` is
   `CuspidalPairLocalDataStatement.{u, uQ} →
   CuspidalArchimedeanParameterExistenceTCStatement.{u} →
   CuspidalPairCompletedEquationTCStatement.{u, uQ} →
   CuspidalPairGlobalFunctionalEquationTCStatement.{u, uQ}`. It is the published
   `CuspidalPairFunctionalEquationReductionStatement`
   (`Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction`) with its
   second, third and fourth propositions replaced by their totally complex forms. The
   first input, the published `CuspidalPairLocalDataStatement` (the finite local data,
   the archimedean additive components and the unramified identities), has no
   archimedean parameter clause and is kept unrestricted.
2. **Link 2, Théorème 2.3 from the functional equation.**
   `AssociatedGammaReductionTCStatement.{u, uV, uP, uQ, uE}` is
   `CuspidalPairGlobalFunctionalEquationTCStatement.{u, u} →
   AssociatedGammaTCStatement.{u, uV, uP, uQ, uE}`. It is the totally complex form of
   the published theorem `associatedGamma_of_inputs`
   (`Langlands.Automorphic.AssociatedGammaFinal`), which derives
   `AssociatedGammaStatement.{u, uV, uP, uQ, uE}` from
   `CuspidalPairGlobalFunctionalEquationStatement.{u, u}` and
   `StableTwistPairGammaMatchStatement.{u, uV, uE}`. The second input is proved in the
   Library (`stableTwistPairGammaMatchStatement`,
   `Langlands.Automorphic.StableTwistGammaMatchProof`), so it is not a hypothesis here.
   The functional equation is needed at the factor universe `u`, as in the original.
3. **Link 3, Corollaire 2.4 from Théorème 2.4 and Corollaire 2.3.**
   `AssociatedCuspidalFactorReductionTCStatement.{u, uV, uP, uQ, uE}` is
   `AssociatedSupercuspidalInductionTCStatement.{u, uV, uP, uQ} →
   AssociatedTemperedFactorTCStatement.{u, uV, uP, uQ, uE} →
   AssociatedCuspidalFactorTCStatement.{u, uV, uP, uQ, uE}`, the published
   `AssociatedCuspidalFactorReductionStatement`
   (`Langlands.Automorphic.AssociatedCuspidalFactorReduction`) with its three
   propositions replaced by their totally complex forms. The five universe levels are
   independent, as in the original.

## 2. Why these links hold

Each published link is proved, or reduced to proved inputs, by an argument that
applies its inputs at the same base field (and, for links 2 and 3, at the same
extension) as its conclusion. With the new instance in scope, the same argument
applies to the totally complex forms.

- Link 1: the published `cuspidalPairFunctionalEquationReduction` combines, at one
  field `F`, the local data, the parameters of the four realizations and the completed
  equation for the finite set given by the local data. A private development check
  compiled the same proof term for the totally complex form.
- Link 2: `associatedGamma_of_inputs` applies the functional equation at the base
  field `F` of the conclusion, to pairs built from Hecke twists over `F`. Its proof
  passes through published auxiliary results that take the unrestricted functional
  equation as a hypothesis: `exists_engineInputs`
  (`Langlands.Automorphic.AssociatedGammaAutomorphicFamily`),
  `commonTwistEulerInputs_families` (`Langlands.Automorphic.AssociatedGammaCommonInputs`)
  and `hasHeckeGammaCertificate_setups` (`Langlands.Automorphic.AssociatedGammaFinal`). A proof of the totally complex form
  needs copies of these with the totally complex hypothesis and the instance added.
- Link 3: the published `associatedCuspidalFactor_of_supercuspidalInduction_of_tempered`
  applies Théorème 2.4 to each realization, deduces temperedness of the local
  components from the published
  `Classification.isTempered_of_equiv_unitarizableSupercuspidalProduct`, restricts
  unitarity along the local map with `localComponent_isUnitary`, and applies
  Corollaire 2.3 at the same data. A private development check compiled
  the same proof for the totally complex form, with the instance introduced.

These checks are not part of this module, which proves nothing.

## 3. Relation to the published links

Each new implication has the same shape as its published link, with the unrestricted
propositions replaced by their totally complex forms. Neither implies the other in
general: the totally complex link has weaker hypotheses and a weaker conclusion. The
totally complex links are the ones the Library's route needs, because the route uses
the global inputs only over totally complex fields
(`HenniartCandidateExistenceTCReductionStatement.md` §3).

## 4. Sources and provenance

Provenance: *derived*. The implications record how Henniart's arguments combine the
results, restricted to totally complex base fields; they are not stated as such in the
sources.

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
  p-adique*, Invent. Math. 139 (2000), 439–455 (`henniart-2000-simple-proof`). §2.3,
  printed pp.444–445 (PDF 6–7): Théorème 2.3 from the global functional equations of
  pair L-functions (link 2). §2.4, printed p.445 (PDF 7): Corollaire 2.4 from Théorème
  2.4 and Corollaire 2.3 (link 3).
- G. Henniart, *On the local Langlands conjecture for GL(n): the cyclic case*, Ann. of
  Math. 123 (1986), 145–203 (`henniart-1986-cyclic`). Theorem 4.1, printed p.157
  (PDF 14), and §4.3, printed pp.158–159 (PDF 15–16): the gamma equality from the
  global functional equations (link 2).
- J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in J. Bernstein and
  S. Gelbart (eds.), *An Introduction to the Langlands Program*, Birkhäuser, 2004,
  197–228 (`cogdell-2004-analytic-theory-gln`), Theorem 4.1, printed p.219 (PDF 222),
  and J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, GTM 300,
  Springer, 2024 (`getz-hahn-2024-automorphic-representations`), Theorem 11.7.1,
  printed p.309 (PDF 320): the completed global functional equation, whose finite,
  archimedean and completed parts link 1 combines.
