# Existence of smoothenings over Henselian discrete valuation rings

Authors: Worker 50 and Worker 348.

`Langlands.GroupScheme.IntegralModel.smoothening_exists : SmootheningStatement.{u}` proves the
Library statement `Langlands.GroupScheme.IntegralModel.SmootheningStatement` (module
`Langlands.GroupScheme.IntegralModel.Smoothening`) at an arbitrary universe `u`, with its
hypotheses unchanged. This is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Appendix A.6
(literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`), over a Henselian discrete valuation
ring `R` with algebraically closed residue field.

## The statement

Let `R` be a Henselian discrete valuation ring with algebraically closed residue field and
fraction field `K`. Let `G` be an affine group scheme over `Spec K` with smooth structure
morphism, and let `M : IntegralModel R K G` be an integral model. The statement asks for an
integral model `N` and a model morphism `π : N.Hom M (𝟙 G)` such that:

1. `N.group` is smooth over `Spec R`;
2. composition with `π` is a bijection on `R`-sections;
3. every homomorphism from a smooth group scheme over `Spec R` to `M.group` factors uniquely
   through `π`.

## The proof

The proof is the one-line combination of two results. Their modules are included in this
contribution.

1. `Langlands.GroupScheme.IntegralModel.Smoothening.smoothening_of_finiteType`
   (module `Smoothening.Model`, Worker 50) reduces the statement to
   `IntegralFunctionsFiniteTypeStatement.{u}` (module
   `Langlands.GroupScheme.IntegralModel.IntegralFunctions`).
   - Let `A` be the coordinate Hopf algebra of `M.group`. Let `B = integralFunctions R K A` be the
     ring of functions on the generic fibre with values in `R` at every `R`-point.
   - If `B` is finitely generated, then `Spec B`, with the map induced by `A → B`, is a
     smoothening. `B` is a Hopf algebra (`Smoothening.Hopf`) with smooth generic fibre and reduced
     special fibre, hence smooth (`Smoothening.Smoothness`).
   - `R`-points of `Spec B` and of `M.group` correspond (`Smoothening.SmoothSections`), and
     homomorphisms from smooth group schemes lift (`Smoothening.Lift`). These are described in
     `Smoothening/Model.md` and the Markdown files of the other `Smoothening` modules.
2. `Langlands.GroupScheme.IntegralModel.Smoothening.Termination.integralFunctions_finiteType`
   (module `Smoothening.TerminationMain`, Worker 348) proves
   `IntegralFunctionsFiniteTypeStatement.{u}`. This is the counterpart of the termination Theorem
   A.6.2 of the source.
   - `B` is the union of an increasing sequence of finitely generated Hopf subalgebras, the ring
     form of the dilatation tower of Construction A.6.1 (`Smoothening.TerminationChain`,
     `Smoothening.TerminationChainHopf`).
   - Their defects of smoothness strictly decrease while positive (`Smoothening.TerminationCore`).
   - A member with torsion-free cotangent module is smooth (`Smoothening.TerminationSmooth`), and a
     smooth member equals `B`.
   - The details are in `Smoothening/TerminationMain.md` and the Markdown files it refers to.

The proof uses the standard axioms `propext`, `Classical.choice` and `Quot.sound` only.

## Relation to the source

Kaletha–Prasad construct the smoothening as the last term of a sequence of dilatations, whose
termination they cite from Bosch–Lütkebohmert–Raynaud, *Néron Models* §3.3. This formalization
works instead with the ring of integral functions, in the spirit of Bruhat–Tits II, 1.7.3. The
dilatation sequence appears only inside `B`. The proof of termination is internal to this project
and does not follow BLR:
- the defect count uses explicit generators and the Γ-trick;
- smoothness of the final member is proved by a graded-independence argument and translations,
  without dimension theory.
