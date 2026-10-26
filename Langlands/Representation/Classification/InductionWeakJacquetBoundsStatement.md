# Preservation of weak upper Jacquet bounds by actual normalized induction

Authors: Worker 540 and Worker 573. Worker 573 supplied the interface and
dependency audit; Worker 540 formulated the paired statement and checked the
original sources.

`Langlands.GLInductionWeakJacquetBoundsStatement.{uF,uV}` is a closed
`Prop`-valued definition. It states an algebraic implication about actual
normalized upper Jacquet and induction constructions. It supplies no proof.

## Input bounds

Quantify every prime `p`, p-adic field `F : PadicField.{uF} p`, compatible
`T : F.TopologicalData`, positive rank `n`, and block shape `B`.
With field topology `T.topology`, the input is any irreducible admissible
actual representation
`σ : Representation ℂ (B.Levi F.Carrier) V`, where `V : Type uV`.
The field and carrier universes are independent. Admissibility includes
smoothness. No analytic temperedness, unitarity, prescribed central
character, tensor presentation, or finite-length hypothesis is added.

The numerical premise is exactly the upper refinement-bound premise of
`GLProductLeviTemperedExponentSufficiencyStatement`. For every
`D : Geometric.BlockRefinement B`, put `A = B.flatten D` and restrict
the actual action `T.normalizedRefinedJacquet B D σ` through
`Geometric.flattenedLeviEquiv F.Carrier B D` and then
`A.blockScalarLevi F.Carrier`.

Every open-kernel character `ψ` of the fine scalar torus that is a
generalized eigencharacter of this action must satisfy `‖ψ(a)‖ ≤ 1`
whenever the values
`T.normalizedAbs (a (B.flattenBlockEquiv D ⟨j,i⟩))` increase with `i`
separately for each outer block `j`. There is no comparison between
distinct outer blocks. Every refinement, including the identity, is
tested. The generalized-eigencharacter predicate uses a common power of
all the character-defect operators on a nonzero vector.

## Exact ambient conclusion

Let `I = T.normalizedParabolicInduced B σ`, on its actual smooth induced
function space. This is positive-half-modulus induction from the standard
upper block parabolic, with action by right translation. The target is

```text
for every C : BlockShape n and χ : (Fin C.length → Fˣ) →* ℂˣ,
  T.IsJacquetExponent C I χ implies
    ‖χ(a)‖ ≤ 1 whenever |a_0| ≤ |a_1| ≤ ... .
```

Here `|·| = T.normalizedAbs`. `T.IsJacquetExponent` includes openness of
the character kernel and generalized occurrence in the actual normalized
upper Jacquet module restricted to `C.blockScalarLevi`. That Jacquet
action uses inverse positive half-modulus.

This is the entire numerical right side of
`GLTemperedExponentCriterionStatement`, applied to the actual induced
representation. It tests every ambient shape and exponent; induced
irreducibility is not a premise. The function-space carrier has the
universe dictated by actual induction, `max uF uV`. It is not replaced by
a same-universe model. The ambient criterion will therefore be needed at
that carrier universe when the statements are assembled.

The proposition has no geometric-lemma certificate, assumed filtration,
spectrum-containment theorem, or opposite-dual eigenfunctional as a
parameter. All such intermediate mathematical work belongs to its proof.

## Original sources and derived provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333,
literature ID `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`:

- I.3, printed pp.243–244 (PDF9–10), defines generalized exponents and the
  normalized Jacquet and induction actions, and describes the filtration
  of Jacquet applied to induction.
- Lemma III.2.3 and its proof, printed pp.266–267 (PDF32–33), use that
  filtration to express induced Jacquet exponents through source refined
  exponents and minimal Weyl representatives. The proof carries the
  source weak cone bounds to the ambient cone. This algebraic step is
  extracted here without an analytic temperedness premise.

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Annales scientifiques de l'École Normale Supérieure
(4) 10 (1977), 441–472, literature ID
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`:

- 2.11–2.12, printed p.448 (PDF9), give the minimal double-coset
  representatives, standard intersections and the functorial filtration.
- 6.3–6.4, printed pp.468–469 (PDF29–30), identify the intersection
  parabolics, use the inverse representative `P w⁻¹`, and prove that the
  possible extra positive character in the graded action is trivial.

These passages were read directly and their formula pages viewed as
images. The registered source hashes were rechecked. No source-specific
errata file was found in the workspace or public notes.

The proposition is derived rather than a literal transcription of a
single displayed source statement. It extracts the algebraic part of
Waldspurger III.2.3, specializes the product Levi to actual GL factors,
and expresses the chambers in the Library's flattened scalar
coordinates. Scalar real parts include the fine block sizes when
translated from determinant coordinates. The statement uses the
constructed flattened Levi equivalence rather than an unspecified
isomorphism.

## Proof obligations and normalization

The published `Langlands.Geometric.PadicGeometricLemmaTheorem` is a
statement target, not an assumed proof. A proof of the present target
must obtain the actual finite filtration of Jacquet applied to induction,
with pieces given by normalized refined Jacquet, inverse-conjugation
transport, and normalized refined induction.

It must detect an ambient generalized eigencharacter in a nonzero graded
piece and compare that piece's central spectrum with the full central
spectrum of the source refined Jacquet action. Admissible compact-open
invariant spaces support the required generalized-spectrum arguments.
Restriction to a smaller central torus and extension to a full refined
exponent need justification; an arbitrary equivariant extension of a dual
functional cannot be presumed.

For each minimal permutation, inverse conjugation must pull ambient
increasing scalar absolute values into the source chambers increasing
within each outer block. Positive induction half-moduli and inverse
Jacquet half-moduli must cancel with the actual transported moduli.
The BZ normalization computation supports this comparison; no additional
character is allowed in the final bounds. These spectral, permutation,
and modulus comparisons are obligations, not implemented results here.

Together with the separate analytic product-Levi necessity theorem,
this would yield weak bounds for induction from the original analytically
tempered input. Induced admissibility, its scalar character and the
ambient analytic criterion remain separate ingredients. No proof of
`GLTemperedInductionPreservationStatement` is claimed by this module.
