# KP Corollary 11.7.6: the three rational Kottwitz quotients, proof

Lean module: `Langlands.Geometry.Building.Kottwitz.QuotientProof`,
namespace `Langlands.Geometry.Building.Kottwitz`.

## Statement

```
theorem Langlands.Geometry.Building.Kottwitz.quotient : QuotientStatement.{u}
```

The type is exactly the published proposition
`Langlands.Geometry.Building.Kottwitz.QuotientStatement.{u}` of the module
`Langlands.Geometry.Building.Kottwitz.QuotientStatement`, at an arbitrary
universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
  (S : CommGroupScheme (Spec (CommRingCat.of F)))
  (Z : GroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G) (j : Z ⟶ G)
  (d : ZeroSubgroupDatum i j),
  let N := d.zeroSubgroup
  let H := characterValuationKernel (ValuativeRel.valuation F) G
  let A := Multiplicative (ReductiveInvariantTarget F G hG)
  let Ator := fundamentalInvariantTorsion F (UnramifiedClosure F) (SeparableClosure F) G hG
  ∃ hN : N.Normal,
    letI := hN
    N ≤ H ∧
    (∃ e : (rationalPoints G ⧸ N) ≃* A,
      ∀ g, e (QuotientGroup.mk' N g) = reductiveKottwitzRational F G hG g) ∧
    (∃ e : (H ⧸ N.subgroupOf H) ≃* Ator,
      ∀ x : H, (e (QuotientGroup.mk' (N.subgroupOf H) x) : A) =
        reductiveKottwitzRational F G hG x.val) ∧
    (∃ e : (rationalPoints G ⧸ H) ≃* (A ⧸ Ator),
      ∀ g, e (QuotientGroup.mk' H g) =
        QuotientGroup.mk' Ator (reductiveKottwitzRational F G hG g))
```

In words: for every connected reductive group `G` over a nonarchimedean local
field `F` and every datum defining `G(F)^0`, with `G(F)^1` the common kernel of
the valuations of the rational characters, `A = π₁(G)_I` and `Γ = Gal(K/F)`:
`G(F)^0` is normal and contained in `G(F)^1`, and the rational Kottwitz
homomorphism `κ_G` induces isomorphisms `G(F)/G(F)^0 ≃ A^Γ`,
`G(F)^1/G(F)^0 ≃ (A^Γ)_tor` and `G(F)/G(F)^1 ≃ A^Γ/(A^Γ)_tor`, each given on
representatives by `κ_G`.

## Proof

The Lean proof is the single application

```
quotientStatement_of_chamberStatement zeroKernel characterKernel chamber
```

of `quotientStatement_of_chamberStatement` (module
`Geometry.Building.Kottwitz.QuotientReduction`), which derives the statement
from three hypotheses. Each is discharged by a theorem proved in the Library
without hypotheses:

1. `zeroKernel` (module `Geometry.Building.Kottwitz.ZeroKernelProof`): KP
   Proposition 11.5.4, `G(F)^0 = ker κ_G`.
2. `characterKernel` (module `Geometry.Building.Kottwitz.CharacterKernelProof`):
   `G(F)^1` is the preimage under `κ_G` of the invariant torsion.
3. `chamber` (module `Geometry.Building.Kottwitz.ChamberProof`): KP Corollary
   11.7.5; only its first conjunct, the surjectivity of `κ_G`, is used.

Inside the reduction, `quotientReduction` builds the three isomorphisms from
the two kernel identities and the surjectivity; the details are on the page of
`Geometry.Building.Kottwitz.QuotientReduction`. The statement is not modified
and no hypothesis is added.

## Declarations

- `Langlands.Geometry.Building.Kottwitz.quotient : QuotientStatement.{u}`.

## Literature

T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Chapter 11, §11.7, Corollary 11.7.6, printed p. 434: the Kottwitz homomorphism
induces isomorphisms `G(k)/G(k)^0 → π₁(G)_I^{Gal(K/k)}`,
`G(k)^1/G(k)^0 → π₁(G)_{I,tor}^{Gal(K/k)}` and
`G(k)/G(k)^1 → (π₁(G)_I)_free^{Gal(K/k)}`. In the third isomorphism the Lean
statement has the quotient of the invariants by their torsion, as described
on the statement's page.
