# Surjectivity on neutral integral points of an exact sequence of tori

`Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityStatement.{u}`
is an unproved proposition specializing Kaletha–Prasad Corollary B.8.6 to
the maximal unramified field. It isolates a prerequisite for the connected
torus bound in Corollary B.8.7. This module supplies no proof.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Corollary B.8.6, printed pp. 682–683 / PDF pp. 713–714, asserts that an
exact sequence of tori induces a surjection on the integral points of their
connected Néron models. Its proof uses the lft-Néron models over the
completion, finite generation of their component groups, Lemma A.4.25 and
the approximation in Lemma 8.1.2.

Remark B.8.5, printed p. 682 / PDF p. 713, provides the extension of generic
group homomorphisms to smooth affine models of the maximal bounded
subgroups. Proposition B.8.8(2), printed p. 683 / PDF p. 714, gives
uniqueness of the finite-type Néron model by that extension property.
Corollary B.8.7, printed p. 683 / PDF p. 714, applies B.8.6 to the norm
sequence from a Weil restriction.

The registered corrections `kaletha-prasad-2024-corrections` (1 November
2024), SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 49–50, amend Appendix B only in Section B.10 and do not amend
these statements.

## Exact formulation

Let `F : Type u` be a nonarchimedean local field, and put
`K = inertiaFixedField F` and `O = fixedFieldIntegers F`. Take actual
affine commutative group schemes `B` and `C` over `Spec K` which are tori,
and a homomorphism `q : B.toGrp ⟶ C.toGrp`. Assume its underlying scheme
map is surjective and its full scheme-theoretic kernel `kernel q` is a
torus. These hypotheses encode the exact sequence with that kernel; no
chosen subgroup of the kernel is substituted.

Supply `DB : RelativeComponentModelData O K B.toGrp` and the corresponding
`DC` for `C`. Each datum consists of a smooth affine full model, its smooth
neutral model, and a compatible inclusion representing the actual
relative identity component. Assume the full models' integral-point
images equal the common kernels of the valuations of all rational
characters, using `fixedFieldValuation F`. The conclusion is

```text
DC.neutral.integralPoints ≤
  DB.neutral.integralPoints.map (rationalPoints.map q).
```

Thus every rational point arising from an integral section of the target
neutral model is the image of a rational point arising from an integral
section of the source neutral model. Both subgroups use the supplied
generic-fibre identifications.

## Derived scope and remaining proof obligation

The source uses its specific finite-type Néron models and their relative
identity components. This formulation allows every supplied smooth model
with the same maximal-bounded integral-point image. Transport to these
models is part of the proof obligation: over the strictly Henselian DVR
`O`, the smooth extension criterion applied in both directions gives
compatible inverse model homomorphisms, and relative identity components
are preserved by those isomorphisms. The Library's
`IntegralModel.smoothHomExtension` is the available extension theorem.

The conclusion records only the lifting inclusion of the source's
surjectivity assertion. The forward inclusion, and the extension of `q`
to a morphism of the neutral models, are not asserted here. The statement
asserts no model existence, no Néron mapping property, and no norm
comparison. In particular it supplies no proof of B.8.6 or B.8.7.
