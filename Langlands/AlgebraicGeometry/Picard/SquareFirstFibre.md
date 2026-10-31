# First-projection fibres of a square

Internal derived helpers for an arbitrary morphism `s : X → S` of schemes and
section `x : S → X` with `x ≫ s = 𝟙 S`. All schemes have arbitrary universe `u`.

`squareFirstInclusion s x hx` is the actual pullback lift `(s ≫ x, 𝟙 X)` into
`X ×_S X`. Its two projection identities are proved from the pullback lift laws.
`squareFirstFibre_structure` identifies the composite of the first fibre
projection, the second square projection, and `s` with the fibre structure map.
The proof uses both pullback equations and the section identity. The companion
`squareFirstFibre_inclusion` identifies the resulting map back to the square
with the first fibre projection, by the universal property of the square.

`squareFirstFibreIso s x hx` identifies the actual fibre product
`pullback (pullback.fst s s) x` with `X`. Its forward map is the first fibre
projection followed by the second square projection; its inverse is the lift
of `squareFirstInclusion s x hx` and `s`. The inverse identities follow from
the preceding projection equations and pullback extensionality.

No smoothness, properness, field, group scheme, or line bundle premise enters
these geometric identities. This is an internal universal-property derivation,
not a source transcription.

For an affine base `S = Spec R`, an actual module `M : (pullback s s).Modules`,
and every `n : ℕ`, `squareFirstFibreCohomologyIso s x hx M n` has type

```lean
(Modules.DerivedSections.relativeCohomology
  (pullback.snd (pullback.fst s s) x) n).obj
    ((Scheme.Modules.pullback (pullback.fst (pullback.fst s s) x)).obj M) ≅
(Modules.DerivedSections.relativeCohomology s n).obj
    ((Scheme.Modules.pullback (squareFirstInclusion s x hx)).obj M)
```

Its proof first uses `squareFirstFibre_structure` to identify the two structure
maps over `Spec R`. The pullback composition and equality isomorphisms identify
the coefficient on the fibre with the pullback, along `squareFirstFibreIso`,
of the coefficient obtained using `squareFirstInclusion`. Applying the actual
relative-cohomology functor and `relativeCohomologyPullbackIso` then gives the
stated isomorphism. Degree zero is included, and no finiteness or flatness
condition on `M` is needed. For a line bundle the underlying module of its
published `LineBundle.pullback` is definitionally the module pullback, so this
also compares the two expressions used in the first-projection acyclicity
statement. It proves no vanishing assertion without a vanishing hypothesis.
