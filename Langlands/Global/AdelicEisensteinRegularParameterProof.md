# Nonemptiness of the Eisenstein regular-parameter region

`Langlands.Global.eisensteinRegularParameter` proves
`Langlands.Global.EisensteinRegularParameterStatement`. It uses smoothness of
`G` from connected reductivity to supply the locally finite-type instance and
applies `ParabolicRootPresentation.exists_regularParameter` to the given
presentation, split-torus witnesses and real threshold `R`.

The regular-region lemma evaluates each unipotent root on the defining
split-component cocharacter. Each evaluation is a positive integer, so
multiplying by `max R 0 + 1` makes it strictly greater than `R`. The
nondegenerate Weyl-induced form represents the scaled functional by a vector
in the real character space of the split component `A`. Restriction from `P`
to its Levi `M` is bijective on rational characters, and restriction from
`M` to `A` is surjective after tensoring with `ℚ`. The lemma extends scalars
to `ℝ` to lift the vector to a real parameter of `P`, then uses the inclusion
of real scalars into complex scalars to obtain a complex parameter with that
real part. The regularity inequalities are vacuous when there are no
unipotent roots. [Regular-region lemma](AdelicEisensteinRegularRegion.md)

## Sources

- Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*
  (2024), §2.1, p. 190 (PDF p. 4), defines the real character space using
  the rational characters of `P` and `M`. Section 2.2, p. 191 (PDF p. 5),
  uses sufficiently regular real parameters in the positive Weyl chamber
  for (2.1). This motivates the nonemptiness result for the Library's
  Weyl-form inequalities. Source ID
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, folder SHA-256
  `58ab0c92242c29f17cc38fcfde3d73082e15f023a033c1c808282eb783f293b1`,
  file `Bernstein-Lapid--On the meromorphic continuation of Eisenstein series--2024.pdf`.
- Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  I.1.4, proof of (2), p. 6 (PDF p. 6), gives the finite-index restriction
  from rational characters of `M` to those of the maximal split torus of its
  centre. Finite index yields the surjection after tensoring with `ℚ` used
  in the lift. Source ID `moeglin-waldspurger-1995-spectral-decomposition`,
  folder SHA-256 `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`,
  file `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`.
