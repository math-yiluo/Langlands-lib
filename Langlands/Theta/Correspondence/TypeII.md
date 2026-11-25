# Howe duality for type II dual pairs: the statement

**GKT Theorem 18.19** (Howe duality for type II dual pairs, p. 551) for `D = F`, in the form of
Theorem 13.21 (p. 401) written without `Θ` and `θ`, restated on the notions of GKT §13.3.

The module `Langlands.Theta.Correspondence.TypeII` states Howe duality for the type II dual pair
`(GL_m(F), GL_n(F))` (Mínguez's theorem) as a `Prop`, for the Weil representation `typeIIWeil`
of `Langlands.Theta.DualPair.TypeII`. Nothing is proved about the statement here.

## Content

- `HoweDualityTypeIIStatement`: for every nonarchimedean local field `F`, all `m, n ≥ 1` and every
  smooth irreducible representation `π` of `GL_n(F)` that admits a non-zero intertwining map from the
  restriction of `typeIIWeil F m n` to `GL_n(F)` (that is, a quotient, by irreducibility), there is a
  smooth irreducible representation `π'` of `GL_m(F)` such that
  - the space of intertwining maps from `typeIIWeil F m n` to the external tensor product
    `π' ⊠ π` (`Representation.tprod (π'.comp (MonoidHom.fst _ _)) (π.comp (MonoidHom.snd _ _))`, as in
    `Langlands/Representation/Tensor/FiniteEquivalences.lean`) has dimension one, and
  - every smooth irreducible `π''` of `GL_m(F)` with a non-zero intertwining map from
    `typeIIWeil F m n` to `π'' ⊠ π` is isomorphic to `π'`.

  Smoothness is the Library's `Langlands.IsSmooth`; irreducibility is Mathlib's
  `Representation.IsIrreducible`; isomorphism is `Representation.Equiv`.

**Restatement on the general notions** (`Langlands.Theta.Correspondence.ThetaLift`, GKT Theorem
13.21):

- `howeDualityTypeIIStatement_iff`: `HoweDualityTypeIIStatement` is equivalent to
  `ThetaMultiplicityOne (swapRep (typeIIWeil F m n))` for all `F` and `m, n ≥ 1` (the occurring
  representation is of `GL_n(F)`, the first factor after `swapRep`; the equivalence is
  `homSwapEquiv`).
- `thetaMultiplicityOne_typeIISplitting`: the statement for the Weil representation
  `ω_ψ ∘ s` of the type II splitting `typeIISplitting` (GKT Proposition 12.21, Proposition 12.35),
  over fields with `⅟2` (`weil_typeIISplitting`).
- `HoweDualityTypeII`: the full statement (Theorem 18.19 with both parts of Theorem 13.21,
  `HoweDuality (swapRep (typeIIWeil F m n))`); `HoweDualityTypeII.statement`: it implies
  `HoweDualityTypeIIStatement`.

Literature: A. Mínguez, *Correspondance de Howe explicite : paires duales de type II*, Ann. Sci. Éc.
Norm. Sup. (4) 41 (2008), 717–741, Théorème 1, p. 718 (= Corollaire 6.3, p. 734);
Mœglin–Vignéras–Waldspurger, *Correspondances de Howe sur un corps p-adique* (Lecture Notes in
Math. 1291, Springer 1987), chapter 2, III.1–III.2, pp. 44–45 (Howe's conjecture), and III.5,
p. 48 (the conjecture with multiplicities).

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, under
`src/Development/AbelianVarietyTheory/`: `Definitions/GaloisGeometry/IsParahoricVec.lean`, lines
20–24 (`ThetaGL.OmQuot`); `PublishedTheorems/GaloisGeometry₂/HypothesesAbsDet.lean`, lines 12–25
(`MinguezThetaGL`). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- `OmQuot 1 π' π` → a non-zero `IntertwiningMap` from `typeIIWeil F m n` to the external tensor
  product. The multiplicity-one clause (the source: any two such maps, the first non-zero, are
  proportional, together with `OmQuot`) is stated as `Module.finrank ℂ … = 1`, equivalent by
  Mathlib's `finrank_eq_one_iff'`.
- `GL (Fin n) k` → `GeneralLinear n F`; `PRep.IsSmooth` → `Langlands.IsSmooth` (equivalent,
  `Langlands.isSmooth_iff_forall_isOpen`).

## Declarations

- `Langlands.Theta.HoweDualityTypeIIStatement`
- `Langlands.Theta.howeDualityTypeIIStatement_iff`, `thetaMultiplicityOne_typeIISplitting`,
  `HoweDualityTypeII`, `HoweDualityTypeII.statement`

## Dependencies

`Langlands.Theta.DualPair.TypeII`, `Langlands.Theta.Correspondence.ThetaLift`; Mathlib:
`NumberTheory.LocalField.Basic`, `RepresentationTheory.Irreducible`.
