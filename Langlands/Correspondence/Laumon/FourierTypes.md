# The three types of simple perverse sheaves on the line and the Fourier transform

Laumon 1987, (1.4.2) and Théorème (1.4.2.1), pp. 148–149, distinguishes three types of simple
perverse sheaves on the affine line `A` over `k` and shows that the Fourier–Deligne transform
exchanges them. This module states that result on weil-conjectures' Weil complexes of the line
(`AlgebraicGeometry.WeilComplex k ℓ (affineLine k)`), for a finite field `k`, a prime `ℓ ≠ char k`
and a nontrivial character `ψ : k → ℚ̄_ℓ`. It defines the three types and states the exchange; it
does not prove the statement.

## Character and normalizations

The statement quantifies over every nontrivial additive character `ψ : AddChar k (PadicAlgCl ℓ)`.
The character Laumon fixes in (0.2), p. 134, is `Langlands.Henniart.Laumon.fourierCharacter k ℓ` of
the module `Traits`; the statement applies to it, with the hypothesis `ψ ≠ 1` supplied by
`fourierCharacter_ne_one k ℓ`. Laumon uses the same `ψ` for both directions of the transform, as
here.

Weil structures are those of weil-conjectures, defined with the geometric Frobenius. For
`q = #k`, the geometric Frobenius acts on the Tate line `E(1)` by `q⁻¹` and on `E(−1)` by `q`
(weil-conjectures' `WeilSheaf.cyclotomicUnit_eq` and `WeilSheaf.tateTwistSheaf_one`: `E(1)` is the
constant Weil twist by the cyclotomic scalar `q⁻¹`, and `E(−1)` is its dual);
`WeilComplex.tateTwist (-1)` is Laumon's twist `(−1)`. The
transform is weil-conjectures' `fourierTransform ψ`, `Rpr₂!(pr₁^* K ⊗ Lψ(xx'))[1]`, Laumon's
normalization (1.2.1.1) with `r = 1`.

## Laumon's three types

Laumon's types of a simple perverse sheaf `K` on `A` are:

- `(T1)`: `K = i_* F` for a closed point `s` of `A` with inclusion `i : s ↪ A` and `F` an
  irreducible sheaf on `s`;
- `(T2)`: `K = (pr_A)_*(Lψ(x·s') ⊗ pr_{s'}^* F')[1]` for a closed point `s'` of `A'` and `F'`
  irreducible on `s'`, where `Lψ(x·s')` is the restriction of the kernel `Lψ(xx')` to `A × s'`;
- `(T3)`: `K = j_* F[1]` for a dense open `j : U ↪ A` and an irreducible lisse sheaf `F` on `U` such
  that for no `a' ∈ k̄` is `Lψ(x a')|_{U ⊗ k̄}` a subquotient of `F|_{U ⊗ k̄}`;

and `(T1')`, `(T2')`, `(T3')` are the same types on `A'`. By BBD (4.3.1)(ii) every simple perverse
sheaf is of one of the three types.

## Definitions

- `FourierPointDatum k ℓ` bundles the data of weil-conjectures' theorem
  `WeilSheaf.nonempty_iso_fourierTransform_derivedLowerShriek_of_isPullback`: a closed immersion
  `i : Z ↪ 𝔸¹` over `k`; a `k`-scheme `X'` of finite type with `q : X' → Z`, `i' : X' → 𝔸¹ × 𝔸¹`
  and a finite `π : X' → 𝔸¹` with `i' ≫ pr₂ = π` and a cartesian square `q, i', i, pr₁`, so that
  `X' = Z × 𝔸¹` with `i' = i × 1` and `π` the second projection; and a Weil sheaf `sheaf` on `Z`.
  Its fields carry the instances these morphisms need (the structure `WeilSheaf.LisseOnDenseOpen` of
  weil-conjectures is built the same way).
- `FourierPointDatum.punctual P` is `i_* E` in degree `0` (the compact support pushforward
  `WeilComplex.derivedLowerShriek` along the closed immersion `i`), `E = P.sheaf`.
- `FourierPointDatum.kernelSheaf P ψ` is the Weil sheaf `π_*(i'^* Lψ(xx') ⊗ q^* E)` on the line,
  with weil-conjectures' `fourierKernel ψ` for `Lψ(xx')`, `WeilSheaf.upperStar`,
  `WeilSheaf.tensorObj` (tensor with a lisse sheaf) and `WeilSheaf.lowerStar`;
  `FourierPointDatum.kernelType P ψ` is this sheaf placed in degree `−1`
  (`WeilSheaf.toShiftedComplex`), i.e. `π_*(i'^* Lψ(xx') ⊗ q^* E)[1]`.
- `IsPunctualFourierType k ℓ K`: `K ≅ i_* E` for some closed point datum with `E` simple (in the
  abelian category of Weil sheaves on `Z`). A simple Weil sheaf on the finite closed subscheme `Z`
  is supported at a single closed point `s`, where it is an irreducible Weil sheaf; so this is
  type `(T1)`.
- `IsKernelFourierType k ℓ ψ K`: `K ≅ π_*(i'^* Lψ(xx') ⊗ q^* E)[1]` for some closed point datum
  with `E` simple. As the multiplication `x x'` is symmetric, the same Weil complex of the line is
  of type `(T2)` when the line is the source `A` (with `Z = s'` a closed point of `A'`) and of type
  `(T2')` when it is the target `A'` (with `Z = s` a closed point of `A`).
- `IsNonexceptionalFourierType k ℓ ψ K`: `K` is isomorphic to the middle extension
  `D.middleExtension = j_* F[1]` of an irreducible lisse Weil sheaf on a dense open
  (`WeilSheaf.LisseOnDenseOpen` with `IsIrreducibleLisse`) that is nonexceptional in the sense of
  weil-conjectures' `WeilSheaf.IsNonexceptional`: for no `a ∈ k̄` is the geometric linear
  Artin–Schreier sheaf `Lψ(a x)` a constituent of the geometric restriction. This is type `(T3)`
  (and `(T3')` on the target line).

## The statement

**`WeilFourierTypeExchangeStatement`** (Laumon (1.4.2)–Théorème (1.4.2.1), pp. 148–149; BBD
(4.3.1)(ii), p. 112). For every finite field `k`, prime `ℓ ≠ char k` and nontrivial `ψ`:

1. every simple object of the heart of curve perverse Weil complexes on the line
   (`WeilComplex.curvePerverse`) is of type `(T1)`, `(T2)` or `(T3)`;
2. for every closed point datum, `FTψ(i_* E) ≅ π_*(i'^* Lψ(xx') ⊗ q^* E)[1]` — the first formula of
   (1.4.2.1)(i), `(T1) → (T2')`;
3. for every closed point datum, `FTψ(π_*(i'^* Lψ(xx') ⊗ q^* E)[1]) ≅ [−1]^* i_* E (−1)`, with
   `[−1] = affineLine.neg` and the Tate twist `WeilComplex.tateTwist (-1)` — the second formula of
   (1.4.2.1)(i), `(T2) → (T1')`. Laumon writes the pushforward `[−1]_* i'_* F'(−1)`; Lean uses the
   pullback `WeilComplex.upperStar (affineLine.neg k)`. The reflection `[−1]` is an involutive
   automorphism of the line, so its pushforward is canonically isomorphic to pullback along its
   inverse, which is `[−1]` itself; the two forms of the formula are equivalent. The pullback form is
   the one of weil-conjectures' inversion `nonempty_iso_fourierTransform_comp_self`;
4. the transform of a Weil complex of type `(T3)` is of type `(T3')`: its output is again the middle
   extension of an irreducible lisse sheaf on a dense open, and that sheaf is nonexceptional —
   (1.4.2.1)(ii).

Clause 1 combines weil-conjectures' classification `WeilComplex.simple_iff` (a simple object is
punctual or the middle extension of an irreducible lisse sheaf on a dense open) with the
identification of the exceptional middle extensions: an irreducible lisse sheaf on a dense open with
a geometric constituent `Lψ(a x)` is, as recorded in the note
`notes/henniart/laumon-local-fourier-weil-conjectures-design.md` §4.2, induced from the closed
point of parameter `a` and its middle extension is `π_*(i'^* Lψ(xx') ⊗ q^* E)[1]` for that point.
Clause 2 is weil-conjectures' proved theorem
`WeilSheaf.nonempty_iso_fourierTransform_derivedLowerShriek_of_isPullback`; it is restated so that
the exchange is stated as one proposition. Clause 3 follows from clause 2 and the inversion
`nonempty_iso_fourierTransform_comp_self` (Laumon (1.2.2.1)), which is how Laumon proves it. Clause
4 is the content of (1.4.2.1)(ii) beyond weil-conjectures' `exists_middleExtension_fourierTransform`,
which gives the irreducible lisse output on a dense open but not its nonexceptionality; Laumon
deduces it from (1.3.2.4), part (i) and involutivity: an exceptional output would be of type
`(T2')`, whose inverse transform is of type `(T1)`, not `(T3)`.

## External declarations and their axioms

All declarations of weil-conjectures (commit `a25955cde4f85f67bef3149a6efc3efe20c22132`) used here
were checked with `#print axioms` in the pinned environment and depend only on `propext`,
`Classical.choice` and `Quot.sound`: `AlgebraicGeometry.affineLine`, `affineSpacePair` (the plane
`affinePlane k`, weil-conjectures' notation for `affineSpacePair PUnit k`, the codomain of `i'`),
`affinePlane.fst`, `affinePlane.snd`, `fourierKernel`, `ProEtale.IsAdicLisseSheaf.upperStar` (the
lissity of the pulled-back kernel `i'^* Lψ(xx')`, needed for `WeilSheaf.tensorObj`), `isLisse_fourierKernel`, `fourierTransform`, `affineLine.neg`,
`WeilComplex`, `WeilComplex.curvePerverse`, `WeilComplex.derivedLowerShriek`,
`WeilComplex.tateTwist`, `WeilComplex.upperStar`, `WeilSheaf`, `WeilSheaf.toComplex`,
`WeilSheaf.toShiftedComplex`, `WeilSheaf.lowerStar`, `WeilSheaf.upperStar`, `WeilSheaf.tensorObj`,
`WeilSheaf.LisseOnDenseOpen`, `WeilSheaf.LisseOnDenseOpen.middleExtension`,
`WeilSheaf.IsIrreducibleLisse` and `WeilSheaf.IsNonexceptional` (all in the namespace
`AlgebraicGeometry`). The results cited above, `WeilSheaf.nonempty_iso_fourierTransform_derivedLowerShriek_of_isPullback`,
`nonempty_iso_fourierTransform_comp_self`, `WeilComplex.simple_iff` and
`exists_middleExtension_fourierTransform`, have the same three axioms. The declarations of this
module have the same three axioms.
