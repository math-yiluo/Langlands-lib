# Cohen–Macaulay dimension and prime chains

Module `StacksFrontier.RingTheory.CohenMacaulay.Dimension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over a Noetherian local ring, the file relates depth and the dimension of a finite module's support to regular quotients and associated primes. With full support it obtains the lengths of maximal prime chains and the dimension formula at each prime.

- `Module.depth_eq_supportDim_iff_quotSMulTop` says that the depth and support dimension equality holds for M exactly when it holds for M ⧸ xM, if x is in the maximal ideal and acts injectively on M.
- `Module.ringKrullDim_quotient_eq_supportDim_and_minimal_support_of_mem_associatedPrimes` says that, under that depth and dimension equality, each associated prime p is minimal in the support and dim(R ⧸ p) equals the dimension of the support.
- `Module.IsMaximalCohenMacaulay.length_eq_ringKrullDim_of_support_eq_univ` gives length dim R for every saturated prime chain from a minimal prime to the maximal ideal, given a finite maximal Cohen–Macaulay module of full support.
- Under the same module hypotheses, `Module.IsMaximalCohenMacaulay.ringKrullDim_eq_height_add_ringKrullDim_quotient_of_support_eq_univ` gives dim R = height p + dim(R ⧸ p) for every prime p. Its M = R specialization, for R Cohen–Macaulay in the form `Module.IsMaximalCohenMacaulay R R`, is `Module.IsMaximalCohenMacaulay.ringKrullDim_eq_height_add_ringKrullDim_quotient`.

The quotient proof cancels one from the depth and support dimension formulas, and the associated-prime proof squeezes dim(R ⧸ p) between depth and support dimension before using strict decrease of finite coheight. The chain proof uses prime avoidance and associated primes of a quotient by a power of a regular element to shorten the chain, and the dimension formula splices chains that realize height and coheight.

The first two results use the unfolded local Cohen–Macaulay equality in `WithBot ℕ∞` and compute both module invariants over R, including after taking a regular quotient. The quotient equivalence applies to the zero module, with infinite depth and bottom support dimension on each side. The full-support results explicitly require both maximal Cohen–Macaulayness and full support, and height p denotes the dimension of the localization at p. Two module docstrings of the file present the M = R case of the chain result (Tag 00N9) and list it as a main result; the file does not contain it.

## References

Tag 0C6G, Tag 0BUS, Tag 0AAE, Tag 0AAF and Tag 00NA. The proofs use Tag 090R (1), Tag 0B52, Tag 0BK4, Tag 0586, Tag 02CE and Tag 0CN5. EGA 0 16.5.4, 16.5.10 and 16.5.11, EGA IV 7.2.1.1 and 15.4.1, and SGA 2 III 2.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0C6G](https://stacks.math.columbia.edu/tag/0C6G) | `depth_eq_supportDim_iff_quotSMulTop` | Cohen-Macaulayness is written out as the equation `depth_𝔪(N) = dim Supp(N)` \   that Definition 00N3 is, rather than as the predicate, so that each side is verbatim the \   hypothesis of Stacks 0BUS; the two differ by unfolding a definition. It is not spelled as \   the existence of an `M`-regular sequence of length `dim Supp(M)`, which needs Stacks \   090R(2) to be the same condition. |
| [0BUS](https://stacks.math.columbia.edu/tag/0BUS) | `ringKrullDim_quotient_eq_supportDim_and_minimal_support_of_mem_associatedPrimes` | Cohen-Macaulayness is spelled out as `depth_𝔪(M) = dim Supp(M)`, the definition \   Stacks 00N8 unfolds to, there being no predicate for it in this library yet. |
| [0AAE](https://stacks.math.columbia.edu/tag/0AAE) | `Module.IsMaximalCohenMacaulay.length_eq_ringKrullDim_of_support_eq_univ` | The source's `M` Cohen-Macaulay with `Spec(R) = Supp(M)` is the conjunction of `Module.IsMaximalCohenMacaulay R M` (Definition 00NF, i.e. `depth_𝔪(M) = dim R`) and `Module.support R M = Set.univ`, the two being equivalent to it as the source itself remarks; a maximal chain of primes is a `RelSeries` for the covering relation `⋖` on `PrimeSpectrum R` whose head is minimal and whose last is maximal. See the module docstring. |
| [0AAF](https://stacks.math.columbia.edu/tag/0AAF) | `ringKrullDim_eq_height_add_ringKrullDim_quotient_of_support_eq_univ` | The source's `M` Cohen-Macaulay with `Spec(R) = Supp(M)` is the conjunction of `Module.IsMaximalCohenMacaulay R M` (Definition 00NF, i.e. `depth_𝔪(M) = dim R`) and `Module.support R M = Set.univ`, the two being equivalent to it as the source itself remarks; `dim(R_𝔭)` is written `𝔭.height`. See the module docstring. |
| [00NA](https://stacks.math.columbia.edu/tag/00NA) | `Module.IsMaximalCohenMacaulay.ringKrullDim_eq_height_add_ringKrullDim_quotient` | Cohen-Macaulayness of `R` is the hypothesis `Module.IsMaximalCohenMacaulay R R`, i.e. `depth_𝔪(R) = dim R` (Definition 00N8); `dim(R_𝔭)` is written `𝔭.height`; the source's name `d` for `dim R` is dropped. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.5.4 | `ringKrullDim_quotient_eq_supportDim_and_minimal_support_of_mem_associatedPrimes` |  |
| EGA | IV 15.4.1 | `ringKrullDim_quotient_eq_supportDim_and_minimal_support_of_mem_associatedPrimes` | local form |
| EGA | IV 7.2.1.1 | `ringKrullDim_quotient_eq_supportDim_and_minimal_support_of_mem_associatedPrimes` | more general |
| SGA | 2 III 2.1 | `isSMulRegular_iff_forall_notMem_associatedPrimes` | (ii) ⇔ (iv) |
| EGA | IV 15.4.1 | `Module.IsMaximalCohenMacaulay.length_eq_ringKrullDim_of_support_eq_univ` | special case |
| EGA | 0 16.5.11 | `ringKrullDim_eq_height_add_ringKrullDim_quotient_of_support_eq_univ` |  |
| EGA | 0 16.5.10 | `ringKrullDim_eq_height_add_ringKrullDim_quotient_of_support_eq_univ` | (ii), Supp M = Spec A |
| EGA | IV 15.4.1 | `ringKrullDim_eq_height_add_ringKrullDim_quotient_of_support_eq_univ` | special case |
| EGA | 0 16.5.11 | `Module.IsMaximalCohenMacaulay.ringKrullDim_eq_height_add_ringKrullDim_quotient` | case M = R |
| EGA | 0 16.5.10 | `Module.IsMaximalCohenMacaulay.ringKrullDim_eq_height_add_ringKrullDim_quotient` | (ii) for M = A |
| EGA | IV 15.4.1 | `Module.IsMaximalCohenMacaulay.ringKrullDim_eq_height_add_ringKrullDim_quotient` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/CohenMacaulay/Dimension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 28 declarations of the source file 26 are kept. The 2 left out are not needed by the results for which the extract is made: `Module.IsMaximalCohenMacaulay.length_eq_ringKrullDim`, `Stacks.CohenMacaulay.MaximalChains.solution`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 11 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
