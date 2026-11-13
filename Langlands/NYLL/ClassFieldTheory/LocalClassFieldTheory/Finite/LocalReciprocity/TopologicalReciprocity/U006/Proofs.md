# Openness of the norm subgroup with compatible local-field structures (M257.006)

Worker 64 proves the published proposition
`Langlands.NYLL.PortInternal.M257.d006Statement` under the inventory name
`Langlands.NYLL.PortInternal.M257.d006`, with this complete telescope:

```lean
theorem d006
    (K L : Type)
    [NontriviallyNormedField K] [NormedField L] [NormedAlgebra K L]
    [CompleteSpace K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [IsNonarchimedeanLocalField L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    d006Statement K L
```

Both fields stay in `Type 0`. The parameters, their order and all twelve
instance hypotheses are the target's and the source's. The target unfolds to
`IsOpen (localNormSubgroup K L : Set Kˣ)`. Here `localNormSubgroup K L` is the
published range of `normUnits K L = Units.map (Algebra.norm K)`, the field norm
on units. `Kˣ` has Mathlib's unit topology, and `K` has the topology of its
given normed-field structure. The proof neither changes nor restates the
target. It adds no hypothesis on norm-index finiteness, openness or reciprocity.

## Implemented proof

The proof is new and does not use local reciprocity. It shows that the norm
subgroup contains a neighbourhood of `1` in `Kˣ`, so it is open.

1. **An element of nonzero trace.** `IsGalois K L` supplies
   `Algebra.IsSeparable K L`. Mathlib's `Algebra.trace_ne_zero K L` then says
   the trace `Algebra.trace K L` is not the zero map. Some `y : L` therefore
   has `Algebra.trace K L y ≠ 0`.
2. **The polynomial `t ↦ N(1 + t • y)`.** Let `b := Module.finBasis K L` and
   let `M := Algebra.leftMulMatrix b y`. Put
   `Q := det (1 + X • M.map C) : K[X]`. For every `t : K`, the proof shows
   `Q.eval t = Algebra.norm K (1 + t • y)`. It rewrites the norm as
   `det (leftMulMatrix b (1 + t • y))` with `Algebra.norm_eq_matrix_det`. Since
   `leftMulMatrix b` is an algebra homomorphism, this is `det (1 + t • M)`.
   On the other side it moves evaluation inside the determinant with
   `RingHom.map_det` for `evalRingHom t`, then compares the matrices entry by
   entry.
3. **Its derivative at `0`.** `Polynomial.hasStrictDerivAt` gives the strict
   derivative `Q.derivative.eval 0` at `0`. Mathlib's
   `Matrix.derivative_det_one_add_X_smul` identifies this with `trace M`. By
   `Algebra.trace_eq_matrix_trace b`, `trace M` equals `Algebra.trace K L y`.
   Also `Q.eval 0 = Algebra.norm K 1 = 1`.
4. **The inverse function theorem.** `K` is a complete nontrivially normed
   field and the derivative is nonzero. Mathlib's one-variable
   `HasStrictDerivAt.map_nhds_eq` then gives
   `map (fun t => Q.eval t) (𝓝 0) = 𝓝 1`. Every map's range belongs to its
   image filter (`Filter.range_mem_map`), so the range of `t ↦ Q.eval t` is a
   neighbourhood of `1` in `K`.
5. **Into the unit group.** `Units.val : Kˣ → K` is continuous
   (`Units.continuous_val`), so the preimage of that range is a neighbourhood of
   `1 : Kˣ`. Take `u : Kˣ` with `(u : K) = Q.eval t`. Then
   `Algebra.norm K (1 + t • y) = u`, which is nonzero. Since
   `Algebra.norm_zero` gives norm `0` at `0`, `z := 1 + t • y` is nonzero, and
   `normUnits K L (Units.mk0 z _) = u` by `Units.ext`. Hence the preimage lies
   in `localNormSubgroup K L`.
6. **Openness.** A subgroup that is a neighbourhood of one point is open, by
   Mathlib's `Subgroup.isOpen_of_mem_nhds`. This gives the target.

The argument uses only the following hypotheses: the normed-field and normed
algebra structures, `CompleteSpace K`, `FiniteDimensional K L`, and the
separability that comes from `IsGalois K L`. `ValuativeRel K`,
`IsNonarchimedeanLocalField K`, `ValuativeRel L`,
`IsNonarchimedeanLocalField L`, `Valuation.HasExtension` and
`IsIntegralClosure 𝒪[L] 𝒪[K] L` are kept in the telescope exactly as in the
target but are not used. This describes the proof only. The Lean theorem states
openness under the full target telescope and nothing more general.

The axiom inspection of `Langlands.NYLL.PortInternal.M257.d006` reports only
`propext`, `Classical.choice` and `Quot.sound`.

## Dependencies

- The published target module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U006.Statements`,
  through which `localNormSubgroup` and `normUnits` are used. These come from
  the published `NormQuotient.U001` and `NormUnits.U002` definitions.
- Mathlib modules `Analysis.Calculus.InverseFunctionTheorem.Deriv`
  (`HasStrictDerivAt.map_nhds_eq`), `Analysis.Calculus.Deriv.Polynomial`
  (`Polynomial.hasStrictDerivAt`), `RingTheory.Trace.Basic`
  (`Algebra.trace_ne_zero`, `Algebra.trace_eq_matrix_trace`),
  `LinearAlgebra.Matrix.Charpoly.Coeff`
  (`Matrix.derivative_det_one_add_X_smul`), `Topology.Algebra.Group.Units`
  (`Units.continuous_val`) and `Topology.Algebra.OpenSubgroup`
  (`Subgroup.isOpen_of_mem_nhds`). `Algebra.norm_eq_matrix_det` and
  `Algebra.norm_zero` come in transitively.

The proof needs no M257.004–005 compactness or intersection result, no M256
base-unit openness, and neither the M254 equivalence
`abelianizationEquivNormQuotient` nor any other reciprocity input. The
source-local quotient topology `Langlands.NYLL.PortInternal.M257.d001` is not
needed: neither the target nor the proof mentions the norm quotient. It is
therefore not enabled here. No host class-formation, Tate, cup-product or
transfer target is discharged.

## Source correspondence and attribution

The original is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean`,
lines 125–213, unit M257.006, the private theorem
`LocalClassFieldTheory.localNormSubgroup_isOpen_of_compatibleLocalField`.
The original file's SHA-256 is
`28cfb0b56b885089511a7372bfe3bf5e80d444fb91d1e982ba0b5647d26d0108`. It is
kept under
`literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The source proof takes a different route. It shows that the image of the
integer units under the norm is compact, hence closed (M257.004). It writes this
image as the intersection of the norm subgroup with the base integer units
(M257.005). It gets finiteness of `Kˣ ⧸ localNormSubgroup K L` from the local
reciprocity equivalence `abelianizationEquivNormQuotient` (M254.001). The
relative norm subgroup is then a closed, finite-index and therefore open
subgroup of the open base integer units (M256.002). Worker 64 keeps the source
theorem's telescope, the inventory name `d006` and the namespace prefix
`Langlands.NYLL.PortInternal.M257`. The theorem now has the published
proposition as its type, and the source proof is replaced by the
inverse-function argument above. The source imports are replaced by the
published target module and the focused Mathlib modules listed above. The
source's local quotient-topology instance and scope openings are not needed.
The modification notice in the Lean header records these changes.

The original copyright and author header is kept verbatim. The unchanged
Apache-2.0 [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) remain at
`licenses/NYLL/`. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The NOTICE has no entry specific to this module.
