# Geometric averaging bridge for nested compact subgroups

Worker 344 implements this statement. The carried task attributes the bridge
interface to Worker 209 and the proposed geometric argument to Worker 48,
refined by Worker 209. Those are contributors from the previous project
instance; their attribution is retained here.

`Langlands.Jacquet.BlockStableImageAverageBridgeStatement.{uF,uV} F T B V`
is a transparent Prop-valued definition. It imports the existing
`CanonicalLiftDefinitions` and `BlockIwahoriDefinitions` constructions and
introduces no new data. This module states a target; it supplies no proof of
either conclusion.

## Parameters and actual objects

The complete telescope retains every prime `p` with `[Fact p.Prime]`,
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, every natural rank
`n`, every `B : GeneralLinear.BlockShape n`, and every complex module
`V : Type uV` with `[AddCommGroup V] [Module ℂ V]`. The universes `uF` and
`uV` are independent. The body installs `T.topology` and
`T.generalLinearTopologicalGroup n`, just as
`CanonicalLiftCompatibilityStatement` does.

The target quantifies over every actual representation
`ρ : Representation ℂ (GeneralLinear n F.Carrier) V` and a smoothness witness
`hρ : IsSmooth ρ`. It then quantifies over actual open subgroups `K1`, `K0`,
separate compactness witnesses `hK1`, `hK0`, their inclusion `K1 ≤ K0`, and
`B.HasBlockIwahoriFactorization T` for each. That existing predicate uses the
actual lower, Levi and upper intersections and requires its conjugation
containments for every weakly contracting tuple. It is not redefined here.

There is one tuple `a : Fin B.length → F.Carrierˣ`, with
`B.IsStrictlyContracting T a`, and an arbitrary element

```lean
w : stableImage ρ hρ K1 hK1 (B.blockScalar F.Carrier a)
```

Write `A := B.blockScalar F.Carrier a`, and use the actual maps

```lean
v := stableImageToRepresentation ρ hρ K1 hK1 A w
e0 := Compact.averageMap ρ hρ K0 hK0
```

Here `stableImage` is the intersection of the ranges of every natural power
of `compressedAction`, an endomorphism of the actual compact fixed-vector
module. Compression acts by `ρ A` and then takes the normalized compact
average. No stationary exponent is part of the definition.

## The two conclusions

The first conclusion is membership of the actual fixed-vector element

```lean
(⟨e0 v, Compact.averageMap_mem_fixedVectors ρ hρ K0 hK0 v⟩ :
  fixedVectors ρ K0.toSubgroup)
```

in `stableImage ρ hρ K0 hK0 A`. It concerns the same tuple `a` on both
subgroups. It asserts membership in every power range, even without
admissibility or finite-dimensional stabilization.

For the second conclusion, set `N := B.unipotentSubgroup F.Carrier`,
`M := B.leviSubgroup F.Carrier`, and
`hMN := B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier`.
The clause is the implication

```lean
Jacquet.mk ρ N v ∈
    fixedVectors (Jacquet.action ρ N M hMN)
      (K0.toSubgroup.comap M.subtype) →
  Jacquet.mk ρ N (e0 v) = Jacquet.mk ρ N v
```

The action is the existing unnormalized descended action on the actual
coinvariant quotient. The premise says that the original class is fixed by
the larger compact Levi intersection. This premise is essential and remains
explicit. The two clauses are conjoined under the same universally quantified
data.

The statement has no admissibility, finite dimension of `V`, positive rank,
nonempty block, proper parabolic or nonzero representation assumption.
Rank zero, empty shapes, one-block shapes and the zero representation remain
included. It assumes no chosen lift inverse, quotient surjectivity,
canonical-lift bijectivity or compatibility conclusion.

## Internal derivation and intended geometric argument

This is an internal derived prerequisite for the same-class nested averaging
clause `Langlands.Jacquet.BlockStableImageNestedAverageClause`. In that
application, equality with the class of a `K0`-fixed representative supplies
the larger-Levi fixedness premise through the existing `fixedJacquetMap`.
Uniqueness within the stable image is a separate step, using admissibility
and the kernel and Fitting results. This bridge neither asserts uniqueness
nor chooses any representative of a quotient class. Its focused proof
successor is task `4054ca18-7654-4c6c-876b-fa659e5abd88`; the consumer is
task `f87704e4-dd72-413f-92b7-99627cba1a40`.

The following is a proposed proof route, not a proof supplied by this module.
The actual intersection `K0 ∩ Nop` is compact because the opposite radical
is closed. Uniform block contraction makes
`A⁻ʳ (K0 ∩ Nop) Aʳ` lie inside `K1` for every sufficiently large `r`.
For a requested exponent `m`, express `w` as `C1^(r+m) x`, where
`Ci := compressedAction ρ hρ Ki hKi A`. Normalized nested averaging and
the compressed power law give
`e0 v = e0 ρ(A^(r+m)) x`. The vector `y := ρ(A^r) x` is fixed by
`K0 ∩ Nop`. Reverse the `K0` factorization, use upper contraction and
Levi commutation, and average over the finite orbit to obtain
`e0 ρ(A^m) (e0 y) = e0 ρ(A^m) y`.
This would place the displayed fixed-vector element in the range of `C0^m`
for every `m`.

For the quotient clause, express `w` as `C1^r x` at a sufficiently large
exponent. The compressed quotient law identifies the class of
`z := ρ(A^r) x` with the class of `v`. Lower factors fix `z`; Levi
factors fix its class by the explicit premise; upper factors act trivially
on coinvariants. Reversed factorization therefore makes the quotient map
constant on the `K0`-orbit of `z`. Finite-orbit averaging would preserve
that class. These are obligations of the separate proof task.

## Source motivation and scope

Bill Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III: *Induced representations and the Jacquet module*, revision
April 29, 2019, section 4, page 5, and section 5, pages 5–7, especially
Lemma III.5.7 on page 7. Registered source:
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Retained original:
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
Worker 344 read original pages 5–7; no separate project errata file was found.

III.5.7 compares canonical representatives for nested factorizing compact
open subgroups when they have the same Jacquet image. The bridge here is
stronger in allowing arbitrary smooth complex representations, and isolates
only the geometric averaging part. It is not a literal named theorem of
that source. The source's canonical complement is a sufficiently high power
image under admissibility, whereas this target uses the published all-power
intersection directly. The intended argument above uses normalized
finite-orbit averaging and does not silently identify Casselman's
unnormalized coset-sum operator with `compressedAction`. Page 7 restricts
the source argument to coefficient fields and retracts an earlier claim
over general Noetherian rings. This target uses the field `ℂ`.
