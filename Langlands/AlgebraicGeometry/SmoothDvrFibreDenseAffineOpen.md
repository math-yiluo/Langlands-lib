# An actual fibre-dense affine open over an arbitrary DVR

Author: Worker 219.

For every universe `u`, let `R : Type u` be a commutative domain which
is a discrete valuation ring, and let `X : Scheme.{u}` with structural
morphism `p : X ⟶ Spec R`. Assume `p` is smooth, quasi-compact and
separated. Then

```lean
smoothDvrFibreDenseAffineOpen R X p : FibreDenseAffineOpen p
```

constructs actual affine-open data. By definition its result is the subtype

```lean
{U : X.Opens // IsAffineOpen U ∧
  ∀ x : X, ∃ y : X, y ∈ U ∧ p y = p x ∧ y ⤳ x}
```

For `D := smoothDvrFibreDenseAffineOpen R X p`, the open is `D.opens`,
its affineness proof is `D.isAffineOpen`, and `D.exists_generization x`
provides the required point and its three properties. The subtype
projections `D.val` and `D.property` also expose the data directly.
`exists_smoothDvrFibreDenseAffineOpen` is the immediate existential
consequence with exactly the displayed formula.
`smoothDvrFibreDenseAffineOpenStatement` supplies the unchanged published
proposition `SmoothDvrFibreDenseAffineOpenStatement.{u}` by applying that
consequence under its quantified hypotheses.

There is no connectedness, nonempty-fibre, generic-affineness,
henselianity, completeness, excellence, perfectness or
residue-characteristic restriction, and no group structure. In
particular the constructor does not take a common-affine-neighbourhood
theorem as a premise.

The proof applies the actual constructor
`normalCodimensionOneAffineNeighbourhood` to `fibreGenericPoints p`,
the images of all component generic points in all scheme fibres. A DVR
has two spectrum points. Quasi-compactness and local finite type make
this selected set finite. Smoothness over a DVR supplies integrally
closed domain stalks. The previously proved
`SmoothDvrFibreGenericPoints.ringKrullDim_stalk_le_one` shows that each
selected point has stalk dimension at most one: its stalk is a field
on the generic fibre and a DVR on the special fibre.

Thus the general constructor supplies an affine open containing every
fibre-component generic point. `fibreGenericPoints_subset_iff` turns
that containment into the same-fibre generization property. This proof
also covers empty schemes and empty fibres.

The source is Bosch–Lütkebohmert–Raynaud, *Néron Models* (Springer,
1990), §6.4 Lemma 4 and the paragraph immediately following it,
printed p.155 (PDF p.162). Registered source:
`bosch-lutkebohmert-raynaud-1990-neron-models`, SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
This is a derived DVR specialization of the general normal
affine-neighbourhood construction. It uses no downstream group-affineness
conclusion.
