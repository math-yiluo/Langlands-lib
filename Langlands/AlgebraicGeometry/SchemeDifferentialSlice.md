# Scheme slices from residue cotangent spanning

This private draft constructs a local scheme slice from the differential
input on common affine charts. Given `t,s : R → U` with `s` smooth, choose
affine opens `V` in `U` and `W` in `R` with `W` mapping into `V` under
both maps. Put `A = Γ(U,V)` and `B = Γ(R,W)`, using the map induced by `s`
as the `A`-algebra structure of `B`. The map induced by `t` may differ from
this structure and determines the slice equations.

At a chosen prime `q` of `B`, assume that the differentials of the images
under `t` of an allowed ideal `p` span the residue cotangent fiber of
`B_q` over `A`. Assume also that these images vanish at `q`. The affine
differential slicing lemma supplies a finitely generated ideal `I ≤ p`,
a principal neighborhood of `q`, and an etale quotient on that
neighborhood for the algebra structure induced by `s`.

The quotient spectrum `Spec(A/I)` maps to `U` through the affine chart;
this map is locally of finite presentation because `I` is finitely
generated. The localized quotient enters the full pullback
`Spec(A/I) ×_U R` by an open immersion, and is etale over `U` after the
second projection and `s`. A lift of `q` therefore gives a point of the
full pullback projecting to the chart image of `q` where the stalk of that
composite is formally etale. This uses the conditional ambient chart
construction and the explicit tower of algebra maps of the localized
quotient.

This is an internal construction, not an assumption of the slicing
theorem. The residue cotangent spanning condition remains an explicit
hypothesis. Good-point existence, propagation to the whole pullback,
and global surjectivity remain separate obligations.

Equation slices into affine charts are preimmersions, since the quotient
spectrum map is a closed immersion and the chart map is an open immersion.
Their base changes are therefore injective on points. Consequently, if
`e : U → R` is a section of `t` and the selected point lies over `e(x)`,
it is the canonical identity lift of its first projection `a`, with
`g(a) = x`. The formal etaleness conclusion thus holds at this identity
lift. This comparison uses injectivity of the actual second projection;
no general claim that scheme pullback points are determined by two
arbitrary projections is used.

When `g` and `s` are locally of finite presentation, the composite of the
second projection with `s` is locally of finite presentation. Its
formally etale stalk therefore has an open neighborhood etale over `U`,
by the scheme etale-locus construction.

The common-chart lemma chooses an affine neighborhood `V` of a base point
and an affine neighborhood `W` of its identity arrow inside the intersection
of the two inverse images of `V`. It uses only the affine-open basis and
the two section identities. The final identity-slice corollary combines
the differential construction with the preimmersion comparison: when the
chosen chart prime maps to `e(x)`, it returns a scheme `Z`, a preimmersion
`g : Z → U` locally of finite presentation, and a point `a` with `g(a)=x`
where the canonical identity lift has a formally etale stalk. The
cotangent spanning condition and prime containment remain hypotheses.
