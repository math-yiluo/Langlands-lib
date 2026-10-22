# Double-quotient levels and Hecke maps

This is a generic construction of the topological level spaces used in the
complex description of a Shimura tower. The inputs are actual groups `Gamma`
and `G`, a group homomorphism `iota : Gamma -> G`, and an actual `Gamma`-space
`X`. In the intended Shimura specialization these are the rational group, its
finite adelic group, the diagonal map, and the conjugacy-class domain. This file
does not claim to have constructed those specializations or canonical schemes.

`CompactOpenLevel` contains a genuine Mathlib open subgroup and a proof that
its underlying subset is compact. An arrow from `K` to `L` is an actual group
element `g` with `g^-1 K g` contained in `L`. These transporter arrows form a
category: composition is multiplication in the order of right translation.
All categorical laws are proved. The arrows are represented elements, not
their classes modulo the target level; distinct arrows may induce the same map.
The inclusion arrow is represented by the identity element.

`levelSetoid` is the double-quotient relation on `X × G`: `(x,a)` and `(y,b)`
are related precisely when `y = gamma • x` and `b = iota(gamma) a k` for some
`gamma` and `k` in `K`. Reflexivity, symmetry, and transitivity are proved from
the group and action laws. `LevelSpace` is the quotient by this setoid, with
its quotient topology. The equality criterion is proved using Lean's actual
quotient. The group and domain carriers have independent universes.

`translate` sends the class of `(x,a)` to the class of `(x,a g)`. Its
well-definedness uses the conjugated element `g^-1 k g`, not an assumed map
between quotient spaces. Its identity and composition laws are proved.
Every translation is surjective: a class represented by `(x,a)` is the image
of the source class represented by `(x,a g^-1)`.
With continuous multiplication on `G`, continuity follows from the quotient
topology. `tower` packages the resulting genuine functor to `TopCat`.

For a topological group, `heckeLevel K L g` constructs the compact open subgroup
`K ∩ g L g^-1`. Compactness follows because an open subgroup is closed.
`heckeLeft` and `heckeRight` are the actual span of arrows from that level to
`K` and `L`. Applying `tower` gives the topological Hecke correspondence.
This does not assert that its maps are finite etale, or that the quotients
are represented by canonical algebraic schemes.

The construction isolates the quotient and level-map mechanism underlying
Harris 1997, Section 2, printed pages 88–90 (PDF pages 14–16), especially the
finite levels and compatible right actions on page 90. Harris 1999, Section 4,
pages 308–311 (PDF pages 10–13), uses the levels `K(N,m)` and their changes.
Kottwitz 1992, Section 1, pages 654–655 (PDF pages 2–3), specifies the
conjugacy-class domain, compact open levels, and resulting coefficient systems.
All these original passages were read; Kottwitz page 654 was also inspected
visually. These sources motivate the specialization, rather than stating the
generic transporter category verbatim. Its abstract construction and intrinsic
proofs are derived here by Worker 57.

The retained source identifiers and SHA-256 fingerprints are:

- `harris-1997-drinfeld-cohomology`:
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `kottwitz-1992-lambda-adic-simple-shimura`:
  `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.

Only Mathlib is imported: `Topology.Algebra.OpenSubgroup`,
`Topology.Category.TopCat.Basic`, and `Algebra.Group.End`. The pinned version
is commit `5ed2965256430c3649e86755f9576b54eca72435`, with Lean 4.34.0.
The module does not depend on pending project definitions. The generic topology
does not require continuity of the `Gamma` action; no separation, local
triviality, manifold structure or local-system theorem is inferred from that
quotient topology.
