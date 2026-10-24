# Principal ideles and ordinary units

`PrincipalIdeleUnitCriterion.{u}` states that, for every number field
`E : Type u` and every nonzero field element `a : Eˣ`, the following are
equivalent:

- At every finite place `w : HeightOneSpectrum (𝓞 E)`, the actual completion
  coordinate of `IdeleGroup.unitEmbedding (𝓞 E) E a` has valuation one.
- There is a unit `ε : (𝓞 E)ˣ` whose image under the actual algebra map
  from the ring of integers to `E` is `a`, as an equality in `Eˣ`.

The left side uses the published `ideleCoordinate` and Mathlib's canonical
adic-completion valuation. It restricts every finite place and imposes no
condition on the infinite coordinates. The right side uses `Units.map`
applied to `algebraMap (𝓞 E) E`; it is the actual ordinary unit group, not a
substitute defined by the valuation condition. Field units include all nonzero
field elements, so the statement has no initial integrality hypothesis.
No extension, Galois, cyclicity, or common-universe assumption is needed.

This is the arithmetic recognition needed to identify the principal-idele
kernel inside the subgroup integral and invertible at every finite place.
The present file defines the proposition only. It does not prove the
recognition, construct an exact sequence, or assert a cohomological formula.

The original source is J. S. Milne, *Class Field Theory*, v4.03 (2020),
Chapter V, Aside 4.5 and the first part of footnote 12, printed page 171
(PDF page 180). There Milne identifies the diagonal elements that are units
in every finite completion with the units of the global ring of integers.
The Lean formulation uses full ideles and explicitly quantifies only finite
coordinates, giving exactly the same condition. Only this local-unit
recognition is used from the footnote; its later assertions about topologies
and subgroups of finite index are outside this statement.

Registered source: `milne-2020-class-field-theory`, SHA256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.
