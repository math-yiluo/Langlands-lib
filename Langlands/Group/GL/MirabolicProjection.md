# Actual mirabolic projection and the plus-induction subgroup

Author: Worker 749.

This module adds group-theoretic infrastructure for Bernstein and Zelevinsky,
*Representations of the group GL(n,F), where F is a non-archimedean local
field* (1976), §§5.1–5.4, printed pp.44–45 (PDF zero-based indices 43–44), and
§5.11, printed p.46 (index 45). The registered original is
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`. No
applicable errata entry for this source was found in the supplied public notes
or literature.

All declarations live in `Langlands.GeneralLinear.Mirabolic`. They import and
reuse the published `Langlands.Group.GL.MirabolicRadical` pair (`radical`,
`radicalElement`, `radicalCoordinates`, `levi`, `successor`,
`successorSubgroup`, and their continuity results) without changing it. Every
algebraic statement holds for an arbitrary commutative ring `F` in an arbitrary
universe, not only for the source's local fields.

## Provenance and source indexing

Section 5.1 defines, inside `G_r = GL(r,F)`, the mirabolic group
`P_r = {p_rj = 0 for j < r, p_rr = 1}` and the subgroup
`M_r = {m_ij = δ_ij for j < r, m_rr = 1}`. The Library's
`mirabolic n F` is `P_(n+1)`. Its `radical n F` is `M_(n+1)`; the
`MirabolicRadical` Markdown uses the name `V_(n+1)` from Bernstein–Zelevinsky
(1977), and this is the same actual subgroup. Section 5.2 embeds
`G' = G_(r-1)` in `P_r` as the matrices `diag(g,1)`; this is the published
`levi`. Writing `P' = P_(r-1)`, it states that `M` is normal in `P`, that
`P = G'·M` is a semidirect product, and that `M ≅ F^(r-1)`. Section 5.4 fixes
the character `θ` of `M` and the subgroup `P'·M`. Section 5.11(b) sets
`Φ⁺(τ) = ind(P, P'·M, τ')` with `τ'(pm) = θ(m)τ(p)` for `p ∈ P'`, `m ∈ M`,
and §5.11(d) defines `Ψ⁺(ρ)(gm) = ρ(g)` for `g ∈ G'`, `m ∈ M`.

The source states these decompositions without proof. The declarations here are
derived elementary construction lemmas that make the decompositions concrete for
the actual matrix subgroups: the quotient maps `P → G'` and `P'·M → P'`, the
final-column coordinate, and the subgroup `P'·M`. This module does not prove or
assert the Lemma of §5.4 (conjugacy of nonzero characters, the stabilizer
`Norm_P(M,θ) = P'·M`, or the orbit statement). It also constructs no
representations. It does not assert the functors of §5.11, their exactness or
adjunctions (§5.12), any Fourier or stalk equivalence (§§5.9–5.10), or compact
minimality.

## Projection to the Levi block

For `g ∈ mirabolic n F`, write `g = [[A,v],[0,1]]` with `A` the upper-left
`n × n` block and `v` the final column above the last diagonal entry.

`projection : mirabolic n F →* Langlands.GeneralLinear n F` sends `g` to `A`:

```
(projection g).val i j = g.val.val i.castSucc j.castSucc     (projection_apply)
((projection g)⁻¹).val i j = (g⁻¹).val.val i.castSucc j.castSucc
                                                    (projection_inv_apply)
```

The inverse matrix is the upper-left block of the actual mirabolic inverse
`g⁻¹`. The private lemma `upperLeft_mul` proves that for any matrices `X`, `Y`
of size `n+1`, if `Y` has final row `(0,…,0,1)`, then the upper-left block of
`X*Y` is the product of the two upper-left blocks: in the sum over `k`, the
term `k = last` vanishes because `Y last j.castSucc = 0`. Applying this to
`g*g⁻¹ = 1` and `g⁻¹*g = 1` gives both unit equations, so no field or
determinant argument is used. The same lemma gives multiplicativity.

Results: `projection_levi` (`projection (levi a) = a`),
`projection_surjective`, `projection_successor`
(`projection (successor g) = g.val`), and `projection_radicalElement`
(`projection u(v) = 1`). `ker_projection` states
`projection.ker = radical n F`. If the upper-left block is the identity, the
mirabolic last row supplies the remaining identity-column entries. The converse
reads the radical's column equations at `castSucc` rows.
`projection_eq_one_iff` restates this, and the instance `radical_normal`
derives normality of `radical n F` from the kernel equality.

## Final column and radical-then-Levi coordinates

`lastColumn g : Fin n → F` is `fun i => g.val.val i.castSucc (Fin.last n)`
(`lastColumn_apply`). On the radical it is the published coordinate map
(`lastColumn_val : lastColumn u.val = radicalCoordinates u`). Also
`lastColumn (radicalElement v).val = v`, `lastColumn (levi a) = 0`, and
`lastColumn 1 = 0`.

Block multiplication `[[A,v],[0,1]]·[[B,w],[0,1]] = [[AB, A w + v],[0,1]]`
gives

```
lastColumn (g * h) = (projection g).val.mulVec (lastColumn h) + lastColumn g
                                                         (lastColumn_mul)
```

where `mulVec` is `(A w) i = ∑ j, A i j * w j`, without transposition.

`eq_radicalElement_mul_levi` proves the actual factorization

```
g = (radicalElement (lastColumn g)).val * levi (projection g)
```

i.e. `[[A,v],[0,1]] = [[I,v],[0,1]] · [[A,0],[0,1]]`. Its proof is algebraic:
`g * (levi (projection g))⁻¹` lies in the kernel of `projection`, hence in the
radical, and `lastColumn_mul` shows its final column is `lastColumn g`.
`radicalElement_coordinates` then identifies it with
`radicalElement (lastColumn g)`. `eq_radicalElement_mul_levi_iff` proves
uniqueness: `g = u(v) * levi a` iff `v = lastColumn g` and `a = projection g`.
The two auxiliary simp lemmas `projection_radicalElement_mul_levi` and
`lastColumn_radicalElement_mul_levi` compute both coordinates of `u(v)*levi a`.

The source writes `P = G'·M` with the Levi factor first. Here the radical
factor comes first. Both orders describe the same set of products because
`M` is normal. Under the published law `levi_mul_radicalElement`,
`diag(A,1)·u(w) = u(A w)·diag(A,1)`, the
Levi-first coordinates of `g` would be `(A, A⁻¹ v)`. Radical-first coordinates
are the literal matrix entries `(v, A)` and avoid that inverse. This order is
a derived implementation choice.

`radicalLeviEquiv : mirabolic n F ≃ (Fin n → F) × Langlands.GeneralLinear n F`
is `g ↦ (lastColumn g, projection g)` with inverse
`(v, a) ↦ (radicalElement v).val * levi a`. It is an equivalence of types
only. The product is a coordinate space and not a direct-product group
decomposition: by `lastColumn_mul`, matrix multiplication corresponds to
`(v, A)(w, B) = (A w + v, A B)`, not componentwise multiplication. No
statement here asserts otherwise.

## The plus subgroup `P'·M`

Take source rank `r = n+2`. Then `P = P_(n+2) = mirabolic (n+1) F`,
`M = M_(n+2) = radical (n+1) F`, and `P' = P_(n+1) = mirabolic n F`, embedded
by the published `successor` (`g ↦ diag(g,1)`). The source's `P'·M`, the
inducing subgroup of `Φ⁺` in §5.11(b), is

```
plusSubgroup n F : Subgroup (mirabolic (n + 1) F) :=
  (mirabolic n F).comap projection
```

`mem_plusSubgroup` restates the definition; `mem_plusSubgroup_iff_entry`
says row `n` of the `(n+2) × (n+2)` matrix restricted to its first `n+1`
columns is `(0,…,0,1)`:

```
g.val.val (Fin.last n).castSucc j.castSucc = if j = Fin.last n then 1 else 0.
```

Thus the plus elements are exactly the matrices
`[[A',a,x],[0,1,c],[0,0,1]]` with `A'` an invertible `n × n` block; the final
column is `(x, c) = lastColumn g`.

Inclusions: `successor_mem_plusSubgroup`, `successorSubgroup_le_plusSubgroup`,
and `radical_le_plusSubgroup` (the radical has trivial projection).
`plusSubgroup_eq_sup` proves
`plusSubgroup n F = radical (n + 1) F ⊔ successorSubgroup n F`.

`plusProjection : plusSubgroup n F →* mirabolic n F` is `projection`
restricted to the subgroup, with codomain restricted by membership. Its value
is `(plusProjection g).val = projection g.val` (`plusProjection_val`), and its
entry formula is

```
(plusProjection g).val.val i j = g.val.val.val i.castSucc j.castSucc
                                                  (plusProjection_apply)
```

`plusSuccessor : mirabolic n F →* plusSubgroup n F` is `successor` with
codomain restricted, and `plusRadical : radical (n + 1) F →* plusSubgroup n F`
is the subgroup inclusion. Agreement with `successor`:
`plusProjection_plusSuccessor` (`plusProjection (plusSuccessor g) = g`) and
`plusProjection_comp_plusSuccessor`. Hence `plusProjection_surjective`.
Triviality on the radical: `plusProjection_plusRadical`, and
`ker_plusProjection` identifies the kernel with
`(radical (n + 1) F).subgroupOf (plusSubgroup n F)`.

Factorization: `plus_eq_radicalElement_mul_successor` proves

```
g.val = (radicalElement (lastColumn g.val)).val * successor (plusProjection g)
```

and `plus_eq_plusRadical_mul_plusSuccessor` states the same identity inside
the subgroup. `mem_plusSubgroup_iff_exists` characterizes membership as
existence of `v` and `p` with `g = (radicalElement v).val * successor p`.
`radicalSuccessorEquiv : plusSubgroup n F ≃ (Fin (n + 1) → F) × mirabolic n F`
is `g ↦ (lastColumn g.val, plusProjection g)`, with inverse
`(v, p) ↦ (radicalElement v).val * successor p`. Again this is an equivalence
of types only, not a group isomorphism.

`lastColumn_mul_last` records that on the plus subgroup the last coordinate
`c` of the final column is additive:
`lastColumn (g * h).val (Fin.last n) = lastColumn g.val (Fin.last n) + lastColumn h.val (Fin.last n)`.
In `lastColumn_mul`, row `n` of `projection g` is `(0,…,0,1)` for plus
elements, so `(A w)_n = w_n`. This is the entry used by the published
`Langlands.Derivative.Mirabolic.theta` on the radical (via `lastColumn_val`).
The present module neither extends `θ` nor constructs `τ'`, `Φ⁺` or `Ψ⁺`. The
homomorphisms `plusProjection` and `projection` are the inflation maps that
those later constructions need.

## Topology

All groups carry their inherited matrix-unit topologies: `GeneralLinear` has
the units topology, and mirabolic and plus groups have subspace topologies.

With only `[TopologicalSpace F]`:

- `continuous_projection`: entries of the value are continuous entries of `g`,
  and entries of the inverse value are continuous entries of `g⁻¹`, read
  through `Units.continuous_coe_inv`. No continuity of ring operations or
  inversion in `F` is assumed.
- `continuous_lastColumn`: coordinatewise entries.
- `continuous_plusProjection`: composite with the subtype inclusion.
- `projectionContinuous` and `plusProjectionContinuous` package the two
  homomorphisms as `ContinuousMonoidHom`s.

With additionally `[T2Space F]`, `plusSubgroup_isClosed` proves that the plus
subgroup is closed in `mirabolic (n + 1) F`. It is the preimage under the
continuous `projection` of the published closed subgroup
`mirabolic n F ⊆ GeneralLinear (n + 1) F`
(`Langlands.GeneralLinear.Mirabolic.isClosed`).

With `[IsTopologicalRing F]`, the coordinate equivalences become
homeomorphisms, `radicalLeviHomeomorph` and `radicalSuccessorHomeomorph`. The
forward maps are continuous by the results above. Each inverse is a matrix
product of the published continuous maps `radicalElement` and `levi`,
respectively `successor`; multiplication in the mirabolic group is continuous
because ring multiplication and addition in `F` are. They are
homeomorphisms only, not topological group isomorphisms. Their `_apply` and
`_symm_apply` simp lemmas restate the formulas above.

## Boundary ranks

No positive-rank or field assumption is imposed; `n = 0` is included in every
declaration.

- Item 1 at `n = 0`: `projection : mirabolic 0 F →* GeneralLinear 0 F` maps
  the trivial group `P_1` onto the actual group of units of the `0 × 0` matrix
  ring `GL_0`. `radical 0 F = M_1` is the trivial subgroup, and the kernel and
  factorization statements hold literally. `lastColumn` takes values in the
  one-point space `Fin 0 → F`.
- Item 3 at `n = 0`: `plusSubgroup 0 F` consists of the
  `[[1,c],[0,1]]` in `P_2 = mirabolic 1 F`. `plusSubgroup_zero` proves
  `plusSubgroup 0 F = radical 1 F`, i.e. `P_1 M_2 = M_2`, from
  `plusSubgroup_eq_sup` and the triviality of `mirabolic 0 F`.
