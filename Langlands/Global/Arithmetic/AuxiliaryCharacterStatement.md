# Auxiliary local characters and unit-norm stabilizers

Author: Worker 35. Proposition definitions for task
`369ca096-d0b6-4e25-8a06-66af3ef95878`, revision 2.
These definitions assert no theorem truth. No local or global Langlands
correspondence is assumed.

## Mathematical content

Let `F` and `M` be arbitrary finite extensions of `Padic p`, with compatible
base algebra structures, and suppose `M/F` is finite Galois. Let `L` be an
actual intermediate field. Mathlib supplies the multiplicative field norm
`Algebra.norm L : M →* L` and the group `M ≃ₐ[F] M`. No norm map, Galois
action, or unspecified general-position predicate is supplied as extra data.

`HasExactUnitNormStabilizer L χ` says that an `F`-automorphism of `M` fixes
the function `χ` composed with the norm on all valuation units of `M` if
and only if it fixes `L` pointwise. More explicitly, for every such
automorphism `σ`,

\[
 \bigl(\forall z\in M^\times,\ |z|=1 \Longrightarrow
       \chi(N_{M/L}(\sigma z))=\chi(N_{M/L}(z))\bigr)
 \quad\Longleftrightarrow\quad \sigma\in\operatorname{Gal}(M/L).
\]

`Units.map` restricts each actual multiplicative map to its unit group.
`L.fixingSubgroup` is Mathlib's pointwise fixing subgroup of the actual
intermediate field. Finite dimensionality ensures that `Algebra.norm` is
the usual finite-extension determinant norm, not its degenerate fallback
outside finite modules.

`AuxiliaryCharacterStatement` asks, for every nonnegative integer `r`,
for a continuous finite-order character `χ : Lˣ →ₜ* ℂˣ` satisfying this
unit-stabilizer condition and nontrivial on some element `x` with

\[
 |x-1| < p^{-r}.
\]

Thus the characters remain nontrivial arbitrarily deep in the principal
units. The target does not supply a conductor function as an unconstrained
parameter. These balls form a neighborhood basis of one, and their
nontriviality is the topological formulation of unbounded conductor.
The finite order is explicit: there exists `n > 0` with `χ^n = 1`.

## Instances, universes and scope

The carrier universes of `F` and `M` are independent (`u` and `v`).
`L` is the subtype of `M` defined by `IntermediateField`. The scalar-tower
instance requires that the specified embeddings of `Padic p` agree with
the extension `F → M`. Finite dimensionality over `F` is explicit, as is
the Galois hypothesis on `M/F`. No Galois hypothesis on `L/F` is imposed.

The target locally installs `M.canonicalNormedField`. The subfield topology
on `L`, and the induced topology on its units, are therefore the actual
topologies coming from the canonical extended p-adic norm. The norm
extends `|p| = p⁻¹`; it is not the residue-cardinality normalized absolute
value. Its norm-one elements are precisely the valuation units, regardless
of this positive-power normalization difference. The statement covers
every prime, including two, and has no degree bound or `n < p` condition.

## Original source correspondence

Henniart 2000, Section 3.4, condition 3, printed p.449, requires the
stabilizer of the norm pullback **restricted to the unit group** to be
exactly the subgroup fixing the local inducing field. Section 3.6,
Lemma 3, p.451, chooses a finite-order auxiliary character having that
property by referring to the proof of Harris's Lemma 4.7. The restriction
to units matters: multiplication by an unramified character does not
change those restrictions.

Harris 1998, Lemma 4.7, p.201, and its proof on pp.204–206 construct
finite-order characters of arbitrarily large conductor in general
position. Equations (4.12) and (4.13), pp.204–205, give the sufficient
norm-pullback stabilizer condition. The proof uses normal bases and
p-adic logarithms on sufficiently small units, together with the
finite-index norm/character descent from local class field theory.

The sources formulate the stabilizer in the Galois closure of `L/F`.
The Lean target allows any specified finite Galois overfield `M/F`.
This is a derived extension of that formulation: the same normal-basis
argument applies to the fixed subgroup `Gal(M/L)` in `Gal(M/F)`.
It is not claimed that the articles quantify over every such overfield
verbatim. A future proof must justify both the norm descent and exact
unit-level stabilizer for that scope.

This target is the auxiliary character-existence input. It does not
yet formalize the Clifford–Mackey implication to irreducibility of all
the constituents in Harris's Definition 4.5. That implication, the
prime-cyclic tower construction, and the global weak automorphic
induction output with its auxiliary supercuspidal component remain
separate required targets.

### Source proof qualification at residue characteristic two

On p.205 Harris passes from a character modulo `p^N` to a complex
character by an embedding of `(ℤ/p^Nℤ)ˣ` into `ℂˣ`. The full group is
not cyclic when `p = 2` and `N ≥ 3`, so that literal embedding is
unavailable. This does not justify removing characteristic two from
the target. A complete proof must instead use a suitable cyclic
principal-unit image, or another correct construction, and verify that
the depth and exact stabilizer survive it. No proof of that repair is
claimed here.

### Retained originals

- Guy Henniart, *Une preuve simple des conjectures de Langlands pour
  GL(n) sur un corps p-adique* (2000), Sections 3.3–3.4, p.449, and
  Section 3.6, Lemma 3 and proof, p.451.
  Source `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
- Michael Harris, *The local Langlands conjecture for GL(n) over a
  p-adic field, n < p* (1998), Definition 4.5 and Lemma 4.7, p.201;
  proof of Lemma 4.7, pp.204–206, especially (4.12)–(4.13), pp.204–205.
  Source `harris-1998-local-langlands`, SHA256
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
  The relevant section has no restriction `n < p`, despite the title.

Both relevant passages and their context were read directly from the
retained originals. The stronger unit formulation is taken from
Henniart's explicit condition and his use of Harris's construction.

## Dependencies and validation boundary

The project import is the published `Langlands.LocalField.Definitions`,
reused by its declarations in Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`. Its Lean SHA256 is
`8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517`.
The local norm,
Galois group, fixing subgroup and continuous characters are Mathlib
constructions. No unpublished global adele norm construction is needed
for this local theorem target.

Native compilation of both the imported project module and this target
completed without warnings or errors under Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. Both complete elaborated
definitions were printed and inspected, retaining the independent
universes, compatible scalar tower, finite Galois extension, arbitrary
intermediate field and arbitrary depth. The selected target returns
`Prop`. Axiom inspection reports only `propext`, `Classical.choice` and
`Quot.sound`.

The development Lake build and registered proposition inspection also
completed with zero warnings and errors and confirmed that the complete
target returns `Prop` with universe parameters `u` and `v`.

These development results do not prove the existence assertion or
constitute independent semantic acceptance. The source qualifications
above remain obligations for any eventual proof.
