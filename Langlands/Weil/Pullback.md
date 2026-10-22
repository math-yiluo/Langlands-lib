# Generic integer-Frobenius pullback

This module constructs a specific group from a continuous homomorphism
`φ : Γ →ₜ* ProfiniteIntegers`. It does not posit an arbitrary group called a
Weil group and does not identify the result with the Weil group of a field.

## Construction and interfaces

`Degree` is `Multiplicative ℤ`, with the usual discrete topology of the integers.
Multiplication in this type means addition of integers: its identity is integer
zero, and `Multiplicative.ofAdd 1` is the positive integer generator.
`ProfiniteIntegers` is Mathlib's actual profinite completion of this group,
constructed as the inverse limit of its finite quotients. It is not an
unspecified profinite group or an assumed procyclic group. `frobenius` is the
canonical homomorphism from the integer group into that completion, bundled
with continuity from the discrete domain.

For a group `Γ` with a topology and a continuous homomorphism `φ`, set

\[
 W(\varphi)=\{(g,n)\in\Gamma\times\mathbf Z:
                 \varphi(g)=\iota(n)\}.
\]

`pullbackSubgroup` implements this equalizer using `MonoidHom.eqLocus`.
`Pullback` is its subtype. Its multiplication is
`(g,n)(h,m) = (gh,n+m)` and its inverse is `(g,n)⁻¹ = (g⁻¹,-n)`.
The topology is precisely the subtype topology from
`Γ × ℤ_discrete`. When `Γ` is a topological group, the existing product and
subgroup instances make the pullback a topological group.

`projection` and `degree` are the two continuous group homomorphisms.
`degreeInt` unwraps the multiplicative integer type. The input is not required
to be surjective, so surjectivity of `degree` is not asserted unconditionally.

`inertia φ = ker φ` is a subgroup of `Γ`, with its inherited topology.
`inertiaSubgroup φ = ker (degree φ)` is a subgroup of the pullback.
`inertiaInclusion` maps `g` to `(g,0)` and includes its elementary continuity
proof. The intended further statements identify its image with
`inertiaSubgroup`, show that it is an open embedding, and characterize the
pullback topology uniquely by the topological group structure and this open
embedding. Those are separate proposition definitions for later proof targets;
this definition artifact does not claim their proof.

The definitions themselves need only `[Group Γ] [TopologicalSpace Γ]`.
The topology characterization requires `[IsTopologicalGroup Γ]`. Formation
of an equalizer and of continuous coordinate projections needs no stronger
hypotheses. Hausdorffness, compactness, total disconnectedness, and
surjectivity of `φ` are not silently assumed.

## Original sources and correspondence

The construction generalizes the concrete definition in Guy Henniart,
*Representations du groupe de Weil d'un corps local*, L'Enseignement
Mathematique (2) 26 (1980), 155-172,
[DOI 10.5169/seals-51064](https://doi.org/10.5169/seals-51064).
Section 2.1, printed page 158 (PDF page 5), defines the local Weil group as the
subgroup of the absolute Galois group acting on the residue field by integer
powers of Frobenius. Inertia is open and has the topology induced from the
absolute Galois group. The beginning of Section 2.2 on the same page identifies
the quotient by inertia with the integers and uses a Frobenius lift.

Exact citation:

- `literature_id`: `henniart-1980-weil-representations`
- `content_sha256`: `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`
- File: `C:/Central-Library/Henniart--Representations du groupe de Weil dun corps local--1980.pdf`
- Locator: Section 2.1 and the first paragraph of Section 2.2, printed page 158,
  PDF page 5. The hypotheses are introduced in Section 1.1, page 155, PDF page 2.

The source's subgroup description becomes the pair description above after
identifying the residue Galois group with the profinite completion and using
injectivity of the integer map. Adding the discrete integer coordinate records
the topology that the source prescribes on inertia. The universal property
and topology characterization are derived interface statements, not quoted
theorems from Henniart.

For the eventual local Langlands application, the convention will send
geometric Frobenius to integer degree `+1`. Henniart,
*Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
p-adique*, Invent. Math. 139 (2000), Section 1.1, printed page 439
(PDF page 1), normalizes reciprocity so geometric Frobenius corresponds
to a uniformizer:

- `literature_id`: `henniart-2000-simple-proof`
- `content_sha256`: `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`
- File: `C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`
- Locator: Section 1.1, page 439, PDF page 1, reciprocity normalization.
- [DOI 10.1007/s002229900033](https://doi.org/10.1007/s002229900033).

The generic `φ` makes no choice between arithmetic and geometric Frobenius.
That choice is part of the later residue-group identification. Replacing
the chosen Frobenius by its inverse reverses integer degree and preserves
the integer-power subgroup and inertia.

## Missing p-adic specialization

To identify this construction with the actual local Weil group of a finite
extension `F/ℚ_p`, later work must provide and verify all of the following.

1. A separable closure, the absolute Galois group with its Krull profinite
   topology, and its topological group structure.
2. The extension of the valuation to the closure, its invariance under
   Galois automorphisms, and the induced action on the residue algebraic
   closure of the finite residue field `k`.
3. The continuous surjective reduction homomorphism
   `G_F → Gal(k_sep/k)`. Its kernel must be identified with field-theoretic
   inertia and its kernel topology with the inherited Krull topology.
   This includes the unramified-extension/residue-extension correspondence
   needed for surjectivity.
4. A topological group isomorphism
   `Gal(k_sep/k) ≃ ProfiniteIntegers`, obtained from the finite-field
   Frobenius description on every finite extension. To match the convention
   above, geometric Frobenius must correspond to the image of `+1`;
   arithmetic Frobenius then corresponds to `-1`.
5. The generic injectivity and image statements for `projection`, the
   degree/kernel statements, and the topology characterization. These
   identify the pair construction with the integer-Frobenius preimage
   equipped with the source's topology. They must not substitute the
   subgroup topology of `G_F` for the Weil topology.
6. If local profiniteness or density in `G_F` is used, corresponding proofs:
   inertia is a closed profinite subgroup of `G_F`; its open copy gives
   local compactness and total disconnectedness of the Weil group; and the
   residue quotient map is open, allowing density to follow from density
   of the integer powers in the residue Galois group. A continuous
   surjection alone is not used as a general density argument.

No field, Galois group, residue homomorphism, local reciprocity map, Frobenius
lift, splitting, or semidirect-product identification is implemented here.
In particular, neither surjectivity nor a splitting is part of the generic
input. The checklist records necessary later mathematics, not completed results.

## Dependencies and validation

There are no project mathematical dependencies. The prepared environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`: Lean 4.34.0, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

The imports supply the profinite completion, continuous monoid homomorphisms,
and the standard integer topology. All structural proof fields in this file
are ordinary construction obligations. There are no axioms, placeholders,
or claimed universal-property proofs. Compilation checks elaboration;
independent source and semantic review is required for acceptance.
