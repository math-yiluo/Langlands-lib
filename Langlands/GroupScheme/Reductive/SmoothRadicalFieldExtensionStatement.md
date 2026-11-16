# Represented unipotent radicals over algebraically closed extensions

`Langlands.GroupScheme.SmoothAlgebraicallyClosedUnipotentRadicalExtensionStatement.{u}`
is a proposition target, with one arbitrary universe parameter `u`. This module
does not prove the proposition. Its provenance is **derived**: the paper argument
below extends the affine source theorem to the Library's broader predicates.
The geometric constructions in this audit are not implemented by this file.

## Exact statement and predicate comparison

For fields `k K : Type u`, with `Algebra k K` and both fields algebraically
closed, let `P U` be actual group schemes over `Spec k` and `r : U ⟶ P`.
If `P` is smooth and `IsUnipotentRadical r`, the target asserts
`IsUnipotentRadical` of the actual homomorphism obtained by applying
`GroupScheme.baseChange` along `Spec K ⟶ Spec k` to `r`.
The extension may be transcendental. Neither field is replaced by a chosen
closure, and no algebraicity or separability typeclass is assumed.

The imported `IsUnipotentRadical` requires a closed immersion, smooth connected
source, `IsUnipotent` of that source, normality of its image on every test scheme,
and greatestness among all closed normal subgroup images with those source
properties. `IsUnipotent` means that every nonzero finite-dimensional matrix
representation has a nonzero ground-field vector fixed on **all** test schemes.
It contains no affineness condition. Finite-dimensional representations can be
written on `k^n`, so this is the usual representation criterion when the group
is affine. Affineness must be established before using that affine equivalence.

Smoothness of `P` is the only additional geometric premise. No affine,
connected, quasi-compact, separated or finite-type premise is added to `P`
or `U`. For example, an abelian variety has only trivial linear representations
and satisfies the imported fixed-vector predicate. Thus that predicate alone
does not identify the source with a classical affine unipotent group.

## Paper audit of the broader scope

All constructions in this section are over an algebraically closed field `k`.

1. **Reduce the geometry to the identity component.** Smoothness implies local
   finite presentation. The identity component `P⁰` is a smooth open subgroup,
   is closed as a connected component, and is of finite type. SGA 3 VI_B,
   Theorem 3.10 and Corollary 3.6 give openness and quasi-compactness; local finite
   presentation then gives finite type over a field. The same argument makes
   every smooth connected competitor, including `U`, finite type. A connected
   subgroup containing the identity factors through the open subgroup `P⁰`.
   Proposition 3.3 gives compatibility of `P⁰` with field extension. These are
   consequences of the stated hypotheses, including when `P` has infinitely
   many components.

2. **Use the affinization of `P⁰`.** Set `Q = (P⁰)af` and write
   `q : P⁰ → Q`, with kernel `A`. SGA 3 VI_B, Theorem 12.2 gives a faithfully
   flat quotient, an affine algebraic group `Q`, and a smooth connected
   anti-affine kernel: `Γ(A, O_A) = k`. It also gives characteristicity of `A`.
   The proof identifies affinization after every flat base change, so `Q`, `q`
   and `A` commute with field extension. Smoothness of `P⁰` implies geometric
   reducedness of `Q` by faithfully flat descent, hence smoothness of the
   algebraic group `Q`; its connectedness follows from the surjection from
   `P⁰`. Every morphism from `A` to an affine scheme is determined by global
   functions. In particular, every group homomorphism `A → GL_n` is the trivial
   homomorphism, as its constant value is its value at the identity.

3. **Construct a qualified subgroup for the actual predicate.** Let
   `R = Ru(Q)` be the ordinary smooth connected affine unipotent radical, and
   `H = q⁻¹(R)`. This is a closed subgroup of `P⁰`, hence of `P`.
   The map `H → R` is the base change of `q`, with smooth geometrically connected
   kernel `A`. It is an `A`-torsor for the fppf topology, so `H` is smooth and
   connected. Every representation of `H` kills `A` and descends through the
   quotient `H/A = R`. The affine unipotence criterion for `R` supplies a
   nonzero fixed vector. Its pullback is fixed on every test scheme, so `H`
   satisfies precisely the imported `IsUnipotent`, without requiring `H`
   to be affine.

4. **Normality is on all tests, including for a disconnected ambient group.**
   Conjugation by each `p ∈ P(k)` preserves `P⁰`, induces an automorphism of its
   canonical affinization `Q`, and preserves the intrinsic subgroup `Ru(Q)`.
   It therefore preserves `H` as a closed subgroup scheme.
   Consider the conjugation morphism `P × H → P`. The inverse image of the
   closed subgroup `H` contains every `k`-point of `P × H`. This product is
   smooth, hence reduced and locally of finite type over the algebraically
   closed field. Its `k`-points are schematically dense: check this on affine
   opens of finite type, where it is the reduced Nullstellensatz criterion.
   The inverse-image closed subscheme is therefore the whole product.
   Conjugation factors through `H`, yielding normality on every test scheme.
   This argument is local on the source and needs no quasi-compactness of `P`.

5. **Greatestness includes all nonaffine competitors.** Let `j : C → P` be any
   competitor in the definition of `IsUnipotentRadical`. By step 1 it factors
   through `P⁰`. The homomorphism theorem for algebraic groups factors
   `q ∘ j` as a faithfully flat map `f : C → J` followed by a closed subgroup
   `J → Q` (Milne 2017, Theorem 5.39). The group `J` is connected. Geometric
   reducedness descends from smooth `C` along `f`, so `J` is also smooth.
   Its normality in `Q` follows by fpqc descent: pull conjugation on `Q × J`
   back along the faithfully flat map `q × f : P⁰ × C → Q × J`.
   There it factors through `J` by the supplied all-test normality of `C`.
   Factorization through a closed immersion descends, proving normality of `J`.
   For any representation of `J`, pull back to `C` and take the nonzero fixed
   vector supplied by `IsUnipotent C`. The fixed-vector equations descend along
   `f`, so the vector is fixed by `J` as a group scheme, on all tests.
   Now `J` is affine, so the classical representation criterion identifies it
   as an ordinary unipotent group. Hence `J ⊂ R` and `j` factors through `H`.
   This actual subgroup factorization gives the required image containment on
   every test scheme, rather than merely containment of rational points.

6. **Compare representatives and extend the field.** Steps 3–5 characterize
   `H → P` by the exact imported radical predicate. Greatestness for the
   supplied `r : U → P` and for `H → P` gives equality of their image functors.
   Both are closed subgroup monomorphisms, so Yoneda gives an isomorphism
   `U ≅ H` over `P`. This isomorphism, not only equality on field-valued points,
   transports under the actual base-change functor.
   For any algebraically closed extension `K/k`, steps 1–2 identify the new
   identity component, affinization and kernel with `P⁰_K`, `Q_K` and `A_K`.
   Conrad 2014, p.81 gives `Ru(Q)_K = Ru(Q_K)` for this **affine** group `Q`.
   Therefore `H_K` is the same construction over `K`.
   Repeating steps 3–5 over `K` supplies smoothness, connectedness, fixed-vector
   unipotence, all-test normality and greatestness against every new
   `K`-competitor. Closedness and the other predicate fields then transport
   through `U_K ≅ H_K` over `P_K`, with exactly the homomorphism appearing in
   the Lean target.

This is a mathematical scope justification for the proposition, not an
existing Library proof. In particular, it does not use the affine-only
`IsUnipotent.baseChange` on a possibly nonaffine source. A proof successor must
formalize the needed geometric route or another valid argument for the exact
target.

## Sources, provenance and limits

All PDF page numbers below are one-based. The retained originals are registered
in the project literature collection.

| Source identifier | Exact locations and role |
| --- | --- |
| `sga3-expose-vib-gille-polo-2024` | J.-E. Bertin, SGA 3 VI_B, Gille–Polo recomposed edition, 13 October 2024: Proposition 3.3, printed pp.347–348/PDF pp.17–18; Corollary 3.6, printed p.348/PDF p.18; Proposition 3.9 and Theorem 3.10, printed p.350/PDF p.20; Theorem 12.2 and its flat-base-change proof, printed p.430/PDF p.100; Lemma 12.3, printed p.431/PDF p.101. The edition incorporates the Tome I errata. These provide the identity component and anti-affine reduction, not a direct statement of this radical target. |
| `milne-2017-algebraic-groups` | J. S. Milne, *Algebraic Groups*, 2017: Proposition 1.10, printed pp.9–10/PDF pp.25–26, for schematic density; Chapter 4 introduction, printed p.83/PDF p.99, for the affine-quotient interpretation of representations; Theorem 5.39, printed p.108/PDF p.124, for images of arbitrary algebraic-group homomorphisms; §14.b, Proposition 14.3 and Theorem 14.5, printed pp.280–281/PDF pp.296–297, for the affine fixed-vector criterion; Corollaries 14.7–14.9, printed p.282/PDF p.298, for affine unipotent structure. Chapter 14 is used only after affineness is established. |
| `milne-2017-algebraic-groups-errata-2026-11-02` | Complete retained official author HTML snapshot, read together with the book. It lists no correction to the density, homomorphism or affine fixed-vector results used above. Its unrelated p.273 properness correction is not used here. |
| `conrad-2014-reductive-group-schemes` | B. Conrad, *Reductive group schemes*, 2014, p.81, immediately after Definition 3.1.1: radical compatibility for arbitrary algebraically closed extensions of a **linear algebraic** group. Applied only to `Q`; it does not directly establish the nonaffine target. The same page discusses preservation of connectedness for finite-type group schemes. |
| `conrad-gabber-prasad-2015-pseudo-reductive` | B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive Groups*, second edition, Proposition 1.1.9(1), printed pp.8–9/PDF pp.34–35. This also allows transcendental separable extensions, but explicitly assumes a smooth connected **affine** ambient group. It is a scope comparison, not the nonaffine justification. |

The preimage construction, the density argument for a possibly non-quasi-compact
ambient group, the descent of the fixed-vector equations, and the comparison
with the supplied representative are the derived content of this audit.
No theorem that a fixed-vector group must be affine is asserted.
