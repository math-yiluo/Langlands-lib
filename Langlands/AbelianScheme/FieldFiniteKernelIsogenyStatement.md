# Finite-kernel endomorphisms of abelian group schemes over fields

`Langlands.GroupScheme.FieldFiniteKernelIsogenyStatement` is a `Prop`-valued
definition, with no proof supplied. It quantifies over every field `K : Type u`,
every actual group object `G : Grp (Over (Spec (CommRingCat.of K)))` with
`IsCommMonObj G.X`, and every homomorphism of group objects `f : G ⟶ G`.
Assume that the structure map `G.X.hom` is smooth, proper, and geometrically
connected, and that `IsFinite (kernel f).X.hom` holds. The target then asserts
`IsIsogeny f`.

The two imported Library definitions retain their existing meanings.

- `kernel f` is the published group-scheme kernel from
  `Langlands.AbelianScheme.Kernel`: the pullback in `Grp (Over S)` of `f` along
  the unit section of the target. By `kernel_isPullback_scheme`, its underlying
  scheme is the fibre product of the actual scheme morphism `f.hom.hom.left`
  with the unit section `η[G.X].left`. The morphism `(kernel f).X.hom` is the
  kernel's structure morphism to `Spec K`, not its inclusion into `G`. So the
  hypothesis says that the kernel is a finite `K`-scheme.
- `IsIsogeny f` from `Langlands.AbelianScheme.Isogeny` asserts that the actual
  underlying scheme morphism `f.hom.hom.left` is finite, flat, and surjective,
  using Mathlib's `IsFinite`, `Flat`, and `Surjective`.

Neither the finite kernel nor the isogeny conclusion is supplied as a structure
field or certificate; both are the predicates above, applied to the given `f`.

## Original source and correspondence

The source is J. S. Milne, *Abelian Varieties*, the 1986 *Arithmetic Geometry*
article in the author's corrected version dated January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
Printed and one-based PDF page numbers agree in this copy. Pages 2–3, 12–13 and
42 were read directly. No errata note for this source exists in the project notes.

- Proposition 8.1, p.12, states for a homomorphism `f : A → B` of abelian
  varieties the equivalence of (a) `f` is an isogeny, (b) `dim A = dim B` and `f`
  is surjective, (c) `dim A = dim B` and `Ker(f)` is a finite group scheme, and
  (d) `f` is finite, flat, and surjective. This target is the implication
  (c) ⇒ (d) in the case `A = B`. For an endomorphism, the equal-dimension part
  of (c) holds trivially, so the only remaining hypothesis of (c) is finiteness
  of the kernel. Condition (d) is exactly the imported `IsIsogeny`.
- The paragraph before Proposition 8.1 says that the kernel of `f`, in the
  sense of Shatz 1986, §2, is a closed subgroup scheme of finite type over `k`.
  Shatz's article was not consulted here. The proof of Proposition 8.1 works with
  the scheme-theoretic fibre `f⁻¹(0)` over the identity. The Library kernel has
  as underlying scheme exactly this fibre product with the unit section. A finite
  group scheme over `k` is a group scheme finite over `k`, which is
  `IsFinite (kernel f).X.hom`.
- The proposition is stated over the article's fixed, arbitrary ground field.
  The proof reduces to an algebraically closed field only as a proof step. The
  target therefore retains every field and every characteristic.
- A homomorphism of abelian varieties is a morphism over `k` respecting the
  group laws (Corollary 2.2, p.3, and the conventions on p.2). A morphism
  `f : G ⟶ G` in `Grp (Over (Spec K))` is exactly a morphism of `K`-schemes
  compatible with unit and multiplication.

### Abelian varieties as group schemes

The conventions on p.2 define varieties to be separated finite-type schemes that
are geometrically integral. Section 1, pp.2–3, describes their group objects,
notes that group varieties are nonsingular, and defines abelian varieties by
completeness and connectedness. Here completeness is properness over the field.
Section 20, opening definition on p.42, defines abelian schemes by smoothness,
properness, and connected geometric fibres, and states that in the presence of
smoothness and properness this is equivalent to the fibres being abelian
varieties. Over `Spec K` this gives the group schemes in the target.

More explicitly, properness gives separatedness and finite type. After extension
to an algebraic closure, smoothness gives regularity and reducedness. A connected
regular noetherian scheme is irreducible, because its irreducible components are
disjoint and open. Thus a geometrically connected smooth scheme is geometrically
integral, as required by the source's convention, and the identity section
guarantees nonemptiness. Conversely, the source's abelian varieties are smooth,
proper, and geometrically connected group schemes. Mathlib's
`GeometricallyConnected` tests connectedness after all field-valued base changes,
an equivalent formulation of connected geometric fibres. This correspondence is
the same as in the published `FieldMultiplicationIsogenyStatement`. This file
does not prove it.

Commutativity is an explicit hypothesis, to match the published field
multiplication target and its consumers. It restricts nothing, since abelian
varieties are commutative by Corollary 2.4, p.3. The target does not prove
commutativity. `kernel` and `IsIsogeny` themselves do not require it.

The provenance is derived: this is the endomorphism case of Proposition 8.1,
(c) ⇒ (d), expressed through the group-scheme presentation on p.42 and the
Library's kernel and isogeny predicates.

## Scope and proof boundary

There is no algebraic-closure, perfectness, characteristic, dimension,
projectivity, surjectivity, flatness, or ample-bundle hypothesis. The target
asserts no degree formula and no étaleness. It concerns only endomorphisms over
fields. Homomorphisms between different abelian varieties, which would need a
dimension hypothesis, and arbitrary bases are outside its scope. The arbitrary-base
fibrewise reduction is the separate published `FiberwiseIsogenyStatement`.

Milne's proof uses the dimension theorem for fibres of morphisms to obtain
surjectivity, translations to identify all fibres with the kernel, properness
and projectivity with quasi-finiteness to obtain finiteness, and the constant
fibre ranks of the coherent sheaf `f_* O_A` to obtain local freeness, hence
flatness. None of these steps is
proved or assumed here. A separate proof task must prove this exact Library
proposition after publication and split missing geometric prerequisites into
focused tasks.
