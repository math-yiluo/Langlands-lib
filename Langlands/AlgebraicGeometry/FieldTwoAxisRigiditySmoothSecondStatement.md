# Two-axis rigidity over fields with a smooth, possibly non-proper second factor

Worker 998 wrote this statement module and checked the original sources.
Worker 1034 specified the task and compiled the Lean text adopted here.
Worker 337 recommended the interface: the Library's
`FieldTwoAxisRigidityStatement`, implemented by Worker 149, with exactly the
hypothesis `IsProper Z.hom` deleted.

`Langlands.AlgebraicGeometry.FieldTwoAxisRigiditySmoothSecondStatement.{u}`
is a `Prop`-valued definition. This module states a derived rigidity result
and supplies no proof. It imports only Mathlib.

## Exact interface

For every field `K : Type u`, set `S = Spec (CommRingCat.of K)` and take
`Y Z P : Over S`. The hypotheses, explicit and in this order, are

```text
Smooth Y.hom, IsProper Y.hom, GeometricallyConnected Y.hom,
Smooth Z.hom, GeometricallyConnected Z.hom,
IsSeparated P.hom, LocallyOfFiniteType P.hom.
```

All are Mathlib's actual scheme-morphism properties. Thus `Y` is smooth,
proper and geometrically connected over `K`, while `Z` is only smooth and
geometrically connected.

The pointed data are actual morphisms

```text
y₀ : Over.mk (𝟙 S) ⟶ Y
z₀ : Over.mk (𝟙 S) ⟶ Z
p₀ : Over.mk (𝟙 S) ⟶ P.
```

The commutativity condition of a morphism in `Over S` says that their
underlying scheme morphisms are sections of the structure morphisms, so
they are `K`-rational points. For `T : Over S`, write
`!T = Over.mkIdTerminal.from T`. Its target is `Over.mk (𝟙 S)` and its
underlying morphism is the structure map of `T`; so `!T ≫ p₀` is the
constant `S`-morphism with value `p₀`.

The product `Y ⨯ Z` is the categorical product in `Over S`, hence a scheme
fibre product over `S`. For `g : Y ⨯ Z ⟶ P` the two hypotheses are

```text
prod.lift (!Z ≫ y₀) (𝟙 Z) ≫ g = !Z ≫ p₀
prod.lift (𝟙 Y) (!Y ≫ z₀) ≫ g = !Y ≫ p₀.
```

The first lift has coordinates `(y₀,z)` and the second `(y,z₀)`. The
conclusion is `g = !(Y ⨯ Z) ≫ p₀`, an equality in `Over S`, hence of the
full morphisms of schemes including their structure-sheaf maps. The field,
schemes, properties, sections, map and equations are all quantified inside
the proposition; its only external parameter is the universe `u`.

## What is not assumed

Nothing is assumed of `Z` beyond smoothness and geometric connectedness:
no properness, quasi-compactness, separatedness, finite type, integrality or
noetherian hypothesis. Smoothness makes `Z` locally of finite presentation
over `K`, hence locally noetherian, but this is a consequence, not a
hypothesis. For example, the affine line with doubled origin over `K` is
smooth and geometrically connected but not separated, and gluing infinitely
many copies of the affine line along the complement of the origin gives such
a scheme that is moreover not quasi-compact.

There is no properness or quasi-compactness hypothesis on `P`, no group
structure and no assumption that the factors coincide. There is no
projectivity, perfectness, algebraic closedness or characteristic
restriction. Neither a global-functions comparison, a rigidity theorem nor a
descent theorem is supplied as a hypothesis; those are proof obligations.

## Relation to the published proper statement and the cube assembly

Apart from the declaration name and documentation, the Lean text is that of
`Langlands.AlgebraicGeometry.FieldTwoAxisRigidityStatement` (module
`Langlands.AlgebraicGeometry.FieldTwoAxisRigidityStatement`) with the
hypothesis `IsProper Z.hom` deleted; all other binders keep their order.
Hence this proposition implies `FieldTwoAxisRigidityStatement.{u}`: given
the proper data, discard the hypothesis `IsProper Z.hom` and apply this
proposition to the remaining arguments in the same order. That implication
is not stated or proved in this module.

The two axes are literally the bodies of `Picard.CubeFace.secondAxis Y Z y₀`
and `Picard.CubeFace.thirdAxis Y Z z₀`, defined in
`Langlands.AlgebraicGeometry.Picard.CubeRelativeTransport` as
`prod.lift (Over.mkIdTerminal.from Z ≫ y₀) (𝟙 Z)` and
`prod.lift (𝟙 Y) (Over.mkIdTerminal.from Y ≫ z₀)`. These axes appear in the
rigidity argument of
`Langlands.AlgebraicGeometry.Picard.cubeTrivializationOfUniversalFamily` in
`Langlands.AlgebraicGeometry.Picard.CubeTrivialityAssembly`. This module
does not import those files.

## Original rigidity sources

The exact statement here is a derived specialization rather than a verbatim
theorem of any of these sources. Each was read at the locations given.

* Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
  2008 thesis, revision of March 14, 2021, Proposition 1.3.1.4 (rigidity
  lemma), printed pp.69–70 (PDF pp.97–98). Given a commutative diagram of
  locally noetherian schemes `f : X → T` over a connected base `B`, with
  `p : X → B` open and closed and with a section `e`, `q : T → B`
  separated, and the canonical map `O_B → p_* O_X` an isomorphism: if
  `f(X_b)` is set-theoretically one point for some `b ∈ B`, then
  `f = η ∘ p` with `η = f ∘ e`. Lan notes that no group structure is needed.
  The revision's conventions, printed p.xxvi (PDF p.26), take schemes to be
  quasi-separated preschemes.
* Lan's errata of March 14, 2021. Page 1 replaces the convention that schemes
  are separated by quasi-separated. Page 8 puts the separatedness assumption
  only on `q`, and says that "p is an open map as it is flat" is not correct
  in general, so openness of `p` must be assumed. The revision above already
  incorporates these corrections.
* Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third edition
  (1994), Chapter 6, Proposition 6.1 (rigidity lemma), printed pp.115–116
  (PDF pp.128–129). For connected `S`, flat `p : X → S` with
  `H⁰(X_s, O) ≅ κ(s)` for all `s`, and either a section with `p` closed or
  `p` proper, a map contracting one fibre factors through `p`. At the start of
  Chapter 6 (printed p.115) all preschemes are assumed locally noetherian and
  to be schemes. The book uses EGA's original terminology, in which a scheme
  is a separated prescheme: the proof of Lemma 0.6, printed pp.13–14
  (PDF pp.26–27), identifies being a scheme with closedness of the diagonal.
  So this source applies verbatim only when `Z` is separated.
* Edixhoven, van der Geer and Moonen, *Abelian Varieties*, retained
  preliminary draft built February 8, 2012: convention (0.4), printed p.1
  (PDF p.5), and the Rigidity Lemma (1.12), printed pp.12–13
  (PDF pp.16–17). For varieties `X`, `Y`, `Z` (separated, of finite type and
  geometrically integral) with `X` complete, a morphism `X × Y → Z` mapping
  one fibre `X × {y}`, `y ∈ Y(k)`, to a point `z ∈ Z(k)` factors through the
  projection to `Y`. Only the first factor is complete; the second is
  arbitrary. It applies here only when `Z` is separated and of finite type
  and `P` is a variety.

No project errata note for these sources was present in the Library used
here. Lan's own errata was read directly.

## Why the target specializes the rigidity lemma

This is an explanation in ordinary mathematics, not a Lean proof supplied by
this module. Work directly over `K`; no field extension is needed.

1. Global functions of `Y`. Since `Y` is proper over `K`, `A = Γ(Y, O_Y)`
   is a finite-dimensional `K`-algebra. Smoothness makes `Y` geometrically
   reduced. Over an algebraic closure `K̄`, flat base change gives
   `Γ(Y_K̄, O) = A ⊗_K K̄`, a finite reduced `K̄`-algebra, hence a product
   of copies of `K̄`. Its idempotents split `Y_K̄` into that many nonempty
   open and closed parts; since `Y_K̄` is connected there is one, so `A = K`.
   The Library proves this as
   `Langlands.AlgebraicGeometry.fieldSmoothProperConnectedGlobalFunctions`.
2. The data of Lan's proposition. Take base `B = Z`, source
   `X = Y ×_K Z` with `p = pr_Z`, target `T = Z ×_K P` with `q = pr_Z`, and
   `f = (pr_Z, g) : X → T`, a morphism over `Z`. The section is
   `e = (y₀ ∘ π_Z, id_Z) : Z → Y ×_K Z`, where `π_Z : Z → Spec K` is the
   structure map.
3. The hypotheses. `Z`, `X` and `T` are locally of finite type over `K`,
   hence locally noetherian; locally noetherian schemes are quasi-separated,
   meeting Lan's convention. `Z` is connected because it is geometrically
   connected. The map `p` is a base change of `Y → Spec K`, so it is proper,
   hence closed, and smooth, hence flat and locally of finite presentation,
   hence open. Thus openness comes from local finite presentation as well as
   flatness, as the errata requires. The map `q` is separated, being a base
   change of `P → Spec K`.
4. The sheaf condition. For an affine open `V = Spec R` of `Z`, flat base
   change for the quasi-compact separated `Y → Spec K` along the flat map
   `K → R` gives `Γ(Y ×_K V, O) = A ⊗_K R = R`. Hence `O_Z → p_* O_X` is an
   isomorphism. The question is local on `Z`, so no quasi-compactness or
   separatedness of `Z` is needed.
5. The contracted fibre. The point `z₀` is `K`-rational, so the fibre
   `X_{z₀}` is `Y`, and the second axis equation `g(y, z₀) = p₀` says that
   `f` maps it to the single point `(z₀, p₀)`.
6. Conclusion. Lan's proposition gives `f = η ∘ p` with `η = f ∘ e`, that is
   `η(z) = (z, g(y₀, z))`. The first axis equation `g(y₀, z) = p₀` gives
   `η = (id_Z, p₀)`. Comparing second components, `g` equals `p₀` composed
   with the structure map of `Y ×_K Z`. This is the stated equality in
   `Over S`, since morphisms in a slice category are determined by their
   underlying morphisms.

No algebraic closure, properness of `Z` or of `P`, or quasi-compactness or
separatedness of `Z` enters. When `Z` is separated, Mumford's Proposition 6.1
in case 2 applies to the same data: the fibre condition
`H⁰(X_s, O) = A ⊗_K κ(s) = κ(s)` follows from step 1 by flat base change.
When `Z` is separated and of finite type and `P` is a variety, the
Edixhoven–van der Geer–Moonen lemma applies with complete factor `Y`, since
smooth geometrically connected schemes are geometrically integral.

By contrast, the published proof
`Langlands.AlgebraicGeometry.fieldTwoAxisRigidity` of the proper statement
applies `Langlands.AbelianScheme.algebraicallyClosedTwoAxisRigidity` to
`A = Y ×_K Z` after base change to an algebraic closure. That theorem assumes
`IsProper A.hom`, so this route uses the properness of `Z`.

## Separate proof boundary

All the geometry above remains the obligation of a separate exact-target
proof task; this module neither assumes nor proves it. A formal proof may
follow another route. Library results that may help include
`Langlands.AlgebraicGeometry.fieldSmoothProperConnectedGlobalFunctions` and
`Langlands.AlgebraicGeometry.factorizationOfGlobalFunctions`.

## Retained source identifiers

* `lan-2008-pel-thesis-revision-2021`, SHA256
  `a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`,
  PDF pp.26 and 97–98.
* `lan-2008-pel-thesis-errata-2021`, SHA256
  `18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
  pp.1 and 8.
* `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
  SHA256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`,
  GIT Chapter 0, PDF pp.26–27, and Chapter 6, PDF pp.128–129.
* `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
  PDF pp.5 and 16–17.
