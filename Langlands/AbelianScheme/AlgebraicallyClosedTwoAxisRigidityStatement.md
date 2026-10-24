# Two-axis rigidity over an algebraically closed field

Authors: Worker 334 specified the interface and suggested the Mathlib proof
route. Worker 360 checked the original literature and implemented this pair.

`Langlands.AbelianScheme.AlgebraicallyClosedTwoAxisRigidity` is a proposition
definition, not a proved theorem. It states that a morphism from a proper
integral square over an algebraically closed field, constant with the same
value on its two pointed axes, is constant everywhere.

## Exact interface

For an arbitrary universe `u`, take a field `K : Type u` with `[IsAlgClosed K]`.
Write `S = Spec (CommRingCat.of K)`. The objects `A H : Over S` are actual
schemes over `S`. The assumptions, in order, are:

1. `IsProper A.hom`.
2. `IsIntegral (A ⊗ A).left`.
3. `IsSeparated H.hom`.
4. `LocallyOfFiniteType H.hom`.

Here `⊗` is the cartesian monoidal product in `Over S`, namely the scheme
fibre product over `S`. Thus integrality is imposed on the entire square,
not merely on a set of rational points. The monoidal unit `𝟙_ (Over S)` is
the terminal object, whose structure map is the identity of `S`.

The quantified maps are sections `a : 𝟙_ (Over S) ⟶ A` and
`b : 𝟙_ (Over S) ⟶ H`, and an arbitrary morphism `g : A ⊗ A ⟶ H`.
The first axis map `a ▷ A` has source `𝟙_ (Over S) ⊗ A`, and the second
axis map `A ◁ a` has source `A ⊗ 𝟙_ (Over S)`. For each of those sources
`T`, its constant map with value `b` is `toUnit T ≫ b`. The two hypotheses
equate the corresponding axis restriction of `g` with that constant map.
The conclusion is the equality of morphisms in `Over S`
`g = toUnit (A ⊗ A) ≫ b`.

No group or commutative-group structure, smoothness, properness of `H`,
quasi-compactness of `H`, or multiplicativity of `g` is a hypothesis.
The four scheme properties are explicit implication hypotheses; the field
and algebraic-closedness hypotheses are instance binders within the
proposition. The declaration has type `Prop` and universe parameter `u`,
with all these data quantified inside its body.

## Original sources and derived provenance

This square-and-axes formulation is a derived specialization of the
geometric rigidity lemma. It is not a verbatim statement from the following
sources, and does not use their group-scheme corollaries as premises.

- Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
  Harvard PhD dissertation (2008), revision dated March 14, 2021,
  Proposition 1.3.1.4, printed pp.69–70 (PDF pp.97–98). It concerns a
  diagram `X → Y → S` with connected `S`, an open and closed map `p : X → S`
  admitting a section, separated `q : Y → S`, and
  `O_S ≅ p_* O_X`. Constancy on one fibre forces factorization through `p`.
  Its schemes are locally noetherian. The following Corollaries 1.3.1.5–6,
  printed pp.70–71 (PDF pp.98–99), apply that lemma to group schemes; they
  explain the intended later use but are not needed for the present result.
- Lan's errata dated March 14, 2021, p.8, explicitly require openness of
  `p` in Proposition 1.3.1.4 and impose separatedness only on `q`.
  The cited revision incorporates these changes.
- Mumford, Fogarty, and Kirwan, *Geometric Invariant Theory*, third edition
  (1994), Chapter 6, Proposition 6.1, printed pp.115–116
  (PDF pp.128–129). This version assumes a connected base, flat `p`,
  and `H⁰(X_s, O_{X_s}) = κ(s)` for every base point. Its third case assumes
  properness of `p`. The chapter's standing convention on printed p.115
  restricts to locally noetherian separated schemes. Corollaries 6.2–6.4,
  printed pp.116–117 (PDF pp.129–130), give subsequent group-scheme
  applications, rather than the exact statement of this module.

Here is the mathematical specialization, including the hypotheses that
are implicit in neither the Lean interface nor the cited lemma.

The section `a` makes `A` nonempty. The projection `A ×_K A → A` is
surjective and faithfully flat: it is a base change of the nonempty
scheme `A` over the field `K`, and also has section `(id_A,a)`.
Integrality of the square implies irreducibility of `A` by surjectivity
and reducedness of `A` by faithfully flat descent. Hence `A` is integral.
Since `A` is of finite type over the algebraically closed field `K`,
it is geometrically integral.

Properness and integrality imply that `H⁰(A,O_A)` is a finite-dimensional
integral `K`-algebra, hence a finite field extension of `K`, hence `K`.
Global sections commute with field extension for this quasi-compact
separated scheme. Consequently, for every extension field `L/K`,
`H⁰(A_L,O_{A_L}) = L`.

Apply GIT Proposition 6.1 with base `A`, source `X = A ×_K A`,
target `Y = A ×_K H`, first projections `p` and `q`, and
`γ = (pr₁,g) : X → Y`. The base `A` is connected. The map `p` is
proper and flat, and its fibre at any `x ∈ A` is `A_{κ(x)}`, whose
global sections are `κ(x)` by the preceding paragraph. All three schemes
are locally noetherian: `A` and `X` are of finite type over `K`, and
`H` and `Y` are locally of finite type over `K`. They are separated over
`K`, and are separated schemes, since `K` is separated over the prime
base. In particular, `q` is separated. This checks the chapter's
standing assumptions as well as the proposition's hypotheses.

The first axis equation says that the image under `γ` of the fibre
`p⁻¹(a)` is the single point `(a,b)`. The lemma gives
`γ = (γ ∘ e) ∘ p`, where `e = (id_A,a)` is a section of `p`.
The second axis equation identifies `γ ∘ e` with `(id_A,b)`.
Taking the second component gives the required constant morphism.
Equivalently, corrected Lan Proposition 1.3.1.4 applies: `p` is closed
by properness and open by flatness and local finite presentation, while
flat base change of `H⁰(A,O_A) = K` gives `O_A ≅ p_*O_X`.
This is the provenance argument for the statement; it is not a Lean
proof supplied by this module.

## Formal proof boundary

Only the proposition is implemented here. The substantial proof is a
separate exact-target obligation in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
It must not depend on a proof of arbitrary-base or field
pointed-morphism rigidity, since this statement is intended as a
prerequisite for that work.

An alternative implementation route is suggested by the proof of
`AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`
in Mathlib `AlgebraicGeometry/Group/Abelian.lean`, pinned at
`5ed2965256430c3649e86755f9576b54eca72435`. Replace its commutator by `g`
and use `γ = lift (fst A A) g`. Its finite-image and dense-closed-point
argument can use the two axis equations in place of the commutator
identities. This is implementation guidance, not an original source or
an assertion that the proof has already been adapted. The statement
imports only Mathlib's scheme-property and algebraically closed field
infrastructure.

## Retained sources read

- `lan-2008-pel-thesis-revision-2021`, SHA256
  `a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`,
  PDF pp.97–99.
- `lan-2008-pel-thesis-errata-2021`, SHA256
  `18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
  p.8.
- `provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
  SHA256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`,
  GIT Chapter 6, PDF pp.128–130.
