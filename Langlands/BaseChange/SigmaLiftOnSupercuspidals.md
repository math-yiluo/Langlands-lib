# σ-lift certification of a local base-change map on supercuspidal classes

Module `Langlands.BaseChange.SigmaLiftOnSupercuspidals`, namespace `Langlands.BaseChange`.
The module contains one mathematical definition, the proposition
`IsSigmaLiftOnSupercuspidals` (universe parameters `uK uV`, in this order). Apart from it the
module declares only the local topological instances described under "Conventions". It proves
no theorem and asserts no existence or uniqueness.

## What the definition says

Fix a prime `p` (with `[Fact p.Prime]`), two p-adic fields `L M : PadicField.{uK} p` (implicit
arguments) and an embedding `ι : L.Carrier →ₐ[Padic p] M.Carrier` over `ℚ_p`. Through
`ι.toRingHom.toAlgebra`, `M` is an `L`-algebra. Take an `L`-algebra automorphism
`σ : M.Carrier ≃ₐ[L.Carrier] M.Carrier` for this algebra structure. Take a map

```
Ch : ∀ k : ℕ, SupercuspidalAutomorphicClass.{uK, uV} L k.succPNat →
  Multiset (Σ k' : ℕ, SupercuspidalAutomorphicClass.{uK, uV} M k'.succPNat)
```

that sends each supercuspidal class of `GL_{k+1}(L)` to a finite multiset of supercuspidal
classes over `M` of various positive ranks `k' + 1`. This is the type of
`CyclicBaseChangeMap S` (module `Langlands.Correspondence.HenniartCyclicBaseChange`) for a step with `S.base = L` and `S.top = M`. The explicit arguments
are, in this order, `ι`, `Ch`, `σ`.

`IsSigmaLiftOnSupercuspidals ι Ch σ` holds when, for every `k : ℕ`, every supercuspidal class
`π : SupercuspidalAutomorphicClass L k.succPNat` and every actual supercuspidal representative
`A : GeneralLinear.SupercuspidalRep (F := L.Carrier) (n := k + 1)` of `π` (that is,
`A.isoClass = π`), there are:

- a smooth complex representation `τ` of `GL_{k+1}(M)`, with carrier universe `max uK uV`;
- a proof `hτ` that `τ` is admissible;
- a σ-intertwiner `I : SigmaIntertwiner σ (k + 1) τ.representation`, that is, a linear
  automorphism `I` of the space of `τ` with `I ∘ τ(g) = τ(g^σ) ∘ I` for all `g`, where `g^σ`
  applies `σ` to the matrix entries (Henniart–Lemaire's isomorphism `A` of `Π` onto `Π^σ`);
- a complex constant `c`;

such that both of the following hold.

1. `IsSigmaLift σ (orderOf σ) A.obj.representation A.property.2.1 τ.representation hτ I c`.
   This is the σ-lift relation of `Langlands.BaseChange.TwistedCharacter` (Henniart–Lemaire II.2.7, Définition, printed p. 67):
   `c ≠ 0`, and for all Haar measures `μF` on `GL_{k+1}(L)` and `μE` on `GL_{k+1}(M)` and
   all Schwartz–Bruhat functions `φ` on `GL_{k+1}(M)` and `f` on `GL_{k+1}(L)` that are
   concordant (`AreConcordant σ (orderOf σ) μF μE φ f`), the twisted trace
   `trace(τ(φ) ∘ I)` equals `c · trace A(f)`. The degree argument `l` of `IsSigmaLift` is the
   order of `σ`. The proof `A.property.2.1` is the admissibility of `A`, which is part of
   being supercuspidal (`A.property` is irreducibility together with `IsSupercuspidal`, whose
   first component is admissibility).
2. `M.canonicalTopologicalData.IsSupercuspidalSupport τ ((Ch k π).map
   (supercuspidalSupportDatum M))`. Each entry `⟨k', Π⟩` of `Ch k π` is read as the cuspidal
   datum of rank `k' + 1` and class `Π` by
   `Langlands.Correspondence.supercuspidalSupportDatum` (module `Langlands.Automorphic.IsobaricLocalSupport`). The Library's relation
   `IsSupercuspidalSupport` (after Zelevinsky 1980, Proposition 1.10) then says that some
   ordering `ρ_1, …, ρ_r` of this multiset has ranks adding up to `k + 1` and that, for some
   actual supercuspidal representatives of the `ρ_i`, `τ` is irreducible and is a subquotient
   of the normalized parabolically induced representation `ρ_1 × ⋯ × ρ_r`.

So the predicate says: every supercuspidal `π` has a σ-lift `τ`, and `Ch k π` is a
supercuspidal support of that σ-lift. It is a statement about `Ch` at the level of character
identities, not only about the shape of the multisets `Ch k π`.

## Conventions and remarks

- Topologies. The fields and the groups `GL_n` carry their canonical topologies from
  `PadicField.canonicalTopologicalData`. The module declares, with `local instance`, the
  field topology, the valuative relation, the nonarchimedean local field structure and the
  Hausdorff property of each `F.Carrier`, and the Hausdorff, locally compact and totally
  disconnected properties of `GL_n(F.Carrier)` (the last one from
  `LocalFieldTopology.generalLinear_totallyDisconnectedSpace`), all for `F : PadicField p`.
  Their names begin with `sigmaLiftSupercuspidal`. They are instances only inside this module;
  importing the module installs no instance. The topology is the one that
  `IsSupercuspidalSupport` and `SupercuspidalAutomorphicClass` use, namely
  `canonicalTopologicalData.topology`.
- The algebra structure. The `L`-algebra structure on `M` is `ι.toRingHom.toAlgebra`, both in
  the type of `σ` (installed with `letI` in the binder) and in the body of the definition. A
  user whose `M` carries another `L`-algebra instance can pass `σ` only if that instance is
  definitionally `ι.toRingHom.toAlgebra`.
- Irreducibility of `τ` is not a separate clause. It is part of `IsSupercuspidalSupport`, as
  Henniart–Lemaire require `Π` irreducible. The σ-stability of `τ` that they also require
  follows from the existence of the intertwiner `I`. Admissibility of `τ` is the explicit
  witness `hτ`, which `IsSigmaLift` needs to define the twisted trace.
- The constant `c` and the intertwiner `I` are existential, as in Henniart–Lemaire II.2.7.
  Arthur–Clozel's Definition 6.1 (Chapter 1, printed p. 51) is stated through character values
  at elements whose norm is regular, with the canonical intertwining operator `I_σ` and the
  constant `1`. Changing `I` by a nonzero scalar changes `c` by the same scalar, so the
  existential form does not fix a normalization.
- The clause is required for every representative `A` of `π`, not for one chosen
  representative. Character distributions do not depend on the representative, so the two
  readings agree mathematically. This module does not prove that.
- For a supercuspidal `π` the σ-lift `τ` may be a supercuspidal representation, with `Ch k π`
  a single class of the same rank, or an irreducible representation induced from several
  `σ`-conjugate supercuspidals of smaller rank. The predicate allows both shapes. It does not
  say which occurs.
- The definition makes sense for any `σ`. The source meaning requires `M/L` to be cyclic and
  `σ` to generate `Gal(M/L)`, so that `orderOf σ` is the degree `[M : L]`: Henniart–Lemaire
  (II.2.1, printed p. 61) fix a generator `σ` of a cyclic group `Σ` of order `d`, and
  Arthur–Clozel (Chapter 1, §6.1, printed p. 51) take `E/F` of degree `ℓ` with `Gal(E/F)`
  generated by `σ`. In the intended use `M/L` is cyclic of prime degree `ℓ` and `σ ≠ 1`, so
  `σ` generates and `orderOf σ = ℓ`. This is not checked or proved here.
- Nothing here says that such a map `Ch` exists, that it is unique, that the σ-lift `τ` of `π`
  is unique, or that the predicate is independent of `σ`.

## Provenance and intended use

The definition is internal vocabulary of the program for the simple trace formula with its
twisted form and local cyclic base change of prime degree. It introduces no new mathematical
notion: it composes published definitions, namely `IsSigmaLift` and `SigmaIntertwiner`
(Henniart–Lemaire II.2.7), the Library's `IsSupercuspidalSupport` (Zelevinsky 1980, 1.10) and
`supercuspidalSupportDatum`, to express what it means for a map on supercuspidal classes to be
the local base change of Arthur–Clozel, Chapter 1, §6, on supercuspidal classes.

- The E2 interface is to state, for each cyclic prime step `S` (`CyclicPrimeStep`) and its
  canonical map `Ch_can S`, that `IsSigmaLiftOnSupercuspidals S.embedding (Ch_can S) σ` holds
  for every `σ ≠ 1` in `Gal(S.top/S.base)`. All such `σ` can be allowed because, by
  Arthur–Clozel, Chapter 1, Theorem 6.2(c) (printed p. 51, proof on printed p. 57), local
  lifting of tempered representations does not depend on the choice of the generator `σ`.
- The general strong-support premise `CyclicStrongBaseChangeSupportStatement` takes
  `∀ σ ≠ 1, IsSigmaLiftOnSupercuspidals S.embedding Ch σ` as its hypothesis on an arbitrary
  map `Ch`. A hypothesis at the level of character identities is needed there: the weak laws of
  `IsWeakCyclicBaseChange` (sizes, Galois invariance, fibres under twists by norm
  characters) do not determine `Ch`, and a support conclusion for every map satisfying only
  those laws could be false.

The predicate is stated for an arbitrary embedding `ι` rather than for
`CyclicPrimeStep`, so that it does not depend on that structure and can also serve other
pairs of p-adic fields. Dot notation `Ch.IsSigmaLiftOnSupercuspidals σ` is therefore not
available; users write `IsSigmaLiftOnSupercuspidals S.embedding Ch σ`, which needs the step's
`L`-algebra instance on `M` to be definitionally `S.embedding.toRingHom.toAlgebra`.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle* (Mém. SMF 124, 2011), Chapter II, §II.2.7, Définition, printed
  p. 67 (PDF p. 75): the σ-lift ("σ-relèvement") through concordant functions, reused here
  through `IsSigmaLift`; §II.2.1, printed p. 61 (PDF p. 69): the generator `σ` of
  the cyclic group `Σ` of order `d`.
- Zelevinsky, *Induced representations of reductive p-adic groups II. On irreducible
  representations of GL(n)* (Ann. Sci. ENS 1980), §1.10, Proposition, printed p. 174 (PDF
  p. 11): the support `supp ω` of an irreducible `ω`, a multiset of cuspidal classes with
  `ω ∈ JH(ρ_1 × ⋯ × ρ_r)`, reused here through the Library's `IsSupercuspidalSupport`.
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
  (1989), Chapter 1, §6.1, Definition 6.1 and Theorem 6.2, printed p. 51 (PDF p. 65), and the
  proof of Theorem 6.2(c), printed p. 57 (PDF p. 71): local base change lifts and their
  independence of the generator `σ`.
