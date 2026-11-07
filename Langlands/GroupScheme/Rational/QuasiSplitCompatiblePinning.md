# Galois-compatible pinnings of quasi-split groups

This module is an internal prerequisite for the quasi-split Steinberg quotient
task. It packages, in one structure, the inputs that the published orbit-image
descent theorem
`SteinbergOrbitImageDescent.definingIdealDescent_of_orthogonalSimpleOrbits`
needs from a quasi-split group:

- an actual split pinning over an extension field;
- a torus over the ground field whose base change is the pinning torus;
- an ordinary Galois action on the simple roots that transports the roots;
- pinning vectors and normalized whole root maps that are compatible with this
  action.

The module then constructs such data. It does so unconditionally from a
ground-field cocharacter that is regular after base change, and from an actual
torus centralizer together with the root-datum existence statement. For a
quasi-split group it obtains the data over a finite Galois extension,
conditional on two named statements of the Library, `ParabolicDynamicStatement`
and `RootDatumExistenceStatement`. Orthogonality of the simple-root orbits is
not proved here; it remains a premise of the descent consequence.

Throughout, `k` and `K` are arbitrary fields in one universe `u` with an
algebra `k → K` and base map `b = algebraBaseMap k K`, and `G/k` is a group
scheme with affine structure morphism. Write `G_K`, `T_K` and `i_K` for the
canonical base changes of the group, a torus `T/k` and an inclusion
`i : T → G`. No perfectness, characteristic or infinitude assumption is made
on `k`.

## A regular cocharacter pairs nonzero with the roots

`IsRootDatumOf.root'_ne_zero_of_isRegularCocharacter` assumes that `P` is a
root datum of an inclusion `i : T → G` (`IsRootDatumOf i P`), and that `ν` is a
cocharacter with `IsRegularCocharacter i ν`. It concludes `P.root' a ν ≠ 0` for
every root index `a`. The proof uses the two parts of `IsRootDatumOf`: the
roots of `P` are the actual roots of `i`, and the pairing of `P` is the lattice
pairing. Regularity is exactly nonzero pairing with every actual root.

## The structure

`GaloisCompatiblePinningData k K G` has the following fields.

- `pinning : SplitPinning G_K`: an actual split pinning of the connected
  reductive group `G_K`. It consists of a split maximal torus, a reduced root
  datum realized by that torus, a base, and trivializations of the simple-root
  weight spaces, which give the nonzero simple root vectors.
- `torus` and `inclusion : torus.toGrp ⟶ G`: a commutative group scheme over
  `k` with a homomorphism into `G`.
- `torusIso : pinning.torus ≅ T_K` and `inclusion_eq`: the pinning torus is
  the base change of `torus`, and the pinning inclusion is the composite of
  this isomorphism with `i_K`.
- `action : (K ≃ₐ[k] K) →* Equiv.Perm pinning.base.support`: a group action of
  the `k`-automorphisms of `K` on the simple roots.
- `action_root`: transported to characters of `T_K`, the root of `action σ a`
  is the image of the root of `a` under the ordinary coefficient-transport
  representation `characterLattice.galoisRepresentation k K torus σ`.
- `rootVectors_compatible`: canonical semilinear Lie transport
  `Lie.baseChangeGaloisEquiv k K G σ` sends the pinning vector of `a` to that
  of `action σ a` (`SplitPinning.RootVectorsGaloisCompatible`).
- `rootMaps` and `rootMaps_compatible`: normalized simple-root
  parametrizations with derivative the pinning vectors, compatible with the
  action as entire root maps (`SplitPinning.RootMapsGaloisCompatible`). The
  additive variable is fixed and the coefficients are conjugated.

The field `action_root` is stated in the same form as the premise `hroot` of
the published descent theorem. No coroot transport is required.

## Descent consequence

`GaloisCompatiblePinningData.definingIdealDescent` assumes `K/k` Galois and the
premise `horth : D.pinning.OrthogonalSimpleOrbits D.action`: distinct simple
roots in one action orbit are orthogonal. It returns a `DefiningIdealDescent`
along `pullback.fst G.X.hom b` for the kernel ideal of the canonical Steinberg
product. That product is formed in the orbit ordering
`D.pinning.simpleOrbitOrdering D.action`, using `D.rootMaps` and the canonical
simple reflection representatives. A `DefiningIdealDescent` is an ideal sheaf on
`G` whose pullback to `G_K` is this ideal. The construction applies the
published theorem to the fields of `D`. It does not prove the orthogonality
premise.

## Construction from a regular ground-field cocharacter

The section `OfRegular` fixes a torus `T/k`, an inclusion `i : T → G` and a
finite type `J`. It also fixes a reduced root datum `P` of `i_K` with index
type `J`, with `hP : IsRootDatumOf i_K P`, and a ground-field cocharacter
`ν₀ : X_*(T)`. Its base change
`ν = cocharacterLattice.baseChange b T ν₀` is assumed to pair nonzero with
every root (`hν`). The section further assumes `G_K` connected reductive
(`hG`), `T_K` split (`hT`) and `i_K` a maximal torus (`hi`).

The published `IsRootDatumOf.regularCocharacterPinning` gives an initial split
pinning of `G_K`. Its torus is `T_K`, its inclusion is `i_K`, its root datum
is `P`, and its base is chosen so that the positive roots are those pairing
positively with `ν`. The published
`IsRootDatumOf.descendedRegularCocharacterSimpleAction` is the ordinary
Galois action on its simple roots. That action is well defined without a Weyl
correction because `ν` is the base change of a ground-field cocharacter.

- `regularCocharacterPinning_inclusion_eq` states that the inclusion of the
  initial pinning is `groupHom (Iso.refl T_K).hom ≫ i_K`. It is proved by
  rewriting the identity morphism and by definitional unfolding.
- `regularCocharacterPinning_action_root` states that the descended action
  transports the roots of the initial pinning, in the form required by
  `action_root` with `torusIso = Iso.refl T_K`. It is proved by simplifying the
  identity transport and applying
  `IsRootDatumOf.descendedRegularCocharacterSimpleAction_root`.
- `ofRegularCocharacter`, assuming in addition `FiniteDimensional k K`, builds
  the structure. The pinning is the published
  `SplitPinning.galoisCompatibleRepinning` of the initial pinning, with the two
  facts above. It keeps the torus, the inclusion, the root datum and the base
  of the initial pinning, and replaces the simple root vectors by
  Galois-compatible ones. The torus is `T`, the inclusion is `i`, `torusIso` is
  the identity of `T_K`, and the action is the descended action. The vector
  compatibility is `SplitPinning.galoisCompatibleRepinning_rootVectors`. The
  whole root maps and their compatibility are
  `SplitPinning.galoisCompatibleRootParametrizations` and
  `SplitPinning.galoisCompatibleRootParametrizations_compatible`.
- `ofRegularCocharacter_isPos` records that a root of the constructed pinning
  is positive exactly when its lattice pairing with `ν` is positive
  (`IsRootDatumOf.regularCocharacterBase_isPos`).

`K/k` need not be separable or Galois for this construction. Finite
dimensionality is used by the published compatible-repinning construction.

## Construction from an actual torus centralizer

`TorusCentralizerTorusData.nonempty_galoisCompatiblePinningData` takes a split
torus `A/k` (`hA`), a homomorphism `a : A → G` and supplied data
`C : TorusCentralizerTorusData a`. That data is an actual torus `C.torus` with
a closed inclusion into `G` that represents the whole centralizer of `a`. The
theorem also assumes that `G` is locally of finite type and connected reductive
(`hG`), and that `K/k` is finite dimensional. Its remaining premises are
`hRDE : RootDatumExistenceStatement.{u}` and splitness of the base change of
`C.torus` to `K` (`hT`). It concludes `Nonempty (GaloisCompatiblePinningData k
K G)`.

The proof proceeds as follows.

1. The published theorem `connectedReductiveFieldExtensionStatement` shows that
   `G_K` is connected reductive.
2. `C.isMaximalTorus_baseChange K` shows that the base-changed centralizer
   inclusion is a maximal torus of `G_K`.
3. `hRDE`, applied over `K` to `G_K`, the split torus and this maximal torus,
   supplies a finite type `J` and a reduced root datum `P` of the base-changed
   inclusion.
4. The ground-field cocharacter is `C.regularCocharacter hA`.
   `C.regularCocharacter_baseChange_isRegular K hA hT` shows that its base
   change is regular. With
   `IsRootDatumOf.root'_ne_zero_of_isRegularCocharacter`, this gives the
   nonzero-pairing premise.
5. `GaloisCompatiblePinningData.ofRegularCocharacter` then gives the data.

`RootDatumExistenceStatement` is a named statement in the Library. This theorem
takes it as an explicit premise and does not prove it.

## Quasi-split groups

`IsQuasiSplit.exists_galoisCompatiblePinningData` assumes
`hPD : ParabolicDynamicStatement.{u}`,
`hRDE : RootDatumExistenceStatement.{u}` and `IsQuasiSplit G`. Here `G` keeps
the affine-structure-morphism instance used to form the structure. The theorem
concludes that some field `K : Type u` with an algebra `k → K` is finite
dimensional and Galois over `k`, and that `GaloisCompatiblePinningData k K G`
is nonempty.

The proof proceeds as follows.

1. Connected reductivity makes `G` smooth, hence locally of finite type.
2. The published
   `IsQuasiSplit.exists_maximalSplitTorus_with_torusCentralizer`, applied with
   the proved theorem `dynamicCentralizerReductive` and with `hPD`, supplies
   three things: a maximal split torus `a : A → G`; a torus `C` with a closed
   inclusion `c : C → G` representing the whole centralizer of `a`; and the
   torus property of `C`.
3. These are assembled into `TorusCentralizerTorusData a`, using commutativity
   of the torus `C`.
4. The proved theorem `torusFiniteGaloisSplitting` gives a finite Galois
   extension `K/k` splitting `C`.
5. The previous theorem then applies, with splitness of `A` taken from
   maximal-split-torus data.

The two named statements `ParabolicDynamicStatement` and
`RootDatumExistenceStatement` are the only premises beyond quasi-splitness.
Neither is proved in this module.

## Scope

This module proves no orthogonality of simple-root orbits, no Steinberg
cross-section, no class quotient and no rational lifting. It also does not
discharge `ParabolicDynamicStatement` or `RootDatumExistenceStatement`. These
remain obligations of the host task and of the prerequisite tasks that own
those statements. All theorems use only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
