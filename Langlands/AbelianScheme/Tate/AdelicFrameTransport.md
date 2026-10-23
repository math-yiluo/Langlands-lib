# Path-independent fixed orbits of actual adelic Tate frames

Author: Worker 142.

This module constructs tensor-algebra-linear frames in the actual full rational
Tate module, the commuting source and geometric monodromy actions, and the
induced equivalence on monodromy-fixed right orbits along a geometric path.
It proves that this orbit equivalence is independent of the supplied path,
with identity, composition, reversal and level-change compatibility.
These are ambient linear-frame orbits. A polarization-pairing restriction is
not imposed in this module.

## Sources and derived provenance

- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), Section III.1, printed p.91 / PDF p.99. Registered source
  `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
  This page defines a level as a fundamental-group-invariant right orbit of
  tensor-algebra-linear Tate frames satisfying a pairing condition. It states
  canonical independence of the geometric point and gives the right map
  `eta ↦ eta ∘ g` under the conjugate-subgroup inclusion.
- Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary version built
  2012-02-08, Chapter X, (10.29), printed p.151 / PDF p.155. Registered source
  `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  This passage explains noncanonical base-point change for the fundamental
  group, including points with different algebraically closed residue fields.

These passages were read from local PDF text extractions. No source-specific
errata directory was available in the supplied Library. The contribution is
**derived**: it specializes `OrbitTransport` to the actual monodromy and
transport maps of `RationalTransport`. The latter constructs transport from
finite fibre-functor components on actual torsion points and rational scalar
extension. This module proves the required equivariance and change-of-path
equations from those constructions. It does not take Tate transport or orbit
independence as an input. The general source representation and removal of the
pairing restriction are an internal intermediate construction, not the full
level structure asserted in Harris–Taylor.

## Actual carriers and inputs

Fix an abelian scheme `A` over `S`, a rational algebra `D`, an algebra map
`i : D →ₐ[ℚ] Rationalization.End A`, and the explicit scalar-comparison hypothesis
`h : Global.RationalProfiniteIntegerAdeleComparison`. Put
`R = D ⊗[ℚ] Global.FiniteAdeles ℚ`. The source `V` is an arbitrary `R`-module;
`G` is an arbitrary group with representation `ρ : G →* (V ≃ₗ[R] V)`.
No faithfulness, finite rank, nonemptiness or topology is assumed for them.

`AdelicFrame A h i V s` abbreviates

```text
V ≃ₗ[R] RationalFull A (Over.mk s).
```

The target is the actual carrier `ℚ ⊗[ℤ] Integral A (Over.mk s) (fun _ => True)`.
The integral module consists of coherent actual torsion points. The target
`R`-module instance is precisely `finiteAdeleAlgebraModule`, using the given
endomorphism action and the finite-adelic scalar action constructed under `h`.
All endpoints use the same `h`; independence of comparison witnesses is not
claimed. Frames may form an empty type.

The field-valued points `s`, `t` and `r` may have different fields, in the same
universe as `S`. Monodromy and transport retain the following hypotheses:

```lean
hs : ∀ Y : FiniteEtale.Cover S, Finite (FiniteEtale.Fiber s Y)
htor : Langlands.AbelianScheme.TorsionFiniteEtaleStatement
hu : ∀ n : GroupScheme.Tate.Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))
p : FiniteEtale.fiberFunctor s hs ≅ FiniteEtale.fiberFunctor t ht
```

There are analogous finite-fibre proofs at each endpoint. The intended
geometric application has algebraically closed point fields and connected,
locally noetherian base. This conditional API assumes only the displayed
inputs: it does not prove existence of paths or the geometric finite-etaleness
and Galois-category theorems. It constructs algebraic equivalences without
rational or adelic topology or continuity.

## Commuting actions and fixed orbits

The generic helpers in `Langlands.Shimura.PEL.LinearFrame` are:

- `rightAction ρ`, an action of the opposite group, sends `eta` and `g` to
  `eta ∘ ρ(g)`. Multiplication in the linear automorphism group is composition,
  giving `(eta · g) · k = eta · (g * k)`.
- `leftAction τ` sends `eta` and `γ` to `τ(γ) ∘ eta` for a target representation.
- `actionsComm` proves that these actions commute by evaluation at each vector.
- `postcomp e` is the equivalence of frame spaces obtained by postcomposing
  with a target linear equivalence; its inverse postcomposes with `e.symm`.

`adelicFrameRightAction` uses the supplied source representation.
`adelicFrameMonodromyAction` uses the existing
`finiteAdeleAlgebraMonodromyRepresentation` of the actual finite fibre-functor
automorphism group. `adelicFrameActionsComm` specializes the generic result.
`AdelicFrameOrbit ... U` is the existing `InvariantOrbit` for these actions:

```text
{ q in AdelicFrame/U | γ • q = q for every γ in FundamentalGroup(s) }.
```

Thus fixedness is a property of the right orbit class. It does not require a
monodromy-fixed representative. The subgroup `U` is arbitrary; a compact open
subgroup can be supplied through its underlying subgroup.

## Constructed transport and independence

`adelicFrameTransport p` postcomposes frames with the actual
`finiteAdeleAlgebraTransport ... p`. Its application formula is

```text
F_p(eta)(v) = rationalTransport(p)(eta(v)).
```

The `_refl`, `_trans` and `_symm` lemmas prove, respectively, identity transport,
`F_(p ≪≫ q) = F_q ∘ F_p`, and equality between the inverse equivalence and
transport along `p.symm`. Pointwise extensionality reduces these to the
corresponding rational Tate transport laws.

`adelicFrameOrbitTransport U p` applies `InvariantOrbit.equiv` with the actual
group isomorphism `pathConjugation p` and frame equivalence `F_p`. Right
equivariance follows from associativity of composition. Left equivariance
follows pointwise from `rationalTransport_monodromy`:

```text
F_p(γ • eta) = pathConjugation(p)(γ) • F_p(eta).
```

For two supplied paths `p` and `q` with the same endpoints, the actual
`rationalTransport_change_path` formula gives

```text
F_q(eta) = (p.symm ≪≫ q) • F_p(eta).
```

The element on the right is an actual target fibre-functor automorphism.
`adelicFrameOrbitTransport_path_independent` applies
`InvariantOrbit.equiv_eq_of_left`: this target action disappears on a fixed
orbit. This proves equality of the whole orbit equivalences, while allowing
distinct induced isomorphisms of fundamental groups. It does not identify
the representative-level frame transports or assert existence of a path.

The orbit `_refl`, `_trans` and `_symm` lemmas establish identity, composition
and reversal as equalities of equivalences. Their proofs use subtype
extensionality, then quotient induction and the corresponding frame laws.
Thus, whenever a path exists, every choice gives the same orbit equivalence,
and these equivalences compose in the stated order.

## Level changes and remaining scope

`adelicFrameOrbitTranslate g hg` is the existing fixed-orbit right translation
specialized to these actual frame actions. Its hypothesis is
`hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U'`; it sends a `U`-orbit to a `U'`-orbit by
`eta ↦ eta ∘ ρ(g)`. `adelicFrameOrbitForget` specializes to `g = 1` and `U ≤ U'`.
`adelicFrameOrbitTransport_translate` proves that path transport commutes with
this translation, using `InvariantOrbit.map_translate` and the established
equivariance. `_forget` gives the corresponding square for forgetting level.

The actual scalar actions, monodromy and path maps have been specialized here,
but Weil pairings, Tate twists and preservation of polarization forms remain
separate. This is not yet the similitude-frame subtype defining PEL levels.
The prime-to-p counterpart, pointed base change, path existence and a canonical
unpointed PEL moduli functor remain separate obligations. No parent-task
completion or representability claim is made.
