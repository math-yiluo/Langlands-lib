# Alternation of the actual finite pairing along a Mumford map

`Langlands.AbelianScheme.MumfordFiniteWeilAlternationStatement` is a
proposition definition. It states a theorem target only; its proof is a
separate task. The module imports exactly
`Langlands.AlgebraicGeometry.Picard.MumfordLineBundle` and
`Langlands.AlgebraicGeometry.Picard.FiniteWeilAlongHom`.

## The asserted identity

Let `lam : A → DA` be an abelian-scheme homomorphism into the actual dual
`DA = dualAbelianSchemeFromEvaluation A ...`, and suppose its underlying
scheme morphism `(groupHom lam).hom.hom` equals the published
`mumfordSchemeMapOfLineBundle preservation A L B evaluationB M evaluation square hA`
of an actual line bundle `L` on `A`. Then for every positive natural
number `n`, writing `P = A[n]` for the actual multiplication kernel
`kernelCommGroupScheme (multiplication A (n : ℤ))`, the equation in
`Over S` is

```text
P -- diagonal --> P ×_S P -- finiteWeilAlongHomPairing(lam,n) --> μ_n
 =
P ----------------------- constant identity -----------------> μ_n.
```

The diagonal is exactly `prod.lift (𝟙 P) (𝟙 P)`. The right-hand side is
`1` in the group of morphisms from `P` to the existing commutative group
scheme `mu S n`, the morphism constant at the identity section; no root
of unity is chosen. By the published `finiteWeilAlongHomPairing_points`,
composing with a point `x : T → A[n]` over any test scheme `T/S` turns the
equation into

```text
e_n(x, lam[n](x)) = beta(lam[n](x))(x) = 1   in Hom_S(T, μ_n),
```

where `lam[n]` is the actual torsion restriction
`finiteWeilAlongHomTorsionMap`. Conversely the point equation at
`T = A[n]` and its identity point is the displayed morphism equation. The
statement therefore covers all test schemes, nonreduced ones included.

## Inputs, exactly as quantified

- The eight published constructor propositions `preservation`, `square`
  (`MumfordBundlePicardZeroStatement`), `composition`, `unitCoherence`,
  `associativity`, `comparison`, `symmetry` and `stability`, with their
  published meanings. None of them states an alternation law. They are the
  inputs of the actual dual abelian scheme, of the finite pairing and of the
  Mumford scheme map.
- A quasi-separated base `S`, an abelian scheme `A/S`, the actual dual-scheme
  witness `hA : HasDualScheme A`, its geometry `geometryA`, and an inverse
  `MA` of the Poincaré bundle with tensor evaluation `evaluationA`.
- An arbitrary line bundle `L` on `A` with the unit-section normalization
  data of `MumfordLineBundle`: a line bundle `B` on `S` with
  `e*L ⊗ B ≅ O_S`, and an inverse `M` of the normalized bundle
  `N = L ⊗ f*B` with its evaluation `N ⊗ M ≅ O_A`.
- The homomorphism `lam` and the equality of scheme morphisms over `S`
  displayed above.

The Mumford map is the classifying map, for the actual Poincaré family,
of the rigidified Mumford family `(m*N ⊗ p1*M) ⊗ p2*M` of the normalized
`N`, with the first factor as parameter. Thus a point `a` goes to the
rigidified class of `t_a*N ⊗ N⁻¹`, in the positive-translation
convention. Since `f ∘ t_a = f`, the base factor `f*B` cancels there,
so this is the source's `φ_L`.

There is no isogeny, ampleness, polarization, characteristic or
invertibility hypothesis on `L` or `n`, and `L` need not be symmetric.
In particular `n` may be divisible by residue characteristics, including
`2`. The homomorphism property of the Mumford map is not assumed as a
separate proposition such as `MumfordSchemeMapHomomorphism`; instead `lam`
is an actual homomorphism whose underlying map is required to be that
Mumford map. For example, `mumfordHomOfLineBundle`, when its
homomorphism equations are supplied, is such a homomorphism: by
`mumfordHomOfLineBundle_hom` its underlying morphism of schemes is this
Mumford map. Unlike `RelativeFiniteWeilAlternationStatement`, which needs
`PicardZeroUniversalBaseChangeStatement` for its `IsPolarization`
hypothesis, this statement does not use `IsPolarization`, and that
proposition is not an input.

## Source and derived provenance

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft
built 2012-02-08, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
Chapter XI, printed p.162 and pp.166-168 (PDF p.166 and pp.170-172), read
in the original PDF:

- Definition (11.11): `e_f(x, y) = β(y)(x)` for an isogeny `f`, the Weil
  pairing `e_n` for `f = [n]`, and, for every homomorphism `λ : X → X^t`,
  `e^λ_n(x₁, x₂) = e_n(x₁, λ(x₂))`, written `e^L_n` when `λ = φ_L`.
- (11.19)-(11.20): for a non-degenerate `L` on an abelian variety over a
  field, the pairing `e^{φ_L}` on `K(L)` attached to the isogeny `φ_L`
  equals the theta-group commutator pairing `e^L`. In the proof, the lifts
  of `T`-valued points to `G(L)` are chosen "possibly after replacing `T`
  by a covering".
- Proposition (11.21)(ii): compatibility of these pairings with a
  composition of isogenies.
- Corollary (11.22): for a polarization `λ` and positive `n`,
  `e^λ_n(x, x) = 1` for every `x ∈ X[n](T)` over every `k`-scheme `T`.
  The proof passes to an algebraic closure, writes `λ = φ_L` with `L`
  ample, and computes
  `e^λ_n(x, x) = e_n(x, λ(i(x))) = e_{nλ}(i(x), i(x)) = 1`. The last step
  is (11.20) for `L^n`, since `nλ = φ_{L^n}`: the commutator pairing of
  the theta group is trivial on the diagonal.

The source's `e^λ_n(x, y) = e_n(x, λ(y))`, with `e_n(x, η) = β(η)(x)`,
has the same argument order as the Library's
`finiteWeilAlongHomPairing`, whose value is `beta(lam[n](y))(x)`. On the
diagonal the order does not matter, and so neither would an inversion of
the pairing.

This statement is **derived content**, not printed in the source. The
source works over a field, with `L` ample, so that `φ_L` is an isogeny
and `λ` a polarization. Here the base is an arbitrary quasi-separated
scheme and `L` is an arbitrary line bundle whose Mumford map underlies a
homomorphism. The rationale for this form is that the source's final
step is the commutator of a theta-group lift with itself. Restricted to
`A[n]`, where `φ_{L^n} = n φ_L` vanishes, this needs neither ampleness
nor nondegeneracy. Over a base, such a lift of a point of `A[n]` exists
only locally on the test scheme, and the identity must descend to the
scheme `mu S n`. No proof of these steps is claimed here: a proof must
build the relative theta group, compare it with the Poincaré-derived
pairing of the Library for these exact maps, and carry out the descent.
Checking geometric points alone does not establish the equality of
scheme morphisms.

The file introduces no proof or new axiom. It asserts neither
nondegeneracy, perfectness or Cartier duality, nor transition
compatibility, dual-map functoriality or an inverse-limit pairing.
