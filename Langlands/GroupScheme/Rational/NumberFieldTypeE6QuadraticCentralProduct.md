# The type `E_6` Levi Hasse statement from a central product of type `A₂` groups

Module: `Langlands.GroupScheme.Rational.NumberFieldTypeE6QuadraticCentralProduct`.

The module splits `NumberFieldTypeE6QuadraticLeviHasseStatement`
([`Rational.NumberFieldTypeE6QuadraticLeviReduction`](NumberFieldTypeE6QuadraticLeviReduction.md))
into a structural statement about groups of type `E_6` and a cohomological argument, and
proves the cohomological part. It contains:

- the structures `TypeA2WeilProduct` (a decomposition of a group as a finite product of Weil
  restrictions of simply connected absolutely almost-simple groups of type `A₂`) and
  `TypeA2CentralIsogenyFactorization t` (a factorization of `t : C ⟶ G` through the target of
  a central isogeny from such a product whose kernel is killed by `3`);
- the statement `NumberFieldTypeE6QuadraticLeviCentralProductStatement.{u}` (a `Prop`): under
  the hypotheses of `NumberFieldTypeE6QuadraticLeviHasseStatement`, such a factorization
  exists;
- the theorem `numberFieldTypeE6QuadraticLeviHasse_of_centralProduct`: this statement and
  `NumberFieldOuterTypeAHasseStatement` imply `NumberFieldTypeE6QuadraticLeviHasseStatement`,
  in every universe `u`;
- the theorems `Cocycle.isTrivial_of_locallyTrivial_typeA`, `Cocycle.IsTrivial.cohomologous`,
  `TypeA2WeilProduct.isTrivial_of_locallyTrivial` and
  `TypeA2CentralIsogenyFactorization.isTrivial_map` used in its proof.

The module does not prove `NumberFieldTypeE6QuadraticLeviCentralProductStatement` or
`NumberFieldOuterTypeAHasseStatement`.

## Lean statements

```lean
structure TypeA2WeilProduct {F : Type u} [Field F]
    (X : GroupScheme (Spec (CommRingCat.of F))) where
  Index : Type u
  [finite : Finite Index]
  field : Index → Type u
  [isField : ∀ i, Field (field i)]
  [algebra : ∀ i, Algebra F (field i)]
  [finiteDimensional : ∀ i, FiniteDimensional F (field i)]
  factor : ∀ i, GroupScheme (Spec (CommRingCat.of (field i)))
  [isAffineHom : ∀ i, IsAffineHom (factor i).X.hom]
  [isAffine : ∀ i, IsAffine (factor i).X.left]
  [locallyFiniteType : ∀ i, LocallyOfFiniteType (factor i).X.hom]
  simplyConnected : ∀ i, IsSimplyConnected (factor i)
  absolutelyAlmostSimple : ∀ i, IsAbsolutelyAlmostSimple (factor i)
  index : ∀ i, TitsIndexData (factor i)
  numbering : ∀ i, (index i).Vertex ≃ Fin 2
  cartan_eq : ∀ i a b, (index i).cartan a b = CartanMatrix.A 2 (numbering i a) (numbering i b)
  iso : X ≅ pi (fun i => AffineWeil.groupScheme F (field i) (factor i))

structure TypeA2CentralIsogenyFactorization {F : Type u} [Field F]
    {C G : GroupScheme (Spec (CommRingCat.of F))} (t : C ⟶ G) where
  target : GroupScheme (Spec (CommRingCat.of F))
  [isAffineHom : IsAffineHom target.X.hom]
  inclusion : target ⟶ G
  leviMap : C ⟶ target
  factorization : leviMap ≫ inclusion = t
  source : GroupScheme (Spec (CommRingCat.of F))
  isogeny : source ⟶ target
  isCentralIsogeny : IsCentralIsogeny isogeny
  kernel_cube : ∀ (K : Type u) [Field K] [Algebra F K]
    (x : source.affinePoints (CommAlgCat.of F K)),
    source.affinePointsTarget isogeny (CommAlgCat.of F K) x = 1 → x ^ 3 = 1
  simplyConnected : IsSimplyConnected source
  product : TypeA2WeilProduct source

def NumberFieldTypeE6QuadraticLeviCentralProductStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    ∀ (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E],
      (∀ [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F E)).obj G).X.hom]
        [LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap F E)).obj G).X.hom]
        (d' : TitsIndexData ((GroupScheme.baseChange (algebraBaseMap F E)).obj G))
        (e' : d'.Vertex ≃ Fin 6),
        (∀ a b, d'.cartan a b = CartanMatrix.E 6 (e' a) (e' b)) →
        e'.symm 1 ∈ d'.distinguishedVertices ∧ e'.symm 3 ∈ d'.distinguishedVertices) →
      ∀ (C : GroupScheme (Spec (CommRingCat.of F))) (t : C ⟶ G),
        IsQuadraticOppositeMinimalParabolicLevi E t →
        Nonempty (TypeA2CentralIsogenyFactorization t)
```

## Conventions

- **Hypotheses.** The hypotheses of `NumberFieldTypeE6QuadraticLeviCentralProductStatement`
  are those of `NumberFieldTypeE6QuadraticLeviHasseStatement`, word for word, up to the
  cocycle: `G` is a simply connected absolutely almost-simple group of type `E_6` over a
  number field `F` (inner or outer form, with actual Tits index data `d` numbered by
  `CartanMatrix.E 6`), `E/F` is a finite Galois extension over which the vertices `1` and `3`
  (Bourbaki's `α₂`, `α₄`) are distinguished in every actual Tits index of `G_E`, and
  `t : C ⟶ G` satisfies `IsQuadraticOppositeMinimalParabolicLevi E t`: `[E : F] = 2`, `t` is a
  closed subgroup, and `C_E = P ∩ σ(P)` is a Levi subgroup of a minimal parabolic subgroup `P`
  of `G_E`, `σ` the nonidentity automorphism of `E/F`. The Markdown of
  [`Rational.NumberFieldTypeE6QuadraticLeviReduction`](NumberFieldTypeE6QuadraticLeviReduction.md)
  explains these conventions.
- **Weil restrictions.** `AffineWeil.groupScheme F B H` is the Weil restriction `R_{B/F}(H)` of
  an affine group `H` over a finite extension `B/F`, and `pi` is the finite product of group
  schemes.
- **Type `A₂`.** A factor `Hᵢ` of a `TypeA2WeilProduct` carries actual Tits index data with a
  numbering of its two simple vertices under which the Cartan pairings are those of
  `CartanMatrix.A 2`. Nothing is assumed about the star action: inner and outer forms are
  both allowed.
- **The kernel condition.** `kernel_cube` says that every point of the source `X` over a field
  `K` (an `F`-algebra) that maps to `1` in `D` has cube one. It holds when the kernel of the
  isogeny is a finite group scheme of order `3`: its `K`-points form a group of order dividing
  `3`.
- **Cocycles.** `Cocycle C (GaloisCocycle.cover F E)` is a cocycle on the cover
  `Spec E → Spec F`, `LocallyTrivial` means trivial at every place on the full pullback cover,
  and `IsTrivial` means being a coboundary.

## The statement and its source

`NumberFieldTypeE6QuadraticLeviCentralProductStatement`: under the hypotheses above there are
a group `D` over `F` with homomorphisms `C ⟶ D ⟶ G` composing to `t`, and a central isogeny
`X ⟶ D` from a simply connected group `X` that is a finite product of Weil restrictions of
simply connected absolutely almost-simple groups of type `A₂`, whose kernel points over fields
have cube one.

**Source.** V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994),
registered as `platonov-rapinchuk-1994-algebraic-groups-number-theory` (printed page `p` is
the one-based PDF page `p + 10`), §6.8, printed pp. 383–385. For the Levi subgroup `C₁` of a
parabolic subgroup of type `Δ = Π ∖ {α₂, α₄}` (the source's `C`), the source takes
`H = [C₁, C₁]`, simply connected of type `A₂ × A₂` with simple systems `{α₁, α₃}` and
`{α₅, α₆}`. The source writes `B = Z_G(H)` on printed p. 384. The simply connected type `A₂`
factor associated with `α₂` and the highest root `μ` is the identity component
`B = Z_G(H)°`. The full centralizer meets `H` in `Z(H)`, which over an algebraic closure is
`μ₃ × μ₃` of order `9`. With connected `B`, one has `D = HB ⊇ C₁` and the exact sequence
`1 → H ∩ B → H × B → D → 1`. The proof of Lemma 6.33 uses `|H ∩ B| ∣ |Z(B)| = 3`.

**Comparison (provenance: derived).** The statement records the source's construction in the
form used by its Lemma 6.33. The Markdown of
[`Rational.NumberFieldTypeE6QuadraticLeviReduction`](NumberFieldTypeE6QuadraticLeviReduction.md)
(section "The second statement") derives it from the hypotheses: the Levi subgroup `C` of
the minimal parabolic `P` lies in an enlarged Levi subgroup `C₁ = Z_G(S₁)` defined over `F`, of
type `Π ∖ {α₂, α₄}` over an algebraic closure, because every automorphism of the `E_6`
diagram fixes `α₂` and `α₄`. The groups `H = [C₁, C₁]` and `B = Z_G(H)°` are simply connected
of types `A₂ × A₂` and `A₂`, respectively, and `C ⊆ C₁ ⊆ D = HB`. The coefficient of `α₄∨`
in `μ∨` gives index `3` for the cocharacter lattice of `H × B` in that of a maximal torus
of `D`, so the kernel `H ∩ B` of the product map has order exactly `3`.
The structure `TypeA2CentralIsogenyFactorization t` is then filled as follows.

- `target` is `D`, affine as a closed subgroup of the affine group `G`; `inclusion` is
  `D ⊆ G` and `leviMap` is `C ⊆ D`, so `factorization` holds.
- `source` is `X = H × B` and `isogeny` the product map, a central isogeny since its kernel
  `{(h, h⁻¹) : h ∈ H ∩ B}` is finite and central: `B` centralizes `H`, so `H ∩ B` lies in the
  centres of `H` and of `B`.
  `kernel_cube` holds as the kernel has order `3`, and `X` is simply connected as a product of
  simply connected groups.
- `product`: `H` is simply connected of type `A₂ × A₂` over `F`, so it is either a product
  `H₁ × H₂` of absolutely almost-simple groups of type `A₂` over `F` or a Weil restriction
  `R_{B'/F}(H')` of an absolutely almost-simple group of type `A₂` over a quadratic extension
  `B'/F` (Galois permutes the two simple factors over an algebraic closure); `B` is absolutely
  almost-simple of type `A₂`. So `X` is a product of two or three Weil restrictions (`R_{F/F}`
  is the identity) of simply connected absolutely almost-simple groups of type `A₂`, each with
  actual Tits index data numbered by `CartanMatrix.A 2`.

Two pieces of the source's data are not recorded: that `D` is a closed subgroup of `G`
(`inclusion` is any homomorphism) and that `C ⟶ D` factors through `C₁`. Neither is used in
the proof below. The statement is not proved in this module.

## The reduction theorem

`numberFieldTypeE6QuadraticLeviHasse_of_centralProduct` assumes
`NumberFieldTypeE6QuadraticLeviCentralProductStatement.{u}` and
`NumberFieldOuterTypeAHasseStatement.{u}` and proves
`NumberFieldTypeE6QuadraticLeviHasseStatement.{u}`, adding no hypothesis to it. Given the data of
that statement and a cocycle `δ` of `C` on `Spec E → Spec F` trivial at the real places, the
first assumption gives a factorization `P`, and `TypeA2CentralIsogenyFactorization.isTrivial_map`
(with `[E : F] = 2` from `IsQuadraticOppositeMinimalParabolicLevi`) makes `δ.map t` trivial.

`TypeA2CentralIsogenyFactorization.isTrivial_map` is Lemma 6.33 of the source (printed
pp. 384–385) in the following form: for a quadratic Galois extension `E/F` of number fields and
a cocycle `δ` of `C` on `Spec E → Spec F` that is trivial at every real place, `δ.map t` is
trivial. The source's argument through `H²(F, H ∩ B)` and corestriction is replaced by explicit
cochain computations on the quadratic cover
([`Rational.CentralCubeKernelQuadraticLift`](CentralCubeKernelQuadraticLift.md)). The proof:

1. `ξ = δ.map leviMap` is a cocycle of `D`. `X` and `D` are affine (`X` is semisimple, `D` by
   the structure). `IsCentralIsogeny.exists_cohomologous_map_of_cube_kernel` gives a cocycle
   `ζ` of `X` on the same cover with `ξ` cohomologous to `ζ.map isogeny`.
2. At a real place `w` of `F`, with `K = F_w` and `M` an algebraic closure of `K`:
   `[M : K] = 2` (`finrank_algebraicClosure_of_equiv_real`, `K ≅ ℝ`), `M/K` is finite
   (`Global.finiteArchimedeanAlgebraicClosure`) and Galois, and `E` embeds in `M` over `F`.
   The pullback of `ξ` is trivial (the image of the pullback of `δ`), hence so is that of
   `ζ.map isogeny` (`Cocycle.Cohomologous.baseChange`); and
   `IsCentralIsogeny.isTrivial_baseChange_of_cube_kernel` makes the pullback of `ζ` trivial.
3. `X` is simply connected, so `simplyConnectedRealToAllPlacesComparison`, applied to `ζ` and
   the trivial cocycle (cohomologous at the real places by step 2,
   `Cocycle.IsTrivial.cohomologous`), makes `ζ` locally trivial at every place.
4. `TypeA2WeilProduct.isTrivial_of_locallyTrivial` makes `ζ` trivial; so `ξ` is trivial
   (`Cocycle.IsTrivial.of_cohomologous`), and so is its image `δ.map t` in `G`, by
   `leviMap ≫ inclusion = t`.

`TypeA2WeilProduct.isTrivial_of_locallyTrivial` is the Hasse principle for finite Galois covers
for a finite product `X ≅ ∏ R_{Bᵢ/F}(Hᵢ)` as above, given `NumberFieldOuterTypeAHasseStatement`.
The image of a locally trivial cocycle of `X` in the product has locally trivial components;
for each component, `AffineWeil.exists_finiteGalois_transfer` gives a finite Galois extension of
the number field `Bᵢ` and a locally trivial cocycle of `Hᵢ` whose triviality gives that of the
component; `Cocycle.isTrivial_of_locallyTrivial_typeA` makes it trivial; `Cocycle.isTrivial_of_pi`
makes the image in the product trivial, and the inverse isomorphism transports this to `X`.

`Cocycle.isTrivial_of_locallyTrivial_typeA` is the Hasse principle on finite Galois covers for
a simply connected absolutely almost-simple group of type `A_n` (`n > 0`) over a number field:
if the star action is trivial (inner form),
`numberFieldInnerTypeASimplyConnectedGaloisHasseKernel_of_reducedNormLocality` with
`CentralSimple.numberFieldReducedNormLocality`; otherwise (outer form),
`NumberFieldOuterTypeAHasseStatement`.

`Cocycle.IsTrivial.cohomologous`: two trivial cocycles on the same cover are cohomologous,
via `f g⁻¹` for trivializations `f`, `g`.

## Imports

- [`Rational.NumberFieldTypeE6QuadraticLeviReduction`](NumberFieldTypeE6QuadraticLeviReduction.md),
  for the target statement and `IsQuadraticOppositeMinimalParabolicLevi`.
- [`Rational.CentralCubeKernelQuadraticLift`](CentralCubeKernelQuadraticLift.md), for the
  quadratic lift and the local correction.
- [`Rational.NumberFieldHasseKernelTypeReduction`](NumberFieldHasseKernelTypeReduction.md), for
  `NumberFieldOuterTypeAHasseStatement`.
- [`Rational.NumberFieldInnerTypeAHasseReduction`](NumberFieldInnerTypeAHasseReduction.md) and
  [`Algebra.NumberFieldReducedNormLocalityProof`](../../Algebra/NumberFieldReducedNormLocalityProof.md),
  for the inner type `A` case.
- [`Rational.SimplyConnectedHasseAbsolute`](SimplyConnectedHasseAbsolute.md), for the Weil
  restriction transfer `AffineWeil.exists_finiteGalois_transfer` and `Cocycle.isTrivial_of_pi`
  (through its imports).
- [`Rational.SimplyConnectedRealPlacesInjectivity`](SimplyConnectedRealPlacesInjectivity.md),
  for `simplyConnectedRealToAllPlacesComparison`.
- [`FieldTheory.RealAlgebraicClosure`](../../FieldTheory/RealAlgebraicClosure.md) and
  [`Global.Arithmetic.ArchimedeanAlgebraicClosure`](../../Global/Arithmetic/ArchimedeanAlgebraicClosure.md),
  for the algebraic closure of a real completion.
