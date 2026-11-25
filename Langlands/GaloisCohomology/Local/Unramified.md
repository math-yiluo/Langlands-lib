# Unramified classes and their orthogonality

`Langlands/GaloisCohomology/Local/Unramified.lean`, namespaces `Langlands.ProfiniteCohomology` (the `Ẑ`-generator `isZHatGenerator_frobenius_one`) and `Langlands.GaloisCohomology.Local`.

Let `K` be a nonarchimedean local field with separable closure `Ksep`, `G = Gal(Ksep/K)` and `I` its
inertia subgroup (the Library's `LocalGalois.SepClosed.absoluteInertia`, the kernel of the action
on the residue field of `Ksep`). The *unramified classes* of a smooth module `M` are the classes in
`H¹(G, M)` whose restriction to `I` vanishes.

- `G/I` is procyclic with a `Ẑ`-generator: through the Library's residue degree
  `Weil.Local.SepClosed.localResidueDegree : G → Ẑ` (kernel `I`, surjective), `G/I` is isomorphic to
  the profinite completion of `ℤ`, in which the image of `1` is a `Ẑ`-generator
  (`exists_isZHatGenerator_inertia`).
- **Number of unramified classes.** For finite `M`, `|H¹_ur(M)| = |M^G|`
  (`card_unramifiedClasses`): the unramified classes are the inflation of `H¹(G/I, M^I)`, and for a
  procyclic group `|H¹(Ẑ, A)| = |A/(σ−1)A| = |A^σ|`.
- **Orthogonality.** The cup product of two unramified classes vanishes (it is inflated from
  `H²(G/I, M^I ⊗ N^I)`, which is zero because the coefficients are finite and `G/I` is procyclic);
  hence unramified classes of `M` and of its Cartier dual `M'` are orthogonal under the local Tate
  pairing. For `|M|` prime to the residue characteristic, the unramified classes of `M'` are
  exactly the orthogonal complement of those of `M` (`mem_unramifiedClasses_cartierDual_iff`): the
  annihilator of `H¹_ur(M)` has `|H¹(M)|/|M^G|` elements, and the Euler characteristic formula
  (`|H¹(M)| = |H⁰(M)| · |H²(M)|` as `|M|` is a unit in `𝒪[K]`) and duality in degrees `0, 2`
  (`|H²(M)| = |H⁰(M')|`) make this `|M'^G| = |H¹_ur(M')|`.

- `coeffMap_mem_unramifiedClasses`, `coeffMap_mem_unramifiedClasses_iff` (namespace
  `Langlands.GaloisCohomology`): a coefficient map sends unramified classes to unramified classes, and an
  isomorphism of coefficients identifies them.

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.coeffMap_mem_unramifiedClasses.{u} {K Ksep : Type u} [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {A B : Rep.{u, u, u} Langlands.ClassFieldTheory.Local.IntegerScalars Gal(Ksep/K)} [Langlands.IsSmoothRep A]
  [Langlands.IsSmoothRep B] (f : A ⟶ B) {x : ↑(Langlands.ProfiniteCohomology.cohomology A 1)}
  (hx : x ∈ Langlands.GaloisCohomology.Local.unramifiedClasses K Ksep A) :
  (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap f 1)) x ∈
    Langlands.GaloisCohomology.Local.unramifiedClasses K Ksep B
Langlands.GaloisCohomology.coeffMap_mem_unramifiedClasses_iff.{u} {K Ksep : Type u} [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {A B : Rep.{u, u, u} Langlands.ClassFieldTheory.Local.IntegerScalars Gal(Ksep/K)} [Langlands.IsSmoothRep A]
  [Langlands.IsSmoothRep B] (e : A ≅ B) (x : ↑(Langlands.ProfiniteCohomology.cohomology A 1)) :
  (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap e.hom 1)) x ∈
      Langlands.GaloisCohomology.Local.unramifiedClasses K Ksep B ↔
    x ∈ Langlands.GaloisCohomology.Local.unramifiedClasses K Ksep A
```

## Declarations

The profinite completion of `ℤ` (namespace `Langlands.ProfiniteCohomology`):

- `isZHatGenerator_frobenius_one`: the image of `1` in the profinite completion of
  `ℤ` (the Library's `Weil.ProfiniteIntegers`) is a `Ẑ`-generator.

The general facts used below are in the foundations: `IsZHatGenerator.map_continuousMulEquiv` and
`card_cohomology_one_eq_card_invariants` (`|H¹(G, A)| = |A^G|` for a `Ẑ`-generator) in
`Langlands.Cohomology.Profinite.Dimension.Procyclic`; `card_ker_res_one`
(`|ker (H¹(G, A) → H¹(N, A))| = |H¹(G/N, A^N)|`) and `invariantsQuotientEquiv` in
`Langlands.Cohomology.Profinite.InflationRestriction.DegreeOne`;
`card_addMonoidHom_rationalModIntegers` and `card_annihilator_mul_card` (annihilators under a
perfect pairing to `ℚ/ℤ`) in `Langlands.Cohomology.Profinite.TorsionDual`.

Local fields (namespace `Langlands.GaloisCohomology.Local`):

- `inertia K Ksep` (abbreviation of the Library's `absoluteInertia`),
  `exists_isZHatGenerator_inertia K Ksep : ∃ σ : G/I, IsZHatGenerator σ`.
- `unramifiedClasses K Ksep M : AddSubgroup (H¹(G, M))`, `mem_unramifiedClasses_iff`.
- `card_unramifiedClasses K Ksep M : |H¹_ur(M)| = |M^G|`.
- `cupPairing_eq_zero_of_mem_unramifiedClasses M N P μ hx hy`,
  `tatePairing_eq_zero_of_mem_unramifiedClasses M hx hy`.
- `mem_unramifiedClasses_cartierDual_iff M hM y`: for `|M|` prime to the residue characteristic,
  `y ∈ H¹_ur(M') ↔ y ⊥ H¹_ur(M)`.

## Source and licence

New file. The definition `unramifiedClasses` (the kernel of restriction to inertia) and the
statement `exists_isZHatGenerator_inertia` are those of the repository
`leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>),
commit `f1f6d65`, file `src/GroundTheory/ArithmeticGeometry/SelmerPairing/Unramified.lean`
(`unramifiedClasses` = `kerRes (inertiaGroup K Ω)`; `exists_isZHatGenerator_inertia` through the
source's `unramifiedDegree`); `invariantsQuotientEquiv` of `InflationRestriction/DegreeOne.lean` is
ported from the same file. The source's
inertia group and unramified degree come from its own local class field theory; here they are the
Library's `absoluteInertia` and `localResidueDegree`. The source states no orthogonality; the
counting, the orthogonality and the generic lemmas are new. The repository has no licence file;
its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`).

`coeffMap_mem_unramifiedClasses` and `coeffMap_mem_unramifiedClasses_iff` contain no text of the source.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, chapter VII, §2, Theorem
  (7.2.15) (stated for unramified, finitely generated modules with torsion prime to `p`; here `M`
  need not be unramified, the unramified classes being the kernel of restriction to inertia), p.
  387.
- J. S. Milne, *Arithmetic Duality Theorems*, chapter I, §2, Theorem 2.6 (for finitely generated
  unramified modules), p. 30.
- J.-P. Serre, *Galois Cohomology*, chapter II, §5.5, Propositions 18 and 19 (for unramified modules
  of order prime to `p`), pp. 94–95.
