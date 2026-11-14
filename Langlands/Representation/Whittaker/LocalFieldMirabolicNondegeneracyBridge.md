# From packaged local fields to the published mirabolic nondegeneracy statement

Module `Langlands.Representation.Whittaker.LocalFieldMirabolicNondegeneracyBridge`.

## Statement

`Langlands.Whittaker.LocalFieldMirabolicNondegeneracyBridge.localFieldMirabolicNondegeneracy_of_packaged`
(universes `uF`, `uV`) has one hypothesis `h`. It is the conclusion of Theorem 4.9 of
Bernstein and Zelevinsky (1977), as published in
`Langlands.Whittaker.LocalFieldMirabolicNondegeneracyStatement`, but phrased for packaged
fields:

> for every `F : Langlands.AllFieldBZ.LocalFieldPackage.{uF}`, every
> `T : F.TopologicalData` (= `LocalFieldData F.Carrier`), every unitary additive
> character `ψ` of `F.Carrier` for the topology `T.topology`, every `n : ℕ`, every complex
> vector space `V : Type uV` and every representation
> `π : Representation ℂ (GL_(n+1)(F.Carrier)) V`: with the topology `T.topology`, if `π` is
> generic (`IsGeneric ψ n π`: irreducible, admissible, with a nonzero standard Whittaker
> functional), then every mirabolic subrepresentation `U` of `π` whose full
> upper-unipotent `(standardCharacter ψ n)`-coinvariants are zero is `⊥`.

From `h` the theorem proves `LocalFieldMirabolicNondegeneracyStatement.{uF, uV}`.

The hypothesis is exactly the type of the theorem
`Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy.mirabolicNondegeneracy` of the
all-field port. The only difference is that `h` takes `F` explicitly. The hypothesis is the theorem to be proved,
stated for packaged fields. It is not an extra property of the representation, such as
nondegeneracy, injectivity of mirabolic restriction or a Kirillov model. It is
discharged by the ported theorem, with no extra premise, in the final proof module.

## Proof

Fix a field `F` with ambient instances `Field F`, `ValuativeRel F`, `TopologicalSpace F`
and `IsNonarchimedeanLocalField F`, together with `n`, `ψ`, `V`, `π`, a proof of
genericity, `U`, and the vanishing of the coinvariants. Apply `h` to the following
arguments:

- the package `LocalFieldPackage.ofField F`, whose `Carrier` is `F` and whose `Field`
  instance is the ambient one, both by definition;
- the datum `LocalFieldData.ofInstances F`, whose `topology`, `valuativeRel` and
  `localField` are the ambient instances, by definition of `ofInstances`;
- `ψ`, `n`, `π`, the genericity proof, `U` and the vanishing hypothesis, unchanged.

All types agree with the ambient ones up to definitional unfolding: the group
`GL_(n+1)(F)`, the mirabolic subgroup, the upper-unipotent subgroup, the character and
the coinvariant module. So the proof is a single `exact`. Universe levels are preserved:
the package lives in `Type uF` and `V` in `Type uV`.

## Use in the final proof

The module `Langlands.Representation.Whittaker.LocalFieldMirabolicNondegeneracyProof` proves the
target as

```lean
theorem localFieldMirabolicNondegeneracy :
    LocalFieldMirabolicNondegeneracyStatement.{uF, uV} :=
  LocalFieldMirabolicNondegeneracyBridge.localFieldMirabolicNondegeneracy_of_packaged
    fun _ => Langlands.AllFieldBZ.Whittaker.PadicMirabolicNondegeneracy.mirabolicNondegeneracy
```

## Provenance

This is an internal adapter between interfaces, with no literature counterpart. The
mathematics is BZ77, Theorem 4.9 (Bernstein, Zelevinsky, *Induced representations of
reductive p-adic groups. I*, Ann. Sci. ÉNS 10 (1977), §4.9). The bridge only converts
ambient instance arguments into the explicit package and datum.
