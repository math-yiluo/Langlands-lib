# A common Galois overfield of a finite family of number fields

This internal construction takes a number field `E` and a finite family `L i`
(`i : ι`, `ι` finite) of number fields with algebra structures over `E`. It
constructs a number field `M` in the universe of `E`, Galois over `E`, with an
algebra structure `L i → M` for every `i` and the scalar tower `E → L i → M`.

The structure `FamilyGaloisOverfield E L` records the field `M`, its number-field
structure, the algebra structures from `E` and from every `L i`, the scalar towers
`IsScalarTower E (L i) M` and the Galois property `IsGalois E M`. All of them are
instances.

The definition `familyGaloisOverfield E L` embeds each `L i` over `E` into the
algebraic closure `Ω` of `E` (Mathlib's `IsAlgClosed.lift`). It takes `M` to be
the supremum in `Ω` of the normal closures over `E` of the `L i`
(`IntermediateField.normalClosure E (L i) Ω`). Each normal closure is a finite
normal extension of `E`, because `L i` is finite over `E` and `Ω` is normal over
`E`. A finite supremum of finite normal intermediate fields is finite and normal
(Mathlib's `IntermediateField.finiteDimensional_iSup_of_finite` and
`IntermediateField.normal_iSup`). So `M` is a number field
(`NumberField.of_module_finite`) and, being separable in characteristic zero,
Galois over `E`. Each embedding `L i → Ω` lands in the normal closure of `L i`,
hence in `M`; its corestriction is the algebra structure `L i → M`. It is an
`E`-algebra map, which gives the scalar tower.

Provenance: derived field-theoretic infrastructure, generalizing the Library's
two-field `CommonGaloisOverfield` to a finite family. It is used in the proof of
`HenniartGlobalizationStatement` (Henniart 2000, §§3.3–3.7) to put the finitely
many CM fields `E'` that Harris's construction attaches to the intermediate
fields of one finite extension of the p-adic field inside one Galois extension
of the common CM base field. No arithmetic assertion is made.
