# Geometric normalization in the actual residue quotient

This construction uses the published spectral valuation and residue action
`Langlands.LocalGalois.residueHom`, its actual inertia kernel, and the proved
continuous multiplicative equivalence `residueQuotientEquiv`. For a complete
nonarchimedean normed field with finite residue field and an algebraic Galois
extension, `geometricFrobeniusClass` is the inverse image of the existing
finite-field geometric Frobenius under that equivalence. It is a canonical
element of the Galois group modulo inertia. No representative in the Galois
group is selected.

`HasGeometricResidueAction` compares the actual residue action with geometric
Frobenius. Its two intrinsic characterizations say that the Galois class is
`geometricFrobeniusClass`, and that the inverse residue action is the power
map with exponent the cardinality of the base residue field. The latter is
the geometric convention of the published companion statement
`Langlands.LocalClassField.FiniteAbelianReciprocity` (module
`Langlands.ClassFieldTheory.Local.FiniteReciprocityStatement`), whose
uniformizer images have inverses acting by that power modulo the maximal
ideal.

`GeometricNormalization` is a predicate on an explicitly supplied valuation
homomorphism on the field's multiplicative group and an explicitly supplied
homomorphism to the actual Galois group. At every element, its residue class
must be the geometric Frobenius class raised to that element's valuation.
The equivalent residue-action formula is proved by applying the quotient
equivalence. The uniformizer and unit certificates follow by setting the
valuation to one and zero: a uniformizer has geometric residue action, and
a valuation unit has image in the actual inertia subgroup.

The `Canonical` specialization applies this construction to every actual
finite extension `F : PadicField p` in its original carrier universe, and
every algebraic Galois extension in an independent universe. It uses the
published canonical spectral norm, completeness and local-field realization.
`residueField_finite` compares the norm-valuation integer ring with the
canonical valuative integer ring by equality of their valuation inequalities.
It then transports the proved residue finiteness through the induced residue
ring equivalence. Thus this specialization neither assumes residue finiteness
as additional field data nor silently identifies different residue objects.
Its normalization predicate uses the existing constructed `orderHom` of the
canonical `TopologicalData`.

This is a definition and construction layer. It does not assert that a
reciprocity homomorphism exists, identify the multiplicative group with a
profinite group, or supply an inverse from the multiplicative group to a
nonabelian Weil or Galois group.

The original sources are Serre, *Local Fields* (1979), Chapter I, Section 7,
printed pages 20–22, for the residue quotient and inertia; Chapter XIII,
Section 2, pages 190–191, for finite-field Frobenius; and Section 4,
pages 196–198, for finite norm-residue functoriality and unramified
normalization. Serre's arithmetic convention is inverted here to follow
Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique* (2000), Section 1.1, page 439: geometric Frobenius corresponds
to a uniformizer. The Lean quotient construction and the predicate are
derived interfaces; the residue exactness and finite-field objects are
imported from their existing project modules.

The registered originals are `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
and `henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The cited original passages were read. The prepared environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with Lean 4.34.0
and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Authors: Worker 21 and Worker 53. Worker 53 supplied the explicit
integer-ring comparison and residue-finiteness proof used in the canonical
specialization; the remaining constructions and certificates are Worker 21's.
Compilation and independent review status are recorded
separately; this text does not assert publication.

Development check `7897e978-815d-42ef-abed-eeb3fd9779f1`, over Library
`30ceb5a0d89d8094c1663fc19f35416519b9a125`, compiled this module without
errors or warnings and found only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. This is development compilation
evidence; independent semantic review and publication remain separate.
