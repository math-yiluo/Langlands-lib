# Idele-class norms when almost every finite completion has degree one

`Langlands.Global.AdelicFunctoriality.AlmostEverywhereSplitIdeleClassNormSurjective.{u,v}`
defines the following proposition. Let `F : Type u` and `E : Type v` be
number fields with a given `Algebra F E`. Suppose `E/F` is Galois and its
actual automorphism group `E ≃ₐ[F] E` is cyclic. For any finite set
`S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))`, assume that every
finite prime `p ∉ S`, every finite prime `q` of `E` above `p`, and every
witness `h : q.asIdeal.LiesOver p.asIdeal` satisfy

`Module.finrank (p.adicCompletion F) (q.adicCompletion E) = 1`.

Then the published continuous homomorphism
`ideleClassNorm (K := F) (L := E)` is surjective from
`NumberField.IdeleClassGroup (𝓞 E) E` to
`NumberField.IdeleClassGroup (𝓞 F) F`.

The primes are actual nonzero prime ideals of the rings of integers.
The fields have independent universes. Inside the splitting hypothesis,
`letI := h` installs the lying-over witness before forming the completed
degree. The open `FiniteExtension` scope selects the published completion
algebra induced by the original field embedding. The number-field structures
give a finite global extension, and the imported infrastructure gives finite
local extensions. Thus finrank one means that the corresponding actual
completion extension is trivial as an extension of the base completion;
no arbitrary local algebra is an input.

This is a proposition definition, not a theorem proof. Its only additional
arithmetic premise is the displayed finite-place splitting condition. It
assumes no local norm openness, approximation result, norm surjectivity,
first or second inequality, cohomology vanishing, Chebotarev theorem, or
equality of the global fields. Degree-one global extensions are included.

## Derived provenance and scope

The source is Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea,
2009, Chapter V §4, the cyclic case of the proof of Theorem 2, printed
page 17 (PDF page 26). The registered source is
`artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The appended errata, PDF page 202, contain no correction to this passage.

This derived statement isolates the intermediate conclusion of that proof:
every base idele `a` can be expressed as a nonzero principal idele `α` times
the norm of an upper idele `b`. Passing to idele classes gives the stated
surjectivity. It stops before the first inequality is used to infer that the
global extension is trivial, and does not state the full nonsplit-prime
theorem.

The source's construction first uses approximation to arrange that
`α⁻¹a` belongs to local norm neighborhoods at the exceptional places.
Outside them, completed degree one permits a local norm preimage.
One chooses one upper place over each base place, uses the chosen preimage
there, and puts `1` at the other upper places.

In the Lean statement `S` contains only finite primes. In the underlying
approximation argument it must be augmented by all archimedean places;
there are finitely many of those for a number field. No splitting hypothesis
is imposed at archimedean places. A later proof must justify approximation,
the needed local norm neighborhoods including the archimedean ones, and
restrictedness of the assembled upper idele. In particular, local lifts
outside a finite set must be units in the valuation rings. It must also
identify the componentwise norm with the published `ideleClassNorm`.
These are proof obligations described by the source argument, not extra
hypotheses or results proved in this file.
