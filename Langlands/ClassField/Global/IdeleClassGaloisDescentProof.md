# Galois descent for the actual idele-class inclusion

`Langlands.ClassField.Global.ideleClassGaloisDescent` proves the full unapplied
proposition `Langlands.ClassField.Global.IdeleClassGaloisDescent.{u, v}`.
The universes of the number fields `K` and `E` remain independent. For a Galois
extension `E/K`, the actual `ideleClassInclusion` is injective, and its image
consists exactly of the classes fixed by every `relativeIdeleClassAut K E σ`.
The theorem imports the published statement unchanged and uses the actual
Mathlib idele class groups and published maps.

## Principal ideles and fixed field units

The private lemma `principal_injective` proves injectivity of
`IdeleGroup.unitEmbedding (𝓞 E) E`: equality of the underlying adeles implies
equality of the field elements by `AdeleRing.algebraMap_injective`, and then
equality of units. The private lemma `principal_smul` is the published
`ideleEquiv_diagonal` with its equality reversed. It identifies the action of
a relative field automorphism on principal ideles with the action on field
units.

The private lemma `units_fixed_descent` takes a unit of `E` fixed by every
`K`-automorphism. Applying
`IsGalois.mem_range_algebraMap_iff_fixed` to its underlying field element
gives a preimage in `K`. This preimage is nonzero because its image is a unit,
so it defines a unit of `K` mapping to the original unit.

## A fixed class has a fixed representative

`exists_fixed_idele_representative` starts with an idele `a` representing a
fixed class. For each relative automorphism `σ`, the quotient equality says
that `σ(a)/a` is a principal idele. Choose its field unit `f(σ)`.
Injectivity and equivariance of the principal embedding show that these units
form a multiplicative 1-cocycle:

`f(στ) = σ(f(τ)) * f(σ)`.

The proof follows the composition convention of the published `ideleEquiv`;
the equality on ideles reduces to cancellation in the commutative group.
Mathlib's
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`
then supplies a field unit `b` with `f(σ) = σ(b)/b`.
Thus `a / unitEmbedding b` is fixed by every automorphism and represents
the same class as `a`, since principal ideles have trivial quotient class.
The Lean proof checks fixedness by applying the principal embedding to the
coboundary identity and rearranging the resulting equality of quotients.
This helper needs no Galois assumption: it is a statement about the full
relative automorphism group and uses the explicit cocycle form of Hilbert 90.

## Passing from idele descent to class descent

`ideleClass_descent_of_idele_descent` takes the injectivity and fixed-image
clauses for the actual idele inclusion and proves the two class clauses.

For injectivity, it suffices to show that a downstairs class whose image is
trivial is itself trivial. Choose a representative `a`; its image is the
principal idele of some field unit `x` of `E`. The image of `a` is fixed by
idele descent, so equivariance and injectivity of the principal embedding
show that `x` is fixed. The field-unit lemma produces a unit `y` of `K`
mapping to `x`. Compatibility of the idele inclusion with principal ideles,
followed by injectivity of that inclusion, identifies `a` with the principal
idele of `y`. Its class is therefore trivial.

For the fixed-image equivalence, a fixed upstairs class has a fixed idele
representative by the Hilbert–90 argument. Idele descent gives a downstairs
idele mapping to that representative. Its quotient class is the required
preimage, by `ideleClassInclusion_mk`. Conversely, choose an idele
representative of any downstairs class. Its image is fixed by the idele
descent hypothesis, hence its quotient class is fixed by the actual relative
class action.

Finally, `ideleClassGaloisDescent` introduces the two fields and their
instances, then applies this reduction to the two clauses of the published
theorem `Langlands.ClassField.Global.ideleGaloisDescent`, imported from
`Langlands.ClassField.Global.IdeleGaloisDescentProof`. This discharges all
idele descent hypotheses; the final theorem has no additional assumptions.

## Source and provenance

The mathematical statement and this deduction from field and idele
invariants and Hilbert 90 are in Emil Artin and John Tate, *Class Field
Theory*, AMS Chelsea edition (2009), Preliminaries section 1, printed
pp. 1–2 (one-based PDF pp. 10–11), registered source
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The final paragraph of p. 1 states the injections, and the first paragraph
of p. 2 identifies the base idele classes with the Galois-fixed classes
upstairs. The auxiliary lemmas here are internal steps implementing that
deduction. The proof uses Mathlib's explicit cocycle Hilbert–90 theorem to
keep both field universes independent. It proves algebraic injectivity and
the stated fixed-image equivalence; it makes no additional topological claim.
