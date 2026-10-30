# Actual rational dual pullback and the Weil similitude equation

Worker 142. The definition `rationalDualPullbackHom0` constructs
`f^vee composed with lamB composed with f`, in the existing rational Hom
category of actual abelian schemes. Both dual schemes are the existing
Picard-zero constructions, and `f^vee` is the constructed `dualHom0`.
`IsRationalDualPullbackMultiple q f lamA lamB` is the geometric equation
`f^vee lamB f = q * lamA` in that rational Hom group. Here `q` is any rational
number. No arbitrary replacement dual map or pairing is introduced.

The first lemma proves
`E_lamB(V(f)x,V(f)y)=E_(f^vee lamB f)(x,y)` for the actual rational Tate
modules and their unchanged twist over every test scheme and selected-order
predicate. It uses `RationalWeilFunctorialityStatement` as an explicit theorem
dependency, then the proved composition law of the actual rational Tate maps.
The second lemma substitutes the geometric multiplier equation and applies
linearity in `lam` from `WeilAlongHom0`. Thus it derives
`E_lamB(V(f)x,V(f)y)=q E_lamA(x,y)` without taking this pairing equation as
input. The named rational-functoriality target is a separate mathematical
obligation; this unit does not prove it.

Every dual-constructor coherence input, inverse Poincare evaluation, dual
geometry, finite Weil transition proposition, and dual-map additivity
proposition remains explicit. No isogeny or polarization condition is needed
for these identities of rationalized section pairings. A later application to
polarized rational isogenies must supply those properties and a nonzero
multiplier; the definitions here do not infer them for arbitrary maps.

This is a derived consequence of the actual Library constructors. Its source
conventions are Edixhoven, van der Geer and Moonen, *Abelian Varieties*, draft
built 2012-02-08, Chapter XI Definition (11.11), printed p.162 / PDF p.166,
Proposition (11.21)(i), printed p.167 / PDF p.171, and paragraph (11.23),
printed p.168 / PDF p.172. They supply the second-variable pullback, the finite
dual-map identity and the inverse-limit twist. The source is registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
No source-specific errata note was found in the consulted project notes.
The all-test-scheme rational extension is explicitly the named theorem
dependency rather than an assertion attributed literally to the field passage.

No compatible-frame equivalence, level-orbit transport, polarization
existence, alternation or nondegeneracy is established by this unit.
