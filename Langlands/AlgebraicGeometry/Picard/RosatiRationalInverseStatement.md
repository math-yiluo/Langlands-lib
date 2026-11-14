# Rational invertibility of an actual geometric polarization

`Langlands.AbelianScheme.Rosati.RationalInverseStatement` asserts that the rationalization of every actual geometric polarization over an algebraically closed field of characteristic zero is an isomorphism in the existing rational category of abelian schemes. This is an unproved proposition.

The source is Milne, *Abelian Varieties*, January 2, 2022 author revision, §17 p.35, the opening paragraph: a polarization is an isogeny and has an inverse in rational Hom. Source ID: `milne-abelian-varieties-1986-author-2022`; the complete registered errata snapshot was read and all its corrections are incorporated in this revision.

`P` and `W` expose the existing tensor, Picard, dual representability, geometry and inverse-Poincare evaluation inputs of the Library. The premise `W.IsPolarization P lam` is exactly its existing `AbelianScheme.IsPolarization` predicate. The conclusion is `IsIso ((rationalization _).map lam)`, as abbreviated by `HasRationalInverse`. No inverse, annihilator of the kernel, dimension, trace property or positivity is assumed.

Once this target is proved, it supplies the construction instance for the actual `polarizationInverse` and `involution` definitions. Their inverse equations are already proved from the categorical inverse laws. The existing more general conditional isogeny inverse target with a uniform-kernel-annihilator premise is not substituted for the unconditional geometric assertion made here.
