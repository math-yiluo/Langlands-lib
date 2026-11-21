# Strictly Henselian DVR extensions preserving a uniformizer

`strictHenselianDvrAt` applies the Library's maximal
fixed-uniformizer subalgebra construction inside the algebraic
closure of the specified fraction field. It retains the actual
subalgebra, the local map from the original DVR, and the proof
that the supplied uniformizer remains irreducible. The maximality
argument gives a Henselian ring with separably closed residue field.

`StrictHenselianDvrAt.fractionMap` extends the actual inclusion of
the original DVR to the supplied fraction field by the localization
property. The residue map is a field embedding, so characteristic
zero of the original residue field also holds upstairs.

This is a derived refinement of the Library's strictly Henselian
DVR extension result. Retaining the original uniformizer allows the
extension to detect ramification of finite subextensions.
