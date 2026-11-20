# Étaleness of the actual full-residue integer algebra

`Langlands.CentralDivision.LocalDivisionFullResidueSubfieldEtaleStatement`
quantifies over a nonarchimedean local field `K` with its given valuative
relation and compatible topology, a finite-dimensional central division
`K`-algebra `D`, and a finite-dimensional field extension `L` with an actual
`K`-algebra embedding `ι : L →ₐ[K] D`. The carriers `K` and `D` have a common
arbitrary universe and `L` has an independent universe. The characteristic
is unrestricted.

The premises for `ι` are surjectivity of `localDivisionSubfieldResidueMap K D ι`
and `Module.finrank K L = CentralSimple.reducedDegree K D`. The residue map is
induced by the original integer inclusion into the division algebra. The
conclusion is `Algebra.Etale 𝒪[K] w.integer`, where
`w = localDivisionSubfieldValuation K D ι`. Its algebra structure is
`localDivisionSubfieldIntegerAlgebra K D ι`, induced by the original integral
scalar map `localDivisionSubfieldBaseIntegerMap`. The theorem
`localDivisionSubfieldInteger_finite` already proves finiteness of this algebra
as a module. Integral étaleness is the proof target of this pair.

The degree hypothesis uses the reduced degree because
`localDivisionResidue_finrank_eq_reducedDegree` computes that dimension for
the actual division residue field over `𝓀[K]`. The residue inclusion is
injective by `localDivisionSubfieldResidueMap_injective`. Under the surjectivity
premise it identifies the two actual residue rings, and
`localDivisionSubfieldBaseIntegerMap_reduction` gives compatibility with the
original base residue scalars. These are the existing ingredients for the
comparison between the field and residue degrees.

Serre's *Local Fields*, Chapter I, §6, Proposition 15 and Corollaries 1–2,
and Proposition 16 (printed pp. 18–19), give the classical DVR comparison.
A monic polynomial with irreducible reduction presents the integer ring in
its fraction field, and separable reduction gives an unramified extension.
Proposition 16 recovers such a presentation for a DVR integral closure
whose residue extension is simple of the full field degree. Here the target
specifies the restriction of the division valuation and the map induced by
`ι`. A proof via Serre's presentation must identify the polynomial algebra
with this specific integer algebra and establish Mathlib's `Algebra.Etale`
for it. The original residue generator and the simple-root lift within the
specified `L` are available from `exists_localDivisionResidue_generator`
and `localDivisionSubfield_lift_base_polynomial`.
